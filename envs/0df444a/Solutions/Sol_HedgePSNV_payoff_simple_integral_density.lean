-- Prove2me | solution 1 for HedgePSNV.payoff_simple_integral_density
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T22:36:26.074199+00:00
-- url     : https://prove2.me/submissions/cfcec2e2-521a-4955-adf5-acd087afc279

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model

set_option maxHeartbeats 2000000

set_option linter.all false
set_option Elab.async false
-- ===== ItoM1 =====

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ItoLib
open EthierKurtz

variable {Ω : Type*} {d : ℕ}

section BM
variable [MeasurableSpace Ω]

/-- The coordinates of a standard `d`-dimensional Brownian motion form one real Gaussian
process indexed by `time × coordinate`. -/
theorem stdBrownian_isGaussianProcess {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) :
    IsGaussianProcess (fun (p : ℝ≥0 × Fin d) ω => W p.1 ω p.2) P := by
  obtain ⟨_, _, hBM, hind⟩ := hW
  refine ⟨fun I => ?_⟩
  classical
  let I' : Finset ℝ≥0 := I.image Prod.fst
  let V : Fin d → Ω → (I' → ℝ) := fun i ω => fun t => W t ω i
  have hV : ∀ i, HasGaussianLaw (V i) P := fun i =>
    (hBM i).isGaussianProcess.hasGaussianLaw I'
  have hVind : iIndepFun V P :=
    hind.comp (fun _ (f : ℝ≥0 → ℝ) => fun t : I' => f t) (fun _ => by fun_prop)
  have hjoint := hVind.hasGaussianLaw hV
  let L0 : (Fin d → (I' → ℝ)) →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun x p => x p.1.2 ⟨p.1.1, Finset.mem_image_of_mem _ p.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have := hjoint.map (LinearMap.toContinuousLinearMap L0)
  have heq : (fun ω => I.restrict (fun p : ℝ≥0 × Fin d => W p.1 ω p.2)) =
      (LinearMap.toContinuousLinearMap L0) ∘ (fun ω x => V x ω) := by
    funext ω p; rfl
  rw [heq]; exact this

/-- The covariance of two coordinates of a standard Brownian motion. -/
theorem stdBrownian_cov {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (s t : ℝ≥0) (i j : Fin d) :
    cov[fun ω => W s ω i, fun ω => W t ω j; P] = if i = j then ((min s t : ℝ≥0) : ℝ) else 0 := by
  obtain ⟨hm, _, hBM, hind⟩ := hW
  split_ifs with hij
  · subst hij
    exact (hBM i).covariance_fun_eval s t
  · have h2 : IndepFun (fun ω => W s ω i) (fun ω => W t ω j) P := by
      have := hind.indepFun hij
      exact this.comp (φ := fun f : ℝ≥0 → ℝ => f s) (ψ := fun f : ℝ≥0 → ℝ => f t)
        (by fun_prop) (by fun_prop)
    have hP : IsProbabilityMeasure P := (hBM i).isGaussianProcess.isProbabilityMeasure
    exact h2.covariance_eq_zero ((hBM i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
      ((hBM j).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

theorem stdBrownian_coord_measurable {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (i : Fin d) : Measurable (fun ω => W t ω i) := by
  have := hW.1 t
  fun_prop

theorem stdBrownian_memLp_two {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (i : Fin d) : MemLp (fun ω => W t ω i) 2 P :=
  ((hW.2.2.1 i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

end BM

section AEC
variable {mΩ : MeasurableSpace Ω}

/-- The `P`-a.e. closure of a σ-algebra `G`: sets a.e. equal to a `G`-set (null sets taken
for the outer measure, so arbitrary subsets of null sets qualify). -/
@[instance_reducible]
def aeClosure (P : Measure Ω) (G : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' A := ∃ B, MeasurableSet[G] B ∧ A =ᵐ[P] B
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ G, EventuallyEq.rfl⟩
  measurableSet_compl A := fun ⟨B, hB, h⟩ => ⟨Bᶜ, hB.compl, h.compl⟩
  measurableSet_iUnion f hf := by
    choose B hB h using hf
    exact ⟨⋃ i, B i, MeasurableSet.iUnion hB, Filter.EventuallyEq.countable_iUnion h⟩

/-- Independence passes to the a.e. closure. -/
theorem indep_aeClosure {P : Measure Ω} {G H : MeasurableSpace Ω} (h : Indep G H P) :
    Indep (aeClosure P G) H P := by
  rw [Indep_iff] at h ⊢
  rintro A C ⟨B, hB, hAB⟩ hC
  rw [measure_congr (hAB.inter (EventuallyEq.refl _ C)), measure_congr hAB]
  exact h B C hB hC

end AEC

section CP
variable [MeasurableSpace Ω]

end CP

section M2

variable [MeasurableSpace Ω]

end M2

section M3
variable [MeasurableSpace Ω]

end M3

section M4
variable [MeasurableSpace Ω]

end M4


section StopCoef

end StopCoef

section M5
variable [MeasurableSpace Ω]

end M5


section M5b

end M5b

section M5c
variable [MeasurableSpace Ω]

end M5c


section M6refine

end M6refine


section M6osc

/-- The dyadic time `j t / 2^N`. -/
noncomputable def dyTime (t : ℝ≥0) (N j : ℕ) : ℝ≥0 := (j : ℝ≥0) * t / (2 : ℝ≥0) ^ N

end M6osc


section M6cauchy
variable [MeasurableSpace Ω]

end M6cauchy


section M6limit
variable [MeasurableSpace Ω]

end M6limit


section M6trunc

end M6trunc

section M6exist
variable [MeasurableSpace Ω]

end M6exist


section M7grid

end M7grid

section M7zero
variable [MeasurableSpace Ω]

end M7zero


section M7qv
variable [MeasurableSpace Ω]

end M7qv

section M7c
variable [MeasurableSpace Ω]

end M7c

section M8a
variable [MeasurableSpace Ω]

end M8a

section M8b
variable [MeasurableSpace Ω]

end M8b

section M8c
variable [MeasurableSpace Ω]

end M8c

section M8d
variable [MeasurableSpace Ω]

end M8d

section M8e
variable [MeasurableSpace Ω]

end M8e


section M8f
variable [MeasurableSpace Ω]

end M8f


section M8f2
variable [MeasurableSpace Ω]

end M8f2


section M8f3
variable [MeasurableSpace Ω]

end M8f3


section M8gTaylor
open Set

end M8gTaylor

section M8g
variable [MeasurableSpace Ω]

end M8g


section M8g2

end M8g2


section M8g3
variable [MeasurableSpace Ω]

end M8g3

section M8g4
variable [MeasurableSpace Ω]

end M8g4

section M8g5
variable [MeasurableSpace Ω]

end M8g5

section M9a
variable [MeasurableSpace Ω]

end M9a


section M9c

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF

end M9cF


section M9c2

end M9c2


section M9d

end M9d


section M9d2

end M9d2



section M9e1

end M9e1


section M9e2

end M9e2


end ItoLib

open EthierKurtz in



set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcBr

open HedgePSNV EthierKurtz

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma pair_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) :
    Measurable (fun ω => (M.B t ω, M.Bt t ω)) := by
  have h1 : MeasurableSpace.comap (fun ω => (M.B t ω, M.Bt t ω)) inferInstance ≤ M.F t := by
    rw [hM.filtF t]
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le (f := fun s (_ : s ≤ t) =>
      MeasurableSpace.comap (fun ω => (M.B s ω, M.Bt s ω)) inferInstance) t le_rfl le_rfl
  exact Measurable.of_comap_le (h1.trans (M.F.le t))

lemma B_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (M.B t) :=
  measurable_fst.comp (pair_measurable M hM t)

lemma Bt_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (M.Bt t) :=
  measurable_snd.comp (pair_measurable M hM t)

/-- The exceptional null set off which both Brownian paths are continuous. -/
def Nbad (M : Model p Ω) : Set Ω :=
  toMeasurable M.P {ω | ¬ (Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω))}

lemma Nbad_meas (M : Model p Ω) : MeasurableSet (Nbad M) := measurableSet_toMeasurable _ _

lemma Nbad_null (M : Model p Ω) (hM : M.Standing) : M.P (Nbad M) = 0 := by
  rw [Nbad, measure_toMeasurable]
  exact ae_iff.1 (hM.brownB.cont.and hM.brownBt.cont)

lemma not_Nbad (M : Model p Ω) {ω : Ω} (h : ω ∉ Nbad M) :
    Continuous (fun t => M.B t ω) ∧ Continuous (fun t => M.Bt t ω) := by
  by_contra h'
  exact h (subset_toMeasurable _ _ h')

lemma ae_not_Nbad (M : Model p Ω) (hM : M.Standing) : ∀ᵐ ω ∂M.P, ω ∉ Nbad M := by
  rw [ae_iff]; simpa using Nbad_null M hM

open Classical in
/-- The two coordinates, set to `0` on `Nbad`. -/
noncomputable def gB (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ Nbad M then 0 else M.B t ω

open Classical in
noncomputable def gBt (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ Nbad M then 0 else M.Bt t ω

/-- The standard 2-d Brownian motion `(B, B~)` with everywhere continuous paths. -/
noncomputable def W (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : SDEState 2 :=
  WithLp.toLp 2 ![gB M t ω, gBt M t ω]

@[simp] lemma W_zero (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : W M t ω 0 = gB M t ω := by
  simp [W]

@[simp] lemma W_one (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : W M t ω 1 = gBt M t ω := by
  simp [W]

lemma ae_W (M : Model p Ω) (hM : M.Standing) :
    ∀ᵐ ω ∂M.P, ∀ t, W M t ω 0 = M.B t ω ∧ W M t ω 1 = M.Bt t ω := by
  filter_upwards [ae_not_Nbad M hM] with ω hω t
  simp [gB, gBt, hω]

lemma gB_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (gB M t) :=
  Measurable.ite (Nbad_meas M) measurable_const (B_measurable M hM t)

lemma gBt_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (gBt M t) :=
  Measurable.ite (Nbad_meas M) measurable_const (Bt_measurable M hM t)

lemma W_measurable (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : Measurable (W M t) := by
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp ?_
  refine measurable_pi_lambda _ (fun i => ?_)
  fin_cases i
  · simpa using gB_measurable M hM t
  · simpa using gBt_measurable M hM t

lemma gB_cont (M : Model p Ω) (ω : Ω) : Continuous (fun t => gB M t ω) := by
  by_cases h : ω ∈ Nbad M
  · simp only [gB, h, if_true]; exact continuous_const
  · simp only [gB, h, if_false]; exact (not_Nbad M h).1

lemma gBt_cont (M : Model p Ω) (ω : Ω) : Continuous (fun t => gBt M t ω) := by
  by_cases h : ω ∈ Nbad M
  · simp only [gBt, h, if_true]; exact continuous_const
  · simp only [gBt, h, if_false]; exact (not_Nbad M h).2

lemma W_cont (M : Model p Ω) (ω : Ω) : Continuous (fun t => W M t ω) := by
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · simpa using gB_cont M ω
  · simpa using gBt_cont M ω

lemma gB_brownian (M : Model p Ω) (hM : M.Standing) : IsBrownianReal (gB M) M.P := by
  have hae : ∀ t, M.B t =ᵐ[M.P] gB M t := by
    intro t
    filter_upwards [ae_not_Nbad M hM] with ω hω
    simp [gB, hω]
  exact { toIsPreBrownianReal := hM.brownB.toIsPreBrownianReal.congr hae,
          cont := Eventually.of_forall fun ω => gB_cont M ω }

lemma gBt_brownian (M : Model p Ω) (hM : M.Standing) : IsBrownianReal (gBt M) M.P := by
  have hae : ∀ t, M.Bt t =ᵐ[M.P] gBt M t := by
    intro t
    filter_upwards [ae_not_Nbad M hM] with ω hω
    simp [gBt, hω]
  exact { toIsPreBrownianReal := hM.brownBt.toIsPreBrownianReal.congr hae,
          cont := Eventually.of_forall fun ω => gBt_cont M ω }

lemma gB_indep (M : Model p Ω) (hM : M.Standing) :
    IndepFun (fun ω t => gB M t ω) (fun ω t => gBt M t ω) M.P := by
  refine hM.indep.congr ?_ ?_
  · filter_upwards [ae_not_Nbad M hM] with ω hω
    funext t; simp [gB, hω]
  · filter_upwards [ae_not_Nbad M hM] with ω hω
    funext t; simp [gBt, hω]

lemma iIndepFun_fin_two {β : Type*} [MeasurableSpace β] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Fin 2 → Ω → β} (h : IndepFun (f 0) (f 1) μ) : iIndepFun f μ := by
  have hcases : ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = Finset.univ := by decide
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hS
  rcases hcases S with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · have h0 := hS 0 (by simp)
    have h1 := hS 1 (by simp)
    rw [indepFun_iff_measure_inter_preimage_eq_mul] at h
    have := h _ _ h0 h1
    have hI : (⋂ i, f i ⁻¹' sets i) = f 0 ⁻¹' sets 0 ∩ f 1 ⁻¹' sets 1 := by
      ext ω; simp [Fin.forall_fin_two]
    simpa [Fin.prod_univ_two, hI] using this

lemma isStandardBrownian (M : Model p Ω) (hM : M.Standing) : IsStandardBrownian M.P (W M) := by
  refine ⟨W_measurable M hM, W_cont M, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa using gB_brownian M hM
    · simpa using gBt_brownian M hM
  · have := hM.prob
    apply iIndepFun_fin_two
    simpa using gB_indep M hM

end StochCalcBr


set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace StochCalcD1a

variable {Ω : Type*} [MeasurableSpace Ω]

end StochCalcD1a


namespace StochCalcD1aW

open HedgePSNV EthierKurtz StochCalcBr

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma G_le_F (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : M.G t ≤ M.F t := by
  rw [hM.filtG t, hM.filtF t]
  refine sup_le_sup_right (iSup₂_mono fun s _ => ?_) _
  have h : M.B s = Prod.fst ∘ (fun ω => (M.B s ω, M.Bt s ω)) := rfl
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_fst.comap_le

end StochCalcD1aW


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcL2M

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}




end StochCalcL2M


namespace StochCalcD1b

open HedgePSNV EthierKurtz StochCalcBr StochCalcL2M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcD1b


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology

namespace StochCalcIndep

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-- Index set of the "past of coordinate `j`, everything of the others". -/
abbrev PastIdx (d : ℕ) (t₀ : ℝ≥0) (j : Fin d) : Type := {q : ℝ≥0 × Fin d // q.1 ≤ t₀ ∨ q.2 ≠ j}

theorem indep_coord_shift {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t₀ : ℝ≥0) (j : Fin d) :
    IndepFun (fun ω (r : ℝ≥0) => W (t₀ + r) ω j - W t₀ ω j)
      (fun ω (q : PastIdx d t₀ j) => W q.1.1 ω q.1.2) P := by
  have hG := stdBrownian_isGaussianProcess hW
  have hP : IsProbabilityMeasure P := hG.isProbabilityMeasure
  have hm := stdBrownian_coord_measurable hW
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
    (X := fun (r : ℝ≥0) ω => W (t₀ + r) ω j - W t₀ ω j)
    (Y := fun (q : PastIdx d t₀ j) ω => W q.1.1 ω q.1.2)
  · apply hG.of_isGaussianProcess
    rintro (r | ⟨⟨t, i⟩, hq⟩)
    · exact ⟨{(t₀ + r, j), (t₀, j)},
        { toFun x := x ⟨(t₀ + r, j), by simp⟩ - x ⟨(t₀, j), by simp⟩
          map_add' x y := by simp; abel
          map_smul' c x := by simp; ring }, by simp⟩
    · exact ⟨{(t, i)},
        { toFun x := x ⟨(t, i), by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  · intro r; exact ((hm (t₀ + r) j).sub (hm t₀ j)).aemeasurable
  · intro q; exact (hm _ _).aemeasurable
  · rintro r ⟨⟨t, i⟩, hq⟩
    simp only
    rw [covariance_fun_sub_left (stdBrownian_memLp_two hW _ _) (stdBrownian_memLp_two hW _ _)
      (stdBrownian_memLp_two hW _ _), stdBrownian_cov hW, stdBrownian_cov hW]
    by_cases hij : j = i
    · subst hij
      rcases hq with ht | hne
      · have ht' : t ≤ t₀ := ht
        simp only [if_true]
        rw [min_eq_right (ht'.trans (le_add_right le_rfl)), min_eq_right ht', sub_self]
      · exact absurd rfl hne
    · simp [hij]

/-- σ-algebra form: the increments of coordinate `j` after `t₀` are independent of the
a.e.-closure of the past-of-`j`/all-of-the-others σ-algebra. -/
theorem indep_coord_shift_aeClosure {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t₀ : ℝ≥0) (j : Fin d) :
    Indep (aeClosure P (MeasurableSpace.comap
        (fun ω (q : PastIdx d t₀ j) => W q.1.1 ω q.1.2) inferInstance))
      (MeasurableSpace.comap (fun ω (r : ℝ≥0) => W (t₀ + r) ω j - W t₀ ω j) inferInstance) P :=
  indep_aeClosure ((IndepFun_iff_Indep _ _ _).1 (indep_coord_shift hW t₀ j)).symm

end StochCalcIndep


namespace StochCalcHs

open HedgePSNV EthierKurtz StochCalcBr StochCalcIndep ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Past of `B~` up to `c`, all of `B`. -/
noncomputable abbrev Ysig (M : Model p Ω) (c : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (q : PastIdx 2 c 1) => W M q.1.1 ω q.1.2) inferInstance

lemma coord_meas (M : Model p Ω) (c : ℝ≥0) (q : PastIdx 2 c 1) :
    Measurable[Ysig M c] (fun ω => W M q.1.1 ω q.1.2) := fun S hS =>
  ⟨(fun f : PastIdx 2 c 1 → ℝ => f q) ⁻¹' S, measurable_pi_apply q hS, rfl⟩

lemma B_aeC (M : Model p Ω) (hM : M.Standing) (c s : ℝ≥0) :
    MeasurableSpace.comap (M.B s) inferInstance ≤ aeClosure M.P (Ysig M c) := by
  rintro A ⟨S, hS, rfl⟩
  have hq : (s, (0 : Fin 2)).1 ≤ c ∨ (s, (0 : Fin 2)).2 ≠ 1 := Or.inr (show (0 : Fin 2) ≠ 1 by decide)
  refine ⟨(fun ω => W M s ω 0) ⁻¹' S, coord_meas M c ⟨(s, 0), hq⟩ hS, ?_⟩
  filter_upwards [ae_W M hM] with ω hω
  show (M.B s ω ∈ S) = (W M s ω 0 ∈ S)
  rw [(hω s).1]

lemma pair_aeC (M : Model p Ω) (hM : M.Standing) (c s : ℝ≥0) (hs : s ≤ c) :
    MeasurableSpace.comap (fun ω => (M.B s ω, M.Bt s ω)) inferInstance ≤
      aeClosure M.P (Ysig M c) := by
  rintro A ⟨S, hS, rfl⟩
  have hq0 : (s, (0 : Fin 2)).1 ≤ c ∨ (s, (0 : Fin 2)).2 ≠ 1 := Or.inr (show (0 : Fin 2) ≠ 1 by decide)
  have hq1 : (s, (1 : Fin 2)).1 ≤ c ∨ (s, (1 : Fin 2)).2 ≠ 1 := Or.inl hs
  have hm : Measurable[Ysig M c] (fun ω => (W M s ω 0, W M s ω 1)) :=
    (coord_meas M c ⟨(s, 0), hq0⟩).prodMk (coord_meas M c ⟨(s, 1), hq1⟩)
  refine ⟨(fun ω => (W M s ω 0, W M s ω 1)) ⁻¹' S, hm hS, ?_⟩
  filter_upwards [ae_W M hM] with ω hω
  show ((M.B s ω, M.Bt s ω) ∈ S) = ((W M s ω 0, W M s ω 1) ∈ S)
  rw [(hω s).1, (hω s).2]

lemma null_aeC (M : Model p Ω) (c : ℝ≥0) :
    MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet N ∧ M.P N = 0} ≤
      aeClosure M.P (Ysig M c) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro N ⟨-, hN0⟩
  exact ⟨∅, @MeasurableSet.empty Ω (Ysig M c), ae_eq_empty.2 hN0⟩

theorem FG_le (M : Model p Ω) (hM : M.Standing) (c T' : ℝ≥0) :
    M.F c ⊔ M.G T' ≤ aeClosure M.P (Ysig M c) := by
  refine sup_le ?_ ?_
  · rw [hM.filtF c]
    exact sup_le (iSup₂_le fun s hs => pair_aeC M hM c s hs) (null_aeC M c)
  · rw [hM.filtG T']
    exact sup_le (iSup₂_le fun s _ => B_aeC M hM c s) (null_aeC M c)

/-- The `B~` increments after `c` are independent of `F_c ⊔ G_T'`. -/
theorem indep_Bt_incr (M : Model p Ω) (hM : M.Standing) (c T' : ℝ≥0) :
    Indep (M.F c ⊔ M.G T')
      (MeasurableSpace.comap (fun ω (r : ℝ≥0) => W M (c + r) ω 1 - W M c ω 1) inferInstance)
      M.P :=
  indep_of_indep_of_le_left (indep_coord_shift_aeClosure (isStandardBrownian M hM) c 1)
    (FG_le M hM c T')

end StochCalcHs


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcGauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : Ω → ℝ} {v : ℝ≥0}

lemma integrable_exp_mul (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * ξ ω)) P := by
  have h := integrable_exp_mul_gaussianReal (μ := 0) (v := v) c
  rw [← hξ.map_eq] at h
  exact (integrable_map_measure h.aestronglyMeasurable hm.aemeasurable).1 h

lemma integrable_exp_abs (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * |ξ ω|)) P := by
  refine Integrable.mono' ((integrable_exp_mul hm hξ c).add (integrable_exp_mul hm hξ (-c)))
    (by fun_prop) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply]
  rcases le_total 0 (ξ ω) with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-c * ξ ω)]
  · rw [abs_of_nonpos h]
    have : c * -ξ ω = -c * ξ ω := by ring
    rw [this]; linarith [Real.exp_pos (c * ξ ω)]

/-- The dominating function of the difference quotients. -/
noncomputable def G (ξ : Ω → ℝ) (v : ℝ≥0) (ω : Ω) : ℝ :=
  (|ξ ω| + v) * Real.exp (|ξ ω| + v)

lemma memLp_G (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) :
    MemLp (G ξ v) 2 P := by
  have hmeas : Measurable (G ξ v) := by unfold G; fun_prop
  refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 ?_
  have hint : Integrable (fun ω => 2 * Real.exp (3 * (v : ℝ)) * Real.exp (3 * |ξ ω|)) P :=
    (integrable_exp_abs hm hξ 3).const_mul _
  refine Integrable.mono' hint (by fun_prop) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  set y := |ξ ω| + (v : ℝ) with hy
  have hy0 : 0 ≤ y := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy0
  have hG : G ξ v ω ^ 2 = y ^ 2 * Real.exp (2 * y) := by
    rw [G, ← hy, mul_pow, sq (Real.exp y), ← Real.exp_add, two_mul]
  have he : 2 * Real.exp (3 * (v : ℝ)) * Real.exp (3 * |ξ ω|) = 2 * Real.exp (3 * y) := by
    rw [mul_assoc, ← Real.exp_add, hy]; ring_nf
  rw [hG, he]
  have h3 : Real.exp (3 * y) = Real.exp y * Real.exp (2 * y) := by
    rw [← Real.exp_add]; ring_nf
  rw [h3]
  have hpos := Real.exp_pos (2 * y)
  nlinarith [Real.exp_pos y]

lemma memLp_xi (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) : MemLp ξ 2 P := by
  refine (memLp_G hm hξ).mono hm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  have h1 : |ξ ω| ≤ |ξ ω| + v := le_add_of_nonneg_right v.2
  have h2 : 1 ≤ Real.exp (|ξ ω| + v) := Real.one_le_exp (by positivity)
  have h3 : 0 ≤ G ξ v ω := by unfold G; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h3]
  unfold G
  have h4 : (0 : ℝ) ≤ |ξ ω| + v := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 h4]

end StochCalcGauss


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcTilt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end StochCalcTilt

namespace StochCalcTiltM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `B~` increment on `[u, w]`. -/
noncomputable def ξ (M : Model p Ω) (u w : ℝ≥0) (ω : Ω) : ℝ := M.Bt w ω - M.Bt u ω

/-- Its variance. -/
noncomputable def V (u w : ℝ≥0) : ℝ≥0 := nndist (w : ℝ) (u : ℝ)

lemma V_eq {u w : ℝ≥0} (h : u ≤ w) : (V u w : ℝ) = (w : ℝ) - u := by
  rw [V, coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast h))]

lemma ξ_meas (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) : Measurable (ξ M u w) :=
  (Bt_measurable M hM w).sub (Bt_measurable M hM u)

lemma ξ_law (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) :
    HasLaw (ξ M u w) (gaussianReal 0 (V u w)) M.P :=
  hM.brownBt.hasLaw_sub w u

lemma Bt_measF (M : Model p Ω) (hM : M.Standing) {r s : ℝ≥0} (hr : r ≤ s) :
    Measurable[M.F s] (M.Bt r) := by
  have h : MeasurableSpace.comap (fun ω => (M.B r ω, M.Bt r ω)) inferInstance ≤ M.F s := by
    rw [hM.filtF s]
    exact le_sup_of_le_left (le_iSup₂_of_le r hr le_rfl)
  exact measurable_snd.comp (Measurable.of_comap_le h)

end StochCalcTiltM

namespace StochCalcOrth

open HedgePSNV EthierKurtz StochCalcBr StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcOrth


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcStein

/-- `m1 ⊥ m2` and `(m1 ⊔ m2) ⊥ m3` give `m1 ⊥ (m2 ⊔ m3)`. -/
lemma indep_sup_of_triple {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (m1 m2 m3 : MeasurableSpace Ω) (h1 : m1 ≤ mΩ) (h2 : m2 ≤ mΩ)
    (h3 : m3 ≤ mΩ) (hAi : Indep m2 m1 P) (hBi : Indep (m1 ⊔ m2) m3 P) :
    Indep m1 (m2 ⊔ m3) P := by
  rw [Indep_iff] at hAi hBi
  refine IndepSets.indep (_mΩ := mΩ) (p1 := {s | MeasurableSet[m1] s})
    (p2 := {s | ∃ B C, MeasurableSet[m2] B ∧ MeasurableSet[m3] C ∧ s = B ∩ C}) h1 (sup_le h2 h3)
    (@MeasurableSpace.isPiSystem_measurableSet Ω m1) ?_ (@MeasurableSpace.generateFrom_measurableSet Ω m1).symm
    ?_ ?_
  · rintro _ ⟨B, C, hB, hC, rfl⟩ _ ⟨B', C', hB', hC', rfl⟩ _
    exact ⟨B ∩ B', C ∩ C', MeasurableSet.inter (m := m2) hB hB',
      MeasurableSet.inter (m := m3) hC hC', Set.inter_inter_inter_comm B C B' C'⟩
  · apply le_antisymm
    · refine sup_le (fun B hB => MeasurableSpace.measurableSet_generateFrom
        ⟨B, Set.univ, hB, @MeasurableSet.univ Ω m3, (Set.inter_univ B).symm⟩)
        (fun C hC => MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, C, @MeasurableSet.univ Ω m2, hC, (Set.univ_inter C).symm⟩)
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨B, C, hB, hC, rfl⟩
      exact MeasurableSet.inter (m := m2 ⊔ m3) (le_sup_left (a := m2) (b := m3) B hB)
        (le_sup_right (a := m2) (b := m3) C hC)
  · rw [IndepSets_iff]
    rintro A _ hA' ⟨B, C, hB, hC, rfl⟩
    have e1 := hBi (A ∩ B) C (MeasurableSet.inter (m := m1 ⊔ m2)
      (le_sup_left (a := m1) (b := m2) A hA') (le_sup_right (a := m1) (b := m2) B hB)) hC
    have e2 := hBi B C (le_sup_right (a := m1) (b := m2) B hB) hC
    have e3 := hAi B A hB hA'
    rw [← Set.inter_assoc, e1, e2, Set.inter_comm A B, e3]
    ring

/-- Independence from `comap f` transfers along an a.e. equality of `f`. -/
lemma indep_comap_congr {Ω β : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    {P : Measure Ω} (m : MeasurableSpace Ω) {f f' : Ω → β} (hf : f =ᵐ[P] f')
    (h : Indep m (MeasurableSpace.comap f' mβ) P) : Indep m (MeasurableSpace.comap f mβ) P := by
  rw [Indep_iff] at h ⊢
  rintro t1 _ ht1 ⟨S, hS, rfl⟩
  have e : (f ⁻¹' S : Set Ω) =ᵐ[P] f' ⁻¹' S := hf.fun_comp (fun y => y ∈ S)
  rw [measure_congr ((ae_eq_refl t1).inter e), measure_congr e]
  exact h t1 _ ht1 ⟨S, hS, rfl⟩

end StochCalcStein

namespace StochCalcSteinM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcTiltM StochCalcStein

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma ξ_ae (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) :
    ξ M u w =ᵐ[M.P] fun ω => gBt M w ω - gBt M u ω := by
  filter_upwards [ae_W M hM] with ω hω
  simp only [ξ, ← (hω w).2, ← (hω u).2, W_one]

lemma ξ_measF (M : Model p Ω) (hM : M.Standing) {u w : ℝ≥0} (huw : u ≤ w) :
    Measurable[M.F w] (ξ M u w) := by
  unfold ξ
  exact (Bt_measF M hM le_rfl).sub (Bt_measF M hM huw)

/-- `B~_w - B~_u` is independent of `F_u ⊔ G_T'`. -/
lemma indep_ξ (M : Model p Ω) (hM : M.Standing) {u w : ℝ≥0} (huw : u ≤ w) (T' : ℝ≥0) :
    Indep (M.F u ⊔ M.G T') (MeasurableSpace.comap (ξ M u w) inferInstance) M.P := by
  refine indep_comap_congr _ (ξ_ae M hM u w) ?_
  refine indep_of_indep_of_le_right (indep_Bt_incr M hM u T') ?_
  set inc : Ω → ℝ≥0 → ℝ := fun ω r => W M (u + r) ω 1 - W M u ω 1 with hinc
  have heq : (fun ω => gBt M w ω - gBt M u ω) = (fun f : ℝ≥0 → ℝ => f (w - u)) ∘ inc := by
    funext ω
    simp only [Function.comp, hinc, W_one, add_tsub_cancel_of_le huw]
  rw [heq]
  exact ((measurable_pi_apply _).comp (comap_measurable inc)).comap_le

end StochCalcSteinM


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6


set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integral_gauss {ξ : Ω → ℝ} {v : ℝ≥0} (hξ : HasLaw ξ (gaussianReal 0 v) P) :
    ∫ ω, ξ ω ∂P = 0 := by
  rw [hξ.integral_eq, integral_id_gaussianReal]

lemma memLp_bdd_mul {Y ξ : Ω → ℝ} (hξ : MemLp ξ 2 P) (hY : AEStronglyMeasurable Y P) {C : ℝ}
    (hYb : ∀ ω, |Y ω| ≤ C) : MemLp (fun ω => Y ω * ξ ω) 2 P := by
  refine (hξ.const_mul C).of_le (hY.mul hξ.aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hYb ω).trans (le_abs_self C)) (abs_nonneg _)

variable (m : ℕ → MeasurableSpace Ω) (ξ Y : ℕ → Ω → ℝ)

end StochCalcP6S


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedgeDeg

open HedgePSNV

variable {p : Params} {Ω : Type*} [MeasurableSpace Ω]

lemma H_memLp (M : Model p Ω) (hM : M.Standing)
    (hL2 : M.NegPartL2) (P R : ℝ) : MemLp (M.H P R) 2 M.P := by
  have := hM.prob
  have hCm : StronglyMeasurable (M.C p.T) := (hM.C_adapted p.T).mono (M.G.le p.T)
  have hBlaw : HasLaw (M.Bt p.T) (gaussianReal 0 p.T) M.P :=
    hM.brownBt.toIsPreBrownianReal.hasLaw_eval p.T
  have hBm : AEMeasurable (M.Bt p.T) M.P := hBlaw.aemeasurable
  have hB2 : MemLp (M.Bt p.T) 2 M.P := by
    have h := memLp_id_gaussianReal' (μ := 0) (v := p.T) 2 (by simp)
    rw [← hBlaw.map_eq] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id hBm).1 h
  have hg : MemLp (fun ω => |R| + max (-(M.C p.T ω)) 0 + |p.σt| * |M.Bt p.T ω|) 2 M.P :=
    ((memLp_const |R|).add hL2).add (hB2.abs.const_mul |p.σt|)
  have hmeas : AEStronglyMeasurable
      (fun ω => max (R - (M.C p.T ω + p.σt * M.Bt p.T ω)) 0) M.P := by
    have hCa : AEMeasurable (M.C p.T) M.P := hCm.measurable.aemeasurable
    exact (by fun_prop : AEMeasurable
      (fun ω => max (R - (M.C p.T ω + p.σt * M.Bt p.T ω)) 0) M.P).aestronglyMeasurable
  have hmax : MemLp (fun ω => max (R - (M.C p.T ω + p.σt * M.Bt p.T ω)) 0) 2 M.P := by
    refine hg.mono' hmeas (Filter.Eventually.of_forall fun ω => ?_)
    have h1 : -(p.σt * M.Bt p.T ω) ≤ |p.σt| * |M.Bt p.T ω| :=
      (neg_le_abs _).trans_eq (abs_mul _ _)
    have h2 := le_abs_self R
    have h3 := le_max_left (-(M.C p.T ω)) 0
    have h4 : (0 : ℝ) ≤ max (-(M.C p.T ω)) 0 := le_max_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (by positivity)
  have hH : M.H P R = fun ω => (P - p.c) * (R - p.b * P) -
      (P - p.s) * max (R - (M.C p.T ω + p.σt * M.Bt p.T ω)) 0 := by
    funext ω; rfl
  rw [hH]
  exact (memLp_const _).sub (hmax.const_mul (P - p.s))

end StochCalcHedgeDeg


namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg StochCalcGauss

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Grid points `t_k = k T / n`. -/
noncomputable def gr (p : Params) (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) * (p.T / n)

lemma gr_mono (p : Params) (n : ℕ) : Monotone (gr p n) := fun i j hij => by
  unfold gr; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

lemma gr_le_T (p : Params) {n k : ℕ} (hk : k ≤ n) : gr p n k ≤ p.T := by
  unfold gr
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn : (0 : ℝ≥0) < n := by exact_mod_cast h
    calc (k : ℝ≥0) * (p.T / n) ≤ n * (p.T / n) := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
      _ = p.T := by field_simp

lemma V_gr (p : Params) (n k : ℕ) : (V (gr p n k) (gr p n (k + 1)) : ℝ) = (p.T : ℝ) / n := by
  rw [V_eq (gr_mono p n k.le_succ)]
  unfold gr; push_cast; ring

end StochCalcD2


namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcD2

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcP6

end StochCalcP6

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (m : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ)

end StochCalcP6S

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcD3

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `B`-increment. -/
noncomputable def dB (M : Model p Ω) (u w : ℝ≥0) (ω : Ω) : ℝ := M.B w ω - M.B u ω

lemma gr_mul (p : Params) {m : ℕ} (hm : 0 < m) (n k : ℕ) : gr p (n * m) (k * m) = gr p n k := by
  unfold gr
  have hm' : (m : ℝ≥0) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast h.ne'
    field_simp

/-- Exact refinement of a grid sum from mesh `T/n` to mesh `T/(n m)`. -/
lemma refine_sum (p : Params) (W : ℝ≥0 → Ω → ℝ) (Z : ℕ → Ω → ℝ) {m : ℕ} (hm : 0 < m)
    (n : ℕ) (ω : Ω) : ∀ K : ℕ,
    ∑ k ∈ Finset.range K, Z k ω * (W (gr p n (k + 1)) ω - W (gr p n k) ω) =
      ∑ j ∈ Finset.range (K * m), Z (j / m) ω *
        (W (gr p (n * m) (j + 1)) ω - W (gr p (n * m) j) ω) := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, add_mul, one_mul, Finset.sum_range_add]
    beta_reduce
    congr 1
    have hdiv : ∀ i ∈ Finset.range m, (K * m + i) / m = K := fun i hi => by
      rw [add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt (Finset.mem_range.1 hi),
        zero_add]
    have hblk : ∑ i ∈ Finset.range m, Z ((K * m + i) / m) ω *
        (W (gr p (n * m) (K * m + i + 1)) ω - W (gr p (n * m) (K * m + i)) ω) =
        Z K ω * ∑ i ∈ Finset.range m,
        (W (gr p (n * m) (K * m + i + 1)) ω - W (gr p (n * m) (K * m + i)) ω) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i hi => by rw [hdiv i hi]
    rw [hblk]
    congr 1
    have htel := Finset.sum_range_sub (fun i => W (gr p (n * m) (K * m + i)) ω) m
    simp only [add_zero] at htel
    rw [← gr_mul p hm n K, ← gr_mul p hm n (K + 1), add_mul, one_mul, ← htel]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_assoc]

lemma dB_law (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) :
    HasLaw (dB M u w) (gaussianReal 0 (V u w)) M.P :=
  hM.brownB.hasLaw_sub w u

lemma dB_meas (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) : Measurable (dB M u w) :=
  (B_measurable M hM w).sub (B_measurable M hM u)

lemma sum_memLp (M : Model p Ω) (hM : M.Standing) (n : ℕ) (Y : ℕ → Ω → ℝ) (C : ℝ)
    (hYm : ∀ k, StronglyMeasurable[M.F (gr p n k)] (Y k)) (hYb : ∀ k ω, |Y k ω| ≤ C)
    (G : ℝ≥0 → ℝ≥0 → Ω → ℝ) (hG : ∀ u w, MemLp (G u w) 2 M.P) (K : ℕ) :
    MemLp (fun ω => ∑ k ∈ Finset.range K, Y k ω * G (gr p n k) (gr p n (k + 1)) ω) 2 M.P := by
  have := hM.prob
  induction K with
  | zero => simpa using (memLp_const (0 : ℝ) : MemLp (fun _ : Ω => (0 : ℝ)) 2 M.P)
  | succ K ih =>
    simp_rw [Finset.sum_range_succ]
    exact ih.add (StochCalcP6S.memLp_bdd_mul (hG _ _)
      (((hYm K).mono (M.F.le _)).aestronglyMeasurable) (hYb K))

end StochCalcD3


set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace StochCalcR1

lemma norm_Z_le (t : ℝ) :
    ‖Complex.exp (Complex.I * t) - 1 - Complex.I * t‖ ≤ 2 * t ^ 2 := by
  have hn : ‖Complex.I * (t : ℂ)‖ = |t| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt |t| 1 with h | h
  · have h1 := Complex.norm_exp_sub_one_sub_id_le (x := Complex.I * t) (by rw [hn]; exact h)
    rw [hn, sq_abs] at h1
    nlinarith [sq_nonneg t]
  · have h2 : ‖Complex.exp (Complex.I * t) - 1‖ ≤ |t| := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t)
      rwa [Real.norm_eq_abs] at this
    calc _ ≤ ‖Complex.exp (Complex.I * t) - 1‖ + ‖Complex.I * (t : ℂ)‖ := norm_sub_le _ _
      _ ≤ |t| + |t| := by rw [hn]; exact add_le_add h2 le_rfl
      _ ≤ 2 * t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]

lemma tel {R : Type*} [CommRing R] (g e : ℕ → R) (n : ℕ) :
    ∏ i ∈ range n, g i - ∏ i ∈ range n, e i =
      ∑ k ∈ range n, (∏ i ∈ range k, g i) * (g k - e k) * ∏ i ∈ Finset.Ico (k + 1) n, e i := by
  have key := Finset.sum_range_sub (fun k => (∏ i ∈ range k, g i) * ∏ i ∈ Finset.Ico k n, e i) n
  have hI : Finset.Ico 0 n = range n := by ext i; simp
  simp only [Finset.Ico_self, Finset.prod_empty, mul_one, Finset.range_zero, one_mul, hI] at key
  rw [← key]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < n := Finset.mem_range.1 hk
  simp only [Finset.prod_range_succ, Finset.prod_eq_prod_Ico_succ_bot hk']
  ring

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma memLp_bdd_mul {Y ξ : Ω → ℝ} (hξ : MemLp ξ 2 P) (hY : AEStronglyMeasurable Y P) {C : ℝ}
    (hYb : ∀ ω, |Y ω| ≤ C) : MemLp (fun ω => Y ω * ξ ω) 2 P := by
  refine (hξ.const_mul C).of_le (hY.mul hξ.aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hYb ω).trans (le_abs_self C)) (abs_nonneg _)

/-- Orthogonality of martingale-difference sums. -/
theorem orth_sum (m : ℕ → MeasurableSpace Ω) (hmono : Monotone m)
    (w : ℕ → Ω → ℝ) (hwm : ∀ k, Measurable[m (k + 1)] (w k)) (hw2 : ∀ k, MemLp (w k) 2 P)
    (hperp : ∀ k (S : Ω → ℝ), Measurable[m k] S → MemLp S 2 P → ∫ ω, S ω * w k ω ∂P = 0)
    (n : ℕ) :
    Measurable[m n] (fun ω => ∑ k ∈ range n, w k ω) ∧
    MemLp (fun ω => ∑ k ∈ range n, w k ω) 2 P ∧
    ∫ ω, (∑ k ∈ range n, w k ω) ^ 2 ∂P = ∑ k ∈ range n, ∫ ω, w k ω ^ 2 ∂P := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_zero]
    exact ⟨measurable_const, memLp_const 0, by simp⟩
  | succ n ih =>
    obtain ⟨hSm, hS2, hSsq⟩ := ih
    simp only [Finset.sum_range_succ]
    refine ⟨(hSm.mono (hmono n.le_succ) le_rfl).add (hwm n), hS2.add (hw2 n), ?_⟩
    have hc := hperp n _ hSm hS2
    have i1 : Integrable (fun ω => (∑ k ∈ range n, w k ω) ^ 2) P := hS2.integrable_sq
    have i2 : Integrable (fun ω => 2 * ((∑ k ∈ range n, w k ω) * w n ω)) P :=
      (hS2.integrable_mul (hw2 n)).const_mul 2
    have i3 : Integrable (fun ω => w n ω ^ 2) P := (hw2 n).integrable_sq
    have hcongr : (fun ω => (∑ k ∈ range n, w k ω + w n ω) ^ 2) = fun ω =>
        ((∑ k ∈ range n, w k ω) ^ 2 + 2 * ((∑ k ∈ range n, w k ω) * w n ω)) + w n ω ^ 2 := by
      funext ω; ring
    have i12 : Integrable (fun ω => (∑ k ∈ range n, w k ω) ^ 2 +
        2 * ((∑ k ∈ range n, w k ω) * w n ω)) P := i1.add i2
    rw [hcongr, integral_add i12 i3, integral_add i1 i2, integral_const_mul, hc, hSsq]
    ring

lemma perp_indep (m G : MeasurableSpace Ω) (hm : m ≤ mΩ) (hG : G ≤ mΩ) (hind : Indep m G P)
    (Y u : Ω → ℝ) (hY : Measurable[m] Y) (hu : Measurable[G] u) (hu0 : ∫ ω, u ω ∂P = 0)
    (S : Ω → ℝ) (hS : Measurable[m] S) :
    ∫ ω, S ω * (Y ω * u ω) ∂P = 0 := by
  have hSY : Measurable[m] (fun ω => S ω * Y ω) := hS.mul hY
  have hind' : IndepFun (fun ω => S ω * Y ω) u P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hSY.comap_le) hu.comap_le
  have e : (fun ω => S ω * (Y ω * u ω)) = fun ω => (S ω * Y ω) * u ω := by funext ω; ring
  rw [e, hind'.integral_fun_mul_eq_mul_integral (hSY.mono hm le_rfl).aestronglyMeasurable
    (hu.mono hG le_rfl).aestronglyMeasurable, hu0, mul_zero]

lemma sq_int_le (x : Ω → ℝ) (hx2 : MemLp x 2 P) (hx4 : Integrable (fun ω => x ω ^ 4) P) :
    (∫ ω, x ω ^ 2 ∂P) ^ 2 ≤ ∫ ω, x ω ^ 4 ∂P := by
  set a := ∫ ω, x ω ^ 2 ∂P with ha
  have i2 := hx2.integrable_sq
  have h0 : 0 ≤ ∫ ω, (x ω ^ 2 - a) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hc : (fun ω => (x ω ^ 2 - a) ^ 2) = fun ω => (x ω ^ 4 - (2 * a) * x ω ^ 2) + a ^ 2 := by
    funext ω; ring
  have i3 : Integrable (fun ω => 2 * a * x ω ^ 2) P := i2.const_mul _
  have i43 : Integrable (fun ω => x ω ^ 4 - 2 * a * x ω ^ 2) P := hx4.sub i3
  rw [hc, integral_add i43 (integrable_const _), integral_sub hx4 i3, integral_const_mul, integral_const] at h0
  simp only [probReal_univ, one_smul] at h0
  rw [← ha] at h0
  nlinarith

lemma eps_bound (x : Ω → ℝ) (hxm : Measurable x) (hx2 : MemLp x 2 P)
    (hx4 : Integrable (fun ω => x ω ^ 4) P) (hx0 : ∫ ω, x ω ∂P = 0) :
    ∫ ω, ‖Complex.exp (Complex.I * x ω) - (∫ ω', Complex.exp (Complex.I * x ω') ∂P) -
      Complex.I * x ω‖ ^ 2 ∂P ≤ 16 * ∫ ω, x ω ^ 4 ∂P := by
  set Z : Ω → ℂ := fun ω => Complex.exp (Complex.I * x ω) - 1 - Complex.I * x ω with hZ
  have hZm : Measurable Z := by fun_prop
  have hZb : ∀ ω, ‖Z ω‖ ≤ 2 * x ω ^ 2 := fun ω => norm_Z_le (x ω)
  have i2 := hx2.integrable_sq
  have hZi : Integrable Z P := (i2.const_mul 2).mono' hZm.aestronglyMeasurable (ae_of_all _ hZb)
  have hxi : Integrable (fun ω => Complex.I * (x ω : ℂ)) P :=
    (hx2.integrable one_le_two).ofReal.const_mul _
  have he : ∫ ω, Complex.exp (Complex.I * x ω) ∂P = (∫ ω, Z ω ∂P) + 1 := by
    have : (fun ω => Complex.exp (Complex.I * x ω)) = fun ω => (Z ω + 1) + Complex.I * x ω := by
      funext ω; simp only [hZ]; ring
    have hZ1 : Integrable (fun ω => Z ω + 1) P := hZi.add (integrable_const 1)
    rw [this, integral_add hZ1 hxi, integral_add hZi (integrable_const 1),
      integral_const_mul, integral_complex_ofReal, hx0]
    simp
  rw [he]
  set EZ := ∫ ω, Z ω ∂P with hEZdef
  have hpt : ∀ ω, ‖Complex.exp (Complex.I * x ω) - (EZ + 1) - Complex.I * x ω‖ ^ 2 ≤
      8 * x ω ^ 4 + 2 * ‖EZ‖ ^ 2 := by
    intro ω
    have h1 : Complex.exp (Complex.I * x ω) - (EZ + 1) - Complex.I * x ω = Z ω - EZ := by
      simp only [hZ]; ring
    rw [h1]
    have h2 := norm_sub_le (Z ω) EZ
    have h3 := hZb ω
    calc ‖Z ω - EZ‖ ^ 2 ≤ (‖Z ω‖ + ‖EZ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ ≤ 2 * ‖Z ω‖ ^ 2 + 2 * ‖EZ‖ ^ 2 := by nlinarith [sq_nonneg (‖Z ω‖ - ‖EZ‖)]
      _ ≤ 2 * (2 * x ω ^ 2) ^ 2 + 2 * ‖EZ‖ ^ 2 := by gcongr
      _ = 8 * x ω ^ 4 + 2 * ‖EZ‖ ^ 2 := by ring
  have hEZ : ‖EZ‖ ≤ 2 * ∫ ω, x ω ^ 2 ∂P := by
    calc ‖EZ‖ ≤ ∫ ω, ‖Z ω‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, 2 * x ω ^ 2 ∂P := integral_mono hZi.norm (i2.const_mul 2) hZb
      _ = 2 * ∫ ω, x ω ^ 2 ∂P := integral_const_mul _ _
  have hJ := sq_int_le x hx2 hx4
  have hEZ2 : ‖EZ‖ ^ 2 ≤ 4 * ∫ ω, x ω ^ 4 ∂P := by
    calc ‖EZ‖ ^ 2 ≤ (2 * ∫ ω, x ω ^ 2 ∂P) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hEZ 2
      _ = 4 * (∫ ω, x ω ^ 2 ∂P) ^ 2 := by ring
      _ ≤ 4 * ∫ ω, x ω ^ 4 ∂P := by linarith
  calc _ ≤ ∫ ω, (8 * x ω ^ 4 + 2 * ‖EZ‖ ^ 2) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
          ((hx4.const_mul 8).add (integrable_const _)) (ae_of_all _ hpt)
    _ = 8 * ∫ ω, x ω ^ 4 ∂P + 2 * ‖EZ‖ ^ 2 := by
        rw [integral_add (hx4.const_mul 8) (integrable_const _), integral_const_mul, integral_const]
        simp
    _ ≤ 16 * ∫ ω, x ω ^ 4 ∂P := by linarith

set_option maxHeartbeats 1000000 in
/-- Orthogonal sum bound: `E‖Σ A_k ε_k‖² ≤ n B`. -/
theorem sum_bound (m : ℕ → MeasurableSpace Ω) (hmono : Monotone m) (hle : ∀ k, m k ≤ mΩ)
    (x : ℕ → Ω → ℝ) (hxM : ∀ k, Measurable (x k))
    (hind : ∀ k, Indep (m k) (MeasurableSpace.comap (x k) inferInstance) P)
    (hx2 : ∀ k, MemLp (x k) 2 P) (A ε : ℕ → Ω → ℂ) (hAm : ∀ k, Measurable[m k] (A k))
    (hAn : ∀ k ω, ‖A k ω‖ ≤ 1)
    (hεc : ∀ k, Measurable[MeasurableSpace.comap (x k) inferInstance] (ε k))
    (hεm : ∀ k, Measurable[m (k + 1)] (ε k)) (hεb : ∀ k ω, ‖ε k ω‖ ≤ 2 + |x k ω|)
    (hε0 : ∀ k, ∫ ω, ε k ω ∂P = 0) (B : ℝ) (hB : ∀ k, ∫ ω, ‖ε k ω‖ ^ 2 ∂P ≤ B) (n : ℕ) :
    ∫ ω, ‖∑ k ∈ range n, A k ω * ε k ω‖ ^ 2 ∂P ≤ n * B := by
  have hB2 : ∀ k, MemLp (fun ω => (2 : ℝ) + |x k ω|) 2 P := fun k => by
    have h1 : MemLp (fun _ : Ω => (2 : ℝ)) 2 P := memLp_const _
    have h2 : MemLp (fun ω => |x k ω|) 2 P :=
      (hx2 k).of_le (continuous_abs.measurable.comp (hxM k)).aestronglyMeasurable
        (ae_of_all _ fun ω => by simp)
    exact h1.add h2
  have hεb' : ∀ k ω, ‖ε k ω‖ ≤ ‖(2 : ℝ) + |x k ω|‖ := fun k ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hεb k ω
  have hεM : ∀ k, Measurable (ε k) := fun k => (hεm k).mono (hle _) le_rfl
  have hε2 : ∀ k, MemLp (ε k) 2 P := fun k =>
    (hB2 k).of_le (hεM k).aestronglyMeasurable (ae_of_all _ (hεb' k))
  have hεre0 : ∀ k, ∫ ω, (ε k ω).re ∂P = 0 := fun k => by
    have h := integral_re ((hε2 k).integrable one_le_two)
    simp only [RCLike.re_to_complex] at h
    rw [h, hε0 k, Complex.zero_re]
  have hεim0 : ∀ k, ∫ ω, (ε k ω).im ∂P = 0 := fun k => by
    have h := integral_im ((hε2 k).integrable one_le_two)
    simp only [RCLike.im_to_complex] at h
    rw [h, hε0 k, Complex.zero_im]
  have hre2 : ∀ k, MemLp (fun ω => (ε k ω).re) 2 P := fun k =>
    (hB2 k).of_le (Complex.measurable_re.comp (hεM k)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hεb' k ω))
  have him2 : ∀ k, MemLp (fun ω => (ε k ω).im) 2 P := fun k =>
    (hB2 k).of_le (Complex.measurable_im.comp (hεM k)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact (Complex.abs_im_le_norm _).trans (hεb' k ω))
  have hAre : ∀ k, Measurable[m k] (fun ω => (A k ω).re) := fun k =>
    Complex.measurable_re.comp (hAm k)
  have hAim : ∀ k, Measurable[m k] (fun ω => (A k ω).im) := fun k =>
    Complex.measurable_im.comp (hAm k)
  have hAreb : ∀ k ω, |(A k ω).re| ≤ 1 := fun k ω => (Complex.abs_re_le_norm _).trans (hAn k ω)
  have hAimb : ∀ k ω, |(A k ω).im| ≤ 1 := fun k ω => (Complex.abs_im_le_norm _).trans (hAn k ω)
  have hreC : ∀ k, Measurable[MeasurableSpace.comap (x k) inferInstance]
      (fun ω => (ε k ω).re) := fun k => Complex.measurable_re.comp (hεc k)
  have himC : ∀ k, Measurable[MeasurableSpace.comap (x k) inferInstance]
      (fun ω => (ε k ω).im) := fun k => Complex.measurable_im.comp (hεc k)
  have hGle : ∀ k, MeasurableSpace.comap (x k) inferInstance ≤ mΩ := fun k => (hxM k).comap_le
  have hAre' : ∀ k, AEStronglyMeasurable (fun ω => (A k ω).re) P := fun k =>
    ((hAre k).mono (hle k) le_rfl).aestronglyMeasurable
  have hAim' : ∀ k, AEStronglyMeasurable (fun ω => (A k ω).im) P := fun k =>
    ((hAim k).mono (hle k) le_rfl).aestronglyMeasurable
  have m1 : ∀ k, MemLp (fun ω => (A k ω).re * (ε k ω).re) 2 P := fun k =>
    memLp_bdd_mul (hre2 k) (hAre' k) (hAreb k)
  have m2 : ∀ k, MemLp (fun ω => (A k ω).im * (ε k ω).im) 2 P := fun k =>
    memLp_bdd_mul (him2 k) (hAim' k) (hAimb k)
  have m3 : ∀ k, MemLp (fun ω => (A k ω).re * (ε k ω).im) 2 P := fun k =>
    memLp_bdd_mul (him2 k) (hAre' k) (hAreb k)
  have m4 : ∀ k, MemLp (fun ω => (A k ω).im * (ε k ω).re) 2 P := fun k =>
    memLp_bdd_mul (hre2 k) (hAim' k) (hAimb k)
  have m12 : ∀ k, MemLp (fun ω => (A k ω).re * (ε k ω).re - (A k ω).im * (ε k ω).im) 2 P :=
    fun k => (m1 k).sub (m2 k)
  have m34 : ∀ k, MemLp (fun ω => (A k ω).re * (ε k ω).im + (A k ω).im * (ε k ω).re) 2 P :=
    fun k => (m3 k).add (m4 k)
  have hmk : ∀ k, m k ≤ m (k + 1) := fun k => hmono k.le_succ
  have Or := orth_sum m hmono
    (fun k ω => (A k ω).re * (ε k ω).re - (A k ω).im * (ε k ω).im)
    (fun k => (((hAre k).mono (hmk k) le_rfl).mul (Complex.measurable_re.comp (hεm k))).sub
      (((hAim k).mono (hmk k) le_rfl).mul (Complex.measurable_im.comp (hεm k))))
    m12
    (fun k S hS hS2 => by
      have e1 : (fun ω => S ω * ((A k ω).re * (ε k ω).re - (A k ω).im * (ε k ω).im)) =
          fun ω => S ω * ((A k ω).re * (ε k ω).re) - S ω * ((A k ω).im * (ε k ω).im) := by
        funext ω; ring
      have j1 : Integrable (fun ω => S ω * ((A k ω).re * (ε k ω).re)) P :=
        hS2.integrable_mul (m1 k)
      have j2 : Integrable (fun ω => S ω * ((A k ω).im * (ε k ω).im)) P :=
        hS2.integrable_mul (m2 k)
      rw [e1, integral_sub j1 j2,
        perp_indep _ _ (hle k) (hGle k) (hind k) _ _ (hAre k) (hreC k) (hεre0 k) S hS,
        perp_indep _ _ (hle k) (hGle k) (hind k) _ _ (hAim k) (himC k) (hεim0 k) S hS, sub_zero])
    n
  have Oi := orth_sum m hmono
    (fun k ω => (A k ω).re * (ε k ω).im + (A k ω).im * (ε k ω).re)
    (fun k => (((hAre k).mono (hmk k) le_rfl).mul (Complex.measurable_im.comp (hεm k))).add
      (((hAim k).mono (hmk k) le_rfl).mul (Complex.measurable_re.comp (hεm k))))
    m34
    (fun k S hS hS2 => by
      have e1 : (fun ω => S ω * ((A k ω).re * (ε k ω).im + (A k ω).im * (ε k ω).re)) =
          fun ω => S ω * ((A k ω).re * (ε k ω).im) + S ω * ((A k ω).im * (ε k ω).re) := by
        funext ω; ring
      have j1 : Integrable (fun ω => S ω * ((A k ω).re * (ε k ω).im)) P :=
        hS2.integrable_mul (m3 k)
      have j2 : Integrable (fun ω => S ω * ((A k ω).im * (ε k ω).re)) P :=
        hS2.integrable_mul (m4 k)
      rw [e1, integral_add j1 j2,
        perp_indep _ _ (hle k) (hGle k) (hind k) _ _ (hAre k) (himC k) (hεim0 k) S hS,
        perp_indep _ _ (hle k) (hGle k) (hind k) _ _ (hAim k) (hreC k) (hεre0 k) S hS, add_zero])
    n
  have hsq : ∀ ω, ‖∑ k ∈ range n, A k ω * ε k ω‖ ^ 2 =
      (∑ k ∈ range n, ((A k ω).re * (ε k ω).re - (A k ω).im * (ε k ω).im)) ^ 2 +
      (∑ k ∈ range n, ((A k ω).re * (ε k ω).im + (A k ω).im * (ε k ω).re)) ^ 2 := fun ω => by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
    simp only [Complex.mul_re, Complex.mul_im]; ring
  have hI1 : Integrable (fun ω =>
      (∑ k ∈ range n, ((A k ω).re * (ε k ω).re - (A k ω).im * (ε k ω).im)) ^ 2) P :=
    Or.2.1.integrable_sq
  have hI2 : Integrable (fun ω =>
      (∑ k ∈ range n, ((A k ω).re * (ε k ω).im + (A k ω).im * (ε k ω).re)) ^ 2) P :=
    Oi.2.1.integrable_sq
  rw [integral_congr_ae (ae_of_all _ hsq), integral_add hI1 hI2, Or.2.2, Oi.2.2,
    ← Finset.sum_add_distrib]
  have hterm : ∀ k, ∫ ω, ((A k ω).re * (ε k ω).re - (A k ω).im * (ε k ω).im) ^ 2 ∂P +
      ∫ ω, ((A k ω).re * (ε k ω).im + (A k ω).im * (ε k ω).re) ^ 2 ∂P ≤ B := fun k => by
    have hpt2 : ∀ ω, ((A k ω).re * (ε k ω).re - (A k ω).im * (ε k ω).im) ^ 2 +
        ((A k ω).re * (ε k ω).im + (A k ω).im * (ε k ω).re) ^ 2 ≤ ‖ε k ω‖ ^ 2 := fun ω => by
      have h1 : ((A k ω).re * (ε k ω).re - (A k ω).im * (ε k ω).im) ^ 2 +
          ((A k ω).re * (ε k ω).im + (A k ω).im * (ε k ω).re) ^ 2 = ‖A k ω * ε k ω‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.mul_re, Complex.mul_im]; ring
      rw [h1, norm_mul]
      have := hAn k ω
      have h0 := norm_nonneg (A k ω)
      have h0' := norm_nonneg (ε k ω)
      calc (‖A k ω‖ * ‖ε k ω‖) ^ 2 ≤ (1 * ‖ε k ω‖) ^ 2 := by gcongr
        _ = ‖ε k ω‖ ^ 2 := by ring
    have hεsq : Integrable (fun ω => ‖ε k ω‖ ^ 2) P := by
      refine (hB2 k).integrable_sq.mono' ((hεM k).norm.pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hεb k ω) 2
    calc _ = ∫ ω, (((A k ω).re * (ε k ω).re - (A k ω).im * (ε k ω).im) ^ 2 +
          ((A k ω).re * (ε k ω).im + (A k ω).im * (ε k ω).re) ^ 2) ∂P :=
          (integral_add (m12 k).integrable_sq (m34 k).integrable_sq).symm
      _ ≤ ∫ ω, ‖ε k ω‖ ^ 2 ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity) hεsq (ae_of_all _ hpt2)
      _ ≤ B := hB k
  calc _ ≤ ∑ k ∈ range n, B := Finset.sum_le_sum fun k _ => hterm k
    _ = n * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **R1 core.** -/
theorem core (m : ℕ → MeasurableSpace Ω) (hmono : Monotone m) (hle : ∀ k, m k ≤ mΩ)
    (x : ℕ → Ω → ℝ) (hxm : ∀ k, Measurable[m (k + 1)] (x k))
    (hind : ∀ k, Indep (m k) (MeasurableSpace.comap (x k) inferInstance) P)
    (hx0 : ∀ k, ∫ ω, x k ω ∂P = 0) (hx2 : ∀ k, MemLp (x k) 2 P)
    (hx4 : ∀ k, Integrable (fun ω => x k ω ^ 4) P) (D : ℝ)
    (hD : ∀ k, ∫ ω, x k ω ^ 4 ∂P ≤ D) (n : ℕ) :
    ∃ c : ℂ, ∃ A : ℕ → Ω → ℂ, (∀ k, Measurable[m k] (A k)) ∧ (∀ k ω, ‖A k ω‖ ≤ 1) ∧
      ∫ ω, ‖Complex.exp (Complex.I * ∑ k ∈ range n, (x k ω : ℂ)) - c -
        ∑ k ∈ range n, A k ω * (Complex.I * (x k ω : ℂ))‖ ^ 2 ∂P ≤ n * (16 * D) := by
  have hxM : ∀ k, Measurable (x k) := fun k => (hxm k).mono (hle (k + 1)) le_rfl
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Ω → ℂ, g = fun k ω => Complex.exp (Complex.I * x k ω) := ⟨_, rfl⟩
  have hgn : ∀ k ω, ‖g k ω‖ = 1 := fun k ω => by
    simp only [hg]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hgm : ∀ k, Measurable[m (k + 1)] (g k) := fun k => by
    rw [hg]; exact ((Complex.measurable_ofReal.comp (hxm k)).const_mul Complex.I).cexp
  have hgi : ∀ k, Integrable (g k) P := fun k =>
    (memLp_top_of_bound ((hgm k).mono (hle _) le_rfl).aestronglyMeasurable 1
      (ae_of_all _ fun ω => (hgn k ω).le)).integrable le_top
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℂ, e = fun k => ∫ ω, g k ω ∂P := ⟨_, rfl⟩
  have hen : ∀ k, ‖e k‖ ≤ 1 := fun k => by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := g k) (C := 1)
      (ae_of_all _ fun ω => (hgn k ω).le)
    rw [he]; simpa using this
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Ω → ℂ,
      A = fun k ω => (∏ i ∈ range k, g i ω) * ∏ i ∈ Finset.Ico (k + 1) n, e i := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ → Ω → ℂ, ε = fun k ω => g k ω - e k - Complex.I * x k ω := ⟨_, rfl⟩
  have hAm : ∀ k, Measurable[m k] (A k) := fun k => by
    rw [hA]
    refine Measurable.mul_const ?_ _
    exact Finset.measurable_prod _ fun i hi =>
      (hgm i).mono (hmono (Nat.succ_le_of_lt (Finset.mem_range.1 hi))) le_rfl
  have hAn : ∀ k ω, ‖A k ω‖ ≤ 1 := fun k ω => by
    rw [hA]
    simp only [norm_mul, norm_prod, hgn, Finset.prod_const_one, one_mul]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hen i)
  refine ⟨∏ i ∈ range n, e i, A, hAm, hAn, ?_⟩
  have hpt : ∀ ω, Complex.exp (Complex.I * ∑ k ∈ range n, (x k ω : ℂ)) - ∏ i ∈ range n, e i -
      ∑ k ∈ range n, A k ω * (Complex.I * (x k ω : ℂ)) = ∑ k ∈ range n, A k ω * ε k ω := by
    intro ω
    have h1 : Complex.exp (Complex.I * ∑ k ∈ range n, (x k ω : ℂ)) = ∏ k ∈ range n, g k ω := by
      rw [Finset.mul_sum, Complex.exp_sum, hg]
    rw [h1, tel (fun k => g k ω) e n, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA, hε]; ring
  simp only [hpt]
  have hεc : ∀ k, Measurable[MeasurableSpace.comap (x k) inferInstance] (ε k) := fun k => by
    have hφ : Measurable fun t : ℝ => Complex.exp (Complex.I * t) - e k - Complex.I * t :=
      (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (Complex.I * t) - e k - Complex.I * t).measurable
    have : ε k = (fun t : ℝ => Complex.exp (Complex.I * t) - e k - Complex.I * t) ∘ x k := by
      rw [hε, hg]; rfl
    rw [this]; exact hφ.comp (comap_measurable (x k))
  have hεm : ∀ k, Measurable[m (k + 1)] (ε k) := fun k =>
    (hεc k).mono (hxm k).comap_le le_rfl
  have hεb : ∀ k ω, ‖ε k ω‖ ≤ 2 + |x k ω| := fun k ω => by
    have h1 : ‖Complex.I * (x k ω : ℂ)‖ = |x k ω| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖ε k ω‖ ≤ ‖g k ω‖ + ‖e k‖ + ‖Complex.I * (x k ω : ℂ)‖ := by
      rw [hε]; exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    rw [hgn, h1] at h2; linarith [hen k]
  have hε0 : ∀ k, ∫ ω, ε k ω ∂P = 0 := fun k => by
    have hge : Integrable (fun ω => g k ω - e k) P := (hgi k).sub (integrable_const _)
    have hxI : Integrable (fun ω => Complex.I * (x k ω : ℂ)) P :=
      ((hx2 k).integrable one_le_two).ofReal.const_mul _
    rw [hε]
    simp only
    rw [integral_sub hge hxI, integral_sub (hgi k) (integrable_const _), integral_const_mul,
      integral_complex_ofReal, hx0 k]
    simp [he]
  have hB : ∀ k, ∫ ω, ‖ε k ω‖ ^ 2 ∂P ≤ 16 * D := fun k => by
    have hb := eps_bound (x k) (hxM k) (hx2 k) (hx4 k) (hx0 k)
    have : ε k = fun ω => Complex.exp (Complex.I * x k ω) -
        (∫ ω', Complex.exp (Complex.I * x k ω') ∂P) - Complex.I * x k ω := by
      rw [hε, he, hg]
    rw [this]; linarith [hD k]
  exact sum_bound m hmono hle x hxM hind hx2 A ε hAm hAn hεc hεm hεb hε0 (16 * D) hB n

/-- Gaussian fourth moment by scaling. -/
lemma gauss4 {ξ : Ω → ℝ} {v : ℝ≥0} (hξ : HasLaw ξ (gaussianReal 0 v) P) :
    Integrable (fun ω => ξ ω ^ 4) P ∧
      ∫ ω, ξ ω ^ 4 ∂P = (v : ℝ) ^ 2 * ∫ x, x ^ 4 ∂(gaussianReal 0 1) := by
  have hint : ∀ w : ℝ≥0, Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 w) := fun w => by
    have h4 : MemLp (id : ℝ → ℝ) ((4 : ℕ) : ℝ≥0∞) (gaussianReal 0 w) := by
      have := memLp_id_gaussianReal (μ := 0) (v := w) 4
      exact_mod_cast this
    have := h4.integrable_norm_pow (by norm_num)
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [id, Real.norm_eq_abs]
    exact Even.pow_abs ⟨2, rfl⟩ x
  have hc : AEStronglyMeasurable (fun x : ℝ => x ^ 4) (gaussianReal 0 v) :=
    (continuous_pow 4).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure (f := ξ) (g := fun x : ℝ => x ^ 4) (μ := P)
      (by rw [hξ.map_eq]; exact hc) hξ.aemeasurable).1 (by rw [hξ.map_eq]; exact hint v)
  · have h := hξ.integral_comp (f := fun x : ℝ => x ^ 4) hc
    simp only [Function.comp_def] at h
    rw [h]
    have hmap : (gaussianReal 0 1).map (fun x => Real.sqrt v * x) = gaussianReal 0 v := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · simp
      · ext; simp
    rw [← hmap, integral_map (by fun_prop : AEMeasurable (fun x : ℝ => Real.sqrt v * x)
      (gaussianReal 0 1)) (continuous_pow 4).aestronglyMeasurable]
    have : ∀ x : ℝ, (Real.sqrt v * x) ^ 4 = (v : ℝ) ^ 2 * x ^ 4 := fun x => by
      rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt v.coe_nonneg]
    simp_rw [this]; exact integral_const_mul _ _

end StochCalcR1


namespace StochCalcR1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcIndep ItoLib StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcD2 StochCalcD3 StochCalcGauss StochCalcP6S Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Past of `B` up to `c`, all of `B~`. -/
noncomputable abbrev YsigB (M : Model p Ω) (c : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (q : PastIdx 2 c 0) => W M q.1.1 ω q.1.2) inferInstance

lemma coordB_meas (M : Model p Ω) (c : ℝ≥0) (q : PastIdx 2 c 0) :
    Measurable[YsigB M c] (fun ω => W M q.1.1 ω q.1.2) := fun S hS =>
  ⟨(fun f : PastIdx 2 c 0 → ℝ => f q) ⁻¹' S, measurable_pi_apply q hS, rfl⟩

lemma pair_aeC0 (M : Model p Ω) (hM : M.Standing) (c s : ℝ≥0) (hs : s ≤ c) :
    MeasurableSpace.comap (fun ω => (M.B s ω, M.Bt s ω)) inferInstance ≤
      aeClosure M.P (YsigB M c) := by
  rintro A ⟨S, hS, rfl⟩
  have hq0 : (s, (0 : Fin 2)).1 ≤ c ∨ (s, (0 : Fin 2)).2 ≠ 0 := Or.inl hs
  have hq1 : (s, (1 : Fin 2)).1 ≤ c ∨ (s, (1 : Fin 2)).2 ≠ 0 :=
    Or.inr (show (1 : Fin 2) ≠ 0 by decide)
  have hm : Measurable[YsigB M c] (fun ω => (W M s ω 0, W M s ω 1)) :=
    (coordB_meas M c ⟨(s, 0), hq0⟩).prodMk (coordB_meas M c ⟨(s, 1), hq1⟩)
  refine ⟨(fun ω => (W M s ω 0, W M s ω 1)) ⁻¹' S, hm hS, ?_⟩
  filter_upwards [ae_W M hM] with ω hω
  show ((M.B s ω, M.Bt s ω) ∈ S) = ((W M s ω 0, W M s ω 1) ∈ S)
  rw [(hω s).1, (hω s).2]

lemma null_aeC0 (M : Model p Ω) (c : ℝ≥0) :
    MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet N ∧ M.P N = 0} ≤
      aeClosure M.P (YsigB M c) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro N ⟨-, hN0⟩
  exact ⟨∅, @MeasurableSet.empty Ω (YsigB M c), ae_eq_empty.2 hN0⟩

lemma F_le0 (M : Model p Ω) (hM : M.Standing) (c : ℝ≥0) :
    M.F c ≤ aeClosure M.P (YsigB M c) := by
  rw [hM.filtF c]
  exact sup_le (iSup₂_le fun s hs => pair_aeC0 M hM c s hs) (null_aeC0 M c)

/-- The `B` increments after `c` are independent of `F_c`. -/
theorem indep_B_incr (M : Model p Ω) (hM : M.Standing) (c : ℝ≥0) :
    Indep (M.F c)
      (MeasurableSpace.comap (fun ω (r : ℝ≥0) => W M (c + r) ω 0 - W M c ω 0) inferInstance)
      M.P :=
  indep_of_indep_of_le_left (indep_coord_shift_aeClosure (isStandardBrownian M hM) c 0)
    (F_le0 M hM c)

lemma dB_ae (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) :
    dB M u w =ᵐ[M.P] fun ω => gB M w ω - gB M u ω := by
  filter_upwards [ae_W M hM] with ω hω
  simp only [dB, ← (hω w).1, ← (hω u).1, W_zero]

lemma indep_dB (M : Model p Ω) (hM : M.Standing) {u w : ℝ≥0} (huw : u ≤ w) :
    Indep (M.F u) (MeasurableSpace.comap (dB M u w) inferInstance) M.P := by
  refine indep_comap_congr _ (dB_ae M hM u w) ?_
  refine indep_of_indep_of_le_right (indep_B_incr M hM u) ?_
  set inc : Ω → ℝ≥0 → ℝ := fun ω r => W M (u + r) ω 0 - W M u ω 0 with hinc
  have heq : (fun ω => gB M w ω - gB M u ω) = (fun f : ℝ≥0 → ℝ => f (w - u)) ∘ inc := by
    funext ω
    simp only [Function.comp, hinc, W_zero, add_tsub_cancel_of_le huw]
  rw [heq]
  exact ((measurable_pi_apply _).comp (comap_measurable inc)).comap_le

lemma B_measF (M : Model p Ω) (hM : M.Standing) {r s : ℝ≥0} (hr : r ≤ s) :
    Measurable[M.F s] (M.B r) := by
  have h : MeasurableSpace.comap (fun ω => (M.B r ω, M.Bt r ω)) inferInstance ≤ M.F s := by
    rw [hM.filtF s]
    exact le_sup_of_le_left (le_iSup₂_of_le r hr le_rfl)
  exact measurable_fst.comp (Measurable.of_comap_le h)

lemma B_measG (M : Model p Ω) (hM : M.Standing) {r s : ℝ≥0} (hr : r ≤ s) :
    Measurable[M.G s] (M.B r) := by
  have h : MeasurableSpace.comap (M.B r) inferInstance ≤ M.G s := by
    rw [hM.filtG s]
    exact le_sup_of_le_left (le_iSup₂_of_le r hr le_rfl)
  exact Measurable.of_comap_le h

/-- Joint independence of the increment pair `(ΔB, ΔB~)` on `[u, w]` from `F_u`. -/
lemma indep_pair (M : Model p Ω) (hM : M.Standing) {u w : ℝ≥0} (huw : u ≤ w) :
    Indep (M.F u) (MeasurableSpace.comap (dB M u w) inferInstance ⊔
      MeasurableSpace.comap (ξ M u w) inferInstance) M.P := by
  have := hM.prob
  refine indep_sup_of_triple _ _ _ (M.F.le u) (dB_meas M hM u w).comap_le
    (ξ_meas M hM u w).comap_le (indep_dB M hM huw).symm ?_
  refine indep_of_indep_of_le_left (indep_ξ M hM huw w) (sup_le_sup_left ?_ _)
  have h : Measurable[M.G w] (dB M u w) := by
    unfold dB; exact (B_measG M hM le_rfl).sub (B_measG M hM huw)
  exact h.comap_le

/-- Fine-grid combined increment. -/
noncomputable def xg (M : Model p Ω) (m : ℕ) (a b : ℕ → ℝ) (l : ℕ) (ω : Ω) : ℝ :=
  a l * dB M (gr p m l) (gr p m (l + 1)) ω + b l * ξ M (gr p m l) (gr p m (l + 1)) ω

lemma xg_measF (M : Model p Ω) (hM : M.Standing) (m : ℕ) (a b : ℕ → ℝ) (l : ℕ) :
    Measurable[M.F (gr p m (l + 1))] (xg M m a b l) := by
  have hle : gr p m l ≤ gr p m (l + 1) := gr_mono p m (Nat.le_succ l)
  have h1 : Measurable[M.F (gr p m (l + 1))] (dB M (gr p m l) (gr p m (l + 1))) := by
    unfold dB; exact (B_measF M hM le_rfl).sub (B_measF M hM hle)
  unfold xg
  exact (h1.const_mul (a l)).add ((ξ_measF M hM hle).const_mul (b l))

lemma xg_indep (M : Model p Ω) (hM : M.Standing) (m : ℕ) (a b : ℕ → ℝ) (l : ℕ) :
    Indep (M.F (gr p m l)) (MeasurableSpace.comap (xg M m a b l) inferInstance) M.P := by
  have hle : gr p m l ≤ gr p m (l + 1) := gr_mono p m (Nat.le_succ l)
  refine indep_of_indep_of_le_right (indep_pair M hM hle) ?_
  have h1 : Measurable[MeasurableSpace.comap (dB M (gr p m l) (gr p m (l + 1))) inferInstance ⊔
      MeasurableSpace.comap (ξ M (gr p m l) (gr p m (l + 1))) inferInstance] (xg M m a b l) := by
    unfold xg
    exact (((comap_measurable _).mono le_sup_left le_rfl).const_mul (a l)).add
      (((comap_measurable _).mono le_sup_right le_rfl).const_mul (b l))
  exact h1.comap_le

lemma xg_mean (M : Model p Ω) (hM : M.Standing) (m : ℕ) (a b : ℕ → ℝ) (l : ℕ) :
    ∫ ω, xg M m a b l ω ∂M.P = 0 := by
  have := hM.prob
  set u := gr p m l
  set w := gr p m (l + 1)
  have h1 := memLp_xi (dB_meas M hM u w) (dB_law M hM u w)
  have h2 := memLp_xi (ξ_meas M hM u w) (ξ_law M hM u w)
  unfold xg
  rw [integral_add ((h1.integrable one_le_two).const_mul _) ((h2.integrable one_le_two).const_mul _),
    integral_const_mul, integral_const_mul, integral_gauss (dB_law M hM u w),
    integral_gauss (ξ_law M hM u w)]
  ring

lemma xg_memLp (M : Model p Ω) (hM : M.Standing) (m : ℕ) (a b : ℕ → ℝ) (l : ℕ) :
    MemLp (xg M m a b l) 2 M.P := by
  have := hM.prob
  have h1 := memLp_xi (dB_meas M hM (gr p m l) (gr p m (l + 1)))
    (dB_law M hM (gr p m l) (gr p m (l + 1)))
  have h2 := memLp_xi (ξ_meas M hM (gr p m l) (gr p m (l + 1)))
    (ξ_law M hM (gr p m l) (gr p m (l + 1)))
  exact (h1.const_mul (a l)).add (h2.const_mul (b l))

lemma pow4_add_le (x y : ℝ) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h1 : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have h2 : (x ^ 2 + y ^ 2) ^ 2 ≤ 2 * (x ^ 4 + y ^ 4) := by nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  have h3 : (x + y) ^ 4 = ((x + y) ^ 2) ^ 2 := by ring
  rw [h3]
  calc ((x + y) ^ 2) ^ 2 ≤ (2 * (x ^ 2 + y ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = 4 * (x ^ 2 + y ^ 2) ^ 2 := by ring
    _ ≤ 8 * (x ^ 4 + y ^ 4) := by linarith

/-- Standard-Gaussian fourth moment constant. -/
noncomputable def K4 : ℝ := ∫ x, x ^ 4 ∂(gaussianReal 0 1)

lemma K4_nonneg : 0 ≤ K4 := integral_nonneg fun x => Even.pow_nonneg ⟨2, rfl⟩ x

lemma xg_four (M : Model p Ω) (hM : M.Standing) (m : ℕ) (a b : ℕ → ℝ) (L : ℝ)
    (hL : ∀ l, |a l| ≤ L ∧ |b l| ≤ L) (l : ℕ) :
    Integrable (fun ω => xg M m a b l ω ^ 4) M.P ∧
      ∫ ω, xg M m a b l ω ^ 4 ∂M.P ≤ 16 * L ^ 4 * K4 * ((p.T : ℝ) / m) ^ 2 := by
  have := hM.prob
  set u := gr p m l
  set w := gr p m (l + 1)
  obtain ⟨i1, e1⟩ := StochCalcR1.gauss4 (dB_law M hM u w)
  obtain ⟨i2, e2⟩ := StochCalcR1.gauss4 (ξ_law M hM u w)
  have hV : (V u w : ℝ) = (p.T : ℝ) / m := V_gr p m l
  have ha4 : a l ^ 4 ≤ L ^ 4 := by
    rw [← Even.pow_abs ⟨2, rfl⟩ (a l)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hL l).1 4
  have hb4 : b l ^ 4 ≤ L ^ 4 := by
    rw [← Even.pow_abs ⟨2, rfl⟩ (b l)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hL l).2 4
  have hbd : ∀ ω, xg M m a b l ω ^ 4 ≤
      8 * L ^ 4 * (dB M u w ω ^ 4 + ξ M u w ω ^ 4) := fun ω => by
    have h := pow4_add_le (a l * dB M u w ω) (b l * ξ M u w ω)
    have hd : 0 ≤ dB M u w ω ^ 4 := Even.pow_nonneg ⟨2, rfl⟩ _
    have hx : 0 ≤ ξ M u w ω ^ 4 := Even.pow_nonneg ⟨2, rfl⟩ _
    unfold xg
    calc _ ≤ 8 * ((a l * dB M u w ω) ^ 4 + (b l * ξ M u w ω) ^ 4) := h
      _ = 8 * (a l ^ 4 * dB M u w ω ^ 4 + b l ^ 4 * ξ M u w ω ^ 4) := by ring
      _ ≤ 8 * (L ^ 4 * dB M u w ω ^ 4 + L ^ 4 * ξ M u w ω ^ 4) := by gcongr
      _ = 8 * L ^ 4 * (dB M u w ω ^ 4 + ξ M u w ω ^ 4) := by ring
  have hI : Integrable (fun ω => 8 * L ^ 4 * (dB M u w ω ^ 4 + ξ M u w ω ^ 4)) M.P :=
    (i1.add i2).const_mul _
  have hxm : Measurable (xg M m a b l) :=
    (xg_measF M hM m a b l).mono (M.F.le _) le_rfl
  have hint : Integrable (fun ω => xg M m a b l ω ^ 4) M.P :=
    hI.mono' (hxm.pow_const 4).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Even.pow_nonneg ⟨2, rfl⟩ _)]; exact hbd ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, xg M m a b l ω ^ 4 ∂M.P
      ≤ ∫ ω, 8 * L ^ 4 * (dB M u w ω ^ 4 + ξ M u w ω ^ 4) ∂M.P :=
        integral_mono hint hI hbd
    _ = 8 * L ^ 4 * (∫ ω, dB M u w ω ^ 4 ∂M.P + ∫ ω, ξ M u w ω ^ 4 ∂M.P) := by
        rw [integral_const_mul, integral_add i1 i2]
    _ = 16 * L ^ 4 * K4 * ((p.T : ℝ) / m) ^ 2 := by
        rw [e1, e2, hV, K4]; ring

/-- **R1 (model).** -/
theorem trig_approx (M : Model p Ω) (hM : M.Standing) (n : ℕ) (hn : 0 < n)
    (lam mu : ℕ → ℝ) (L : ℝ) (hL : ∀ k, |lam k| ≤ L ∧ |mu k| ≤ L) (η : ℝ) (hη : 0 < η) :
    ∃ m : ℕ, 0 < m ∧ ∃ a b : ℕ → ℝ, (∀ l, |a l| ≤ L ∧ |b l| ≤ L) ∧ ∃ c : ℂ,
      ∃ A : ℕ → Ω → ℂ, (∀ l, Measurable[M.F (gr p m l)] (A l)) ∧ (∀ l ω, ‖A l ω‖ ≤ 1) ∧
      ∫ ω, ‖Complex.exp (Complex.I * ((∑ k ∈ range n, (lam k * dB M (gr p n k) (gr p n (k + 1)) ω +
          mu k * ξ M (gr p n k) (gr p n (k + 1)) ω) : ℝ) : ℂ)) - c -
        ∑ l ∈ range m, A l ω * (Complex.I * (xg M m a b l ω : ℂ))‖ ^ 2 ∂M.P ≤ η := by
  have := hM.prob
  have hK := K4_nonneg
  set C0 : ℝ := 256 * L ^ 4 * K4 * (p.T : ℝ) ^ 2 with hC0
  have hC0nn : 0 ≤ C0 := by positivity
  obtain ⟨N0, hN0⟩ := exists_nat_gt (C0 / η)
  set N := N0 + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos N0
  set m := n * N with hmdef
  have hm : 0 < m := Nat.mul_pos hn hN
  set a : ℕ → ℝ := fun l => lam (l / N) with ha
  set b : ℕ → ℝ := fun l => mu (l / N) with hb
  have hab : ∀ l, |a l| ≤ L ∧ |b l| ≤ L := fun l => hL (l / N)
  set D : ℝ := 16 * L ^ 4 * K4 * ((p.T : ℝ) / m) ^ 2 with hD
  obtain ⟨c, A, hAm, hAn, hbd⟩ := StochCalcR1.core (fun l => M.F (gr p m l))
    (fun i j hij => M.F.mono (gr_mono p m hij)) (fun l => M.F.le _) (xg M m a b)
    (xg_measF M hM m a b) (xg_indep M hM m a b) (xg_mean M hM m a b) (xg_memLp M hM m a b)
    (fun l => (xg_four M hM m a b L hab l).1) D (fun l => (xg_four M hM m a b L hab l).2) m
  refine ⟨m, hm, a, b, hab, c, A, hAm, hAn, ?_⟩
  have hsum : ∀ ω, (∑ k ∈ range n, (lam k * dB M (gr p n k) (gr p n (k + 1)) ω +
      mu k * ξ M (gr p n k) (gr p n (k + 1)) ω) : ℝ) = ∑ l ∈ range m, xg M m a b l ω := by
    intro ω
    simp only [xg, dB, ξ, Finset.sum_add_distrib, ha, hb, hmdef]
    rw [refine_sum p M.B (fun k _ => lam k) hN n ω n, refine_sum p M.Bt (fun k _ => mu k) hN n ω n]
  have hcongr : (fun ω => ‖Complex.exp (Complex.I * ((∑ k ∈ range n,
      (lam k * dB M (gr p n k) (gr p n (k + 1)) ω + mu k * ξ M (gr p n k) (gr p n (k + 1)) ω) : ℝ) : ℂ)) -
      c - ∑ l ∈ range m, A l ω * (Complex.I * (xg M m a b l ω : ℂ))‖ ^ 2) =
      fun ω => ‖Complex.exp (Complex.I * ∑ l ∈ range m, (xg M m a b l ω : ℂ)) - c -
      ∑ l ∈ range m, A l ω * (Complex.I * (xg M m a b l ω : ℂ))‖ ^ 2 := by
    funext ω; rw [hsum ω, Complex.ofReal_sum]
  rw [hcongr]
  refine hbd.trans ?_
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNm : (N0 : ℝ) < m := by
    have : (N0 : ℝ) < N := by rw [hNdef]; push_cast; linarith
    have h2 : (N : ℝ) ≤ m := by
      rw [hmdef]; push_cast
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    linarith
  have heq : (m : ℝ) * (16 * D) = C0 / m := by
    rw [hD, hC0]; field_simp; ring
  rw [heq, div_le_iff₀ hmR]
  have := (div_lt_iff₀ hη).1 (hN0.trans hNm)
  linarith

end StochCalcR1M


namespace StochCalcR4

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcGauss Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Grid sums on a uniform grid with bounded adapted coefficients. -/
def IsGS (M : Model p Ω) (f : Ω → ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ c : ℝ, ∃ Y Z : ℕ → Ω → ℝ, ∃ C : ℝ,
    (∀ k, StronglyMeasurable[M.F (gr p n k)] (Y k)) ∧ (∀ k ω, |Y k ω| ≤ C) ∧
    (∀ k, StronglyMeasurable[M.F (gr p n k)] (Z k)) ∧ (∀ k ω, |Z k ω| ≤ C) ∧
    f = fun ω => c + ∑ k ∈ range n, Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω +
      ∑ k ∈ range n, Z k ω * ξ M (gr p n k) (gr p n (k + 1)) ω

lemma IsGS_zero (M : Model p Ω) : IsGS M 0 := by
  refine ⟨1, one_pos, 0, fun _ _ => 0, fun _ _ => 0, 0, fun _ => stronglyMeasurable_const,
    fun _ _ => by simp, fun _ => stronglyMeasurable_const, fun _ _ => by simp, ?_⟩
  funext ω; simp

lemma IsGS_smul (M : Model p Ω) (r : ℝ) {f : Ω → ℝ} (hf : IsGS M f) : IsGS M (r • f) := by
  obtain ⟨n, hn, c, Y, Z, C, hYm, hYb, hZm, hZb, rfl⟩ := hf
  refine ⟨n, hn, r * c, fun k ω => r * Y k ω, fun k ω => r * Z k ω, |r| * C,
    fun k => (hYm k).const_mul r, fun k ω => ?_, fun k => (hZm k).const_mul r, fun k ω => ?_, ?_⟩
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hYb k ω) (abs_nonneg r)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hZb k ω) (abs_nonneg r)
  · funext ω
    simp only [Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

/-- Coefficient transported to a refined grid `n → n * m` (as `j ↦ Y (j / m)`). -/
lemma coef_refine (M : Model p Ω) {n m : ℕ} (hm : 0 < m) {Y : ℕ → Ω → ℝ}
    (hYm : ∀ k, StronglyMeasurable[M.F (gr p n k)] (Y k)) (j : ℕ) :
    StronglyMeasurable[M.F (gr p (n * m) j)] (Y (j / m)) := by
  refine (hYm (j / m)).mono (M.F.mono ?_)
  rw [← gr_mul p hm n (j / m)]
  exact gr_mono p (n * m) (Nat.div_mul_le_self j m)

lemma IsGS_add (M : Model p Ω) {f g : Ω → ℝ} (hf : IsGS M f) (hg : IsGS M g) :
    IsGS M (f + g) := by
  obtain ⟨n1, hn1, c1, Y1, Z1, C1, hYm1, hYb1, hZm1, hZb1, rfl⟩ := hf
  obtain ⟨n2, hn2, c2, Y2, Z2, C2, hYm2, hYb2, hZm2, hZb2, rfl⟩ := hg
  have e21 : n2 * n1 = n1 * n2 := Nat.mul_comm n2 n1
  have hY2' : ∀ j, StronglyMeasurable[M.F (gr p (n1 * n2) j)] (Y2 (j / n1)) := fun j => by
    rw [← e21]; exact coef_refine M hn1 hYm2 j
  have hZ2' : ∀ j, StronglyMeasurable[M.F (gr p (n1 * n2) j)] (Z2 (j / n1)) := fun j => by
    rw [← e21]; exact coef_refine M hn1 hZm2 j
  refine ⟨n1 * n2, Nat.mul_pos hn1 hn2, c1 + c2,
    fun j ω => Y1 (j / n2) ω + Y2 (j / n1) ω, fun j ω => Z1 (j / n2) ω + Z2 (j / n1) ω, C1 + C2,
    fun j => (coef_refine M hn2 hYm1 j).add (hY2' j),
    fun j ω => (abs_add_le _ _).trans (add_le_add (hYb1 _ ω) (hYb2 _ ω)),
    fun j => (coef_refine M hn2 hZm1 j).add (hZ2' j),
    fun j ω => (abs_add_le _ _).trans (add_le_add (hZb1 _ ω) (hZb2 _ ω)), ?_⟩
  funext ω
  have r1 := refine_sum p M.B Y1 hn2 n1 ω n1
  have r2 := refine_sum p M.B Y2 hn1 n2 ω n2
  have r3 := refine_sum p M.Bt Z1 hn2 n1 ω n1
  have r4 := refine_sum p M.Bt Z2 hn1 n2 ω n2
  rw [e21] at r2 r4
  simp only [Pi.add_apply, dB, ξ, add_mul, Finset.sum_add_distrib]
  rw [r1, r2, r3, r4]
  ring

lemma IsGS_props (M : Model p Ω) (hM : M.Standing) {f : Ω → ℝ} (hf : IsGS M f) :
    StronglyMeasurable[M.F p.T] f ∧ MemLp f 2 M.P := by
  have := hM.prob
  obtain ⟨n, hn, c, Y, Z, C, hYm, hYb, hZm, hZb, rfl⟩ := hf
  have hYT : ∀ k ∈ range n, Measurable[M.F p.T] (Y k) := fun k hk =>
    ((hYm k).mono (M.F.mono (gr_le_T p (Finset.mem_range.1 hk).le))).measurable
  have hZT : ∀ k ∈ range n, Measurable[M.F p.T] (Z k) := fun k hk =>
    ((hZm k).mono (M.F.mono (gr_le_T p (Finset.mem_range.1 hk).le))).measurable
  have hBT : ∀ k ∈ range n, Measurable[M.F p.T] (dB M (gr p n k) (gr p n (k + 1))) := fun k hk => by
    have h1 : gr p n (k + 1) ≤ p.T := gr_le_T p (Finset.mem_range.1 hk)
    have h0 : gr p n k ≤ p.T := (gr_mono p n (Nat.le_succ k)).trans h1
    unfold dB
    exact (StochCalcR1M.B_measF M hM h1).sub (StochCalcR1M.B_measF M hM h0)
  have hξT : ∀ k ∈ range n, Measurable[M.F p.T] (ξ M (gr p n k) (gr p n (k + 1))) := fun k hk => by
    have h1 : gr p n (k + 1) ≤ p.T := gr_le_T p (Finset.mem_range.1 hk)
    have h0 : gr p n k ≤ p.T := (gr_mono p n (Nat.le_succ k)).trans h1
    unfold ξ
    exact (Bt_measF M hM h1).sub (Bt_measF M hM h0)
  refine ⟨?_, ?_⟩
  · refine Measurable.stronglyMeasurable ?_
    refine (measurable_const.add (Finset.measurable_sum _ fun k hk => (hYT k hk).mul (hBT k hk))).add
      (Finset.measurable_sum _ fun k hk => (hZT k hk).mul (hξT k hk))
  · have h1 := sum_memLp M hM n Y C hYm hYb (dB M)
      (fun u w => memLp_xi (dB_meas M hM u w) (dB_law M hM u w)) n
    have h2 := sum_memLp M hM n Z C hZm hZb (ξ M)
      (fun u w => memLp_xi (ξ_meas M hM u w) (ξ_law M hM u w)) n
    exact ((memLp_const c).add h1).add h2

end StochCalcR4


open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace StochCalcR2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [mE : MeasurableSpace E] [BorelSpace E]

/-- The complex integral against `exp(i⟪Δ,t⟫)` splits into the cos and sin integrals. -/
lemma integral_cexp_eq (Δ : Ω → E) (hΔ : Measurable Δ) (V : Ω → ℝ) (hV : Integrable V P)
    (t : E) :
    ∫ ω, (V ω : ℂ) * cexp ((inner ℝ (Δ ω) t : ℝ) * I) ∂P =
      ((∫ ω, V ω * Real.cos (inner ℝ (Δ ω) t) ∂P : ℝ) : ℂ) +
        ((∫ ω, V ω * Real.sin (inner ℝ (Δ ω) t) ∂P : ℝ) : ℂ) * I := by
  have hc : Integrable (fun ω => V ω * Real.cos (inner ℝ (Δ ω) t)) P := by
    refine hV.mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (Real.continuous_cos.measurable.comp
        ((continuous_inner.comp (continuous_id.prodMk continuous_const)).measurable.comp hΔ)
        ).aestronglyMeasurable
    · simpa using Real.abs_cos_le_one _
  have hs : Integrable (fun ω => V ω * Real.sin (inner ℝ (Δ ω) t)) P := by
    refine hV.mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (Real.continuous_sin.measurable.comp
        ((continuous_inner.comp (continuous_id.prodMk continuous_const)).measurable.comp hΔ)
        ).aestronglyMeasurable
    · simpa using Real.abs_sin_le_one _
  have hfun : (fun ω => (V ω : ℂ) * cexp ((inner ℝ (Δ ω) t : ℝ) * I)) =
      fun ω => ((V ω * Real.cos (inner ℝ (Δ ω) t) : ℝ) : ℂ) +
        ((V ω * Real.sin (inner ℝ (Δ ω) t) : ℝ) : ℂ) * I := by
    funext ω
    rw [← Complex.cos_add_sin_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring
  rw [hfun, integral_add, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]
  · exact hc.ofReal
  · exact hs.ofReal.mul_const _

/-- **R2a.** Orthogonality to all trigonometric functions of `Δ` kills every `σ(Δ)` set integral. -/
theorem setIntegral_eq_zero_of_trig (Δ : Ω → E) (hΔ : Measurable Δ) (V : Ω → ℝ)
    [IsFiniteMeasure P] (hVm : Measurable V) (hV : Integrable V P)
    (h : ∀ t : E, ∫ ω, V ω * Real.cos (inner ℝ (Δ ω) t) ∂P = 0 ∧
      ∫ ω, V ω * Real.sin (inner ℝ (Δ ω) t) ∂P = 0) :
    ∀ A, MeasurableSet[mE.comap Δ] A → ∫ ω in A, V ω ∂P = 0 := by
  have hpm : Measurable fun ω => (V ω).toNNReal := measurable_real_toNNReal.comp hVm
  have hnm : Measurable fun ω => (-V ω).toNNReal := measurable_real_toNNReal.comp hVm.neg
  haveI : IsFiniteMeasure (P.withDensity fun ω => ENNReal.ofReal (V ω)) :=
    isFiniteMeasure_withDensity_ofReal hV.2
  haveI : IsFiniteMeasure (P.withDensity fun ω => ENNReal.ofReal (-V ω)) :=
    isFiniteMeasure_withDensity_ofReal hV.neg.2
  have he : ∀ t : E, Continuous fun x : E => cexp ((inner ℝ x t : ℝ) * I) := fun t => by
    fun_prop
  have hint : ∀ (t : E) (g : Ω → ℝ), Integrable g P →
      Integrable (fun ω => (g ω : ℂ) * cexp ((inner ℝ (Δ ω) t : ℝ) * I)) P := by
    intro t g hg
    refine hg.ofReal.mul_bdd (c := 1) ((he t).measurable.comp hΔ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Function.comp_apply, Complex.norm_exp_ofReal_mul_I, le_refl]
  have hch : ∀ t : E, charFun ((P.withDensity fun ω => ENNReal.ofReal (V ω)).map Δ) t =
      charFun ((P.withDensity fun ω => ENNReal.ofReal (-V ω)).map Δ) t := by
    intro t
    rw [charFun_apply, charFun_apply,
      integral_map hΔ.aemeasurable (he t).aestronglyMeasurable,
      integral_map hΔ.aemeasurable (he t).aestronglyMeasurable]
    change ∫ ω, cexp ((inner ℝ (Δ ω) t : ℝ) * I) ∂(P.withDensity fun ω => ((V ω).toNNReal : ℝ≥0∞))
      = ∫ ω, cexp ((inner ℝ (Δ ω) t : ℝ) * I) ∂(P.withDensity fun ω => ((-V ω).toNNReal : ℝ≥0∞))
    rw [integral_withDensity_eq_integral_smul hpm, integral_withDensity_eq_integral_smul hnm]
    simp_rw [NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal']
    have hn : Integrable (fun ω => max (-V ω) 0) P := hV.neg.pos_part
    rw [← sub_eq_zero, ← integral_sub (hint t _ hV.pos_part) (hint t _ hn)]
    have : (fun ω => ((max (V ω) 0 : ℝ) : ℂ) * cexp ((inner ℝ (Δ ω) t : ℝ) * I) -
        ((max (-V ω) 0 : ℝ) : ℂ) * cexp ((inner ℝ (Δ ω) t : ℝ) * I)) =
        fun ω => (V ω : ℂ) * cexp ((inner ℝ (Δ ω) t : ℝ) * I) := by
      funext ω; rw [← sub_mul, ← Complex.ofReal_sub, max_zero_sub_max_neg_zero_eq_self]
    rw [this, integral_cexp_eq Δ hΔ V hV t, (h t).1, (h t).2]; simp
  have hμ := Measure.ext_of_charFun (funext hch)
  intro A hA
  obtain ⟨U, hU, rfl⟩ := hA
  have h1 := congrArg (fun μ : Measure E => μ U) hμ
  simp only [Measure.map_apply hΔ hU, withDensity_apply _ (hΔ hU)] at h1
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hV.integrableOn, h1, sub_self]

end StochCalcR2


open MeasureTheory Filter
open scoped ENNReal Topology

namespace StochCalcR2


/-- The augmentation of a σ-algebra `m` by the measurable `P`-null sets. -/
def aug {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) :
    MeasurableSpace Ω :=
  m ⊔ MeasurableSpace.generateFrom {N : Set Ω | MeasurableSet[mΩ] N ∧ P N = 0}

lemma aug_le {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (hm : m ≤ mΩ) : aug m P ≤ mΩ :=
  sup_le hm (MeasurableSpace.generateFrom_le fun _ h => h.1)

lemma le_aug {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) :
    m ≤ aug m P := le_sup_left

lemma null_mem_aug {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {N : Set Ω} (hN : MeasurableSet[mΩ] N) (h0 : P N = 0) :
    MeasurableSet[aug m P] N :=
  le_sup_right (a := m) _ (MeasurableSpace.measurableSet_generateFrom ⟨hN, h0⟩)

/-- **R2b.** Vanishing set integrals pass from an increasing sequence of σ-algebras to the
augmented supremum. -/
theorem setIntegral_zero_aug_iSup {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (V : Ω → ℝ) (hV : Integrable V P)
    (𝒢 : ℕ → MeasurableSpace Ω) (hmono : Monotone 𝒢) (hle : ∀ n, 𝒢 n ≤ mΩ)
    (h : ∀ n A, MeasurableSet[𝒢 n] A → ∫ ω in A, V ω ∂P = 0) :
    ∀ A, MeasurableSet[aug (⨆ n, 𝒢 n) P] A → ∫ ω in A, V ω ∂P = 0 := by
  have hK : aug (⨆ n, 𝒢 n) P ≤ mΩ := aug_le (iSup_le hle)
  set S : Set (Set Ω) := {s | ∃ n, MeasurableSet[𝒢 n] s} ∪ {N | MeasurableSet[mΩ] N ∧ P N = 0}
  have hgen : aug (⨆ n, 𝒢 n) P = MeasurableSpace.generateFrom S := by
    unfold aug
    rw [← MeasurableSpace.generateFrom_sup_generateFrom]
    congr 1
    exact le_antisymm (iSup_le fun n s hs => MeasurableSpace.measurableSet_generateFrom ⟨n, hs⟩)
      (MeasurableSpace.generateFrom_le fun s ⟨n, hs⟩ => le_iSup 𝒢 n s hs)
  have hpi : IsPiSystem S := by
    rintro s (⟨n, hs⟩ | ⟨hs, hs0⟩) t (⟨k, ht⟩ | ⟨ht, ht0⟩) _
    · exact Or.inl ⟨max n k, (hmono (le_max_left n k) s hs).inter (hmono (le_max_right n k) t ht)⟩
    · exact Or.inr ⟨(hle n s hs).inter ht, measure_mono_null Set.inter_subset_right ht0⟩
    · exact Or.inr ⟨hs.inter (hle k t ht), measure_mono_null Set.inter_subset_left hs0⟩
    · exact Or.inr ⟨hs.inter ht, measure_mono_null Set.inter_subset_left hs0⟩
  have htot : ∫ ω, V ω ∂P = 0 := by
    simpa using h 0 Set.univ MeasurableSet.univ
  refine MeasurableSpace.induction_on_inter (C := fun A _ => ∫ ω in A, V ω ∂P = 0) hgen hpi
    (by simp) ?_ ?_ ?_
  · rintro t (⟨n, ht⟩ | ⟨ht, ht0⟩)
    · exact h n t ht
    · rw [Measure.restrict_eq_zero.mpr ht0, integral_zero_measure]
  · intro t htm ht
    rw [setIntegral_compl (hK _ htm) hV, htot, ht, sub_zero]
  · intro f hdisj hfm hf
    rw [integral_iUnion (fun i => hK _ (hfm i)) hdisj hV.integrableOn]
    simp [hf]

/-- A variable that is a.e. equal to an `m`-measurable one is `aug P m`-measurable. -/
lemma comap_le_aug {Ω E : Type*} [mE : MeasurableSpace E] (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (Y g : Ω → E) (hY : Measurable[mΩ] Y) (hg : Measurable[m] g)
    (hN : MeasurableSet[mΩ] {ω | Y ω ≠ g ω}) (hYg : Y =ᵐ[P] g) :
    MeasurableSpace.comap Y mE ≤ aug m P := by
  rintro s ⟨U, hU, rfl⟩
  have h0 : P {ω | Y ω ≠ g ω} = 0 := ae_iff.mp hYg
  have hsplit : Y ⁻¹' U = (g ⁻¹' U ∩ {ω | Y ω ≠ g ω}ᶜ) ∪ (Y ⁻¹' U ∩ {ω | Y ω ≠ g ω}) := by
    ext ω
    by_cases hω : Y ω = g ω <;> simp [hω]
  rw [hsplit]
  refine MeasurableSet.union (MeasurableSet.inter (le_aug m P _ (hg hU))
    (null_mem_aug m hN h0).compl) (null_mem_aug m ((hY hU).inter hN)
      (measure_mono_null (μ := P) Set.inter_subset_right h0))

end StochCalcR2


namespace StochCalcR2

open MeasureTheory

/-- **R2c.** If `V` is measurable for a σ-algebra `F` lying below the augmented supremum of an
increasing sequence `σ(Δ j)` of finite-dimensional Gaussian-free "grid" variables, and `V` is
orthogonal to all trigonometric functions of every `Δ j`, then `V = 0` a.e. -/
theorem ae_eq_zero_of_trig {Ω : Type*} (F : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    [IsFiniteMeasure P] (d : ℕ → ℕ) (Δ : (j : ℕ) → Ω → EuclideanSpace ℝ (Fin (d j)))
    (hΔ : ∀ j, Measurable (Δ j))
    (hmono : Monotone fun j => MeasurableSpace.comap (Δ j) inferInstance)
    (hF : F ≤ aug (⨆ j, MeasurableSpace.comap (Δ j) inferInstance) P)
    (V : Ω → ℝ) (hVF : StronglyMeasurable[F] V) (hV : Integrable V P)
    (htrig : ∀ j (t : EuclideanSpace ℝ (Fin (d j))),
      ∫ ω, V ω * Real.cos (inner ℝ (Δ j ω) t) ∂P = 0 ∧
      ∫ ω, V ω * Real.sin (inner ℝ (Δ j ω) t) ∂P = 0) :
    V =ᵐ[P] 0 := by
  have hle : ∀ j, MeasurableSpace.comap (Δ j) inferInstance ≤ mΩ := fun j => (hΔ j).comap_le
  have hFle : F ≤ mΩ := hF.trans (aug_le (iSup_le hle))
  have hVm : Measurable V := (hVF.mono hFle).measurable
  have hA : ∀ A, MeasurableSet[F] A → ∫ ω in A, V ω ∂P = 0 := fun A hA =>
    setIntegral_zero_aug_iSup V hV _ hmono hle
      (fun j B hB => setIntegral_eq_zero_of_trig (Δ j) (hΔ j) V hVm hV (htrig j) B hB) A (hF A hA)
  exact ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim hFle
    (fun s _ _ => hV.integrableOn) (fun s hs _ => hA s hs)
    (hVF.finStronglyMeasurable (P.trim hFle))

end StochCalcR2


open MeasureTheory Filter
open scoped ENNReal

namespace StochCalcR3

theorem approx_of_sep {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (𝒯 : (Ω → ℝ) → Prop) (hL2 : ∀ f, 𝒯 f → MemLp f 2 P) (h0 : 𝒯 0)
    (hadd : ∀ f g, 𝒯 f → 𝒯 g → 𝒯 (f + g)) (hsmul : ∀ (c : ℝ) f, 𝒯 f → 𝒯 (c • f))
    (hsep : ∀ V : Ω → ℝ, MemLp V 2 P → (∀ f, 𝒯 f → ∫ ω, V ω * f ω ∂P = 0) → V =ᵐ[P] 0)
    (H : Ω → ℝ) (hH : MemLp H 2 P) (η : ℝ) (hη : 0 < η) :
    ∃ f, 𝒯 f ∧ ∫ ω, (H ω - f ω) ^ 2 ∂P ≤ η := by
  let K : Submodule ℝ (Lp ℝ 2 P) :=
    { carrier := {u | ∃ f, 𝒯 f ∧ (u : Ω → ℝ) =ᵐ[P] f}
      zero_mem' := ⟨0, h0, Lp.coeFn_zero _ _ _⟩
      add_mem' := by
        rintro u v ⟨f, hf, hu⟩ ⟨g, hg, hv⟩
        exact ⟨f + g, hadd f g hf hg, (Lp.coeFn_add u v).trans (hu.add hv)⟩
      smul_mem' := by
        rintro c u ⟨f, hf, hu⟩
        exact ⟨c • f, hsmul c f hf, (Lp.coeFn_smul c u).trans (hu.const_smul c)⟩ }
  have hnorm : ∀ w : Lp ℝ 2 P, ‖w‖ ^ 2 = ∫ ω, (w : Ω → ℝ) ω ^ 2 ∂P := by
    intro w
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    congr 1; funext ω; simp [sq]
  have hperp : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_orthogonal] at hv
    have hz : (v : Ω → ℝ) =ᵐ[P] 0 := by
      refine hsep v (Lp.memLp v) fun f hf => ?_
      have h1 := hv ((hL2 f hf).toLp f) ⟨f, hf, (hL2 f hf).coeFn_toLp⟩
      rw [MeasureTheory.L2.inner_def] at h1
      rw [← h1]
      refine integral_congr_ae ?_
      filter_upwards [(hL2 f hf).coeFn_toLp] with ω hω
      simp [hω, mul_comm]
    exact Lp.ext (hz.trans (Lp.coeFn_zero _ _ _).symm)
  have hcl : K.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.mpr hperp
  have hmem : hH.toLp H ∈ K.topologicalClosure := by rw [hcl]; trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  obtain ⟨b, ⟨f, hf, hb⟩, hdist⟩ := hmem (Real.sqrt η) (Real.sqrt_pos.mpr hη)
  refine ⟨f, hf, ?_⟩
  have h2 : ‖hH.toLp H - b‖ ^ 2 ≤ η := by
    rw [← dist_eq_norm]
    calc dist (hH.toLp H) b ^ 2 ≤ Real.sqrt η ^ 2 := by
          gcongr
      _ = η := Real.sq_sqrt hη.le
  rw [hnorm] at h2
  refine le_of_eq_of_le (integral_congr_ae ?_) h2
  filter_upwards [Lp.coeFn_sub (hH.toLp H) b, hH.coeFn_toLp, hb] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]

end StochCalcR3


set_option autoImplicit false

open MeasureTheory

namespace StochCalcR6

lemma amgm_abs (ε a b : ℝ) (hε : 0 < ε) :
    |a * b| ≤ (ε / 2) * a ^ 2 + (ε⁻¹ / 2) * b ^ 2 := by
  have h1 : 0 ≤ ε⁻¹ * (ε * |a| - |b|) ^ 2 := by positivity
  have h2 : ε⁻¹ * (ε * |a| - |b|) ^ 2 = ε * |a| ^ 2 + ε⁻¹ * |b| ^ 2 - 2 * (|a| * |b|) := by
    field_simp; ring
  rw [sq_abs, sq_abs] at h2
  rw [abs_mul]
  linarith

theorem orth_of_approx {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (V g : Ω → ℝ) (hV : MemLp V 2 P) (hg : MemLp g 2 P)
    (happ : ∀ η : ℝ, 0 < η → ∃ f : Ω → ℝ, MemLp f 2 P ∧ ∫ ω, V ω * f ω ∂P = 0 ∧
      ∫ ω, (g ω - f ω) ^ 2 ∂P ≤ η) :
    ∫ ω, V ω * g ω ∂P = 0 := by
  set A := ∫ ω, V ω ^ 2 ∂P with hA
  have hA0 : 0 ≤ A := integral_nonneg fun ω => sq_nonneg _
  have key : ∀ ε : ℝ, 0 < ε → |∫ ω, V ω * g ω ∂P| ≤ ε * (A + 1) / 2 := by
    intro ε hε
    obtain ⟨f, hf, hVf, hgf⟩ := happ (ε ^ 2) (by positivity)
    have hd : MemLp (fun ω => g ω - f ω) 2 P := hg.sub hf
    have i1 : Integrable (fun ω => V ω * g ω) P := hV.integrable_mul hg
    have i2 : Integrable (fun ω => V ω * f ω) P := hV.integrable_mul hf
    have i3 : Integrable (fun ω => V ω * (g ω - f ω)) P := hV.integrable_mul hd
    have hsplit : ∫ ω, V ω * g ω ∂P = ∫ ω, V ω * (g ω - f ω) ∂P := by
      have : (fun ω => V ω * (g ω - f ω)) = fun ω => V ω * g ω - V ω * f ω := by
        funext ω; ring
      rw [this, integral_sub i1 i2, hVf, sub_zero]
    have j1 : Integrable (fun ω => (ε / 2) * V ω ^ 2) P := hV.integrable_sq.const_mul _
    have j2 : Integrable (fun ω => (ε⁻¹ / 2) * (g ω - f ω) ^ 2) P := hd.integrable_sq.const_mul _
    have hle : ∫ ω, |V ω * (g ω - f ω)| ∂P ≤
        ∫ ω, ((ε / 2) * V ω ^ 2 + (ε⁻¹ / 2) * (g ω - f ω) ^ 2) ∂P :=
      integral_mono i3.abs (j1.add j2) fun ω => amgm_abs ε _ _ hε
    rw [integral_add j1 j2, integral_const_mul, integral_const_mul] at hle
    have hinv : (ε⁻¹ / 2) * ∫ ω, (g ω - f ω) ^ 2 ∂P ≤ (ε⁻¹ / 2) * ε ^ 2 :=
      mul_le_mul_of_nonneg_left hgf (by positivity)
    have he : (ε⁻¹ / 2) * ε ^ 2 = ε / 2 := by field_simp
    rw [hsplit]
    calc |∫ ω, V ω * (g ω - f ω) ∂P| ≤ ∫ ω, |V ω * (g ω - f ω)| ∂P :=
          abs_integral_le_integral_abs
      _ ≤ ε * (A + 1) / 2 := by rw [← hA] at hle; nlinarith
  by_contra hne
  have hpos : 0 < |∫ ω, V ω * g ω ∂P| := abs_pos.2 hne
  have h := key (|∫ ω, V ω * g ω ∂P| / (A + 1)) (by positivity)
  have e : |∫ ω, V ω * g ω ∂P| / (A + 1) * (A + 1) / 2 = |∫ ω, V ω * g ω ∂P| / 2 := by
    field_simp
  rw [e] at h
  linarith

end StochCalcR6


namespace StochCalcR5

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR2 Finset Filter
open scoped Topology

/-- Generic: measurability of an appended vector from its coordinates. -/
lemma meas_append {Ω : Type*} [m : MeasurableSpace Ω] {N : ℕ} (u v : Fin N → Ω → ℝ)
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i)) :
    Measurable (fun ω => (WithLp.toLp 2 (Fin.append (fun i => u i ω) (fun i => v i ω)) :
      EuclideanSpace ℝ (Fin (N + N)))) := by
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_lambda _ fun i => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [WithLp.ofLp_toLp, Fin.append_left]; exact hu i
  · simp only [WithLp.ofLp_toLp, Fin.append_right]; exact hv i

/-- Generic: `limsup` of measurable real sequences, for an arbitrary σ-algebra. -/
lemma meas_limsup {Ω : Type*} [m : MeasurableSpace Ω] (f : ℕ → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => limsup (fun i => f i ω) atTop) :=
  Measurable.limsup hf

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Grid-`2^j` increments of `B` (first block) and `B~` (second block) on `[0, T]`. -/
noncomputable def Δ (M : Model p Ω) (j : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin (2 ^ j + 2 ^ j)) :=
  WithLp.toLp 2 (Fin.append
    (fun i : Fin (2 ^ j) => dB M (gr p (2 ^ j) i) (gr p (2 ^ j) ((i : ℕ) + 1)) ω)
    (fun i : Fin (2 ^ j) => ξ M (gr p (2 ^ j) i) (gr p (2 ^ j) ((i : ℕ) + 1)) ω))

lemma Δ_left (M : Model p Ω) (j : ℕ) (ω : Ω) (i : Fin (2 ^ j)) :
    Δ M j ω (Fin.castAdd (2 ^ j) i) = dB M (gr p (2 ^ j) i) (gr p (2 ^ j) ((i : ℕ) + 1)) ω := by
  simp only [Δ, PiLp.toLp_apply, Fin.append_left]

lemma Δ_right (M : Model p Ω) (j : ℕ) (ω : Ω) (i : Fin (2 ^ j)) :
    Δ M j ω (Fin.natAdd (2 ^ j) i) = ξ M (gr p (2 ^ j) i) (gr p (2 ^ j) ((i : ℕ) + 1)) ω := by
  simp only [Δ, PiLp.toLp_apply, Fin.append_right]

lemma Δ_meas (M : Model p Ω) (hM : M.Standing) (j : ℕ) : Measurable (Δ M j) :=
  meas_append _ _ (fun i => dB_meas M hM _ _) (fun i => ξ_meas M hM _ _)

lemma coord_meas (M : Model p Ω) (j : ℕ) (k : Fin (2 ^ j + 2 ^ j)) :
    Measurable[MeasurableSpace.comap (Δ M j) inferInstance] (fun ω => Δ M j ω k) :=
  ((continuous_apply k).comp (PiLp.continuous_ofLp 2 _)).measurable.comp (comap_measurable (Δ M j))

lemma gr_fine (p : Params) (j i : ℕ) : gr p (2 ^ (j + 1)) (2 * i) = gr p (2 ^ j) i := by
  rw [pow_succ, mul_comm 2 i, gr_mul p two_pos]

lemma gr_fine' (p : Params) (j i : ℕ) : gr p (2 ^ (j + 1)) (2 * i + 1 + 1) = gr p (2 ^ j) (i + 1) := by
  rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, gr_fine]

lemma Δ_mono (M : Model p Ω) :
    Monotone fun j => MeasurableSpace.comap (Δ M j) inferInstance := by
  refine monotone_nat_of_le_succ fun j => ?_
  refine Measurable.comap_le ?_
  refine meas_append (m := MeasurableSpace.comap (Δ M (j + 1)) inferInstance) _ _
    (fun i => ?_) (fun i => ?_)
  · have h1 : 2 * (i : ℕ) < 2 ^ (j + 1) := by have := i.isLt; rw [pow_succ]; omega
    have h2 : 2 * (i : ℕ) + 1 < 2 ^ (j + 1) := by have := i.isLt; rw [pow_succ]; omega
    have e : dB M (gr p (2 ^ j) i) (gr p (2 ^ j) ((i : ℕ) + 1)) = fun ω =>
        Δ M (j + 1) ω (Fin.castAdd _ ⟨2 * i, h1⟩) + Δ M (j + 1) ω (Fin.castAdd _ ⟨2 * i + 1, h2⟩) := by
      funext ω
      rw [Δ_left, Δ_left]
      simp only [Fin.val_mk, dB, gr_fine, gr_fine']
      ring
    rw [e]
    exact (coord_meas M (j + 1) _).add (coord_meas M (j + 1) _)
  · have h1 : 2 * (i : ℕ) < 2 ^ (j + 1) := by have := i.isLt; rw [pow_succ]; omega
    have h2 : 2 * (i : ℕ) + 1 < 2 ^ (j + 1) := by have := i.isLt; rw [pow_succ]; omega
    have e : ξ M (gr p (2 ^ j) i) (gr p (2 ^ j) ((i : ℕ) + 1)) = fun ω =>
        Δ M (j + 1) ω (Fin.natAdd _ ⟨2 * i, h1⟩) + Δ M (j + 1) ω (Fin.natAdd _ ⟨2 * i + 1, h2⟩) := by
      funext ω
      rw [Δ_right, Δ_right]
      simp only [Fin.val_mk, ξ, gr_fine, gr_fine']
      ring
    rw [e]
    exact (coord_meas M (j + 1) _).add (coord_meas M (j + 1) _)

/-- Partial sums of the `B` block: `B (gr k) - B 0`. -/
lemma PB_meas (M : Model p Ω) (j : ℕ) :
    ∀ k, k ≤ 2 ^ j → Measurable[MeasurableSpace.comap (Δ M j) inferInstance]
      (fun ω => M.B (gr p (2 ^ j) k) ω - M.B 0 ω) := by
  intro k
  induction k with
  | zero => intro _; simp [gr]
  | succ k ih =>
    intro hk
    have hk' : k < 2 ^ j := by omega
    have e : (fun ω => M.B (gr p (2 ^ j) (k + 1)) ω - M.B 0 ω) = fun ω =>
        (M.B (gr p (2 ^ j) k) ω - M.B 0 ω) + Δ M j ω (Fin.castAdd _ ⟨k, hk'⟩) := by
      funext ω
      rw [Δ_left]
      simp only [Fin.val_mk, dB]
      ring
    rw [e]
    exact (ih hk'.le).add (coord_meas M j _)

lemma PBt_meas (M : Model p Ω) (j : ℕ) :
    ∀ k, k ≤ 2 ^ j → Measurable[MeasurableSpace.comap (Δ M j) inferInstance]
      (fun ω => M.Bt (gr p (2 ^ j) k) ω - M.Bt 0 ω) := by
  intro k
  induction k with
  | zero => intro _; simp [gr]
  | succ k ih =>
    intro hk
    have hk' : k < 2 ^ j := by omega
    have e : (fun ω => M.Bt (gr p (2 ^ j) (k + 1)) ω - M.Bt 0 ω) = fun ω =>
        (M.Bt (gr p (2 ^ j) k) ω - M.Bt 0 ω) + Δ M j ω (Fin.natAdd _ ⟨k, hk'⟩) := by
      funext ω
      rw [Δ_right]
      simp only [Fin.val_mk, ξ]
      ring
    rw [e]
    exact (ih hk'.le).add (coord_meas M j _)

/-- The grid index just below `s`. -/
noncomputable def kj (p : Params) (s : ℝ≥0) (j : ℕ) : ℕ := ⌊(s : ℝ) * 2 ^ j / p.T⌋₊

lemma kj_le (p : Params) {s : ℝ≥0} (hs : s ≤ p.T) (j : ℕ) : kj p s j ≤ 2 ^ j := by
  have hT : (0 : ℝ) < p.T := p.hT
  have hs' : (s : ℝ) ≤ p.T := hs
  refine Nat.floor_le_of_le ?_
  rw [div_le_iff₀ hT]
  push_cast
  nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) j]

lemma gr_tendsto (p : Params) {s : ℝ≥0} :
    Tendsto (fun j => gr p (2 ^ j) (kj p s j)) atTop (𝓝 s) := by
  have hT : (0 : ℝ) < p.T := p.hT
  rw [← NNReal.tendsto_coe]
  have hval : ∀ j, ((gr p (2 ^ j) (kj p s j) : ℝ≥0) : ℝ) =
      (⌊(s : ℝ) * 2 ^ j / p.T⌋₊ : ℝ) * ((p.T : ℝ) / 2 ^ j) := fun j => by
    simp [gr, kj]
  have hd : ∀ j, (0 : ℝ) < (p.T : ℝ) / 2 ^ j := fun j => by positivity
  have hx : ∀ j, (s : ℝ) * 2 ^ j / p.T * ((p.T : ℝ) / 2 ^ j) = s := fun j => by
    field_simp
  have hup : ∀ j, ((gr p (2 ^ j) (kj p s j) : ℝ≥0) : ℝ) ≤ s := fun j => by
    have h1 := mul_le_mul_of_nonneg_right
      (Nat.floor_le (a := (s : ℝ) * 2 ^ j / p.T) (by positivity)) (hd j).le
    rw [hx j] at h1
    rw [hval]; exact h1
  have hlow : ∀ j, (s : ℝ) - (p.T : ℝ) / 2 ^ j ≤ ((gr p (2 ^ j) (kj p s j) : ℝ≥0) : ℝ) := fun j => by
    rw [hval]
    have h1 := Nat.lt_floor_add_one ((s : ℝ) * 2 ^ j / p.T)
    have h2 : ((s : ℝ) * 2 ^ j / p.T - 1) * ((p.T : ℝ) / 2 ^ j) ≤
        (⌊(s : ℝ) * 2 ^ j / p.T⌋₊ : ℝ) * ((p.T : ℝ) / 2 ^ j) :=
      mul_le_mul_of_nonneg_right (by linarith) (hd j).le
    rw [sub_mul, hx j, one_mul] at h2
    exact h2
  have h0 : Tendsto (fun j : ℕ => (p.T : ℝ) / 2 ^ j) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hl : Tendsto (fun j : ℕ => (s : ℝ) - (p.T : ℝ) / 2 ^ j) atTop (𝓝 (s : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (s : ℝ))).sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hup

/-- The σ-algebra generated by all grid increments. -/
noncomputable def GΔ (M : Model p Ω) : MeasurableSpace Ω := ⨆ j, MeasurableSpace.comap (Δ M j) inferInstance

lemma le_GΔ (M : Model p Ω) (j : ℕ) : MeasurableSpace.comap (Δ M j) inferInstance ≤ GΔ M :=
  le_iSup (fun i => MeasurableSpace.comap (Δ M i) inferInstance) j

/-- **R5.** `F_T` lies below the augmented σ-algebra of all grid increments. -/
theorem F_le_aug (M : Model p Ω) (hM : M.Standing) :
    M.F p.T ≤ aug (⨆ j, MeasurableSpace.comap (Δ M j) inferInstance) M.P := by
  change M.F p.T ≤ aug (GΔ M) M.P
  have h𝒢le : GΔ M ≤ mΩ := iSup_le fun j => (Δ_meas M hM j).comap_le
  rw [hM.filtF p.T]
  refine sup_le (iSup₂_le fun s hs => ?_) le_sup_right
  set g : Ω → ℝ × ℝ := fun ω =>
    (limsup (fun j => M.B (gr p (2 ^ j) (kj p s j)) ω - M.B 0 ω) atTop,
     limsup (fun j => M.Bt (gr p (2 ^ j) (kj p s j)) ω - M.Bt 0 ω) atTop) with hg
  have hgm : Measurable[GΔ M] g := by
    refine Measurable.prodMk ?_ ?_
    · exact meas_limsup (m := GΔ M) _ fun j => (PB_meas M j _ (kj_le p hs j)).mono (le_GΔ M j) le_rfl
    · exact meas_limsup (m := GΔ M) _ fun j => (PBt_meas M j _ (kj_le p hs j)).mono (le_GΔ M j) le_rfl
  have hY := StochCalcBr.pair_measurable M hM s
  refine comap_le_aug (GΔ M) _ g hY hgm ?_ ?_
  · exact (measurableSet_eq_fun hY (hgm.mono h𝒢le le_rfl)).compl
  · filter_upwards [hM.brownB.cont, hM.brownBt.cont, hM.brownB.eval_zero_ae_eq_zero,
      hM.brownBt.eval_zero_ae_eq_zero] with ω h1 h2 h3 h4
    have t1 : Tendsto (fun j => M.B (gr p (2 ^ j) (kj p s j)) ω - M.B 0 ω) atTop
        (𝓝 (M.B s ω - M.B 0 ω)) := ((h1.tendsto s).comp (gr_tendsto p)).sub_const _
    have t2 : Tendsto (fun j => M.Bt (gr p (2 ^ j) (kj p s j)) ω - M.Bt 0 ω) atTop
        (𝓝 (M.Bt s ω - M.Bt 0 ω)) := ((h2.tendsto s).comp (gr_tendsto p)).sub_const _
    show (M.B s ω, M.Bt s ω) = g ω
    rw [hg]
    simp only
    rw [t1.limsup_eq, t2.limsup_eq]
    simp [h3, h4]

/-- Coefficients of `⟪Δ_j, t⟫` on the two blocks. -/
noncomputable def lamt {j : ℕ} (t : EuclideanSpace ℝ (Fin (2 ^ j + 2 ^ j))) (k : ℕ) : ℝ :=
  if h : k < 2 ^ j then t (Fin.castAdd (2 ^ j) ⟨k, h⟩) else 0

noncomputable def muT {j : ℕ} (t : EuclideanSpace ℝ (Fin (2 ^ j + 2 ^ j))) (k : ℕ) : ℝ :=
  if h : k < 2 ^ j then t (Fin.natAdd (2 ^ j) ⟨k, h⟩) else 0

lemma inner_Δ (M : Model p Ω) (j : ℕ) (ω : Ω) (t : EuclideanSpace ℝ (Fin (2 ^ j + 2 ^ j))) :
    inner ℝ (Δ M j ω) t = ∑ k ∈ range (2 ^ j),
      (lamt t k * dB M (gr p (2 ^ j) k) (gr p (2 ^ j) (k + 1)) ω +
        muT t k * ξ M (gr p (2 ^ j) k) (gr p (2 ^ j) (k + 1)) ω) := by
  rw [PiLp.inner_apply, Fin.sum_univ_add, ← Fin.sum_univ_eq_sum_range, Finset.sum_add_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · rw [Δ_left]; simp [lamt, i.isLt, mul_comm]
  · rw [Δ_right]; simp [muT, i.isLt, mul_comm]

lemma lamt_le {j : ℕ} (t : EuclideanSpace ℝ (Fin (2 ^ j + 2 ^ j))) (k : ℕ) :
    |lamt t k| ≤ ∑ i, |t i| ∧ |muT t k| ≤ ∑ i, |t i| := by
  have h0 : (0 : ℝ) ≤ ∑ i, |t i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  unfold lamt muT
  split_ifs with h
  · exact ⟨Finset.single_le_sum (f := fun i => |t i|) (fun i _ => abs_nonneg _) (Finset.mem_univ _),
      Finset.single_le_sum (f := fun i => |t i|) (fun i _ => abs_nonneg _) (Finset.mem_univ _)⟩
  · simp [h0]

end StochCalcR5


namespace StochCalcR7

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR5 StochCalcR1M
  Finset Filter

lemma re_AIx (A : ℂ) (x : ℝ) : (A * (Complex.I * (x : ℂ))).re = -(A.im * x) := by
  simp [Complex.mul_re]

lemma im_AIx (A : ℂ) (x : ℝ) : (A * (Complex.I * (x : ℂ))).im = A.re * x := by
  simp [Complex.mul_im]

lemma memLp_trim_of {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure[m0] Ω} (hm : m ≤ m0)
    {f : Ω → ℝ} (hf : StronglyMeasurable[m] f) (h : MemLp f 2 μ) : MemLp f 2 (μ.trim hm) :=
  ⟨hf.aestronglyMeasurable, by rw [eLpNorm_trim hm hf]; exact h.2⟩

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma cos_meas (M : Model p Ω) (hM : M.Standing) (j : ℕ) (t : EuclideanSpace ℝ (Fin (2 ^ j + 2 ^ j))) :
    Measurable (fun ω => Real.cos (inner ℝ (Δ M j ω) t)) :=
  Real.continuous_cos.measurable.comp
    ((continuous_inner.comp (continuous_id.prodMk continuous_const)).measurable.comp (Δ_meas M hM j))

lemma sin_meas (M : Model p Ω) (hM : M.Standing) (j : ℕ) (t : EuclideanSpace ℝ (Fin (2 ^ j + 2 ^ j))) :
    Measurable (fun ω => Real.sin (inner ℝ (Δ M j ω) t)) :=
  Real.continuous_sin.measurable.comp
    ((continuous_inner.comp (continuous_id.prodMk continuous_const)).measurable.comp (Δ_meas M hM j))

lemma cos_memLp (M : Model p Ω) (hM : M.Standing) (j : ℕ) (t : EuclideanSpace ℝ (Fin (2 ^ j + 2 ^ j))) :
    MemLp (fun ω => Real.cos (inner ℝ (Δ M j ω) t)) 2 M.P := by
  have := hM.prob
  exact MemLp.of_bound (cos_meas M hM j t).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one _)

lemma sin_memLp (M : Model p Ω) (hM : M.Standing) (j : ℕ) (t : EuclideanSpace ℝ (Fin (2 ^ j + 2 ^ j))) :
    MemLp (fun ω => Real.sin (inner ℝ (Δ M j ω) t)) 2 M.P := by
  have := hM.prob
  exact MemLp.of_bound (sin_meas M hM j t).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one _)

/-- **R7a.** `cos⟪Δ_j, t⟫` and `sin⟪Δ_j, t⟫` are `L²`-approximable by grid sums. -/
theorem trig_mem (M : Model p Ω) (hM : M.Standing) (j : ℕ)
    (t : EuclideanSpace ℝ (Fin (2 ^ j + 2 ^ j))) (η : ℝ) (hη : 0 < η) :
    ∃ f g : Ω → ℝ, IsGS M f ∧ IsGS M g ∧
      ∫ ω, (Real.cos (inner ℝ (Δ M j ω) t) - f ω) ^ 2 ∂M.P ≤ η ∧
      ∫ ω, (Real.sin (inner ℝ (Δ M j ω) t) - g ω) ^ 2 ∂M.P ≤ η := by
  have := hM.prob
  obtain ⟨m, hm, a, b, hab, c, A, hAm, hAn, hbd⟩ := trig_approx M hM (2 ^ j) (pow_pos two_pos j)
    (lamt t) (muT t) (∑ i, |t i|) (lamt_le t) η hη
  have hS : ∀ ω, (∑ k ∈ range (2 ^ j), (lamt t k * dB M (gr p (2 ^ j) k) (gr p (2 ^ j) (k + 1)) ω +
      muT t k * ξ M (gr p (2 ^ j) k) (gr p (2 ^ j) (k + 1)) ω) : ℝ) = inner ℝ (Δ M j ω) t :=
    fun ω => (inner_Δ M j ω t).symm
  simp only [hS] at hbd
  set f : Ω → ℝ := fun ω => c.re +
    ∑ l ∈ range m, (-(A l ω).im * a l) * dB M (gr p m l) (gr p m (l + 1)) ω +
    ∑ l ∈ range m, (-(A l ω).im * b l) * ξ M (gr p m l) (gr p m (l + 1)) ω with hf
  set g : Ω → ℝ := fun ω => c.im +
    ∑ l ∈ range m, ((A l ω).re * a l) * dB M (gr p m l) (gr p m (l + 1)) ω +
    ∑ l ∈ range m, ((A l ω).re * b l) * ξ M (gr p m l) (gr p m (l + 1)) ω with hg
  have hbA : ∀ l ω, |(A l ω).im| ≤ 1 ∧ |(A l ω).re| ≤ 1 := fun l ω =>
    ⟨(Complex.abs_im_le_norm _).trans (hAn l ω), (Complex.abs_re_le_norm _).trans (hAn l ω)⟩
  have hfG : IsGS M f := by
    refine ⟨m, hm, c.re, fun l ω => -(A l ω).im * a l, fun l ω => -(A l ω).im * b l,
      ∑ i, |t i|, fun l => ?_, fun l ω => ?_, fun l => ?_, fun l ω => ?_, rfl⟩
    · exact ((Complex.measurable_im.comp (hAm l)).neg.mul_const _).stronglyMeasurable
    · rw [abs_mul, abs_neg]
      exact (mul_le_mul (hbA l ω).1 (hab l).1 (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    · exact ((Complex.measurable_im.comp (hAm l)).neg.mul_const _).stronglyMeasurable
    · rw [abs_mul, abs_neg]
      exact (mul_le_mul (hbA l ω).1 (hab l).2 (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hgG : IsGS M g := by
    refine ⟨m, hm, c.im, fun l ω => (A l ω).re * a l, fun l ω => (A l ω).re * b l,
      ∑ i, |t i|, fun l => ?_, fun l ω => ?_, fun l => ?_, fun l ω => ?_, rfl⟩
    · exact ((Complex.measurable_re.comp (hAm l)).mul_const _).stronglyMeasurable
    · rw [abs_mul]
      exact (mul_le_mul (hbA l ω).2 (hab l).1 (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    · exact ((Complex.measurable_re.comp (hAm l)).mul_const _).stronglyMeasurable
    · rw [abs_mul]
      exact (mul_le_mul (hbA l ω).2 (hab l).2 (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  set z : Ω → ℂ := fun ω => Complex.exp (Complex.I * ((inner ℝ (Δ M j ω) t : ℝ) : ℂ)) - c -
    ∑ l ∈ range m, A l ω * (Complex.I * (xg M m a b l ω : ℂ)) with hz
  have hre : ∀ ω, (z ω).re = Real.cos (inner ℝ (Δ M j ω) t) - f ω := by
    intro ω
    have e1 : (Complex.exp (Complex.I * ((inner ℝ (Δ M j ω) t : ℝ) : ℂ))).re =
        Real.cos (inner ℝ (Δ M j ω) t) := by
      rw [mul_comm, Complex.exp_ofReal_mul_I_re]
    have e2 : ∑ l ∈ range m, (A l ω * (Complex.I * (xg M m a b l ω : ℂ))).re =
        ∑ l ∈ range m, (-(A l ω).im * a l) * dB M (gr p m l) (gr p m (l + 1)) ω +
        ∑ l ∈ range m, (-(A l ω).im * b l) * ξ M (gr p m l) (gr p m (l + 1)) ω := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [re_AIx]; simp only [xg]; ring
    simp only [hz, Complex.sub_re, Complex.re_sum, e1, e2, hf]
    ring
  have him : ∀ ω, (z ω).im = Real.sin (inner ℝ (Δ M j ω) t) - g ω := by
    intro ω
    have e1 : (Complex.exp (Complex.I * ((inner ℝ (Δ M j ω) t : ℝ) : ℂ))).im =
        Real.sin (inner ℝ (Δ M j ω) t) := by
      rw [mul_comm, Complex.exp_ofReal_mul_I_im]
    have e2 : ∑ l ∈ range m, (A l ω * (Complex.I * (xg M m a b l ω : ℂ))).im =
        ∑ l ∈ range m, ((A l ω).re * a l) * dB M (gr p m l) (gr p m (l + 1)) ω +
        ∑ l ∈ range m, ((A l ω).re * b l) * ξ M (gr p m l) (gr p m (l + 1)) ω := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [im_AIx]; simp only [xg]; ring
    simp only [hz, Complex.sub_im, Complex.im_sum, e1, e2, hg]
    ring
  have hI1 : Integrable (fun ω => (Real.cos (inner ℝ (Δ M j ω) t) - f ω) ^ 2) M.P :=
    ((cos_memLp M hM j t).sub (IsGS_props M hM hfG).2).integrable_sq
  have hI2 : Integrable (fun ω => (Real.sin (inner ℝ (Δ M j ω) t) - g ω) ^ 2) M.P :=
    ((sin_memLp M hM j t).sub (IsGS_props M hM hgG).2).integrable_sq
  have hsum : ∫ ω, (Real.cos (inner ℝ (Δ M j ω) t) - f ω) ^ 2 ∂M.P +
      ∫ ω, (Real.sin (inner ℝ (Δ M j ω) t) - g ω) ^ 2 ∂M.P ≤ η := by
    rw [← integral_add hI1 hI2]
    refine le_of_eq_of_le (integral_congr_ae (ae_of_all _ fun ω => ?_)) hbd
    show _ = ‖z ω‖ ^ 2
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have h1 : 0 ≤ ∫ ω, (Real.cos (inner ℝ (Δ M j ω) t) - f ω) ^ 2 ∂M.P :=
    integral_nonneg fun ω => sq_nonneg _
  have h2 : 0 ≤ ∫ ω, (Real.sin (inner ℝ (Δ M j ω) t) - g ω) ^ 2 ∂M.P :=
    integral_nonneg fun ω => sq_nonneg _
  exact ⟨f, g, hfG, hgG, by linarith, by linarith⟩

lemma H_measF (M : Model p Ω) (hM : M.Standing) (P R : ℝ) : Measurable[M.F p.T] (M.H P R) := by
  have hC : Measurable[M.F p.T] (M.C p.T) :=
    ((hM.C_adapted p.T).mono (StochCalcD1aW.G_le_F M hM p.T)).measurable
  have hA : Measurable[M.F p.T] M.AT := hC.add ((Bt_measF M hM le_rfl).const_mul _)
  show Measurable[M.F p.T] (fun ω => payoff p P R (M.AT ω))
  unfold payoff
  exact measurable_const.sub (measurable_const.mul ((measurable_const.sub hA).max measurable_const))

/-- **R7b (hsep).** On `(Ω, F_T, P)`, an `L²` variable orthogonal to all grid sums vanishes. -/
theorem hsep (M : Model p Ω) (hM : M.Standing) (V : Ω → ℝ)
    (hV : MemLp V 2 (M.P.trim (M.F.le p.T)))
    (horth : ∀ f, IsGS M f → ∫ ω, V ω * f ω ∂(M.P.trim (M.F.le p.T)) = 0) :
    V =ᵐ[M.P.trim (M.F.le p.T)] 0 := by
  have := hM.prob
  have hFle := M.F.le p.T
  set V' := hV.1.mk V with hV'def
  have hV'sm : StronglyMeasurable[M.F p.T] V' := hV.1.stronglyMeasurable_mk
  have hVV' : V =ᵐ[M.P.trim hFle] V' := hV.1.ae_eq_mk
  have hV'2 : MemLp V' 2 M.P := memLp_of_memLp_trim hFle (hV.ae_eq hVV')
  have horth' : ∀ f, IsGS M f → ∫ ω, V' ω * f ω ∂M.P = 0 := by
    intro f hf
    obtain ⟨hfm, -⟩ := IsGS_props M hM hf
    rw [integral_trim hFle (f := fun ω => V' ω * f ω) (hV'sm.mul hfm), ← horth f hf]
    refine integral_congr_ae ?_
    filter_upwards [hVV'] with ω h
    rw [h]
  have htrig : ∀ j (t : EuclideanSpace ℝ (Fin (2 ^ j + 2 ^ j))),
      ∫ ω, V' ω * Real.cos (inner ℝ (Δ M j ω) t) ∂M.P = 0 ∧
      ∫ ω, V' ω * Real.sin (inner ℝ (Δ M j ω) t) ∂M.P = 0 := by
    intro j t
    constructor
    · refine StochCalcR6.orth_of_approx V' _ hV'2 (cos_memLp M hM j t) fun η hη => ?_
      obtain ⟨f, g, hf, hg, h1, h2⟩ := trig_mem M hM j t η hη
      exact ⟨f, (IsGS_props M hM hf).2, horth' f hf, h1⟩
    · refine StochCalcR6.orth_of_approx V' _ hV'2 (sin_memLp M hM j t) fun η hη => ?_
      obtain ⟨f, g, hf, hg, h1, h2⟩ := trig_mem M hM j t η hη
      exact ⟨g, (IsGS_props M hM hg).2, horth' g hg, h2⟩
  have hV'0 : V' =ᵐ[M.P] 0 :=
    StochCalcR2.ae_eq_zero_of_trig (M.F p.T) (fun j => 2 ^ j + 2 ^ j) (Δ M) (Δ_meas M hM)
      (Δ_mono M) (F_le_aug M hM) V' hV'sm (hV'2.integrable one_le_two) htrig
  exact hVV'.trans (hV'sm.ae_eq_trim_of_stronglyMeasurable hFle stronglyMeasurable_const hV'0)

/-- **R7 (hR of `dens_of_rep`).** -/
theorem hR (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2) (P R : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ n : ℕ, 0 < n ∧ ∃ c : ℝ, ∃ Y Z : ℕ → Ω → ℝ, ∃ C : ℝ,
      (∀ k, StronglyMeasurable[M.F (gr p n k)] (Y k)) ∧ (∀ k ω, |Y k ω| ≤ C) ∧
      (∀ k, StronglyMeasurable[M.F (gr p n k)] (Z k)) ∧ (∀ k ω, |Z k ω| ≤ C) ∧
      ∫ ω, (M.H P R ω - c - ∑ k ∈ Finset.range n, Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω -
        ∑ k ∈ Finset.range n, Z k ω * ξ M (gr p n k) (gr p n (k + 1)) ω) ^ 2 ∂M.P ≤ η := by
  intro η hη
  have := hM.prob
  have hFle := M.F.le p.T
  have hHm : StronglyMeasurable[M.F p.T] (M.H P R) := (H_measF M hM P R).stronglyMeasurable
  have hH2 : MemLp (M.H P R) 2 (M.P.trim hFle) := memLp_trim_of hFle hHm (StochCalcHedgeDeg.H_memLp M hM hL2 P R)
  obtain ⟨f, hf, hfη⟩ := StochCalcR3.approx_of_sep (mΩ := M.F p.T) (P := M.P.trim hFle) (IsGS M)
    (fun f hf => memLp_trim_of hFle (IsGS_props M hM hf).1 (IsGS_props M hM hf).2) (IsGS_zero M)
    (fun f g hf hg => IsGS_add M hf hg) (fun c f hf => IsGS_smul M c hf)
    (fun V hV h => hsep M hM V hV h) (M.H P R) hH2 η hη
  have hfm := (IsGS_props M hM hf).1
  rw [← integral_trim hFle (f := fun ω => (M.H P R ω - f ω) ^ 2)
    ((hHm.measurable.sub hfm.measurable).pow_const 2).stronglyMeasurable] at hfη
  obtain ⟨n, hn, c, Y, Z, C, hYm, hYb, hZm, hZb, rfl⟩ := hf
  refine ⟨n, hn, c, Y, Z, C, hYm, hYb, hZm, hZb,
    le_of_eq_of_le (integral_congr_ae (ae_of_all _ fun ω => ?_)) hfη⟩
  show _ = (M.H P R ω - (c + _ + _)) ^ 2
  ring

end StochCalcR7


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}


end StochCalcTC


namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcTC


namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

end StochCalcTC


namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

end StochCalcTC


set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcMart

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcMart


namespace StochCalcS1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcS1M


namespace StochCalcS2

open ItoLib StochCalcTC StochCalcL2M

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

section pathwise

variable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) {R : ℝ} (hR : 0 ≤ R) (ω : Ω) {g : ℝ → ℝ}
  (hg : Measurable g) (hg2 : IntervalIntegrable (fun u => g u ^ 2) volume 0 t.val)
include hR hg hg2

end pathwise

end StochCalcS2


namespace StochCalcS2

open ItoLib StochCalcTC StochCalcL2M

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

end StochCalcS2


namespace StochCalcS2

open ItoLib StochCalcTC StochCalcL2M

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcS2


namespace StochCalcS2M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcD2 StochCalcD3

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcS2M


open MeasureTheory Filter
open scoped NNReal Topology

namespace StochCalcS2X

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS2M StochCalcD2 StochCalcD3

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcS2X


open MeasureTheory Filter
open scoped NNReal Topology ENNReal

namespace StochCalcS3

open EthierKurtz ItoLib StochCalcTC StochCalcS2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcS3


namespace StochCalcS3M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS2M StochCalcS3

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcS3M


namespace StochCalcFe

open Real

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end line

end StochCalcFe


namespace StochCalcS3c

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS2M StochCalcS3 StochCalcS3M StochCalcFe

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcS3c


namespace StochCalcDegFinal

open HedgePSNV StochCalcD1aW StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcDegFinal



end StochCalcP6

open MeasureTheory ProbabilityTheory HedgePSNV
open scoped NNReal ENNReal

theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (P R : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ n : ℕ, 0 < n ∧ ∃ c : ℝ, ∃ Y Z : ℕ → Ω → ℝ, ∃ C : ℝ,
      (∀ k, StronglyMeasurable[M.F (((k : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0)))] (Y k)) ∧ (∀ k ω, |Y k ω| ≤ C) ∧
      (∀ k, StronglyMeasurable[M.F (((k : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0)))] (Z k)) ∧ (∀ k ω, |Z k ω| ≤ C) ∧
      ∫ ω, (M.H P R ω - c - ∑ k ∈ Finset.range n, Y k ω * (M.B ((((k + 1 : ℕ) : ℝ≥0)) * (p.T / (n : ℝ≥0))) ω - M.B (((k : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0))) ω) -
        ∑ k ∈ Finset.range n, Z k ω * (M.Bt ((((k + 1 : ℕ) : ℝ≥0)) * (p.T / (n : ℝ≥0))) ω - M.Bt (((k : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0))) ω)) ^ 2 ∂M.P ≤ η := by
  exact StochCalcP6.StochCalcR7.hR M hM hL2 P R
