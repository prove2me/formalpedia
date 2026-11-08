-- Prove2me | solution 1 for HedgePSNV.theorem_1_ii_degenerate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T22:50:03.801666+00:00
-- url     : https://prove2.me/submissions/f3330abf-965f-4976-a2eb-d314152fd4d4

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
import Theorems.Thm_HedgePSNV_degenerate_price_martingale
import Theorems.Thm_HedgePSNV_payoff_simple_integral_density
import Theorems.Thm_HedgePSNV_degenerate_simple_integrals_attainable
import Theorems.Thm_HedgePSNV_degenerate_price_volatility_ne_zero

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

lemma integral_exp_mul (hξ : HasLaw ξ (gaussianReal 0 v) P) (c : ℝ) :
    ∫ ω, Real.exp (c * ξ ω) ∂P = Real.exp ((v : ℝ) * c ^ 2 / 2) := by
  have := mgf_gaussianReal (μ := 0) (v := v) hξ.map_eq c
  rw [mgf] at this
  rw [this]; simp

/-- The exponential tilt. -/
noncomputable def L (ξ : Ω → ℝ) (v : ℝ≥0) (c : ℝ) (ω : Ω) : ℝ :=
  Real.exp (c * ξ ω - (v : ℝ) * c ^ 2 / 2)

lemma L_pos (c : ℝ) (ω : Ω) : 0 < L ξ v c ω := Real.exp_pos _

lemma L_eq (c : ℝ) (ω : Ω) :
    L ξ v c ω = Real.exp (c * ξ ω) * Real.exp (-((v : ℝ) * c ^ 2 / 2)) := by
  rw [L, ← Real.exp_add]; ring_nf

lemma L_measurable (hm : Measurable ξ) (c : ℝ) : Measurable (L ξ v c) := by
  unfold L; fun_prop

lemma integral_L (hξ : HasLaw ξ (gaussianReal 0 v) P) (c : ℝ) :
    ∫ ω, L ξ v c ω ∂P = 1 := by
  simp_rw [L_eq]
  rw [integral_mul_const, integral_exp_mul hξ, ← Real.exp_add]; simp

lemma memLp_L (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) (c : ℝ) :
    MemLp (L ξ v c) 2 P := by
  refine (memLp_two_iff_integrable_sq (L_measurable hm c).aestronglyMeasurable).2 ?_
  have : (fun ω => L ξ v c ω ^ 2) =
      fun ω => Real.exp ((2 * c) * ξ ω) * Real.exp (-((v : ℝ) * c ^ 2)) := by
    funext ω; rw [L, sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [this]
  exact (integrable_exp_mul hm hξ _).mul_const _

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

/-- `|e^a - 1| ≤ |a| e^{|a|}`. -/
lemma abs_exp_sub_one_le' (a : ℝ) : |Real.exp a - 1| ≤ |a| * Real.exp |a| := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by linarith [Real.add_one_le_exp a])]
    have h1 := Real.add_one_le_exp (-a)
    have h2 : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos a]
  · rw [abs_of_nonpos h, abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 h])]
    have h1 := Real.add_one_le_exp a
    have h2 : 1 ≤ Real.exp (-a) := Real.one_le_exp (by linarith)
    nlinarith

/-- The dominating function of the difference quotients. -/
noncomputable def G (ξ : Ω → ℝ) (v : ℝ≥0) (ω : Ω) : ℝ :=
  (|ξ ω| + v) * Real.exp (|ξ ω| + v)

lemma L_sub_one_le (c : ℝ) (hc : |c| ≤ 1) (ω : Ω) :
    |L ξ v c ω - 1| ≤ |c| * G ξ v ω := by
  have hv : (0 : ℝ) ≤ v := v.2
  have hcc : c ^ 2 ≤ |c| := by
    rw [← sq_abs]; nlinarith [abs_nonneg c]
  have ha : |c * ξ ω - (v : ℝ) * c ^ 2 / 2| ≤ |c| * (|ξ ω| + v) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (v : ℝ) * c ^ 2 / 2)]
    nlinarith [abs_nonneg (ξ ω), abs_nonneg c]
  have ha' : |c * ξ ω - (v : ℝ) * c ^ 2 / 2| ≤ |ξ ω| + v := by
    refine ha.trans ?_
    nlinarith [abs_nonneg (ξ ω), abs_nonneg c]
  refine (abs_exp_sub_one_le' _).trans ?_
  rw [G, ← mul_assoc]
  exact mul_le_mul ha (Real.exp_le_exp.2 ha') (Real.exp_pos _).le
    (by positivity)

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

lemma tendsto_slope_L (ω : Ω) :
    Tendsto (fun c : ℝ => (L ξ v c ω - 1) / c) (𝓝[≠] 0) (𝓝 (ξ ω)) := by
  have hd : HasDerivAt (fun c : ℝ => L ξ v c ω) (ξ ω) 0 := by
    have h1 : HasDerivAt (fun c : ℝ => c * ξ ω - (v : ℝ) * c ^ 2 / 2) (ξ ω) 0 := by
      have h2 : HasDerivAt (fun c : ℝ => (v : ℝ) * c ^ 2 / 2) 0 0 := by
        have := ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (v : ℝ)).div_const 2
        simpa using this
      have h3 : HasDerivAt (fun c : ℝ => c * ξ ω) (ξ ω) 0 := by
        simpa using (hasDerivAt_id' (0 : ℝ)).mul_const (ξ ω)
      have h4 := h3.fun_sub h2; rw [sub_zero] at h4; exact h4
    have := h1.exp
    simpa [L] using this
  have := hd.tendsto_slope_zero
  simp only [zero_add, smul_eq_mul] at this
  refine this.congr' (Eventually.of_forall fun c => ?_)
  simp [L, div_eq_inv_mul]

lemma memLp_xi (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P) : MemLp ξ 2 P := by
  refine (memLp_G hm hξ).mono hm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  have h1 : |ξ ω| ≤ |ξ ω| + v := le_add_of_nonneg_right v.2
  have h2 : 1 ≤ Real.exp (|ξ ω| + v) := Real.one_le_exp (by positivity)
  have h3 : 0 ≤ G ξ v ω := by unfold G; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h3]
  unfold G
  have h4 : (0 : ℝ) ≤ |ξ ω| + v := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 h4]

/-- `E[ξ Y] = 0` when `E[(L c - 1) Y] = 0` for all small `c ≠ 0` and `Y ∈ L²`. -/
theorem integral_mul_eq_zero (hm : Measurable ξ) (hξ : HasLaw ξ (gaussianReal 0 v) P)
    {Y : Ω → ℝ} (hY : MemLp Y 2 P)
    (h : ∀ c : ℝ, c ≠ 0 → |c| ≤ 1 → ∫ ω, (L ξ v c ω - 1) * Y ω ∂P = 0) :
    ∫ ω, ξ ω * Y ω ∂P = 0 := by
  set cs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hcs
  have hcs0 : ∀ n, cs n ≠ 0 := fun n => by simp [hcs]; positivity
  have hcs1 : ∀ n, |cs n| ≤ 1 := fun n => by
    rw [abs_of_pos (by simp [hcs]; positivity)]
    rw [hcs, div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hlim : Tendsto cs atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hcs0⟩
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hGY : Integrable (fun ω => G ξ v ω * Y ω) P := (memLp_G hm hξ).integrable_mul hY
  have hYm : AEStronglyMeasurable Y P := hY.aestronglyMeasurable
  have hdct := tendsto_integral_of_dominated_convergence (μ := P)
    (F := fun n ω => (L ξ v (cs n) ω - 1) / cs n * Y ω) (f := fun ω => ξ ω * Y ω)
    (fun ω => ‖G ξ v ω * Y ω‖)
    (fun n => (((L_measurable hm _).sub_const 1).div_const _).aestronglyMeasurable.mul hYm)
    hGY.norm
    (fun n => Eventually.of_forall fun ω => by
      rw [norm_mul, norm_mul, norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := L_sub_one_le (ξ := ξ) (v := v) (cs n) (hcs1 n) ω
      have hc : 0 < |cs n| := abs_pos.2 (hcs0 n)
      have hG0 : 0 ≤ G ξ v ω := by unfold G; positivity
      rw [Real.norm_eq_abs (G ξ v ω), abs_of_nonneg hG0]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [div_le_iff₀ hc]; linarith)
    (Eventually.of_forall fun ω => ((tendsto_slope_L ω).comp hlim).mul_const (Y ω))
  have hzero : ∀ n, ∫ ω, (L ξ v (cs n) ω - 1) / cs n * Y ω ∂P = 0 := fun n => by
    have : (fun ω => (L ξ v (cs n) ω - 1) / cs n * Y ω) =
        fun ω => (cs n)⁻¹ * ((L ξ v (cs n) ω - 1) * Y ω) := by
      funext ω; rw [div_eq_inv_mul]; ring
    rw [this, integral_const_mul, h _ (hcs0 n) (hcs1 n), mul_zero]
  simp_rw [hzero] at hdct
  exact tendsto_nhds_unique hdct tendsto_const_nhds

end StochCalcGauss


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcTilt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The tilted measure. -/
noncomputable abbrev Qd (P : Measure Ω) (D : Ω → ℝ) : Measure Ω :=
  P.withDensity fun ω => ENNReal.ofReal (D ω)

lemma Qd_prob {D : Ω → ℝ} (hD : Integrable D P) (hpos : ∀ ω, 0 < D ω)
    (h1 : ∫ ω, D ω ∂P = 1) : IsProbabilityMeasure (Qd P D) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall fun ω => (hpos ω).le), h1,
    ENNReal.ofReal_one]

lemma Qd_ac (D : Ω → ℝ) : Qd P D ≪ P := withDensity_absolutelyContinuous _ _

lemma ac_Qd {D : Ω → ℝ} (hm : Measurable D) (hpos : ∀ ω, 0 < D ω) : P ≪ Qd P D :=
  withDensity_absolutelyContinuous' hm.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun ω => (ENNReal.ofReal_pos.2 (hpos ω)).ne')

lemma memLp_rnDeriv {D : Ω → ℝ} (hm : Measurable D) (hpos : ∀ ω, 0 < D ω)
    (h2 : MemLp D 2 P) : MemLp (fun ω => ((Qd P D).rnDeriv P ω).toReal) 2 P := by
  refine h2.ae_eq ?_
  filter_upwards [Measure.rnDeriv_withDensity P hm.ennreal_ofReal] with ω hω
  rw [hω, ENNReal.toReal_ofReal (hpos ω).le]

lemma setIntegral_Qd {D : Ω → ℝ} (hm : Measurable D) (hpos : ∀ ω, 0 < D ω) (g : Ω → ℝ)
    {A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω in A, g ω ∂(Qd P D) = ∫ ω in A, D ω * g ω ∂P := by
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hm.ennreal_ofReal
    (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top) g hA]
  refine setIntegral_congr_fun hA fun ω _ => ?_
  rw [ENNReal.toReal_ofReal (hpos ω).le, smul_eq_mul]

lemma integrable_Qd_iff {D : Ω → ℝ} (hm : Measurable D) (hpos : ∀ ω, 0 < D ω) (g : Ω → ℝ) :
    Integrable g (Qd P D) ↔ Integrable (fun ω => D ω * g ω) P := by
  rw [integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
    (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun ω => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hpos ω).le]

/-- Martingale property under the tilted measure from set-integral identities under `P`. -/
theorem martingale_Qd {D : Ω → ℝ} (hm : Measurable D) (hpos : ∀ ω, 0 < D ω)
    (hD : Integrable D P) (h1 : ∫ ω, D ω ∂P = 1)
    (T : ℝ≥0) (F : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ)
    (hadapt : ∀ t, t ≤ T → StronglyMeasurable[F t] (X t))
    (hint : ∀ t, t ≤ T → Integrable (fun ω => D ω * X t ω) P)
    (hset : ∀ s t : ℝ≥0, s ≤ t → t ≤ T → ∀ A, MeasurableSet[F s] A →
      ∫ ω in A, D ω * X t ω ∂P = ∫ ω in A, D ω * X s ω ∂P) :
    HedgePSNV.IsMartingaleOn T F (Qd P D) X := by
  haveI : IsProbabilityMeasure (Qd P D) := Qd_prob hD hpos h1
  refine ⟨hadapt, fun t ht => (integrable_Qd_iff hm hpos _).2 (hint t ht), fun s t hst ht => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le s)
    ((integrable_Qd_iff hm hpos _).2 (hint t ht))
    (fun A _ _ => ((integrable_Qd_iff hm hpos _).2 (hint s (hst.trans ht))).integrableOn)
    (fun A hA _ => ?_) (hadapt s (hst.trans ht)).aestronglyMeasurable).symm
  rw [setIntegral_Qd hm hpos _ (F.le s _ hA), setIntegral_Qd hm hpos _ (F.le s _ hA),
    hset s t hst ht A hA]

/-- `∫_A Y X_v = ∫_A Y X_s` for an `𝓕`-measurable L² weight and an L² martingale step. -/
lemma setIntegral_mul_step {𝓕 : MeasurableSpace Ω} (h𝓕 : 𝓕 ≤ mΩ) {E Xv Xs : Ω → ℝ}
    (hE : StronglyMeasurable[𝓕] E) (hE2 : MemLp E 2 P) (hXv2 : MemLp Xv 2 P)
    (hmart : condExp 𝓕 P Xv =ᵐ[P] Xs) {A : Set Ω} (hA : MeasurableSet[𝓕] A) :
    ∫ ω in A, E ω * Xv ω ∂P = ∫ ω in A, E ω * Xs ω ∂P := by
  have hA' : MeasurableSet[mΩ] A := h𝓕 _ hA
  have hY : StronglyMeasurable[𝓕] (A.indicator E) := hE.indicator hA
  have hY2 : MemLp (A.indicator E) 2 P := hE2.indicator hA'
  have hint : Integrable (A.indicator E * Xv) P := hY2.integrable_mul hXv2
  have e1 : ∫ ω in A, E ω * Xv ω ∂P = ∫ ω, (A.indicator E * Xv) ω ∂P := by
    rw [← integral_indicator hA']
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases h : ω ∈ A <;> simp [h]
  have e2 : ∫ ω in A, E ω * Xs ω ∂P = ∫ ω, (A.indicator E * Xs) ω ∂P := by
    rw [← integral_indicator hA']
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases h : ω ∈ A <;> simp [h]
  rw [e1, e2, ← integral_condExp h𝓕]
  refine integral_congr_ae ?_
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hY hint (hXv2.integrable one_le_two),
    hmart] with ω h1 h2
  rw [h1, Pi.mul_apply, h2, Pi.mul_apply]

/-- An independent mean-one factor drops out of a set integral. -/
theorem setIntegral_indep {𝓗 : MeasurableSpace Ω} (h𝓗 : 𝓗 ≤ mΩ)
    {E R R' X : Ω → ℝ} (hE : StronglyMeasurable[𝓗] E) (hX : StronglyMeasurable[𝓗] X)
    (hR' : Measurable[mΩ] R') (hRR : R =ᵐ[P] R') (hR1 : ∫ ω, R ω ∂P = 1)
    (hind : Indep 𝓗 (MeasurableSpace.comap R' inferInstance) P)
    {A : Set Ω} (hA : MeasurableSet[𝓗] A) :
    ∫ ω in A, E ω * R ω * X ω ∂P = ∫ ω in A, E ω * X ω ∂P := by
  have hA' : MeasurableSet[mΩ] A := h𝓗 _ hA
  have hR1' : ∫ ω, R' ω ∂P = 1 := by rw [← integral_congr_ae hRR, hR1]
  set f : Ω → ℝ := A.indicator (fun ω => E ω * X ω) with hf
  have hfm : StronglyMeasurable[𝓗] f := (hE.mul hX).indicator hA
  have hind' : IndepFun f R' P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hind hfm.measurable.comap_le
  calc ∫ ω in A, E ω * R ω * X ω ∂P = ∫ ω, f ω * R' ω ∂P := by
        rw [← integral_indicator hA']
        refine integral_congr_ae ?_
        filter_upwards [hRR] with ω h
        by_cases hω : ω ∈ A <;> simp [hf, hω, h]; ring
    _ = (∫ ω, f ω ∂P) * ∫ ω, R' ω ∂P :=
        hind'.integral_fun_mul_eq_mul_integral (hfm.mono h𝓗).aestronglyMeasurable
          hR'.aestronglyMeasurable
    _ = ∫ ω in A, E ω * X ω ∂P := by rw [hR1', mul_one, hf, integral_indicator hA']

/-- One tilt step: `R` independent of `𝓗 ⊇ 𝓕` with mean one drops out. -/
theorem tilt_step {𝓕 𝓗 : MeasurableSpace Ω} (h𝓕 : 𝓕 ≤ 𝓗) (h𝓗 : 𝓗 ≤ mΩ)
    {E R R' Xv Xs : Ω → ℝ} (hE : StronglyMeasurable[𝓕] E) (hE2 : MemLp E 2 P)
    (hR' : Measurable[mΩ] R') (hRR : R =ᵐ[P] R') (hR1 : ∫ ω, R ω ∂P = 1)
    (hind : Indep 𝓗 (MeasurableSpace.comap R' inferInstance) P)
    (hXv : StronglyMeasurable[𝓗] Xv) (hXs : StronglyMeasurable[𝓗] Xs)
    (hXv2 : MemLp Xv 2 P) (hXs2 : MemLp Xs 2 P) (hmart : condExp 𝓕 P Xv =ᵐ[P] Xs)
    {A : Set Ω} (hA : MeasurableSet[𝓕] A) :
    ∫ ω in A, E ω * R ω * Xv ω ∂P = ∫ ω in A, E ω * R ω * Xs ω ∂P :=
  (setIntegral_indep (mΩ := mΩ) h𝓗 (hE.mono h𝓕) hXv hR' hRR hR1 hind (h𝓕 _ hA)).trans
    ((setIntegral_mul_step (mΩ := mΩ) (h𝓕.trans h𝓗) hE hE2 hXv2 hmart hA).trans
      (setIntegral_indep (mΩ := mΩ) h𝓗 (hE.mono h𝓕) hXs hR' hRR hR1 hind (h𝓕 _ hA)).symm)

end StochCalcTilt

namespace StochCalcTiltM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `B~` increment on `[u, w]`. -/
noncomputable def ξ (M : Model p Ω) (u w : ℝ≥0) (ω : Ω) : ℝ := M.Bt w ω - M.Bt u ω

/-- Its variance. -/
noncomputable def V (u w : ℝ≥0) : ℝ≥0 := nndist (w : ℝ) (u : ℝ)

/-- The tilt density. -/
noncomputable def Lm (M : Model p Ω) (u w : ℝ≥0) (c : ℝ) : Ω → ℝ := L (ξ M u w) (V u w) c

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

lemma Lm_measF (M : Model p Ω) (hM : M.Standing) {u w s : ℝ≥0} (hu : u ≤ s) (hw : w ≤ s)
    (c : ℝ) : StronglyMeasurable[M.F s] (Lm M u w c) := by
  have h1 := Bt_measF M hM hw
  have h2 := Bt_measF M hM hu
  have : Measurable[M.F s] (Lm M u w c) := by
    unfold Lm L ξ
    exact Real.measurable_exp.comp ((measurable_const.mul (h1.sub h2)).sub measurable_const)
  exact this.stronglyMeasurable

/-- The version of the tilt built from the library Brownian motion. -/
noncomputable def Lw (M : Model p Ω) (u w : ℝ≥0) (c : ℝ) (ω : Ω) : ℝ :=
  Real.exp (c * (gBt M w ω - gBt M u ω) - (V u w : ℝ) * c ^ 2 / 2)

lemma Lm_ae (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) (c : ℝ) :
    Lm M u w c =ᵐ[M.P] Lw M u w c := by
  filter_upwards [ae_W M hM] with ω hω
  simp only [Lm, L, ξ, Lw]
  simp only [← (hω w).2, ← (hω u).2, W_one]

lemma Lw_meas (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) (c : ℝ) :
    Measurable (Lw M u w c) := by
  unfold Lw
  have := gBt_measurable M hM w
  have := gBt_measurable M hM u
  fun_prop

lemma indep_Lw (M : Model p Ω) (hM : M.Standing) {u w : ℝ≥0} (huw : u ≤ w) (c : ℝ)
    (T' : ℝ≥0) :
    Indep (M.F u ⊔ M.G T') (MeasurableSpace.comap (Lw M u w c) inferInstance) M.P := by
  refine indep_of_indep_of_le_right (indep_Bt_incr M hM u T') ?_
  set inc : Ω → ℝ≥0 → ℝ := fun ω r => W M (u + r) ω 1 - W M u ω 1 with hinc
  have hφ : Measurable (fun f : ℝ≥0 → ℝ => Real.exp (c * f (w - u) - (V u w : ℝ) * c ^ 2 / 2)) := by
    fun_prop
  have heq : Lw M u w c = (fun f : ℝ≥0 → ℝ => Real.exp (c * f (w - u) - (V u w : ℝ) * c ^ 2 / 2))
      ∘ inc := by
    funext ω
    simp only [Lw, Function.comp, hinc, W_one, add_tsub_cancel_of_le huw]
  rw [heq]
  exact (hφ.comp (comap_measurable inc)).comap_le

lemma memLp_Lm (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) (c : ℝ) :
    MemLp (Lm M u w c) 2 M.P := by
  have := hM.prob
  exact memLp_L (ξ_meas M hM u w) (ξ_law M hM u w) c

lemma integral_Lm (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) (c : ℝ) :
    ∫ ω, Lm M u w c ω ∂M.P = 1 := by
  have := hM.prob
  exact integral_L (ξ_law M hM u w) c

lemma Lm_mul (M : Model p Ω) {t s t' : ℝ≥0} (h1 : t ≤ s) (h2 : s ≤ t') (c : ℝ) (ω : Ω) :
    Lm M t s c ω * Lm M s t' c ω = Lm M t t' c ω := by
  simp only [Lm, L, ξ]
  rw [← Real.exp_add, V_eq h1, V_eq h2, V_eq (h1.trans h2)]
  ring_nf

lemma X_measH (M : Model p Ω) (hM : M.Standing) (u : ℝ≥0) {v : ℝ≥0} (hv : v ≤ p.T) :
    StronglyMeasurable[M.F u ⊔ M.G p.T] (M.X v) :=
  ((hM.X_adapted v).mono (M.G.mono hv)).mono le_sup_right

/-- The key set-integral identity under the tilt. -/
theorem setIntegral_tilt (M : Model p Ω) (hM : M.Standing)
    (hX : IsMartingaleOn p.T M.F M.P M.X) (hX2 : ∀ t, t ≤ p.T → MemLp (M.X t) 2 M.P)
    {t t' : ℝ≥0} (htt : t ≤ t') (c : ℝ) (s v : ℝ≥0) (hsv : s ≤ v) (hv : v ≤ p.T)
    (A : Set Ω) (hA : MeasurableSet[M.F s] A) :
    ∫ ω in A, Lm M t t' c ω * M.X v ω ∂M.P = ∫ ω in A, Lm M t t' c ω * M.X s ω ∂M.P := by
  have := hM.prob
  have hmart := hX.2.2 s v hsv hv
  have hs : s ≤ p.T := hsv.trans hv
  rcases le_total t' s with h1 | h1
  · -- the tilt is `F s`-measurable
    exact setIntegral_mul_step (M.F.le s) (Lm_measF M hM (htt.trans h1) h1 c)
      (memLp_Lm M hM t t' c) (hX2 v hv) hmart hA
  rcases le_total s t with h2 | h2
  · -- the tilt is independent of `F t ⊔ G T`
    have key := tilt_step (mΩ := mΩ) (P := M.P) (𝓕 := M.F s) (𝓗 := M.F t ⊔ M.G p.T)
      ((M.F.mono h2).trans le_sup_left) (sup_le (M.F.le t) (M.G.le p.T))
      (E := fun _ => (1 : ℝ)) (stronglyMeasurable_const) (memLp_const 1)
      (Lw_meas M hM t t' c) (Lm_ae M hM t t' c) (integral_Lm M hM t t' c)
      (indep_Lw M hM htt c p.T) (X_measH M hM t hv) (X_measH M hM t hs)
      (hX2 v hv) (hX2 s hs) hmart hA
    simpa using key
  · -- split the tilt at `s`
    have key := tilt_step (mΩ := mΩ) (P := M.P) (𝓕 := M.F s) (𝓗 := M.F s ⊔ M.G p.T)
      le_sup_left (sup_le (M.F.le s) (M.G.le p.T))
      (Lm_measF M hM h2 le_rfl c) (memLp_Lm M hM t s c)
      (Lw_meas M hM s t' c) (Lm_ae M hM s t' c) (integral_Lm M hM s t' c)
      (indep_Lw M hM h1 c p.T) (X_measH M hM s hv) (X_measH M hM s hs)
      (hX2 v hv) (hX2 s hs) hmart hA
    simpa only [Lm_mul M h2 h1] using key

/-- P3: the tilts are in `M_X`. -/
theorem tilt_mem_MX (M : Model p Ω) (hM : M.Standing)
    (hX : IsMartingaleOn p.T M.F M.P M.X) (hX2 : ∀ t, t ≤ p.T → MemLp (M.X t) 2 M.P)
    {t t' : ℝ≥0} (htt : t ≤ t') (c : ℝ) :
    Qd M.P (Lm M t t' c) ∈ M.MX := by
  have := hM.prob
  have hm : Measurable (Lm M t t' c) := by
    unfold Lm; exact L_measurable (ξ_meas M hM t t') c
  have hpos : ∀ ω, 0 < Lm M t t' c ω := fun ω => L_pos c ω
  have hint : Integrable (Lm M t t' c) M.P := (memLp_Lm M hM t t' c).integrable one_le_two
  refine ⟨Qd_prob hint hpos (integral_Lm M hM t t' c), Qd_ac _, ac_Qd hm hpos,
    memLp_rnDeriv hm hpos (memLp_Lm M hM t t' c), ?_⟩
  exact martingale_Qd hm hpos hint (integral_Lm M hM t t' c) p.T M.F M.X hX.1
    (fun u hu => (memLp_Lm M hM t t' c).integrable_mul (hX2 u hu))
    (fun s v hsv hv A hA => setIntegral_tilt M hM hX hX2 htt c s v hsv hv A hA)

end StochCalcTiltM

namespace StochCalcOrth

open HedgePSNV EthierKurtz StochCalcBr StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma P_mem_MX' (M : Model p Ω) (hM : M.Standing) (hX : IsMartingaleOn p.T M.F M.P M.X) :
    M.P ∈ M.MX := by
  have := hM.prob
  refine ⟨hM.prob, Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl, ?_, hX⟩
  refine (memLp_const (1 : ℝ)).ae_eq ?_
  filter_upwards [Measure.rnDeriv_self M.P] with ω hω
  simp [hω]

/-- set-integral form of a martingale step under any probability measure. -/
lemma setIntegral_mart {Q : Measure Ω} [IsProbabilityMeasure Q] (M : Model p Ω)
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsMartingaleOn p.T M.F Q Y) {t : ℝ≥0} (ht : t ≤ p.T)
    {A : Set Ω} (hA : MeasurableSet[M.F t] A) :
    ∫ ω in A, Y p.T ω ∂Q = ∫ ω in A, Y t ω ∂Q := by
  rw [← setIntegral_condExp (M.F.le t) (hY.2.1 p.T le_rfl) hA]
  exact setIntegral_congr_ae (M.F.le t _ hA)
    (by filter_upwards [hY.2.2 t p.T ht le_rfl] with ω h _; exact h)

theorem setIntegral_xi_chi (M : Model p Ω) (hM : M.Standing)
    (hX : IsMartingaleOn p.T M.F M.P M.X) (hX2 : ∀ t, t ≤ p.T → MemLp (M.X t) 2 M.P)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX)
    {t t' : ℝ≥0} (htt : t ≤ t') (ht : t ≤ p.T) (A : Set Ω) (hA : MeasurableSet[M.F t] A) :
    ∫ ω in A, ξ M t t' ω * θχ.2 p.T ω ∂M.P = 0 := by
  have := hM.prob
  obtain ⟨-, hχad, -, hχ2, hmart⟩ := hθ
  have hA' : MeasurableSet A := M.F.le t _ hA
  have hP := setIntegral_mart M (hmart M.P (P_mem_MX' M hM hX)) ht hA
  have hc : ∀ c : ℝ, ∫ ω, (Lm M t t' c ω - 1) * A.indicator (θχ.2 p.T) ω ∂M.P = 0 := by
    intro c
    have hQ := tilt_mem_MX M hM hX hX2 htt c
    haveI : IsProbabilityMeasure (Qd M.P (Lm M t t' c)) := hQ.1
    have hm : Measurable (Lm M t t' c) := L_measurable (ξ_meas M hM t t') c
    have hpos : ∀ ω, 0 < Lm M t t' c ω := fun ω => L_pos c ω
    have h1 := setIntegral_mart M (hmart _ hQ) ht hA
    rw [setIntegral_Qd hm hpos _ hA', setIntegral_Qd hm hpos _ hA'] at h1
    have h2 : ∫ ω in A, Lm M t t' c ω * θχ.2 t ω ∂M.P = ∫ ω in A, θχ.2 t ω ∂M.P := by
      have := setIntegral_indep (mΩ := mΩ) (P := M.P) (𝓗 := M.F t ⊔ M.G p.T)
        (sup_le (M.F.le t) (M.G.le p.T)) (E := fun _ => (1 : ℝ)) stronglyMeasurable_const
        ((hχad t).mono le_sup_left) (Lw_meas M hM t t' c) (Lm_ae M hM t t' c)
        (integral_Lm M hM t t' c) (indep_Lw M hM htt c p.T)
        (A := A) ((le_sup_left : M.F t ≤ M.F t ⊔ M.G p.T) A hA)
      simpa using this
    have hint1 : Integrable (fun ω => Lm M t t' c ω * θχ.2 p.T ω) M.P :=
      (memLp_Lm M hM t t' c).integrable_mul hχ2
    have hint2 : Integrable (θχ.2 p.T) M.P := hχ2.integrable one_le_two
    calc ∫ ω, (Lm M t t' c ω - 1) * A.indicator (θχ.2 p.T) ω ∂M.P
        = ∫ ω in A, (Lm M t t' c ω * θχ.2 p.T ω - θχ.2 p.T ω) ∂M.P := by
          rw [← integral_indicator hA']
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          by_cases h : ω ∈ A <;> simp [h]; ring
      _ = ∫ ω in A, Lm M t t' c ω * θχ.2 p.T ω ∂M.P - ∫ ω in A, θχ.2 p.T ω ∂M.P :=
          integral_sub hint1.integrableOn hint2.integrableOn
      _ = 0 := by rw [h1, h2, hP]; ring
  have key := integral_mul_eq_zero (ξ_meas M hM t t') (ξ_law M hM t t')
    (hχ2.indicator hA') (fun c _ _ => hc c)
  rw [← key, ← integral_indicator hA']
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  by_cases h : ω ∈ A <;> simp [h]

/-- P4: `E[Y ξ χ_T] = 0` for bounded `F_t`-measurable `Y`. -/
theorem integral_Y_xi_chi (M : Model p Ω) (hM : M.Standing)
    (hX : IsMartingaleOn p.T M.F M.P M.X) (hX2 : ∀ t, t ≤ p.T → MemLp (M.X t) 2 M.P)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX)
    {t t' : ℝ≥0} (htt : t ≤ t') (ht : t ≤ p.T) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[M.F t] Y) {C : ℝ} (hYb : ∀ ω, |Y ω| ≤ C) :
    ∫ ω, Y ω * (ξ M t t' ω * θχ.2 p.T ω) ∂M.P = 0 := by
  have := hM.prob
  have hχ2 : MemLp (θχ.2 p.T) 2 M.P := hθ.2.2.2.1
  have hint : Integrable (fun ω => ξ M t t' ω * θχ.2 p.T ω) M.P :=
    (memLp_xi (ξ_meas M hM t t') (ξ_law M hM t t')).integrable_mul hχ2
  have hYint : Integrable (fun ω => Y ω * (ξ M t t' ω * θχ.2 p.T ω)) M.P :=
    hint.bdd_mul (hY.mono (M.F.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hYb ω)
  have hce : condExp (M.F t) M.P (fun ω => ξ M t t' ω * θχ.2 p.T ω) =ᵐ[M.P] 0 :=
    (ae_eq_condExp_of_forall_setIntegral_eq (M.F.le t) hint
      (fun _ _ _ => integrableOn_zero)
      (fun A hA _ => by
        rw [setIntegral_xi_chi M hM hX hX2 θχ hθ htt ht A hA]; simp)
      stronglyMeasurable_zero.aestronglyMeasurable).symm
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := M.F t) (μ := M.P) hY hYint hint
  have h0 : condExp (M.F t) M.P (fun ω => Y ω * (ξ M t t' ω * θχ.2 p.T ω)) =ᵐ[M.P] 0 := by
    refine hpull.trans ?_
    filter_upwards [hce] with ω h
    simp [h]
  rw [← integral_condExp (M.F.le t), integral_congr_ae h0]
  simp

end StochCalcOrth


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcStein

lemma integrable_id_g (v : ℝ≥0) : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal' (μ := 0) (v := v) 1 (by simp)).integrable le_rfl

lemma integrable_sq_g (v : ℝ≥0) : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by simp)).integrable_sq

lemma integrable_hinge (v : ℝ≥0) (k s : ℝ) :
    Integrable (fun x : ℝ => x * max (k - s * x) 0) (gaussianReal 0 v) := by
  refine (((integrable_id_g v).norm.const_mul |k|).add
    ((integrable_sq_g v).const_mul |s|)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |max (k - s * x) 0| ≤ |k| + |s| * |x| := by
    rcases le_total (k - s * x) 0 with h | h
    · rw [max_eq_right h, abs_zero]; positivity
    · rw [max_eq_left h, abs_of_nonneg h]
      have := neg_abs_le (s * x); have := neg_abs_le k
      rw [abs_mul] at *; linarith [le_abs_self k, abs_mul s x, neg_abs_le (s * x)]
  have h2 : |x| * |max (k - s * x) 0| ≤ |x| * (|k| + |s| * |x|) :=
    mul_le_mul_of_nonneg_left h1 (abs_nonneg x)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_abs x, abs_nonneg x, abs_nonneg k, abs_nonneg s]

/-- One-dimensional Stein identity for the hinge. -/
theorem stein1 (v : ℝ≥0) {s : ℝ} (hs : 0 < s) (k : ℝ) :
    ∫ x, x * max (k - s * x) 0 ∂gaussianReal 0 v =
      -(s * v) * ∫ x, Set.indicator {x : ℝ | s * x ≤ k} (fun _ => (1 : ℝ)) x ∂gaussianReal 0 v := by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var]
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  set φ : ℝ → ℝ := gaussianPDFReal 0 v with hφdef
  set C : ℝ := (√(2 * Real.pi * v))⁻¹ with hC
  set q : ℝ := k / s with hq
  have hb : 0 < 1 / (2 * (v : ℝ)) := by positivity
  have hφe : ∀ x, φ x = C * Real.exp (-(1 / (2 * (v : ℝ))) * x ^ 2) := by
    intro x; simp only [hφdef, gaussianPDFReal, hC]; congr 2; ring
  have hmem : ∀ x, x ≤ q ↔ s * x ≤ k := by
    intro x; rw [hq, le_div_iff₀ hs, mul_comm]
  -- integrability
  have i0 : Integrable φ := integrable_gaussianPDFReal 0 v
  have i1 : Integrable (fun x => x * φ x) := by
    refine ((integrable_mul_exp_neg_mul_sq hb).const_mul C).congr (ae_of_all _ fun x => ?_)
    simp only [hφe]; ring
  have i2 : Integrable (fun x => x ^ 2 * φ x) := by
    refine ((integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)).const_mul C).congr
      (ae_of_all _ fun x => ?_)
    simp only [hφe, Real.rpow_two]; ring
  -- derivative
  have hφd : ∀ x, HasDerivAt φ (-(x / v) * φ x) x := by
    intro x
    have h := (((hasDerivAt_pow 2 x).const_mul (-(1 / (2 * (v : ℝ))))).exp).const_mul C
    have hfun : φ = fun y => C * Real.exp (-(1 / (2 * (v : ℝ))) * y ^ 2) := funext hφe
    rw [hfun]
    refine h.congr_deriv ?_
    beta_reduce
    field_simp
    ring
  set f : ℝ → ℝ := fun x => -(v : ℝ) * (φ x * (k - s * x)) with hf
  set f' : ℝ → ℝ := fun x => φ x * (x * (k - s * x)) + s * v * φ x with hf'
  have hfd : ∀ x, HasDerivAt f (f' x) x := by
    intro x
    have h := ((hφd x).mul (((hasDerivAt_id' x).const_mul s).const_sub k)).const_mul (-(v : ℝ))
    refine h.congr_deriv ?_
    simp only [hf']
    field_simp
    ring
  have f'int : Integrable f' := by
    refine (((i1.const_mul k).sub (i2.const_mul s)).add (i0.const_mul (s * v))).congr
      (ae_of_all _ fun x => ?_)
    simp only [hf', Pi.add_apply, Pi.sub_apply]; ring
  have t0 : Tendsto (fun x : ℝ => Real.exp (-(1 / (2 * (v : ℝ))) * x ^ 2)) atBot (𝓝 0) := by
    have := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb 0
    simp only [Real.rpow_zero, one_mul] at this
    exact this.mono_left atBot_le_cocompact
  have t1 : Tendsto (fun x : ℝ => x * Real.exp (-(1 / (2 * (v : ℝ))) * x ^ 2)) atBot (𝓝 0) := by
    have := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb 1
    simp only [Real.rpow_one] at this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (this.mono_left atBot_le_cocompact).congr (fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have tf : Tendsto f atBot (𝓝 0) := by
    have := ((t0.const_mul (k * C)).sub (t1.const_mul (s * C))).const_mul (-(v : ℝ))
    simp only [mul_zero, sub_zero] at this
    refine this.congr (fun x => ?_)
    simp only [hf, hφe]; ring
  have hftc := integral_Iic_of_hasDerivAt_of_tendsto (f := f) (f' := f') (a := q) (m := 0)
    (hfd q).continuousAt.continuousWithinAt (fun x _ => hfd x) f'int.integrableOn tf
  have hfq : f q = 0 := by
    simp only [hf, hq]; rw [mul_div_cancel₀ k hs.ne']; ring
  have hA : IntegrableOn (fun x => φ x * (x * (k - s * x))) (Iic q) :=
    (((i1.const_mul k).sub (i2.const_mul s)).congr (ae_of_all _ fun x => by
      simp only [Pi.sub_apply]; ring)).integrableOn
  have hsplit : ∫ x in Iic q, f' x =
      (∫ x in Iic q, φ x * (x * (k - s * x))) + s * v * ∫ x in Iic q, φ x := by
    simp only [hf']
    rw [integral_add hA (i0.const_mul (s * v)).integrableOn, integral_const_mul]
  rw [hsplit, hfq, sub_zero] at hftc
  -- assemble
  have hL : ∫ x, x * max (k - s * x) 0 ∂gaussianReal 0 v =
      ∫ x in Iic q, φ x * (x * (k - s * x)) := by
    rw [integral_gaussianReal_eq_integral_smul hv, ← integral_indicator measurableSet_Iic]
    congr 1; funext x
    by_cases hx : x ≤ q
    · have h' := (hmem x).1 hx
      simp [Set.indicator, hx, hφdef, max_eq_left (sub_nonneg.2 h')]
    · have h' : ¬ s * x ≤ k := fun h => hx ((hmem x).2 h)
      simp [Set.indicator, hx, max_eq_right (by linarith [not_le.1 h'] : k - s * x ≤ 0)]
  have hR : ∫ x, Set.indicator {x : ℝ | s * x ≤ k} (fun _ => (1 : ℝ)) x ∂gaussianReal 0 v =
      ∫ x in Iic q, φ x := by
    rw [integral_gaussianReal_eq_integral_smul hv, ← integral_indicator measurableSet_Iic]
    congr 1; funext x
    by_cases hx : x ≤ q
    · simp [Set.indicator, hx, (hmem x).1 hx, hφdef]
    · have h' : ¬ s * x ≤ k := fun h => hx ((hmem x).2 h)
      simp [Set.indicator, hx, h']
  rw [hL, hR]
  linarith

/-- Stein identity for a Gaussian `ξ ~ N(0, v)` independent of `(U, Y)`, `Y` bounded. -/
theorem stein_indep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ U Y : Ω → ℝ} {v : ℝ≥0} (hξ : Measurable ξ) (hU : Measurable U) (hY : Measurable Y)
    (hlaw : HasLaw ξ (gaussianReal 0 v) P) (hind : IndepFun (fun ω => (U ω, Y ω)) ξ P)
    {s : ℝ} (hs : 0 < s) (k0 a R K : ℝ) (hYb : ∀ ω, |Y ω| ≤ K)
    (hint : Integrable (fun ω => ξ ω * ((k0 - a * max (R - (U ω + s * ξ ω)) 0) * Y ω)) P) :
    ∫ ω, ξ ω * ((k0 - a * max (R - (U ω + s * ξ ω)) 0) * Y ω) ∂P =
      a * s * v * ∫ ω, Set.indicator {ω | U ω + s * ξ ω ≤ R} Y ω ∂P := by
  set V : Ω → ℝ × ℝ := fun ω => (U ω, Y ω) with hVdef
  have hV : Measurable V := hU.prodMk hY
  set Φ : Ω → (ℝ × ℝ) × ℝ := fun ω => (V ω, ξ ω) with hΦdef
  have hΦ : Measurable Φ := hV.prodMk hξ
  set μV := P.map V with hμV
  have : IsProbabilityMeasure μV := Measure.isProbabilityMeasure_map hV.aemeasurable
  set N := gaussianReal 0 v with hN
  have hmap : P.map Φ = μV.prod N := by
    rw [← hlaw.map_eq]
    exact (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hξ.aemeasurable).1 hind
  let g : (ℝ × ℝ) × ℝ → ℝ := fun z => z.2 * ((k0 - a * max (R - (z.1.1 + s * z.2)) 0) * z.1.2)
  let h : (ℝ × ℝ) × ℝ → ℝ := fun z => if z.1.1 + s * z.2 ≤ R then z.1.2 else 0
  have hgm : Measurable g := by fun_prop
  have hhm : Measurable h :=
    Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (by fun_prop) measurable_const
  have hgi : Integrable g (μV.prod N) := by
    rw [← hmap]
    exact (integrable_map_measure hgm.aestronglyMeasurable hΦ.aemeasurable).2 hint
  have hhi : Integrable h (μV.prod N) := by
    rw [← hmap]
    refine (integrable_map_measure hhm.aestronglyMeasurable hΦ.aemeasurable).2 ?_
    refine (integrable_const K).mono' (hhm.comp hΦ).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simp only [Function.comp, h, Φ, V, Real.norm_eq_abs]
    split_ifs
    · exact hYb ω
    · simp only [abs_zero]; exact (abs_nonneg _).trans (hYb ω)
  have hL : ∫ ω, ξ ω * ((k0 - a * max (R - (U ω + s * ξ ω)) 0) * Y ω) ∂P =
      ∫ z, g z ∂(μV.prod N) := by
    rw [← hmap, integral_map hΦ.aemeasurable hgm.aestronglyMeasurable]
  have hR : ∫ ω, Set.indicator {ω | U ω + s * ξ ω ≤ R} Y ω ∂P = ∫ z, h z ∂(μV.prod N) := by
    rw [← hmap, integral_map hΦ.aemeasurable hhm.aestronglyMeasurable]
    congr 1
  rw [hL, hR, integral_prod g hgi, integral_prod h hhi, ← integral_const_mul]
  congr 1; funext w
  have e1 : ∫ x, g (w, x) ∂N = w.2 * k0 * ∫ x, x ∂N -
      w.2 * a * ∫ x, x * max ((R - w.1) - s * x) 0 ∂N := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((integrable_id_g v).const_mul _) ((integrable_hinge v _ _).const_mul _)]
    congr 1; funext x
    simp only [g]
    rw [show R - (w.1 + s * x) = (R - w.1) - s * x by ring]
    ring
  have e2 : ∫ x, h (w, x) ∂N =
      w.2 * ∫ x, Set.indicator {x : ℝ | s * x ≤ R - w.1} (fun _ => (1 : ℝ)) x ∂N := by
    rw [← integral_const_mul]
    congr 1; funext x
    by_cases hx : w.1 + s * x ≤ R
    · have : s * x ≤ R - w.1 := by linarith
      simp [h, Set.indicator, hx, this]
    · have : ¬ s * x ≤ R - w.1 := by intro h'; exact hx (by linarith)
      simp [h, Set.indicator, hx, this]
  rw [e1, e2, hN, integral_id_gaussianReal, stein1 v hs]
  ring

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

/-- `F_t ⊔ G_T ⊔ σ(B~_T - B~_{t'})` (top-level, so that it is never a local instance). -/
noncomputable def Ksig (M : Model p Ω) (t t' : ℝ≥0) : MeasurableSpace Ω :=
  M.F t ⊔ M.G p.T ⊔ MeasurableSpace.comap (ξ M t' p.T) inferInstance

theorem stein_model (M : Model p Ω) (hM : M.Standing) {t t' : ℝ≥0} (htt : t ≤ t')
    (ht'T : t' ≤ p.T) (P R : ℝ) {Y : Ω → ℝ} (hYm : Measurable[M.F t] Y) (K : ℝ)
    (hYb : ∀ ω, |Y ω| ≤ K)
    (hint : Integrable (fun ω => ξ M t t' ω * (M.H P R ω * Y ω)) M.P) :
    ∫ ω, ξ M t t' ω * (M.H P R ω * Y ω) ∂M.P =
      (P - p.s) * p.σt * (StochCalcTiltM.V t t' : ℝ) *
        ∫ ω, Set.indicator {ω | M.AT ω ≤ R} Y ω ∂M.P := by
  have := hM.prob
  set ξ1 := ξ M t t' with hξ1
  set η := ξ M t' p.T with hη
  set U : Ω → ℝ := fun ω => M.C p.T ω + p.σt * (M.Bt t ω + η ω) with hU
  have hAT : ∀ ω, M.AT ω = U ω + p.σt * ξ1 ω := by
    intro ω; simp only [Model.AT, hU, hη, hξ1, ξ]; ring
  have hξm : Measurable ξ1 := ξ_meas M hM t t'
  have hηm : Measurable η := ξ_meas M hM t' p.T
  have hKle : Ksig M t t' ≤ mΩ := sup_le (sup_le (M.F.le t) (M.G.le p.T)) hηm.comap_le
  have hCm : Measurable[Ksig M t t'] (M.C p.T) :=
    ((hM.C_adapted p.T).measurable).mono (le_sup_right.trans le_sup_left) le_rfl
  have hBm : Measurable[Ksig M t t'] (M.Bt t) :=
    (Bt_measF M hM le_rfl).mono (le_sup_left.trans le_sup_left) le_rfl
  have hηm' : Measurable[Ksig M t t'] η := (comap_measurable η).mono le_sup_right le_rfl
  have hUm' : Measurable[Ksig M t t'] U := hCm.add (measurable_const.mul (hBm.add hηm'))
  have hYm' : Measurable[Ksig M t t'] Y := hYm.mono (le_sup_left.trans le_sup_left) le_rfl
  have hUY : Measurable[Ksig M t t'] (fun ω => (U ω, Y ω)) := hUm'.prodMk hYm'
  -- independence of ξ from Ksig M t t'
  have hind1 : Indep (M.F t ⊔ M.G p.T) (MeasurableSpace.comap ξ1 inferInstance) M.P :=
    indep_ξ M hM htt p.T
  have hind2 : Indep (MeasurableSpace.comap ξ1 inferInstance ⊔ (M.F t ⊔ M.G p.T))
      (MeasurableSpace.comap η inferInstance) M.P := by
    have h0 := indep_ξ M hM ht'T p.T
    refine indep_of_indep_of_le_left h0 ?_
    exact sup_le ((ξ_measF M hM htt).comap_le.trans le_sup_left)
      (sup_le ((M.F.mono htt).trans le_sup_left) le_sup_right)
  have hind : Indep (MeasurableSpace.comap ξ1 inferInstance) (Ksig M t t') M.P :=
    indep_sup_of_triple _ _ _ hξm.comap_le (sup_le (M.F.le t) (M.G.le p.T)) hηm.comap_le
      hind1 hind2
  have hindF : IndepFun (fun ω => (U ω, Y ω)) ξ1 M.P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hind.symm hUY.comap_le
  have hUm : Measurable U := hUm'.mono hKle le_rfl
  have hY0 : Measurable Y := hYm.mono (M.F.le t) le_rfl
  have hfun : (fun ω => ξ1 ω * (M.H P R ω * Y ω)) = fun ω => ξ1 ω *
      (((P - p.c) * (R - p.b * P) - (P - p.s) * max (R - (U ω + p.σt * ξ1 ω)) 0) * Y ω) := by
    funext ω; simp only [Model.H, payoff, hAT]
  have hset : {ω | M.AT ω ≤ R} = {ω | U ω + p.σt * ξ1 ω ≤ R} := by
    ext ω; simp only [Set.mem_setOf_eq, hAT]
  rw [hfun] at hint ⊢
  rw [hset, stein_indep hξm hUm hY0 (ξ_law M hM t t') hindF p.hσt _ _ R K hYb hint]

end StochCalcSteinM


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6

/-- `E D = 0`, `E[D U] = E[D²]` give `E[D²] ≤ Var U`. -/
theorem sq_le_evariance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U D : Ω → ℝ} (hU : MemLp U 2 P) (hD : MemLp D 2 P) (hD0 : ∫ ω, D ω ∂P = 0)
    (hDU : ∫ ω, D ω * U ω ∂P = ∫ ω, D ω ^ 2 ∂P) :
    ENNReal.ofReal (∫ ω, D ω ^ 2 ∂P) ≤ evariance U P := by
  set m := ∫ ω, U ω ∂P with hm
  have hV : MemLp (fun ω => U ω - m) 2 P := hU.sub (memLp_const m)
  have i1 : Integrable (fun ω => (U ω - m) ^ 2) P := hV.integrable_sq
  have i2 : Integrable (fun ω => D ω ^ 2) P := hD.integrable_sq
  have i3 : Integrable (fun ω => D ω * (U ω - m)) P := hD.integrable_mul hV
  have i4 : Integrable (fun ω => D ω * U ω) P := hD.integrable_mul hU
  have i5 : Integrable D P := hD.integrable one_le_two
  have hnn : 0 ≤ ∫ ω, (U ω - m - D ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  have hexp : ∫ ω, (U ω - m - D ω) ^ 2 ∂P =
      ∫ ω, (U ω - m) ^ 2 ∂P - 2 * ∫ ω, D ω * (U ω - m) ∂P + ∫ ω, D ω ^ 2 ∂P := by
    have e : (fun ω => (U ω - m - D ω) ^ 2) =
        fun ω => ((U ω - m) ^ 2 - 2 * (D ω * (U ω - m))) + D ω ^ 2 := by funext ω; ring
    have i6 : Integrable (fun ω => (U ω - m) ^ 2 - 2 * (D ω * (U ω - m))) P :=
      i1.sub (i3.const_mul 2)
    rw [e, integral_add i6 i2, integral_sub i1 (i3.const_mul 2),
      integral_const_mul]
  have hcross : ∫ ω, D ω * (U ω - m) ∂P = ∫ ω, D ω ^ 2 ∂P := by
    have : (fun ω => D ω * (U ω - m)) = fun ω => D ω * U ω - m * D ω := by funext ω; ring
    rw [this, integral_sub i4 (i5.const_mul m), integral_const_mul, hD0, hDU]; ring
  have hle : ∫ ω, D ω ^ 2 ∂P ≤ ∫ ω, (U ω - m) ^ 2 ∂P := by linarith
  rw [← hU.ofReal_variance_eq, variance_eq_integral hU.aestronglyMeasurable.aemeasurable]
  exact ENNReal.ofReal_le_ofReal hle

/-- Right Riemann sums dominate the integral of a monotone function. -/
theorem integral_le_right_sum {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : MonotoneOn f (Icc 0 T))
    (n : ℕ) (hn : 0 < n) :
    ∫ x in (0 : ℝ)..T, f x ≤ ∑ i ∈ Finset.range n, (T / n) * f ((i + 1 : ℕ) * (T / n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set h := T / n with hh
  have hpos : 0 < h := div_pos hT hn'
  have hnh : (n : ℝ) * h = T := by rw [hh]; field_simp
  have hg : MonotoneOn (fun y => f (h * y)) (Icc 0 (0 + (n : ℝ))) := by
    intro x hx y hy hxy
    refine hf ⟨by nlinarith [hx.1], ?_⟩ ⟨by nlinarith [hy.1], ?_⟩ (by nlinarith)
    · have := hx.2; rw [zero_add] at this; nlinarith
    · have := hy.2; rw [zero_add] at this; nlinarith
  have key := hg.integral_le_sum
  rw [intervalIntegral.integral_comp_mul_left (fun x => f x) hpos.ne'] at key
  simp only [mul_zero, zero_add, smul_eq_mul] at key
  rw [mul_comm h (n : ℝ), hnh] at key
  have := mul_le_mul_of_nonneg_left key hpos.le
  rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, Finset.mul_sum] at this
  refine this.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  congr 2; push_cast; ring

/-- Left Riemann sums plus the end correction dominate the integral. -/
theorem integral_le_left_sum {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : MonotoneOn f (Icc 0 T))
    (n : ℕ) (hn : 0 < n) :
    ∫ x in (0 : ℝ)..T, f x ≤
      ∑ i ∈ Finset.range n, (T / n) * f (i * (T / n)) + (T / n) * (f T - f 0) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (integral_le_right_sum hT hf n hn).trans (le_of_eq ?_)
  have htel := Finset.sum_range_sub (fun i : ℕ => (T / n) * f (i * (T / n))) n
  have hT' : (n : ℝ) * (T / n) = T := by field_simp
  rw [hT', Nat.cast_zero, zero_mul] at htel
  rw [Finset.sum_sub_distrib] at htel
  linear_combination htel


set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integral_gauss {ξ : Ω → ℝ} {v : ℝ≥0} (hξ : HasLaw ξ (gaussianReal 0 v) P) :
    ∫ ω, ξ ω ∂P = 0 := by
  rw [hξ.integral_eq, integral_id_gaussianReal]

lemma integral_sq_gauss {ξ : Ω → ℝ} {v : ℝ≥0} (hξ : HasLaw ξ (gaussianReal 0 v) P) :
    ∫ ω, ξ ω ^ 2 ∂P = v := by
  have h := hξ.integral_comp (f := fun x : ℝ => x ^ 2) (continuous_pow 2).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h]
  have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hv
  simpa [integral_id_gaussianReal] using hv

lemma memLp_bdd_mul {Y ξ : Ω → ℝ} (hξ : MemLp ξ 2 P) (hY : AEStronglyMeasurable Y P) {C : ℝ}
    (hYb : ∀ ω, |Y ω| ≤ C) : MemLp (fun ω => Y ω * ξ ω) 2 P := by
  refine (hξ.const_mul C).of_le (hY.mul hξ.aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hYb ω).trans (le_abs_self C)) (abs_nonneg _)

variable (m : ℕ → MeasurableSpace Ω) (ξ Y : ℕ → Ω → ℝ)

theorem sum_props (hmono : Monotone m) (hle : ∀ k, m k ≤ mΩ)
    (hξm : ∀ k, Measurable[m (k + 1)] (ξ k))
    (hind : ∀ k, Indep (m k) (MeasurableSpace.comap (ξ k) inferInstance) P)
    (hξ2 : ∀ k, MemLp (ξ k) 2 P) (hξ0 : ∀ k, ∫ ω, ξ k ω ∂P = 0)
    (hYm : ∀ k, Measurable[m k] (Y k)) (C : ℝ) (hYb : ∀ k ω, |Y k ω| ≤ C) (n : ℕ) :
    Measurable[m n] (fun ω => ∑ k ∈ Finset.range n, Y k ω * ξ k ω) ∧
    MemLp (fun ω => ∑ k ∈ Finset.range n, Y k ω * ξ k ω) 2 P ∧
    ∫ ω, (∑ k ∈ Finset.range n, Y k ω * ξ k ω) ^ 2 ∂P =
      ∑ k ∈ Finset.range n, (∫ ω, Y k ω ^ 2 ∂P) * ∫ ω, ξ k ω ^ 2 ∂P := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_zero]
    exact ⟨measurable_const, memLp_const 0, by simp⟩
  | succ n ih =>
    obtain ⟨hSm, hS2, hSsq⟩ := ih
    set S : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, Y k ω * ξ k ω with hS
    have hmn : m n ≤ m (n + 1) := hmono n.le_succ
    have hYn : Measurable (Y n) := (hYm n).mono (hle n) le_rfl
    have hYξ : MemLp (fun ω => Y n ω * ξ n ω) 2 P :=
      memLp_bdd_mul (hξ2 n) hYn.aestronglyMeasurable (hYb n)
    have hSY : Measurable[m n] (fun ω => S ω * Y n ω) := hSm.mul (hYm n)
    have hSY2 : MemLp (fun ω => S ω * Y n ω) 2 P := by
      have : (fun ω => S ω * Y n ω) = fun ω => Y n ω * S ω := by funext ω; ring
      rw [this]; exact memLp_bdd_mul hS2 hYn.aestronglyMeasurable (hYb n)
    have hsum : (fun ω => ∑ k ∈ Finset.range (n + 1), Y k ω * ξ k ω) =
        fun ω => S ω + Y n ω * ξ n ω := by
      funext ω; simp only [Finset.sum_range_succ, hS]
    rw [hsum]
    refine ⟨(hSm.mono hmn le_rfl).add (((hYm n).mono hmn le_rfl).mul (hξm n)), hS2.add hYξ, ?_⟩
    have hξn : Measurable (ξ n) := (hξm n).mono (hle (n + 1)) le_rfl
    have hindSY : IndepFun (fun ω => S ω * Y n ω) (ξ n) P := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left (hind n) hSY.comap_le
    have hindY : IndepFun (Y n) (ξ n) P := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left (hind n) (hYm n).comap_le
    have hcross : ∫ ω, S ω * Y n ω * ξ n ω ∂P = 0 := by
      rw [hindSY.integral_fun_mul_eq_mul_integral
        (hSY.mono (hle n) le_rfl).aestronglyMeasurable hξn.aestronglyMeasurable, hξ0, mul_zero]
    have hdiag : ∫ ω, (Y n ω * ξ n ω) ^ 2 ∂P = (∫ ω, Y n ω ^ 2 ∂P) * ∫ ω, ξ n ω ^ 2 ∂P := by
      have h2 := (hindY.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2))
      have e : (fun ω => (Y n ω * ξ n ω) ^ 2) = fun ω => Y n ω ^ 2 * ξ n ω ^ 2 := by
        funext ω; ring
      rw [e]
      exact h2.integral_fun_mul_eq_mul_integral (hYn.pow_const 2).aestronglyMeasurable
        (hξn.pow_const 2).aestronglyMeasurable
    have i1 : Integrable (fun ω => S ω ^ 2) P := hS2.integrable_sq
    have i2 : Integrable (fun ω => S ω * Y n ω * ξ n ω) P := hSY2.integrable_mul (hξ2 n)
    have i3 : Integrable (fun ω => (Y n ω * ξ n ω) ^ 2) P := hYξ.integrable_sq
    have e : (fun ω => (∑ k ∈ Finset.range (n + 1), Y k ω * ξ k ω) ^ 2) =
        fun ω => (S ω ^ 2 + 2 * (S ω * Y n ω * ξ n ω)) + (Y n ω * ξ n ω) ^ 2 := by
      funext ω; simp only [Finset.sum_range_succ, hS]; ring
    have i4 : Integrable (fun ω => S ω ^ 2 + 2 * (S ω * Y n ω * ξ n ω)) P := i1.add (i2.const_mul 2)
    rw [e, integral_add i4 i3, integral_add i1 (i2.const_mul 2),
      integral_const_mul, hcross, hSsq, hdiag, Finset.sum_range_succ]
    ring

theorem integral_sum_eq_zero (hle : ∀ k, m k ≤ mΩ)
    (hind : ∀ k, Indep (m k) (MeasurableSpace.comap (ξ k) inferInstance) P)
    (hξm : ∀ k, Measurable (ξ k)) (hξ2 : ∀ k, MemLp (ξ k) 2 P) (hξ0 : ∀ k, ∫ ω, ξ k ω ∂P = 0)
    (hYm : ∀ k, Measurable[m k] (Y k)) (C : ℝ) (hYb : ∀ k ω, |Y k ω| ≤ C) (n : ℕ) :
    ∫ ω, ∑ k ∈ Finset.range n, Y k ω * ξ k ω ∂P = 0 := by
  have hk : ∀ k, ∫ ω, Y k ω * ξ k ω ∂P = 0 := by
    intro k
    have hindY : IndepFun (Y k) (ξ k) P := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left (hind k) (hYm k).comap_le
    rw [hindY.integral_fun_mul_eq_mul_integral ((hYm k).mono (hle k) le_rfl).aestronglyMeasurable
      (hξm k).aestronglyMeasurable, hξ0, mul_zero]
  rw [integral_finsetSum _ fun k _ => (memLp_bdd_mul (hξ2 k)
    ((hYm k).mono (hle k) le_rfl).aestronglyMeasurable (hYb k)).integrable one_le_two]
  exact Finset.sum_eq_zero fun k _ => hk k

end StochCalcP6S


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedgeDeg

open HedgePSNV

variable {p : Params} {Ω : Type*} [MeasurableSpace Ω]

/-- The unhedgeable-risk term of (21). -/
noncomputable def Psi (M : Model p Ω) (P R : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ∫⁻ ω,
    ENNReal.ofReal (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * M.delta P R u.toNNReal ω ^ 2) ∂M.P

/-- Any `HasBrownianItoIntegral` vanishes a.s. at time `0`. -/
lemma ito_zero_ae (Q : Measure Ω) (ℱ : ℝ≥0 → MeasurableSpace Ω) (W Hh J : ℝ≥0 → Ω → ℝ)
    (h : EthierKurtz.HasBrownianItoIntegral Q ℱ W Hh J) : J 0 =ᵐ[Q] fun _ => (0 : ℝ) := by
  obtain ⟨a, -, -, -, hlim⟩ := h.2 0
  have hsum : ∀ n, EthierKurtz.itoStepSum W 0 n (a n) = fun _ => (0 : ℝ) := by
    intro n
    funext ω
    unfold EthierKurtz.itoStepSum
    simp
  have h0 : TendstoInMeasure Q (fun n => EthierKurtz.itoStepSum W 0 n (a n)) Filter.atTop
      (fun _ => (0 : ℝ)) := by
    intro ε hε
    simp [hsum, not_le.mpr hε]
  exact tendstoInMeasure_ae_unique hlim h0

lemma PM_eq_P_of_deg (M : Model p Ω) (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) :
    M.PM = M.P := by
  unfold Model.PM
  rw [withDensity_congr_ae (g := fun _ => (1 : ℝ≥0∞))
    (by filter_upwards [hdeg] with ω hω; simp [hω]), ← Pi.one_def, withDensity_one]

lemma Z_eq_one_of_deg (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (t : ℝ≥0) (ht : t ≤ p.T) :
    M.Z t =ᵐ[M.P] fun _ => (1 : ℝ) := by
  have := hM.prob
  refine (h5.1.2.2 t p.T ht le_rfl).symm.trans ?_
  refine (condExp_congr_ae hdeg).trans ?_
  rw [condExp_const (M.F.le t)]

lemma ZM_eq_one_of_deg (M : Model p Ω) (hM : M.Standing)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (t : ℝ≥0) :
    M.ZM t =ᵐ[M.P] fun _ => (1 : ℝ) := by
  have := hM.prob
  unfold Model.ZM
  rw [PM_eq_P_of_deg M hdeg]
  refine (condExp_congr_ae hdeg).trans ?_
  rw [condExp_const (M.F.le t)]

/-- Under `Z_T = 1`, `Psi = ∫_0^T E[δ_t²] dt`. -/
lemma Psi_deg (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (P R : ℝ) :
    Psi M P R = ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ∫⁻ ω,
      ENNReal.ofReal (M.delta P R u.toNNReal ω ^ 2) ∂M.P := by
  unfold Psi
  refine setLIntegral_congr_fun measurableSet_Icc fun u hu => ?_
  have hu' : u.toNNReal ≤ p.T := by
    rw [Real.toNNReal_le_iff_le_coe]; exact hu.2
  refine lintegral_congr_ae ?_
  filter_upwards [Z_eq_one_of_deg M hM h5 hdeg _ hu', ZM_eq_one_of_deg M hM hdeg u.toNNReal]
    with ω h1 h2
  rw [h1, h2]; simp

lemma P_mem_MX (M : Model p Ω) (hM : M.Standing) (hX : IsMartingaleOn p.T M.F M.P M.X) :
    M.P ∈ M.MX := by
  have := hM.prob
  refine ⟨hM.prob, Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl, ?_, hX⟩
  refine (memLp_const (1 : ℝ)).ae_eq ?_
  filter_upwards [Measure.rnDeriv_self M.P] with ω hω
  simp [hω]

/-- Every admissible gains process has `E χ_T = 0` once `P ∈ M_X`. -/
lemma integral_chi_T (M : Model p Ω) (hM : M.Standing) (hX : IsMartingaleOn p.T M.F M.P M.X)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX) :
    ∫ ω, θχ.2 p.T ω ∂M.P = 0 := by
  have := hM.prob
  obtain ⟨-, -, hg, -, hmart⟩ := hθ
  have hm := hmart M.P (P_mem_MX M hM hX)
  obtain ⟨K, hK, hχ⟩ := hg.2
  have hK0 := ito_zero_ae M.P (fun t => M.F t) M.B _ K hK
  have hχ0 : θχ.2 0 =ᵐ[M.P] fun _ => (0 : ℝ) := by
    filter_upwards [hχ, hK0] with ω h1 h2
    rw [h1 0 zero_le, h2]; simp
  rw [← integral_condExp (M.F.le 0),
    integral_congr_ae ((hm.2.2 0 p.T zero_le le_rfl).trans hχ0)]
  simp

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

/-- **Reduction of `theorem_1_ii_degenerate`** to (D1) `X` a `P`-martingale, (D2) the lower
bound and (D3) approximate attainment. -/
theorem deg_of_obligations (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ))
    (hX : IsMartingaleOn p.T M.F M.P M.X)
    (hLow : ∀ P R : ℝ, ∀ θχ ∈ M.AX,
      Psi M P R ≤ evariance (fun ω => M.H P R ω + θχ.2 p.T ω) M.P)
    (hUp : ∀ P R : ℝ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ θχ ∈ M.AX,
      evariance (fun ω => M.H P R ω + θχ.2 p.T ω) M.P ≤ Psi M P R + ε) :
    ∀ m P R : ℝ, M.Bval m P R = (if M.V0 P R = m then 0 else ⊤) + Psi M P R := by
  intro m P R
  have := hM.prob
  have hmean : ∀ θχ ∈ M.AX, ∫ ω, (M.H P R ω + θχ.2 p.T ω) ∂M.P = M.V0 P R := by
    intro θχ hθ
    have hE0 := integral_chi_T M hM hX θχ hθ
    have hχL2 : MemLp (θχ.2 p.T) 2 M.P := hθ.2.2.2.1
    rw [integral_add ((H_memLp M hM hL2 P R).integrable one_le_two)
      (hχL2.integrable one_le_two), hE0, add_zero]
    unfold Model.V0 nvValue
    rw [PM_eq_P_of_deg M hdeg]
    rfl
  by_cases hV : M.V0 P R = m
  · rw [if_pos hV, zero_add]
    apply le_antisymm
    · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      obtain ⟨θχ, hθ, hvar⟩ := hUp P R ε (by exact_mod_cast hε)
      unfold Model.Bval
      exact (iInf₂_le_of_le θχ hθ (iInf_le_of_le ((hmean θχ hθ).trans hV) le_rfl)).trans hvar
    · unfold Model.Bval
      exact le_iInf₂ fun θχ hθ => le_iInf fun _ => hLow P R θχ hθ
  · rw [if_neg hV, top_add]
    unfold Model.Bval
    refine eq_top_iff.2 (le_iInf₂ fun θχ hθ => le_iInf fun hm => ?_)
    exact absurd ((hmean θχ hθ).symm.trans hm) hV

end StochCalcHedgeDeg


namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg StochCalcGauss

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `c_t = P(A_T ≤ R | F_t)`. -/
noncomputable def cA (M : Model p Ω) (R : ℝ) (t : ℝ≥0) : Ω → ℝ :=
  condExp (M.F t) M.P (Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)))

/-- An everywhere-`[0,1]`-valued `F_t`-measurable version of `c_t`. -/
noncomputable def Yc (M : Model p Ω) (R : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max 0 (min 1 (cA M R t ω))

lemma AT_meas (M : Model p Ω) (hM : M.Standing) : Measurable M.AT := by
  show Measurable fun ω => M.C p.T ω + p.σt * M.Bt p.T ω
  exact ((hM.C_adapted p.T).measurable.mono (M.G.le p.T) le_rfl).add
    (measurable_const.mul (Bt_measurable M hM p.T))

lemma ind_int (M : Model p Ω) (hM : M.Standing) (R : ℝ) :
    Integrable (Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ))) M.P := by
  have := hM.prob
  exact (integrable_const 1).indicator (measurableSet_le (AT_meas M hM) measurable_const)

lemma cA_bounds (M : Model p Ω) (hM : M.Standing) (R : ℝ) (t : ℝ≥0) :
    ∀ᵐ ω ∂M.P, 0 ≤ cA M R t ω ∧ cA M R t ω ≤ 1 := by
  have := hM.prob
  have h0 : 0 ≤ᵐ[M.P] cA M R t :=
    condExp_nonneg (Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have h1 : cA M R t ≤ᵐ[M.P] condExp (M.F t) M.P (fun _ => (1 : ℝ)) := by
    refine condExp_mono (ind_int M hM R) (integrable_const 1) (Eventually.of_forall fun ω => ?_)
    by_cases h : M.AT ω ≤ R <;> simp [Set.indicator, h]
  rw [condExp_const (M.F.le t)] at h1
  filter_upwards [h0, h1] with ω a b
  exact ⟨a, b⟩

lemma Yc_ae (M : Model p Ω) (hM : M.Standing) (R : ℝ) (t : ℝ≥0) :
    Yc M R t =ᵐ[M.P] cA M R t := by
  filter_upwards [cA_bounds M hM R t] with ω h
  simp only [Yc, min_eq_right h.2, max_eq_right h.1]

lemma cA_meas (M : Model p Ω) (R : ℝ) (t : ℝ≥0) : StronglyMeasurable[M.F t] (cA M R t) :=
  stronglyMeasurable_condExp

lemma Yc_meas (M : Model p Ω) (R : ℝ) (t : ℝ≥0) : StronglyMeasurable[M.F t] (Yc M R t) := by
  have h : Measurable[M.F t] (cA M R t) := (cA_meas M R t).measurable
  exact (measurable_const.max (measurable_const.min h)).stronglyMeasurable

lemma Yc_bdd (M : Model p Ω) (R : ℝ) (t : ℝ≥0) (ω : Ω) : |Yc M R t ω| ≤ 1 := by
  unfold Yc
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (min_le_left _ _)

/-- Pull-out: `E[Y c_t] = E[Y 1_A]` for a.e.-bounded `F_t`-measurable `Y`. -/
lemma pull (M : Model p Ω) (hM : M.Standing) (R : ℝ) (t : ℝ≥0) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[M.F t] Y) {C : ℝ} (hYb : ∀ᵐ ω ∂M.P, |Y ω| ≤ C) :
    ∫ ω, Y ω * cA M R t ω ∂M.P =
      ∫ ω, Y ω * Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)) ω ∂M.P := by
  have := hM.prob
  have hi := ind_int M hM R
  have hYi : Integrable (fun ω => Y ω * Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)) ω)
      M.P :=
    hi.bdd_mul (hY.mono (M.F.le t)).aestronglyMeasurable
      (by filter_upwards [hYb] with ω h; rw [Real.norm_eq_abs]; exact h)
  have h1 := condExp_mul_of_stronglyMeasurable_left (m := M.F t) (μ := M.P) hY hYi hi
  have h2 := integral_condExp (m := M.F t) (μ := M.P)
    (f := fun ω => Y ω * Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)) ω) (M.F.le t)
  rw [← h2]
  refine integral_congr_ae ?_
  filter_upwards [h1] with ω hω
  exact hω.symm

lemma cA_abs (M : Model p Ω) (hM : M.Standing) (R : ℝ) (t : ℝ≥0) :
    ∀ᵐ ω ∂M.P, |cA M R t ω| ≤ 1 := by
  filter_upwards [cA_bounds M hM R t] with ω h
  rw [abs_of_nonneg h.1]; exact h.2

lemma cA_memLp (M : Model p Ω) (hM : M.Standing) (R : ℝ) (t : ℝ≥0) :
    MemLp (cA M R t) 2 M.P := by
  have := hM.prob
  exact MemLp.of_bound ((cA_meas M R t).mono (M.F.le t)).aestronglyMeasurable 1
    (by filter_upwards [cA_abs M hM R t] with ω h; rw [Real.norm_eq_abs]; exact h)

/-- `t ↦ E[c_t²]` is nondecreasing. -/
lemma cA_sq_mono (M : Model p Ω) (hM : M.Standing) (R : ℝ) {u v : ℝ≥0} (huv : u ≤ v) :
    ∫ ω, cA M R u ω ^ 2 ∂M.P ≤ ∫ ω, cA M R v ω ^ 2 ∂M.P := by
  have := hM.prob
  have hu := cA_memLp M hM R u
  have hv := cA_memLp M hM R v
  have huu := pull M hM R u (cA_meas M R u) (cA_abs M hM R u)
  have huv' := pull M hM R v ((cA_meas M R u).mono (M.F.mono huv)) (cA_abs M hM R u)
  have hvv := pull M hM R v (cA_meas M R v) (cA_abs M hM R v)
  have i1 : Integrable (fun ω => cA M R v ω * cA M R v ω) M.P := hv.integrable_mul hv
  have i2 : Integrable (fun ω => cA M R u ω * cA M R v ω) M.P := hu.integrable_mul hv
  have i3 : Integrable (fun ω => cA M R u ω * cA M R u ω) M.P := hu.integrable_mul hu
  have hnn : 0 ≤ ∫ ω, (cA M R v ω - cA M R u ω) ^ 2 ∂M.P := integral_nonneg fun _ => sq_nonneg _
  have e : (fun ω => (cA M R v ω - cA M R u ω) ^ 2) = fun ω =>
      (cA M R v ω * cA M R v ω - 2 * (cA M R u ω * cA M R v ω)) + cA M R u ω * cA M R u ω := by
    funext ω; ring
  have i4 : Integrable (fun ω => cA M R v ω * cA M R v ω - 2 * (cA M R u ω * cA M R v ω)) M.P :=
    i1.sub (i2.const_mul 2)
  rw [e, integral_add i4 i3, integral_sub i1 (i2.const_mul 2), integral_const_mul] at hnn
  have s1 : ∫ ω, cA M R u ω ^ 2 ∂M.P = ∫ ω, cA M R u ω * cA M R u ω ∂M.P := by
    simp only [sq]
  have s2 : ∫ ω, cA M R v ω ^ 2 ∂M.P = ∫ ω, cA M R v ω * cA M R v ω ∂M.P := by
    simp only [sq]
  rw [s1, s2]
  linarith

/-- One grid term: `E[(a Y_t ξ) (H + χ_T)] = (t'-t) a² E[Y_t²]`. -/
theorem term_eq (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2)
    (hX : IsMartingaleOn p.T M.F M.P M.X) (hX2 : ∀ t, t ≤ p.T → MemLp (M.X t) 2 M.P)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX) (P R : ℝ)
    {t t' : ℝ≥0} (htt : t ≤ t') (ht'T : t' ≤ p.T) :
    ∫ ω, (p.σt * (P - p.s) * Yc M R t ω * ξ M t t' ω) * (M.H P R ω + θχ.2 p.T ω) ∂M.P =
      (V t t' : ℝ) * ((p.σt * (P - p.s)) ^ 2 * ∫ ω, Yc M R t ω ^ 2 ∂M.P) := by
  have := hM.prob
  set a := p.σt * (P - p.s) with ha
  set Y : Ω → ℝ := fun ω => a * Yc M R t ω with hY
  have hYs : StronglyMeasurable[M.F t] Y := (Yc_meas M R t).const_mul a
  have hYm : Measurable[M.F t] Y := hYs.measurable
  have hYb : ∀ ω, |Y ω| ≤ |a| := fun ω => by
    simp only [hY, abs_mul]; exact mul_le_of_le_one_right (abs_nonneg a) (Yc_bdd M R t ω)
  have hYa : Measurable Y := hYm.mono (M.F.le t) le_rfl
  have hξ2 := memLp_xi (ξ_meas M hM t t') (ξ_law M hM t t')
  have hYξ : MemLp (fun ω => Y ω * ξ M t t' ω) 2 M.P :=
    StochCalcP6S.memLp_bdd_mul hξ2 hYa.aestronglyMeasurable hYb
  have hH := H_memLp M hM hL2 P R
  have hχ : MemLp (θχ.2 p.T) 2 M.P := hθ.2.2.2.1
  have i1 : Integrable (fun ω => Y ω * ξ M t t' ω * M.H P R ω) M.P := hYξ.integrable_mul hH
  have i2 : Integrable (fun ω => Y ω * ξ M t t' ω * θχ.2 p.T ω) M.P := hYξ.integrable_mul hχ
  have e1 : (fun ω => a * Yc M R t ω * ξ M t t' ω * (M.H P R ω + θχ.2 p.T ω)) =
      fun ω => Y ω * ξ M t t' ω * M.H P R ω + Y ω * ξ M t t' ω * θχ.2 p.T ω := by
    funext ω; simp only [hY]; ring
  rw [e1, integral_add i1 i2]
  have h0 : ∫ ω, Y ω * ξ M t t' ω * θχ.2 p.T ω ∂M.P = 0 := by
    have h := integral_Y_xi_chi M hM hX hX2 θχ hθ htt (htt.trans ht'T) hYs hYb
    rw [← h]; congr 1; funext ω; ring
  have hstein : ∫ ω, Y ω * ξ M t t' ω * M.H P R ω ∂M.P = (P - p.s) * p.σt * (V t t' : ℝ) *
      ∫ ω, Set.indicator {ω | M.AT ω ≤ R} Y ω ∂M.P := by
    have hint : Integrable (fun ω => ξ M t t' ω * (M.H P R ω * Y ω)) M.P := by
      refine i1.congr (Eventually.of_forall fun ω => ?_); simp only; ring
    rw [← stein_model M hM htt ht'T P R hYm |a| hYb hint]; congr 1; funext ω; ring
  have hind : ∫ ω, Set.indicator {ω | M.AT ω ≤ R} Y ω ∂M.P = a * ∫ ω, Yc M R t ω ^ 2 ∂M.P := by
    have e2 : (fun ω => Set.indicator {ω | M.AT ω ≤ R} Y ω) =
        fun ω => Y ω * Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)) ω := by
      funext ω; by_cases h : M.AT ω ≤ R <;> simp [Set.indicator, h]
    rw [e2, ← pull M hM R t hYs (Eventually.of_forall hYb), ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Yc_ae M hM R t] with ω hω
    simp only [hY]; rw [hω]; ring
  rw [hstein, h0, hind, ha]; ring

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

/-- The lower bound along the grid of mesh `T/n`. -/
theorem low_n (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2)
    (hX : IsMartingaleOn p.T M.F M.P M.X) (hX2 : ∀ t, t ≤ p.T → MemLp (M.X t) 2 M.P)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX) (P R : ℝ) (n : ℕ) :
    ENNReal.ofReal (∑ k ∈ Finset.range n, ((p.T : ℝ) / n) *
        ((p.σt * (P - p.s)) ^ 2 * ∫ ω, Yc M R (gr p n k) ω ^ 2 ∂M.P)) ≤
      evariance (fun ω => M.H P R ω + θχ.2 p.T ω) M.P := by
  have := hM.prob
  set a := p.σt * (P - p.s) with ha
  let m : ℕ → MeasurableSpace Ω := fun k => M.F (gr p n k)
  let ξs : ℕ → Ω → ℝ := fun k => ξ M (gr p n k) (gr p n (k + 1))
  let Ys : ℕ → Ω → ℝ := fun k ω => a * Yc M R (gr p n k) ω
  have hmono : Monotone m := fun i j hij => M.F.mono (gr_mono p n hij)
  have hle : ∀ k, m k ≤ mΩ := fun k => M.F.le _
  have hξm : ∀ k, Measurable[m (k + 1)] (ξs k) := fun k => ξ_measF M hM (gr_mono p n k.le_succ)
  have hind : ∀ k, Indep (m k) (MeasurableSpace.comap (ξs k) inferInstance) M.P := fun k =>
    indep_of_indep_of_le_left (indep_ξ M hM (gr_mono p n k.le_succ) p.T) le_sup_left
  have hξ2 : ∀ k, MemLp (ξs k) 2 M.P := fun k => memLp_xi (ξ_meas M hM _ _) (ξ_law M hM _ _)
  have hξ0 : ∀ k, ∫ ω, ξs k ω ∂M.P = 0 := fun k => StochCalcP6S.integral_gauss (ξ_law M hM _ _)
  have hYm : ∀ k, Measurable[m k] (Ys k) := fun k =>
    ((Yc_meas M R (gr p n k)).const_mul a).measurable
  have hYb : ∀ k ω, |Ys k ω| ≤ |a| := fun k ω => by
    simp only [Ys, abs_mul]; exact mul_le_of_le_one_right (abs_nonneg a) (Yc_bdd M R _ ω)
  obtain ⟨-, hD2, hDsq⟩ := StochCalcP6S.sum_props m ξs Ys hmono hle hξm hind hξ2 hξ0 hYm |a| hYb n
  have hD0 := StochCalcP6S.integral_sum_eq_zero m ξs Ys hle hind (fun k => ξ_meas M hM _ _)
    hξ2 hξ0 hYm |a| hYb n
  have hU : MemLp (fun ω => M.H P R ω + θχ.2 p.T ω) 2 M.P :=
    (H_memLp M hM hL2 P R).add hθ.2.2.2.1
  have hS : ∫ ω, (∑ k ∈ Finset.range n, Ys k ω * ξs k ω) ^ 2 ∂M.P =
      ∑ k ∈ Finset.range n, ((p.T : ℝ) / n) * (a ^ 2 * ∫ ω, Yc M R (gr p n k) ω ^ 2 ∂M.P) := by
    rw [hDsq]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [StochCalcP6S.integral_sq_gauss (ξ_law M hM _ _), V_gr]
    have e : (fun ω => Ys k ω ^ 2) = fun ω => a ^ 2 * Yc M R (gr p n k) ω ^ 2 := by
      funext ω; simp only [Ys]; ring
    rw [e, integral_const_mul]; ring
  have hDU : ∫ ω, (∑ k ∈ Finset.range n, Ys k ω * ξs k ω) * (M.H P R ω + θχ.2 p.T ω) ∂M.P =
      ∑ k ∈ Finset.range n, ((p.T : ℝ) / n) * (a ^ 2 * ∫ ω, Yc M R (gr p n k) ω ^ 2 ∂M.P) := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum]
    swap
    · intro k _
      exact (StochCalcP6S.memLp_bdd_mul (hξ2 k)
        ((hYm k).mono (hle k) le_rfl).aestronglyMeasurable (hYb k)).integrable_mul hU
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
    rw [← V_gr p n k]
    exact term_eq M hM hL2 hX hX2 θχ hθ P R (gr_mono p n k.le_succ) (gr_le_T p hk')
  have key := StochCalcP6.sq_le_evariance hU hD2 hD0 (hDU.trans hS.symm)
  rw [hS] at key
  exact key

end StochCalcD2


namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `u ↦ E[δ_u²]` on the real line. -/
noncomputable def fD (M : Model p Ω) (P R : ℝ) (u : ℝ) : ℝ :=
  ∫ ω, M.delta P R u.toNNReal ω ^ 2 ∂M.P

lemma delta_eq (M : Model p Ω) (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (P R : ℝ) (t : ℝ≥0)
    (ω : Ω) : M.delta P R t ω = p.σt * (P - p.s) * cA M R t ω := by
  unfold Model.delta cA
  rw [PM_eq_P_of_deg M hdeg]

lemma fD_eq_cA (M : Model p Ω) (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) (P R u : ℝ) :
    fD M P R u = (p.σt * (P - p.s)) ^ 2 * ∫ ω, cA M R u.toNNReal ω ^ 2 ∂M.P := by
  unfold fD
  rw [← integral_const_mul]
  congr 1; funext ω; rw [delta_eq M hdeg]; ring

lemma fD_eq_Yc (M : Model p Ω) (hM : M.Standing) (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ))
    (P R u : ℝ) :
    fD M P R u = (p.σt * (P - p.s)) ^ 2 * ∫ ω, Yc M R u.toNNReal ω ^ 2 ∂M.P := by
  rw [fD_eq_cA M hdeg]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Yc_ae M hM R u.toNNReal] with ω h
  rw [h]

lemma fD_nonneg (M : Model p Ω) (P R u : ℝ) : 0 ≤ fD M P R u :=
  integral_nonneg fun _ => sq_nonneg _

lemma fD_mono (M : Model p Ω) (hM : M.Standing) (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ))
    (P R : ℝ) : Monotone (fD M P R) := fun u v huv => by
  rw [fD_eq_cA M hdeg, fD_eq_cA M hdeg]
  exact mul_le_mul_of_nonneg_left (cA_sq_mono M hM R (Real.toNNReal_le_toNNReal huv))
    (sq_nonneg _)

lemma fD_le (M : Model p Ω) (hM : M.Standing) (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ))
    (P R u : ℝ) : fD M P R u ≤ (p.σt * (P - p.s)) ^ 2 := by
  have := hM.prob
  rw [fD_eq_cA M hdeg]
  refine mul_le_of_le_one_right (sq_nonneg _) ?_
  have h1 : ∫ ω, cA M R u.toNNReal ω ^ 2 ∂M.P ≤ ∫ _ω, (1 : ℝ) ∂M.P := by
    refine integral_mono_ae (cA_memLp M hM R _).integrable_sq (integrable_const 1) ?_
    filter_upwards [cA_bounds M hM R u.toNNReal] with ω h
    nlinarith [h.1, h.2]
  simpa using h1

/-- **D2**: in the degenerate case, `Psi ≤ Var[H + χ_T]` for every admissible strategy. -/
theorem D2 (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ))
    (hX : IsMartingaleOn p.T M.F M.P M.X) (hX2 : ∀ t, t ≤ p.T → MemLp (M.X t) 2 M.P)
    (P R : ℝ) (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX) :
    Psi M P R ≤ evariance (fun ω => M.H P R ω + θχ.2 p.T ω) M.P := by
  have := hM.prob
  have hin : ∀ u : ℝ, ∫⁻ ω, ENNReal.ofReal (M.delta P R u.toNNReal ω ^ 2) ∂M.P =
      ENNReal.ofReal (fD M P R u) := by
    intro u
    have hi : Integrable (fun ω => M.delta P R u.toNNReal ω ^ 2) M.P := by
      have e : (fun ω => M.delta P R u.toNNReal ω ^ 2) =
          fun ω => (p.σt * (P - p.s)) ^ 2 * cA M R u.toNNReal ω ^ 2 := by
        funext ω; rw [delta_eq M hdeg]; ring
      rw [e]; exact ((cA_memLp M hM R _).integrable_sq).const_mul _
    unfold fD
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => sq_nonneg _)]
  rw [Psi_deg M hM h5 hdeg P R, lintegral_congr hin]
  have hmono := fD_mono M hM hdeg P R
  have hFint : IntegrableOn (fD M P R) (Set.Icc 0 (p.T : ℝ)) :=
    (hmono.monotoneOn _).integrableOn_isCompact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hFint (ae_of_all _ fun u => fD_nonneg M P R u)]
  have hTpos : (0 : ℝ) < p.T := by exact_mod_cast p.hT
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hTpos.le]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨n, hn⟩ := exists_nat_gt ((p.T : ℝ) * (p.σt * (P - p.s)) ^ 2 / ε)
  have hn0 : 0 < n := by
    have : (0 : ℝ) ≤ (p.T : ℝ) * (p.σt * (P - p.s)) ^ 2 / ε := by positivity
    exact_mod_cast this.trans_lt hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have h1 := StochCalcP6.integral_le_left_sum hTpos (hmono.monotoneOn _) n hn0
  have h2 : ∑ i ∈ Finset.range n, ((p.T : ℝ) / n) * fD M P R (i * ((p.T : ℝ) / n)) =
      ∑ k ∈ Finset.range n, ((p.T : ℝ) / n) *
        ((p.σt * (P - p.s)) ^ 2 * ∫ ω, Yc M R (gr p n k) ω ^ 2 ∂M.P) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : ((gr p n k : ℝ≥0) : ℝ) = (k : ℝ) * ((p.T : ℝ) / n) := by
      unfold gr; push_cast; ring
    have hk : ((k : ℝ) * ((p.T : ℝ) / n)).toNNReal = gr p n k := by
      rw [← hc, Real.toNNReal_coe]
    rw [fD_eq_Yc M hM hdeg P R, hk]
  have h3 : ((p.T : ℝ) / n) * (fD M P R p.T - fD M P R 0) ≤ ε := by
    have hb := fD_le M hM hdeg P R p.T
    have hb0 := fD_nonneg M P R 0
    calc ((p.T : ℝ) / n) * (fD M P R p.T - fD M P R 0)
        ≤ ((p.T : ℝ) / n) * (p.σt * (P - p.s)) ^ 2 :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hnr]
          have := (div_lt_iff₀ hεr).1 hn
          linarith
  have h4 := low_n M hM hL2 hX hX2 θχ hθ P R n
  rw [← h2] at h4
  calc ENNReal.ofReal (∫ x in (0 : ℝ)..p.T, fD M P R x)
      ≤ ENNReal.ofReal (∑ i ∈ Finset.range n, ((p.T : ℝ) / n) * fD M P R (i * ((p.T : ℝ) / n))
          + ε) := ENNReal.ofReal_le_ofReal (h1.trans (by linarith))
    _ ≤ ENNReal.ofReal (∑ i ∈ Finset.range n, ((p.T : ℝ) / n) * fD M P R (i * ((p.T : ℝ) / n)))
          + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ ≤ evariance (fun ω => M.H P R ω + θχ.2 p.T ω) M.P + ε := by
          rw [ENNReal.ofReal_coe_nnreal]; gcongr

end StochCalcD2

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcP6

/-- Left Riemann sums of a monotone function are below the integral. -/
theorem left_sum_le_integral {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hf : MonotoneOn f (Set.Icc 0 T))
    (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ Finset.range n, (T / n) * f (i * (T / n)) ≤ ∫ x in (0 : ℝ)..T, f x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set h := T / n with hh
  have hpos : 0 < h := div_pos hT hn'
  have hnh : (n : ℝ) * h = T := by rw [hh]; field_simp
  have hg : MonotoneOn (fun y => f (h * y)) (Set.Icc 0 (0 + (n : ℝ))) := by
    intro x hx y hy hxy
    refine hf ⟨by nlinarith [hx.1], ?_⟩ ⟨by nlinarith [hy.1], ?_⟩ (by nlinarith)
    · have := hx.2; rw [zero_add] at this; nlinarith
    · have := hy.2; rw [zero_add] at this; nlinarith
  have key := hg.sum_le_integral
  rw [intervalIntegral.integral_comp_mul_left (fun x => f x) hpos.ne'] at key
  simp only [mul_zero, zero_add, smul_eq_mul] at key
  rw [mul_comm h (n : ℝ), hnh] at key
  have := mul_le_mul_of_nonneg_left key hpos.le
  rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, Finset.mul_sum] at this
  refine (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)).trans this
  rw [mul_comm (i : ℝ) h]

/-- Pythagoras for a projection: if `U − D ⊥ D` and `U − D ⊥ K` then
`E U² ≤ E D² + E (U − K)²`. -/
theorem sq_le_of_proj {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U D K : Ω → ℝ} (hU : MemLp U 2 P) (hD : MemLp D 2 P) (hK : MemLp K 2 P)
    (h1 : ∫ ω, (U ω - D ω) * D ω ∂P = 0) (h2 : ∫ ω, (U ω - D ω) * K ω ∂P = 0) :
    ∫ ω, U ω ^ 2 ∂P ≤ ∫ ω, D ω ^ 2 ∂P + ∫ ω, (U ω - K ω) ^ 2 ∂P := by
  have he : MemLp (fun ω => U ω - D ω) 2 P := hU.sub hD
  have hw : MemLp (fun ω => K ω - D ω) 2 P := hK.sub hD
  have ieD : Integrable (fun ω => (U ω - D ω) * D ω) P := he.integrable_mul hD
  have ieK : Integrable (fun ω => (U ω - D ω) * K ω) P := he.integrable_mul hK
  have iew : Integrable (fun ω => (U ω - D ω) * (K ω - D ω)) P := he.integrable_mul hw
  have iee : Integrable (fun ω => (U ω - D ω) ^ 2) P := he.integrable_sq
  have iDD : Integrable (fun ω => D ω ^ 2) P := hD.integrable_sq
  have iww : Integrable (fun ω => (K ω - D ω) ^ 2) P := hw.integrable_sq
  have ia : Integrable (fun ω => (U ω - D ω) ^ 2 + 2 * ((U ω - D ω) * D ω)) P :=
    iee.add (ieD.const_mul 2)
  have ib : Integrable (fun ω => 2 * ((U ω - D ω) * D ω)) P := ieD.const_mul 2
  have ic : Integrable (fun ω => (U ω - D ω) ^ 2 - 2 * ((U ω - D ω) * (K ω - D ω))) P :=
    iee.sub (iew.const_mul 2)
  have id : Integrable (fun ω => 2 * ((U ω - D ω) * (K ω - D ω))) P := iew.const_mul 2
  have hew : ∫ ω, (U ω - D ω) * (K ω - D ω) ∂P = 0 := by
    have e : (fun ω => (U ω - D ω) * (K ω - D ω)) =
        fun ω => (U ω - D ω) * K ω - (U ω - D ω) * D ω := by funext ω; ring
    rw [e, integral_sub ieK ieD, h1, h2]; ring
  have hUe : ∫ ω, U ω ^ 2 ∂P = ∫ ω, (U ω - D ω) ^ 2 ∂P + ∫ ω, D ω ^ 2 ∂P := by
    have e : (fun ω => U ω ^ 2) =
        fun ω => ((U ω - D ω) ^ 2 + 2 * ((U ω - D ω) * D ω)) + D ω ^ 2 := by funext ω; ring
    rw [e, integral_add ia iDD, integral_add iee ib, integral_const_mul, h1]; ring
  have hr : ∫ ω, (U ω - K ω) ^ 2 ∂P = ∫ ω, (U ω - D ω) ^ 2 ∂P + ∫ ω, (K ω - D ω) ^ 2 ∂P := by
    have e : (fun ω => (U ω - K ω) ^ 2) = fun ω =>
        ((U ω - D ω) ^ 2 - 2 * ((U ω - D ω) * (K ω - D ω))) + (K ω - D ω) ^ 2 := by
      funext ω; ring
    rw [e, integral_add ic iww, integral_sub iee id, integral_const_mul, hew]; ring
  have : 0 ≤ ∫ ω, (K ω - D ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
  linarith

/-- `Var X ≤ E (X − c)²` for every constant `c`. -/
theorem evariance_le_sq_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) (c : ℝ) :
    evariance X P ≤ ENNReal.ofReal (∫ ω, (X ω - c) ^ 2 ∂P) := by
  set m := ∫ ω, X ω ∂P with hm
  have hV : MemLp (fun ω => X ω - m) 2 P := hX.sub (memLp_const m)
  have i1 : Integrable (fun ω => (X ω - m) ^ 2) P := hV.integrable_sq
  have i2 : Integrable (fun ω => X ω - m) P := hV.integrable one_le_two
  have hc : ∫ ω, (X ω - c) ^ 2 ∂P = ∫ ω, (X ω - m) ^ 2 ∂P + (m - c) ^ 2 := by
    have e : (fun ω => (X ω - c) ^ 2) =
        fun ω => ((X ω - m) ^ 2 + 2 * (m - c) * (X ω - m)) + (m - c) ^ 2 := by funext ω; ring
    have h0 : ∫ ω, (X ω - m) ∂P = 0 := by
      rw [integral_sub (hX.integrable one_le_two) (integrable_const m)]; simp [hm]
    have i3 : Integrable (fun ω => 2 * (m - c) * (X ω - m)) P := i2.const_mul _
    have i4 : Integrable (fun ω => (X ω - m) ^ 2 + 2 * (m - c) * (X ω - m)) P := i1.add i3
    rw [e, integral_add i4 (integrable_const _), integral_add i1 i3, integral_const_mul, h0]
    simp
  rw [← hX.ofReal_variance_eq, variance_eq_integral hX.aestronglyMeasurable.aemeasurable]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hc]; nlinarith [sq_nonneg (m - c)]

end StochCalcP6

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (m : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ)

/-- Polarized isometry of simple sums `Σ Z_k ξ_k`. -/
theorem inner_sum (hmono : Monotone m) (hle : ∀ k, m k ≤ mΩ)
    (hξm : ∀ k, Measurable[m (k + 1)] (ξ k))
    (hind : ∀ k, Indep (m k) (MeasurableSpace.comap (ξ k) inferInstance) P)
    (hξ2 : ∀ k, MemLp (ξ k) 2 P) (hξ0 : ∀ k, ∫ ω, ξ k ω ∂P = 0)
    (Z W : ℕ → Ω → ℝ) (hZm : ∀ k, Measurable[m k] (Z k)) (hWm : ∀ k, Measurable[m k] (W k))
    (CZ CW : ℝ) (hZb : ∀ k ω, |Z k ω| ≤ CZ) (hWb : ∀ k ω, |W k ω| ≤ CW) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, Z k ω * ξ k ω) * (∑ k ∈ Finset.range n, W k ω * ξ k ω) ∂P =
      ∑ k ∈ Finset.range n, (∫ ω, Z k ω * W k ω ∂P) * ∫ ω, ξ k ω ^ 2 ∂P := by
  obtain ⟨-, hA2, hA⟩ := sum_props m ξ (fun k ω => Z k ω + W k ω) hmono hle hξm hind hξ2 hξ0
    (fun k => (hZm k).add (hWm k)) (CZ + CW)
    (fun k ω => (abs_add_le _ _).trans (add_le_add (hZb k ω) (hWb k ω))) n
  obtain ⟨-, hB2, hB⟩ := sum_props m ξ (fun k ω => Z k ω - W k ω) hmono hle hξm hind hξ2 hξ0
    (fun k => (hZm k).sub (hWm k)) (CZ + CW)
    (fun k ω => (abs_sub _ _).trans (add_le_add (hZb k ω) (hWb k ω))) n
  obtain ⟨-, hZ2, -⟩ := sum_props m ξ Z hmono hle hξm hind hξ2 hξ0 hZm CZ hZb n
  obtain ⟨-, hW2, -⟩ := sum_props m ξ W hmono hle hξm hind hξ2 hξ0 hWm CW hWb n
  set SZ : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, Z k ω * ξ k ω with hSZ
  set SW : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, W k ω * ξ k ω with hSW
  have eA : (fun ω => ∑ k ∈ Finset.range n, (Z k ω + W k ω) * ξ k ω) = fun ω => SZ ω + SW ω := by
    funext ω; simp only [hSZ, hSW, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  have eB : (fun ω => ∑ k ∈ Finset.range n, (Z k ω - W k ω) * ξ k ω) = fun ω => SZ ω - SW ω := by
    funext ω; simp only [hSZ, hSW, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  have hA' : ∫ ω, (SZ ω + SW ω) ^ 2 ∂P =
      ∑ k ∈ Finset.range n, (∫ ω, (Z k ω + W k ω) ^ 2 ∂P) * ∫ ω, ξ k ω ^ 2 ∂P := by
    rw [← hA]; congr 1; funext ω; rw [← congrFun eA ω]
  have hB' : ∫ ω, (SZ ω - SW ω) ^ 2 ∂P =
      ∑ k ∈ Finset.range n, (∫ ω, (Z k ω - W k ω) ^ 2 ∂P) * ∫ ω, ξ k ω ^ 2 ∂P := by
    rw [← hB]; congr 1; funext ω; rw [← congrFun eB ω]
  have iZW : ∀ k, Integrable (fun ω => Z k ω * W k ω) P := fun k => by
    have hZk : MemLp (Z k) 2 P := MemLp.of_bound
      ((hZm k).mono (hle k) le_rfl).aestronglyMeasurable CZ
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hZb k ω)
    have hWk : MemLp (W k) 2 P := MemLp.of_bound
      ((hWm k).mono (hle k) le_rfl).aestronglyMeasurable CW
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hWb k ω)
    exact hZk.integrable_mul hWk
  have iZ2 : ∀ k, Integrable (fun ω => Z k ω ^ 2 + W k ω ^ 2) P := fun k => by
    have hZk : MemLp (Z k) 2 P := MemLp.of_bound
      ((hZm k).mono (hle k) le_rfl).aestronglyMeasurable CZ
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hZb k ω)
    have hWk : MemLp (W k) 2 P := MemLp.of_bound
      ((hWm k).mono (hle k) le_rfl).aestronglyMeasurable CW
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hWb k ω)
    exact hZk.integrable_sq.add hWk.integrable_sq
  have hk : ∀ k, (∫ ω, (Z k ω + W k ω) ^ 2 ∂P) - ∫ ω, (Z k ω - W k ω) ^ 2 ∂P =
      4 * ∫ ω, Z k ω * W k ω ∂P := fun k => by
    have e1 : (fun ω => (Z k ω + W k ω) ^ 2) =
        fun ω => (Z k ω ^ 2 + W k ω ^ 2) + 2 * (Z k ω * W k ω) := by funext ω; ring
    have e2 : (fun ω => (Z k ω - W k ω) ^ 2) =
        fun ω => (Z k ω ^ 2 + W k ω ^ 2) - 2 * (Z k ω * W k ω) := by funext ω; ring
    rw [e1, e2, integral_add (iZ2 k) ((iZW k).const_mul 2),
      integral_sub (iZ2 k) ((iZW k).const_mul 2), integral_const_mul]; ring
  have iS1 : Integrable (fun ω => (SZ ω + SW ω) ^ 2) P := (hZ2.add hW2).integrable_sq
  have iS2 : Integrable (fun ω => (SZ ω - SW ω) ^ 2) P := (hZ2.sub hW2).integrable_sq
  have hpol : ∫ ω, (SZ ω + SW ω) ^ 2 ∂P - ∫ ω, (SZ ω - SW ω) ^ 2 ∂P =
      4 * ∫ ω, SZ ω * SW ω ∂P := by
    rw [← integral_sub iS1 iS2, ← integral_const_mul]
    congr 1; funext ω; ring
  have hsum : ∑ k ∈ Finset.range n, (∫ ω, (Z k ω + W k ω) ^ 2 ∂P) * ∫ ω, ξ k ω ^ 2 ∂P -
      ∑ k ∈ Finset.range n, (∫ ω, (Z k ω - W k ω) ^ 2 ∂P) * ∫ ω, ξ k ω ^ 2 ∂P =
      4 * ∑ k ∈ Finset.range n, (∫ ω, Z k ω * W k ω ∂P) * ∫ ω, ξ k ω ^ 2 ∂P := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_mul, hk k]; ring
  rw [hA', hB'] at hpol
  show ∫ ω, SZ ω * SW ω ∂P = _
  linarith

end StochCalcP6S

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `term_eq` for a general bounded `F_t`-measurable weight `Z`. -/
theorem term_gen (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2)
    (hX : IsMartingaleOn p.T M.F M.P M.X) (hX2 : ∀ t, t ≤ p.T → MemLp (M.X t) 2 M.P)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX) (P R : ℝ)
    {t t' : ℝ≥0} (htt : t ≤ t') (ht'T : t' ≤ p.T) {Z : Ω → ℝ}
    (hZs : StronglyMeasurable[M.F t] Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, (Z ω * ξ M t t' ω) * (M.H P R ω + θχ.2 p.T ω) ∂M.P =
      (V t t' : ℝ) * (p.σt * (P - p.s)) * ∫ ω, Z ω * Yc M R t ω ∂M.P := by
  have := hM.prob
  have hZm : Measurable[M.F t] Z := hZs.measurable
  have hZa : Measurable Z := hZm.mono (M.F.le t) le_rfl
  have hξ2 := memLp_xi (ξ_meas M hM t t') (ξ_law M hM t t')
  have hZξ : MemLp (fun ω => Z ω * ξ M t t' ω) 2 M.P :=
    StochCalcP6S.memLp_bdd_mul hξ2 hZa.aestronglyMeasurable hZb
  have hH := H_memLp M hM hL2 P R
  have hχ : MemLp (θχ.2 p.T) 2 M.P := hθ.2.2.2.1
  have i1 : Integrable (fun ω => Z ω * ξ M t t' ω * M.H P R ω) M.P := hZξ.integrable_mul hH
  have i2 : Integrable (fun ω => Z ω * ξ M t t' ω * θχ.2 p.T ω) M.P := hZξ.integrable_mul hχ
  have e1 : (fun ω => (Z ω * ξ M t t' ω) * (M.H P R ω + θχ.2 p.T ω)) =
      fun ω => Z ω * ξ M t t' ω * M.H P R ω + Z ω * ξ M t t' ω * θχ.2 p.T ω := by
    funext ω; ring
  rw [e1, integral_add i1 i2]
  have h0 : ∫ ω, Z ω * ξ M t t' ω * θχ.2 p.T ω ∂M.P = 0 := by
    have h := integral_Y_xi_chi M hM hX hX2 θχ hθ htt (htt.trans ht'T) hZs hZb
    rw [← h]; congr 1; funext ω; ring
  have hstein : ∫ ω, Z ω * ξ M t t' ω * M.H P R ω ∂M.P = (P - p.s) * p.σt * (V t t' : ℝ) *
      ∫ ω, Set.indicator {ω | M.AT ω ≤ R} Z ω ∂M.P := by
    have hint : Integrable (fun ω => ξ M t t' ω * (M.H P R ω * Z ω)) M.P := by
      refine i1.congr (Eventually.of_forall fun ω => ?_); simp only; ring
    rw [← stein_model M hM htt ht'T P R hZm C hZb hint]; congr 1; funext ω; ring
  have hind : ∫ ω, Set.indicator {ω | M.AT ω ≤ R} Z ω ∂M.P = ∫ ω, Z ω * Yc M R t ω ∂M.P := by
    have e2 : (fun ω => Set.indicator {ω | M.AT ω ≤ R} Z ω) =
        fun ω => Z ω * Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)) ω := by
      funext ω; by_cases h : M.AT ω ≤ R <;> simp [Set.indicator, h]
    rw [e2, ← pull M hM R t hZs (Eventually.of_forall hZb)]
    refine integral_congr_ae ?_
    filter_upwards [Yc_ae M hM R t] with ω hω
    rw [hω]
  rw [hstein, h0, hind]; ring

/-- **D3 from density.** -/
theorem D3_of_density (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2)
    (h5 : M.Assumption5) (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ))
    (hX : IsMartingaleOn p.T M.F M.P M.X) (hX2 : ∀ t, t ≤ p.T → MemLp (M.X t) 2 M.P) (P R : ℝ)
    (hdens : ∀ η : ℝ, 0 < η → ∃ θχ ∈ M.AX, ∃ n : ℕ, 0 < n ∧ ∃ c : ℝ, ∃ Z : ℕ → Ω → ℝ,
      ∃ C : ℝ, (∀ k, StronglyMeasurable[M.F (gr p n k)] (Z k)) ∧ (∀ k ω, |Z k ω| ≤ C) ∧
      ∫ ω, (M.H P R ω + θχ.2 p.T ω - c -
        ∑ k ∈ Finset.range n, Z k ω * ξ M (gr p n k) (gr p n (k + 1)) ω) ^ 2 ∂M.P ≤ η) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ θχ ∈ M.AX,
      evariance (fun ω => M.H P R ω + θχ.2 p.T ω) M.P ≤ Psi M P R + ε := by
  intro ε hε
  have := hM.prob
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr : 0 < r := by
    by_contra h; push_neg at h; rw [ENNReal.ofReal_of_nonpos h] at hr1; exact lt_irrefl _ hr1
  obtain ⟨θχ, hθ, n, hn, c, Z, C, hZm, hZb, hη⟩ := hdens r hr
  refine ⟨θχ, hθ, ?_⟩
  set a := p.σt * (P - p.s) with ha
  let m : ℕ → MeasurableSpace Ω := fun k => M.F (gr p n k)
  let ξs : ℕ → Ω → ℝ := fun k => ξ M (gr p n k) (gr p n (k + 1))
  let Ys : ℕ → Ω → ℝ := fun k ω => a * Yc M R (gr p n k) ω
  have hmono : Monotone m := fun i j hij => M.F.mono (gr_mono p n hij)
  have hle : ∀ k, m k ≤ mΩ := fun k => M.F.le _
  have hξm : ∀ k, Measurable[m (k + 1)] (ξs k) := fun k => ξ_measF M hM (gr_mono p n k.le_succ)
  have hind : ∀ k, Indep (m k) (MeasurableSpace.comap (ξs k) inferInstance) M.P := fun k =>
    indep_of_indep_of_le_left (indep_ξ M hM (gr_mono p n k.le_succ) p.T) le_sup_left
  have hξ2 : ∀ k, MemLp (ξs k) 2 M.P := fun k => memLp_xi (ξ_meas M hM _ _) (ξ_law M hM _ _)
  have hξ0 : ∀ k, ∫ ω, ξs k ω ∂M.P = 0 := fun k => StochCalcP6S.integral_gauss (ξ_law M hM _ _)
  have hξsq : ∀ k, k < n → ∫ ω, ξs k ω ^ 2 ∂M.P = (p.T : ℝ) / n := fun k _ => by
    rw [StochCalcP6S.integral_sq_gauss (ξ_law M hM _ _), V_gr]
  have hYm : ∀ k, Measurable[m k] (Ys k) := fun k =>
    ((Yc_meas M R (gr p n k)).const_mul a).measurable
  have hYb : ∀ k ω, |Ys k ω| ≤ |a| := fun k ω => by
    simp only [Ys, abs_mul]; exact mul_le_of_le_one_right (abs_nonneg a) (Yc_bdd M R _ ω)
  have hZm' : ∀ k, Measurable[m k] (Z k) := fun k => (hZm k).measurable
  set D : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, Ys k ω * ξs k ω with hD
  set K : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, Z k ω * ξs k ω with hK
  set U : Ω → ℝ := fun ω => M.H P R ω + θχ.2 p.T ω - c with hU
  have hHχ : MemLp (fun ω => M.H P R ω + θχ.2 p.T ω) 2 M.P :=
    (H_memLp M hM hL2 P R).add hθ.2.2.2.1
  have hU2 : MemLp U 2 M.P := hHχ.sub (memLp_const c)
  obtain ⟨-, hD2, hDsq⟩ := StochCalcP6S.sum_props m ξs Ys hmono hle hξm hind hξ2 hξ0 hYm |a| hYb n
  obtain ⟨-, hK2, -⟩ := StochCalcP6S.sum_props m ξs Z hmono hle hξm hind hξ2 hξ0 hZm' C hZb n
  -- orthogonality of `U − D` to every simple sum
  have horth : ∀ (W : ℕ → Ω → ℝ) (CW : ℝ), (∀ k, StronglyMeasurable[m k] (W k)) →
      (∀ k ω, |W k ω| ≤ CW) →
      ∫ ω, (U ω - D ω) * (∑ k ∈ Finset.range n, W k ω * ξs k ω) ∂M.P = 0 := by
    intro W CW hWs hWb
    have hWm : ∀ k, Measurable[m k] (W k) := fun k => (hWs k).measurable
    obtain ⟨-, hS2, -⟩ := StochCalcP6S.sum_props m ξs W hmono hle hξm hind hξ2 hξ0 hWm CW hWb n
    have hS0 := StochCalcP6S.integral_sum_eq_zero m ξs W hle hind (fun k => ξ_meas M hM _ _)
      hξ2 hξ0 hWm CW hWb n
    have hDS := StochCalcP6S.inner_sum m ξs hmono hle hξm hind hξ2 hξ0 Ys W hYm hWm |a| CW hYb
      hWb n
    have hUS : ∫ ω, (M.H P R ω + θχ.2 p.T ω) * (∑ k ∈ Finset.range n, W k ω * ξs k ω) ∂M.P =
        ∑ k ∈ Finset.range n, (∫ ω, Ys k ω * W k ω ∂M.P) * ∫ ω, ξs k ω ^ 2 ∂M.P := by
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum]
      swap
      · intro k _
        exact hHχ.integrable_mul (StochCalcP6S.memLp_bdd_mul (hξ2 k)
          ((hWm k).mono (hle k) le_rfl).aestronglyMeasurable (hWb k))
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
      have h := term_gen M hM hL2 hX hX2 θχ hθ P R (gr_mono p n k.le_succ) (gr_le_T p hk')
        (hWs k) (hWb k)
      have e : (fun ω => (M.H P R ω + θχ.2 p.T ω) * (W k ω * ξs k ω)) =
          fun ω => (W k ω * ξ M (gr p n k) (gr p n (k + 1)) ω) * (M.H P R ω + θχ.2 p.T ω) := by
        funext ω; simp only [ξs]; ring
      rw [e, h, hξsq k (Finset.mem_range.1 hk), ← V_gr p n k]
      have e2 : (fun ω => Ys k ω * W k ω) = fun ω => a * (W k ω * Yc M R (gr p n k) ω) := by
        funext ω; simp only [Ys]; ring
      rw [e2, integral_const_mul]; ring
    have e : (fun ω => (U ω - D ω) * (∑ k ∈ Finset.range n, W k ω * ξs k ω)) = fun ω =>
        (M.H P R ω + θχ.2 p.T ω) * (∑ k ∈ Finset.range n, W k ω * ξs k ω) -
        c * (∑ k ∈ Finset.range n, W k ω * ξs k ω) -
        D ω * (∑ k ∈ Finset.range n, W k ω * ξs k ω) := by
      funext ω; simp only [hU]; ring
    have j1 : Integrable (fun ω => (M.H P R ω + θχ.2 p.T ω) *
        (∑ k ∈ Finset.range n, W k ω * ξs k ω)) M.P := hHχ.integrable_mul hS2
    have j2 : Integrable (fun ω => c * (∑ k ∈ Finset.range n, W k ω * ξs k ω)) M.P :=
      (hS2.integrable one_le_two).const_mul c
    have j3 : Integrable (fun ω => D ω * (∑ k ∈ Finset.range n, W k ω * ξs k ω)) M.P :=
      hD2.integrable_mul hS2
    have j12 : Integrable (fun ω => (M.H P R ω + θχ.2 p.T ω) *
        (∑ k ∈ Finset.range n, W k ω * ξs k ω) -
        c * (∑ k ∈ Finset.range n, W k ω * ξs k ω)) M.P := j1.sub j2
    rw [e, integral_sub j12 j3, integral_sub j1 j2, integral_const_mul, hS0, hUS]
    rw [show (fun ω => D ω * ∑ k ∈ Finset.range n, W k ω * ξs k ω) =
      fun ω => (∑ k ∈ Finset.range n, Ys k ω * ξs k ω) * ∑ k ∈ Finset.range n, W k ω * ξs k ω
      from rfl, hDS]
    ring
  have h1 := horth Ys |a| (fun k => (Yc_meas M R (gr p n k)).const_mul a) hYb
  have h2 := horth Z C hZm hZb
  have key := StochCalcP6.sq_le_of_proj hU2 hD2 hK2 h1 h2
  -- `E D²` is a left Riemann sum of `fD`
  have hDval : ∫ ω, D ω ^ 2 ∂M.P =
      ∑ i ∈ Finset.range n, ((p.T : ℝ) / n) * fD M P R (i * ((p.T : ℝ) / n)) := by
    rw [hDsq]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hξsq k (Finset.mem_range.1 hk)]
    have hc : ((gr p n k : ℝ≥0) : ℝ) = (k : ℝ) * ((p.T : ℝ) / n) := by
      unfold gr; push_cast; ring
    have hk2 : ((k : ℝ) * ((p.T : ℝ) / n)).toNNReal = gr p n k := by
      rw [← hc, Real.toNNReal_coe]
    rw [fD_eq_Yc M hM hdeg P R, hk2]
    have e : (fun ω => Ys k ω ^ 2) = fun ω => a ^ 2 * Yc M R (gr p n k) ω ^ 2 := by
      funext ω; simp only [Ys]; ring
    rw [e, integral_const_mul]; ring
  have hmonoF := fD_mono M hM hdeg P R
  have hTpos : (0 : ℝ) < p.T := by exact_mod_cast p.hT
  have hleft := StochCalcP6.left_sum_le_integral hTpos (hmonoF.monotoneOn _) n hn
  -- `Psi` as the real integral of `fD`
  have hPsi : Psi M P R = ENNReal.ofReal (∫ x in (0 : ℝ)..p.T, fD M P R x) := by
    have hin : ∀ u : ℝ, ∫⁻ ω, ENNReal.ofReal (M.delta P R u.toNNReal ω ^ 2) ∂M.P =
        ENNReal.ofReal (fD M P R u) := by
      intro u
      have hi : Integrable (fun ω => M.delta P R u.toNNReal ω ^ 2) M.P := by
        have e : (fun ω => M.delta P R u.toNNReal ω ^ 2) =
            fun ω => (p.σt * (P - p.s)) ^ 2 * cA M R u.toNNReal ω ^ 2 := by
          funext ω; rw [delta_eq M hdeg]; ring
        rw [e]; exact ((cA_memLp M hM R _).integrable_sq).const_mul _
      unfold fD
      rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => sq_nonneg _)]
    rw [Psi_deg M hM h5 hdeg P R, lintegral_congr hin]
    have hFint : IntegrableOn (fD M P R) (Set.Icc 0 (p.T : ℝ)) :=
      (hmonoF.monotoneOn _).integrableOn_isCompact isCompact_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hFint (ae_of_all _ fun u => fD_nonneg M P R u),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hTpos.le]
  have hUK : ∫ ω, (U ω - K ω) ^ 2 ∂M.P ≤ r := hη
  calc evariance (fun ω => M.H P R ω + θχ.2 p.T ω) M.P
      ≤ ENNReal.ofReal (∫ ω, U ω ^ 2 ∂M.P) := StochCalcP6.evariance_le_sq_sub hHχ c
    _ ≤ ENNReal.ofReal ((∫ x in (0 : ℝ)..p.T, fD M P R x) + r) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (∫ x in (0 : ℝ)..p.T, fD M P R x) + ENNReal.ofReal r :=
        ENNReal.ofReal_add_le
    _ ≤ Psi M P R + ε := by rw [hPsi]; gcongr

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

/-- **hdens from (R) and (XS).** -/
theorem dens_of_rep (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2) (P R : ℝ)
    (hR : ∀ η : ℝ, 0 < η → ∃ n : ℕ, 0 < n ∧ ∃ c : ℝ, ∃ Y Z : ℕ → Ω → ℝ, ∃ C : ℝ,
      (∀ k, StronglyMeasurable[M.F (gr p n k)] (Y k)) ∧ (∀ k ω, |Y k ω| ≤ C) ∧
      (∀ k, StronglyMeasurable[M.F (gr p n k)] (Z k)) ∧ (∀ k ω, |Z k ω| ≤ C) ∧
      ∫ ω, (M.H P R ω - c - ∑ k ∈ Finset.range n, Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω -
        ∑ k ∈ Finset.range n, Z k ω * ξ M (gr p n k) (gr p n (k + 1)) ω) ^ 2 ∂M.P ≤ η)
    (hXS : ∀ n : ℕ, 0 < n → ∀ (Y : ℕ → Ω → ℝ) (C : ℝ),
      (∀ k, StronglyMeasurable[M.F (gr p n k)] (Y k)) → (∀ k ω, |Y k ω| ≤ C) →
      ∀ η : ℝ, 0 < η → ∃ θχ ∈ M.AX, ∃ m : ℕ, 0 < m ∧
      ∫ ω, (θχ.2 p.T ω + ∑ k ∈ Finset.range n, Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω) ^ 2
        ∂M.P ≤ η) :
    ∀ η : ℝ, 0 < η → ∃ θχ ∈ M.AX, ∃ n : ℕ, 0 < n ∧ ∃ c : ℝ, ∃ Z : ℕ → Ω → ℝ,
      ∃ C : ℝ, (∀ k, StronglyMeasurable[M.F (gr p n k)] (Z k)) ∧ (∀ k ω, |Z k ω| ≤ C) ∧
      ∫ ω, (M.H P R ω + θχ.2 p.T ω - c -
        ∑ k ∈ Finset.range n, Z k ω * ξ M (gr p n k) (gr p n (k + 1)) ω) ^ 2 ∂M.P ≤ η := by
  intro η hη
  have := hM.prob
  obtain ⟨n, hn, c, Y, Z, C, hYm, hYb, hZm, hZb, hRη⟩ := hR (η / 4) (by positivity)
  obtain ⟨θχ, hθ, m, hm, hXη⟩ := hXS n hn Y C hYm hYb (η / 4) (by positivity)
  refine ⟨θχ, hθ, n * m, Nat.mul_pos hn hm, c, fun j => Z (j / m), C, ?_, fun j ω => hZb _ ω, ?_⟩
  · intro j
    refine (hZm (j / m)).mono (M.F.mono ?_)
    rw [← gr_mul p hm n (j / m)]
    exact gr_mono p (n * m) (Nat.div_mul_le_self j m)
  set SY : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω
    with hSY
  set SZ : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, Z k ω * ξ M (gr p n k) (gr p n (k + 1)) ω
    with hSZ
  have hSY2 : MemLp SY 2 M.P := sum_memLp M hM n Y C hYm hYb (dB M)
    (fun u w => memLp_xi (dB_meas M hM u w) (dB_law M hM u w)) n
  have hSZ2 : MemLp SZ 2 M.P := sum_memLp M hM n Z C hZm hZb (ξ M)
    (fun u w => memLp_xi (ξ_meas M hM u w) (ξ_law M hM u w)) n
  have hH := H_memLp M hM hL2 P R
  have ha : MemLp (fun ω => M.H P R ω - c - SY ω - SZ ω) 2 M.P :=
    ((hH.sub (memLp_const c)).sub hSY2).sub hSZ2
  have hb : MemLp (fun ω => θχ.2 p.T ω + SY ω) 2 M.P := hθ.2.2.2.1.add hSY2
  have href : ∀ ω, ∑ j ∈ Finset.range (n * m), Z (j / m) ω *
      ξ M (gr p (n * m) j) (gr p (n * m) (j + 1)) ω = SZ ω := fun ω => by
    have h := refine_sum p M.Bt Z hm n ω n
    simp only [hSZ, ξ]; exact h.symm
  have hpt : ∀ ω, (M.H P R ω + θχ.2 p.T ω - c - ∑ j ∈ Finset.range (n * m), Z (j / m) ω *
      ξ M (gr p (n * m) j) (gr p (n * m) (j + 1)) ω) ^ 2 ≤
      2 * (M.H P R ω - c - SY ω - SZ ω) ^ 2 + 2 * (θχ.2 p.T ω + SY ω) ^ 2 := fun ω => by
    rw [href ω]
    nlinarith [sq_nonneg (M.H P R ω - c - SY ω - SZ ω - (θχ.2 p.T ω + SY ω))]
  have hi : Integrable (fun ω => 2 * (M.H P R ω - c - SY ω - SZ ω) ^ 2 +
      2 * (θχ.2 p.T ω + SY ω) ^ 2) M.P :=
    (ha.integrable_sq.const_mul 2).add (hb.integrable_sq.const_mul 2)
  calc _ ≤ ∫ ω, (2 * (M.H P R ω - c - SY ω - SZ ω) ^ 2 + 2 * (θχ.2 p.T ω + SY ω) ^ 2) ∂M.P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) hi (ae_of_all _ hpt)
    _ = 2 * ∫ ω, (M.H P R ω - c - SY ω - SZ ω) ^ 2 ∂M.P +
          2 * ∫ ω, (θχ.2 p.T ω + SY ω) ^ 2 ∂M.P := by
        rw [integral_add (ha.integrable_sq.const_mul 2) (hb.integrable_sq.const_mul 2),
          integral_const_mul, integral_const_mul]
    _ ≤ η := by
        have h1 : ∫ ω, (M.H P R ω - c - SY ω - SZ ω) ^ 2 ∂M.P ≤ η / 4 := hRη
        have h2 : ∫ ω, (θχ.2 p.T ω + SY ω) ^ 2 ∂M.P ≤ η / 4 := hXη
        linarith

end StochCalcD3


set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace StochCalcR1

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end StochCalcR1


namespace StochCalcR1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcIndep ItoLib StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcD2 StochCalcD3 StochCalcGauss StochCalcP6S Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcR1M


namespace StochCalcR4

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcGauss Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcR4


open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace StochCalcR2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [mE : MeasurableSpace E] [BorelSpace E]

end StochCalcR2


open MeasureTheory Filter
open scoped ENNReal Topology

namespace StochCalcR2


end StochCalcR2


namespace StochCalcR2

open MeasureTheory

end StochCalcR2


open MeasureTheory Filter
open scoped ENNReal

namespace StochCalcR3

end StochCalcR3


set_option autoImplicit false

open MeasureTheory

namespace StochCalcR6

end StochCalcR6


namespace StochCalcR5

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR2 Finset Filter
open scoped Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

end StochCalcR5


namespace StochCalcR7

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR5 StochCalcR1M
  Finset Filter

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

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
    (hM : M.Standing) (hL2 : M.NegPartL2) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) :
    ∀ m P R : ℝ, M.Bval m P R =
      (if M.V0 P R = m then 0 else ⊤) +
        ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ∫⁻ ω,
          ENNReal.ofReal (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * M.delta P R u.toNNReal ω ^ 2)
            ∂M.P := by
  have hXm := HedgePSNV.degenerate_price_martingale p M hM h4 h5 hdeg
  have hS3 := HedgePSNV.degenerate_price_volatility_ne_zero p M hM h4 h5 hdeg
  have hXS0 := HedgePSNV.degenerate_simple_integrals_attainable p M hM h4 h5 hdeg hS3
  exact StochCalcP6.StochCalcHedgeDeg.deg_of_obligations M hM hL2 hdeg hXm.1
    (fun P R θχ hθ => StochCalcP6.StochCalcD2.D2 M hM hL2 h5 hdeg hXm.1 hXm.2 P R θχ hθ)
    (fun P R => StochCalcP6.StochCalcD3.D3_of_density M hM hL2 h5 hdeg hXm.1 hXm.2 P R
      (StochCalcP6.StochCalcD3.dens_of_rep M hM hL2 P R
        (HedgePSNV.payoff_simple_integral_density p M hM hL2 P R)
        (fun n hn Y C hY hC η hη => by
          obtain ⟨θχ, hθ, hi⟩ := hXS0 n hn Y C hY hC η hη
          exact ⟨θχ, hθ, 1, one_pos, hi⟩)))
