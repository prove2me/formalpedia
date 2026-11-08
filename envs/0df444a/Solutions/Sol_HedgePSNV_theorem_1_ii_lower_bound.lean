-- Prove2me | solution 1 for HedgePSNV.theorem_1_ii_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T20:33:10.455706+00:00
-- url     : https://prove2.me/submissions/7525e8e0-724a-4c8b-898a-feda5971bdff

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option maxHeartbeats 2000000
set_option linter.all false
set_option Elab.async false

-- ===== slice of Solutions.Sol_pv_1558a108 (probe/slice8c/cuts/r_k2.lean.src/Solutions.Sol_pv_1558a108.lean): 6/153 top-level decls kept =====

set_option linter.all false
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
/-! M9c: calculus for the pathwise-uniqueness test function (line derivatives, cutoff). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

end M9cF


section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

end M9c2


section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

end M9d


section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

end M9d2



section M9e1
/-! Zero integral, measurability of time integrals, the exponential primitive identity, and the
pointwise generator bound with the localizing rate `kap`. -/

end M9e1


section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2


end ItoLib


-- ===== slice of P8c066573M16 (probe/slice8c/cuts/r_k2.lean.src/P8c066573M16.lean): 100/865 top-level decls kept =====

/-! Bridge from the HedgePSNV model to the ItoLib library (Solutions/Sol_pv_1558a108.lean):
a standard 2-d Brownian motion `W = (B, B~)` (modified on a null set so that every path is
continuous), with `F t ≤ completedBrownianPast P W 0 t`, and the transfer of
`HasBrownianItoIntegral` from `(F, B)` / `(F, B~)` to `(cBP, W · · 0)` / `(cBP, W · · 1)`. -/

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

/-! D1a (pathwise half): if an Ito integral `I` equals `-(1/2) ∫_0^· g` at all dyadic grid points
(`g = η²` continuous) and its quadratic-variation sums converge in measure to `∫_0^T g`
(ItoLib.qvJ_tendsto with `B := 1`, `H1 = H2 = η`), then `∫_0^T g = 0` a.s.
The QV sums of a continuous finite-variation path vanish: `∑ (∫_cell g)^2 ≤ M^2 T^2 / 2^n`. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace StochCalcD1a

variable {Ω : Type*} [MeasurableSpace Ω]






end StochCalcD1a

/-! D1a wiring (relay 6): in the degenerate case `Z_T = 1` a.s., the drift `μ` vanishes
`dt`-a.e. on `[0,T]`, so `X_t = x₀ + J_t` for `t ≤ T`. The quadratic-variation input is the
hypothesis `hQV` = statement of the planned platform child C_QV (ItoLib.qvJ_tendsto with
`B := 1`, `j = j'`, `H1 = H2`). -/

namespace StochCalcD1aW

open HedgePSNV EthierKurtz StochCalcBr

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcD1aW

/-! LA / D1b (relay 6 start): an Ito integral `J = ∫ H dW^j` of a continuous adapted integrand with
`E ∫_0^T H² < ∞` (and a.s. continuous paths on `[0,T]`) is square integrable and satisfies the
martingale property in set-integral form for every `A ∈ completedBrownianPast s`, `A` measurable.
(`completedBrownianPast` contains non-measurable null subsets, so `condExp` wrt it is junk;
the model side converts the set-integral form into `IsMartingaleOn` for `F`.)
Dev file: imports the accepted ItoLib (Sol_pv_1558a108); the platform child pastes the prefix. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcL2M

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}










/-! Lemma B (relay 7): martingale property of the Ito integral of a BOUNDED continuous adapted
integrand at dyadic grid times, set-integral form. -/





/-! Lemma C (relay 7): unbounded continuous adapted integrands with `E ∫_0^t H² < ∞`. -/






/-! Lemma D (relay 7): `L²` bound and martingale property at arbitrary times `s ≤ t`. -/



end StochCalcL2M

/-! D1b (relay 7): the model's `dB`-integral `J = ∫ Xσ dB` is a `P`-martingale on `[0,T]` (set-integral
form for `F`), and in the degenerate case `Z_T = 1` the price `X` is a `P`-martingale on `[0,T]`. -/

namespace StochCalcD1b

open HedgePSNV EthierKurtz StochCalcBr StochCalcL2M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcD1b

/-! P1 for D2 (relay 7): the future increments of one Brownian coordinate `j` after `t₀` are
independent of the joint family {all coordinates up to `t₀`} ∪ {the other coordinates at all
times}. Used for the exponential tilts `Q_λ ∈ M_X` (D2) and Gaussian integration by parts. -/

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

/-! P1b (relay 7): the model σ-algebras `F_c ⊔ G_T'` sit inside the a.e. closure of the
past-of-`B~`/all-of-`B` σ-algebra of the library Brownian motion `W M`; hence the `B~`
increments after `c` are independent of `F_c ⊔ G_T'`. -/

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

/-! P2 for D2 (relay 8): Gaussian facts for a centred Gaussian `ξ ~ N(0, v)`:
exponential moments, the tilt `L c = exp(c ξ - v c²/2)` (mean one, in L²), and the
derivative-at-zero limit `E[ξ Y] = 0` from `E[(L c - 1) Y] = 0` for small `c ≠ 0` (DCT). -/

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


end StochCalcGauss

/-! P3 generic part (relay 8): change of measure by a positive mean-one L² density `D`,
set integrals / integrability under `Q = P.withDensity (ofReal ∘ D)`, the martingale property
under `Q` from set-integral identities under `P`, and the one-step tilt identity
`∫_A E R X_v = ∫_A E R X_s` (E `𝓕`-measurable, R independent of `𝓗 ⊇ 𝓕`, mean one). -/

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


end StochCalcTilt
/-! P3 model part (relay 8): the exponential `B~`-increment tilts
`Q_c = P.withDensity (exp(c (B~_{t'} - B~_t) - c²(t'-t)/2))` belong to `M_X` whenever `X` is an
L² `P`-martingale on `[0, T]` (degenerate case). -/

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


lemma Lm_mul (M : Model p Ω) {t s t' : ℝ≥0} (h1 : t ≤ s) (h2 : s ≤ t') (c : ℝ) (ω : Ω) :
    Lm M t s c ω * Lm M s t' c ω = Lm M t t' c ω := by
  simp only [Lm, L, ξ]
  rw [← Real.exp_add, V_eq h1, V_eq h2, V_eq (h1.trans h2)]
  ring_nf

lemma X_measH (M : Model p Ω) (hM : M.Standing) (u : ℝ≥0) {v : ℝ≥0} (hv : v ≤ p.T) :
    StronglyMeasurable[M.F u ⊔ M.G p.T] (M.X v) :=
  ((hM.X_adapted v).mono (M.G.mono hv)).mono le_sup_right



end StochCalcTiltM
/-! P4 (relay 8): every admissible gains process is orthogonal to the future `B~` increments:
`E[Y ξ χ_T] = 0` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y` (degenerate case,
`X` an L² `P`-martingale), via the tilts `Q_c ∈ M_X` and `d/dc|₀`. -/

namespace StochCalcOrth

open HedgePSNV EthierKurtz StochCalcBr StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


/-- set-integral form of a martingale step under any probability measure. -/
lemma setIntegral_mart {Q : Measure Ω} [IsProbabilityMeasure Q] (M : Model p Ω)
    {Y : ℝ≥0 → Ω → ℝ} (hY : IsMartingaleOn p.T M.F Q Y) {t : ℝ≥0} (ht : t ≤ p.T)
    {A : Set Ω} (hA : MeasurableSet[M.F t] A) :
    ∫ ω in A, Y p.T ω ∂Q = ∫ ω in A, Y t ω ∂Q := by
  rw [← setIntegral_condExp (M.F.le t) (hY.2.1 p.T le_rfl) hA]
  exact setIntegral_congr_ae (M.F.le t _ hA)
    (by filter_upwards [hY.2.2 t p.T ht le_rfl] with ω h _; exact h)



end StochCalcOrth

/-! P5 for D2 (relay 9): Gaussian integration by parts (Stein) for the hinge
`x ↦ max (k - s x) 0`, and its independent-conditioning form
`E[ξ (k0 - a (R - (U + s ξ))^+) Y] = a s v E[Y 1{U + s ξ ≤ R}]` for `ξ ~ N(0, v)` independent of `(U, Y)`. -/

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
/-! P5 model part (relay 9): Stein identity for the production payoff against a `B~` increment:
`E[ξ H Y] = (P - s) σ~ (t' - t) E[Y 1{A_T ≤ R}]` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y`
(no degeneracy needed: `ξ` is independent of `F_t ⊔ G_T ⊔ σ(B~_T - B~_{t'})`). -/

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


end StochCalcSteinM

/-! P6 generic pieces (relay 9): (A) a variance lower bound from a test variable `D` with
`E D = 0` and `E[D U] = E[D²]`; (B) left Riemann sums of a monotone function on a uniform grid. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6


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

/-! P6 generic (relay 10): martingale-difference sums `S n = Σ_{k<n} Y k * ξ k` with `ξ k`
independent of `m k`, centred, in `L²`, `m (k+1)`-measurable, and `Y k` bounded `m k`-measurable:
`E S = 0`, `S ∈ L²`, `E S² = Σ E[Y k²] E[ξ k²]`. Plus Gaussian moments. -/

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

/-! Degenerate case `Z_T = 1` a.s. of Theorem 1(ii) (child `HedgePSNV.theorem_1_ii_degenerate` of
proposition_5 cc6d45ce): reduction of the child to three stochastic obligations
  (D1) `X` is a `P`-martingale on `[0,T]`,
  (D2) lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
  (D3) approximate attainment `∃ (θ,χ) ∈ A_X, Var[H + χ_T] ≤ Psi + ε`,
plus the elementary degenerate facts (`P^M = P`, `Z_t = Z^M_t = 1` a.s., `E χ_T = 0`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedgeDeg

open HedgePSNV

variable {p : Params} {Ω : Type*} [MeasurableSpace Ω]


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

/-! D2 (relay 10): the degenerate lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
via the test variables `D_n = Σ_k σ~(P-s) c_{t_k} ξ_k` (P4 orthogonality, P5 Stein, P6 Riemann sums). -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg StochCalcGauss

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



lemma AT_meas (M : Model p Ω) (hM : M.Standing) : Measurable M.AT := by
  show Measurable fun ω => M.C p.T ω + p.σt * M.Bt p.T ω
  exact ((hM.C_adapted p.T).measurable.mono (M.G.le p.T) le_rfl).add
    (measurable_const.mul (Bt_measurable M hM p.T))












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

/-! D2 limit (relay 10): Riemann sums of the monotone `u ↦ E[δ_u²]` and `Psi_deg`. -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcD2
/-! D3 reduction (relay 11): approximate attainment `Var[H + χ_T] ≤ Psi + ε` from ONE
L²-density statement (`hdens` of `StochCalcD3.D3_of_density`): for every `η > 0` some
admissible `χ`, constant `c` and simple `dB̃`-sum `K = Σ Z_k ξ_k` on a uniform grid have
`E[(H + χ_T − c − K)²] ≤ η`.  Proof: `D = Σ σ̃(P−s) Yc_{t_k} ξ_k` is the projection of
`U = H + χ_T − c` onto the simple `dB̃`-sums of the grid (Stein + polarized isometry), so
`E U² ≤ E D² + E (U − K)²`, and `E D²` is a left Riemann sum of the monotone `u ↦ E δ_u²`. -/

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
/-! D3 split (relay 11): `hdens` of `D3_of_density` from
  (R)  representation density: `H ≈ c + Σ Y_k ΔB_k + Σ Z_k ΔB̃_k` in L² on a uniform grid;
  (XS) hedging of a simple `dB`-sum by an admissible strategy: `χ_T ≈ −Σ Y_k ΔB_k` in L².
Grid refinement `n → n*m` is exact (telescoping). -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcD3

/-! R1 generic (relay 13): telescoping-product approximation of `exp (i Σ x_k)` by a constant
plus an adapted "stochastic sum" `Σ A_k (i x_k)`, for a discrete filtration `m` and increments
`x k` that are `m (k+1)`-measurable, independent of `m k`, centred, with `E x_k⁴ ≤ D`.
Error in `L²`: `≤ 16 n D`.  Mathlib only. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace StochCalcR1



variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]









end StochCalcR1

/-! R1 model (relay 13): `exp (i Σ_k (λ_k ΔB_k + μ_k ΔB~_k))` on a uniform grid is `L²`-close to a
constant plus an adapted fine-grid sum `Σ_l A_l · i (a_l ΔB_l + b_l ΔB~_l)`.  Needs the joint
independence of `(ΔB, ΔB~)` on `[u, w]` from `F_u` (new: `indep_B_incr`, `indep_pair`). -/

namespace StochCalcR1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcIndep ItoLib StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcD2 StochCalcD3 StochCalcGauss StochCalcP6S Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






















end StochCalcR1M

/-! R4 (relay 13): the class `IsGS` of grid sums `c + Σ Y_k ΔB_k + Σ Z_k ΔB~_k` (bounded adapted
coefficients on a uniform grid) is a vector space of `F_T`-measurable `L²` functions. -/

namespace StochCalcR4

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcGauss Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcR4

/-! R2a (relay 12): characteristic-function identification.  If an integrable `V` is orthogonal to
`cos ⟪Δ, t⟫` and `sin ⟪Δ, t⟫` for every `t`, then `∫_A V = 0` for every `A ∈ σ(Δ)`.
Mathlib only. -/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace StochCalcR2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [mE : MeasurableSpace E] [BorelSpace E]



end StochCalcR2

/-! R2b (relay 12): π-λ extension of vanishing set integrals from an increasing sequence of
σ-algebras to their supremum joined with the `P`-null sets, and the a.e.-limit criterion that
puts a variable's σ-algebra below it.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace StochCalcR2








end StochCalcR2

/-! R2c (relay 12): the generic identification theorem. -/

namespace StochCalcR2

open MeasureTheory


end StochCalcR2

/-! R3 (relay 12): Hilbert-space glue.  A subspace (given as a predicate on functions) of `L²`
whose orthogonal complement is trivial is `L²`-dense.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal

namespace StochCalcR3


end StochCalcR3

/-! R6 generic (relay 13): orthogonality passes to `L²`-limits.  Mathlib only. -/

set_option autoImplicit false

open MeasureTheory

namespace StochCalcR6



end StochCalcR6

/-! R5 (relay 14): the grid-`2^j` increment vectors `Δ_j` of `(B, B~)`, the monotonicity of
their σ-algebras, `F_T ≤ aug (⨆ σ(Δ_j))`, and `⟪Δ_j, t⟫` as a grid sum. -/

namespace StochCalcR5

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR2 Finset Filter
open scoped Topology



variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





















end StochCalcR5

/-! R7 (relay 14): trigonometric functions of `Δ_j` are `L²`-limits of grid sums; hence the
grid sums are dense in `L²(F_T)` (hsep + R3), which is the hypothesis `hR` of `dens_of_rep`. -/

namespace StochCalcR7

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR5 StochCalcR1M
  Finset Filter




variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcR7

/-! TC (relay 15 of cc6d45ce): truncation consistency of the Ito integral at an ARBITRARY time
`r ≤ t`.  The clamped left-point sums of the horizon-`t` dyadic grid, masked to the cells that
start before `r`, converge in probability to `J r`, given that `J` is continuous in probability
along the dyadic floors `r_n ↑ r`.  Three-term argument: dyadic floor `r_n` (ItoLib M7a
`partialSum_tendsto_of_hasBrownianItoIntegral`), the cells in `[r_n, r)` (Lenglart bound
`itoStepSum_local_chebyshev`, at most `2^m` cells of length `t/2^(n+m)`), and `J r_n → J r`.
Use: hXS step S1 (Ito integral of a simple-in-time strategy times `Xσ`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
















/-! S1b preparation (relay 15): one cell for every coefficient family; `thetaS` bounds. -/





end StochCalcTC

/-! TC2 (relay 16 of cc6d45ce): S1b, the integrated-squared-error clause for the
`thetaS · clamp_N H` approximants. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcTC

/-! TC3 (relay 16 of cc6d45ce): S1 assembly.  The Ito integral of the simple-in-time weight
`thetaS s θ n'` times a continuous adapted `H` is `Σ_i θ_i (J(s_{i+1} ∧ t) − J(s_i ∧ t))`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! TC4 (relay 16 of cc6d45ce): variant of S1c needing `J`-continuity only at the jump times;
dyadic floors converge; clause 1 of the Ito relation for `thetaS · H`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! Mart (relay 16 of cc6d45ce): simple stochastic integrals of a martingale are martingales.
`θ (X(b ∧ t) − X(a ∧ t))` with `θ` bounded `F a`-measurable is an `IsMartingaleOn` martingale;
finite sums too.  Generic (any filtration, any finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcMart

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcMart

/-! S1M (relay 16 of cc6d45ce): in the degenerate model, a simple-in-time strategy
`thetaS s θ n'` (jump times `s_i ≤ T`, `θ_i` bounded `F(s_i)`-measurable) with gains
`chiS = Σ θ_i (X(s_{i+1} ∧ t) − X(s_i ∧ t))` is admissible: `(thetaS, chiS) ∈ A_X`. -/

namespace StochCalcS1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1M

/-! TCR (8c066573 relay 15, O2 core): truncation consistency at a RANDOM cutoff `ρ ≤ t` that is a
stopping time of the completed Brownian past.  Same three-term argument as `truncSum_tendsto`,
with the dyadic CEILING `ρ^n = dyTime t n ⌈ρ/t·2^n⌉` (a stopping time, finitely many values):
masked sums up to `ρ^n` are finitely many deterministic truncations (`trunc_dy_tendsto`), the
cells in `[ρ, ρ^n)` are adapted (Lenglart), and `J (ρ^n) → J ρ` is a hypothesis. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}











end StochCalcTC

/-! S1b with RANDOM jump times `s ω` (8c066573 relay 15): the argument is pathwise. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}



end StochCalcTC

/-! S1RM (8c066573 relay 15, O2b): the Ito relation for a STOPPED simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}` in the model, with `K_t = Y (J(s'∧τ∧t) − J(s∧τ∧t))`.
Append after probe/cc6d45ce_S1M.lean + lib/stochcalc/TCR_tail.lean + lib/stochcalc/S1bR_tail.lean.
Hypothesis `hJc` (J along dyadic ceilings of a random time) is discharged separately (needs s' < T). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcS1R
/-! S1RJ (8c066573 relay 16, O2c): discharge `hJc` of `S1R_model` for random times bounded by
`s' < T`, giving `S1R_modelT` (no `hJc` hypothesis).
Append after probe/8c066573_S1R.lean (= cc6d45ce_S1M + TCR_tail + S1bR_tail + S1RM_tail). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcS1R

/-! OS (8c066573 relay 14): continuous-time optional stopping for `IsMartingaleOn`.
A continuous martingale on `[0,T]` stopped at a stopping time is again a martingale on `[0,T]`.
Proof: grid stopping times `jn` on `s + k (t-s)/(N+1)` (Mathlib discrete optional sampling gives
`X(grid ceiling of ρ) = E[X t | F_ρN]`), uniform integrability of conditional expectations,
pointwise convergence by path continuity, Vitali.  Generic (any filtration, finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcOS

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]



























end StochCalcOS

/-! Hit (8c066573 relay 16, O2a): the hitting time of the closed set `{R ≤ |x|}` by a process
with continuous paths, capped at `T`, is a stopping time of any filtration to which the
process is adapted (no right-continuity of the filtration needed: closed set + continuous paths).
Also: the stopped process is bounded by `R` when it starts inside. Mathlib only. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcHit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcHit
/-! S1RA (8c066573 relay 16, O2d): the stopped simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}`, `χ_t = Y (X_{s'∧τ∧t} − X_{s∧τ∧t})` is admissible (`∈ M.AX`) when
`s ≤ s' < T`, `τ` is a stopping time and the stopped price is bounded (e.g. `τ = hitR`).
Append after probe/8c066573_S1RJ.lean + the body of lib/stochcalc/Hit.lean (no import line). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib StochCalcOS StochCalcHit

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1R

/-! RieszIso (8c066573 relay 16, O3 core): if a linear map `T : S → F` into a Hilbert space is
isometric for a seminorm given by a linear map `e : S → E` into another Hilbert space
(`‖T s‖ = ‖e s‖`), then every `f ∈ F` has a "representing integrand" `a ∈ E` with
`⟪f, T s⟫ = ⟪a, e s⟫` for all `s`.  (Use: `S` = simple adapted processes, `e` = their class in
`L²(dt ⊗ dP)`, `T` = the elementary stochastic integral into `L²(P)`.)  Mathlib only; no quotient
by null processes is needed. -/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StochCalcRiesz

variable {S E F : Type*} [AddCommGroup S] [Module ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]




end StochCalcRiesz

/-! O3gen (8c066573 relay 17, O3 instantiation, generic; append after RieszIso.lean, Mathlib only).
For a real process `W` with independent centred increments of variance `v - u` w.r.t. a monotone family
`m t` of σ-algebras, every `f ∈ L²(P)` has a representing integrand `a ∈ L²(dt|[0,T] ⊗ P)` (in the closure of
the adapted simple processes) with `E[f · Y (W_v - W_u)] = ∫∫ a · 1_[u,v) Y` for all bounded `m u`-measurable `Y`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}
































end StochCalcO3

/-! O3M (8c066573 relay 17, O3 model instantiation): `B` and `B~` satisfy `StochCalcO3.IncrHyp` w.r.t. `M.F`,
so every `f ∈ L²(P)` has representing integrands `a, b ∈ L²(dt|[0,T) ⊗ P)` (in the closure of adapted simple processes):
`E[f Y (B_v - B_u)] = ∫∫ a 1_[u,v) Y` and `E[f Y (B~_v - B~_u)] = ∫∫ b 1_[u,v) Y`.
Append after probe/8c066573_S1RA.lean + RieszIso.lean body + O3gen_tail.lean (no import lines). -/

namespace StochCalcO3M

open HedgePSNV StochCalcBr StochCalcO3 StochCalcD3 StochCalcR1M StochCalcTiltM StochCalcSteinM
  StochCalcGauss StochCalcP6S

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcO3M

/-! O4gen (8c066573 relay 17, O4 generic part; append after O3gen_tail.lean, Mathlib only).
If elementary combinations `s n` have time-space classes `eL (s n) → ψ` in `L²(μT)` and elementary integrals
`TL (s n) → J` in measure, then `J` has an `L²` version `K` with `‖K‖ = ‖ψ‖` (isometry) and `⟪f, K⟫ = ⟪a, ψ⟫`
for the representing integrand `a` of `f` (O3).  Plus pointwise formulas `coe_TL` / `coe_eL` for combinations. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

/-! O4step (8c066573 relay 18, O4 generic step-approximation part).  Append after O4gen_tail.lean.
Needs `Definitions.Def_EthierKurtz_itoStepValue`, `Definitions.Def_EthierKurtz_itoStepSum` and
`Solutions.Sol_pv_1558a108` (ItoLib) imported.
`O4fun`: function form of O4gen.  `O4step`: given EK approximants `a0` of a BOUNDED jointly measurable
integrand `H` (integrated squared error → 0 in probability, step sums → `J` in probability) and the ItoLib
"zero lemma" for step sums, the approximants clamped at the bound of `H` are elementary combinations whose
time-space classes converge to `H` in `L²(μT)` and whose integrals still converge to `J`; hence
`∫ f J dP = ∫ a H dμT` for the representing integrand `a` of `f` (O3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



/-! Clamping and step values. -/








/-! The clamped approximants as elementary combinations. -/











end StochCalcO3

/-! O4 model (8c066573 relay 18; append after O4step_tail.lean in the model dev file).
The doubly stopped simple strategy `θ = Y 1{s∧τ ≤ u < s'∧τ}`, `τ = hitR X R ∧ hitR σ R'`, is admissible
(`dblSimple_mem_AX`) and its Itô integrand `θ X σ` is bounded by `C R R'`, so `O4step` gives
`E[f · Y (J_{s'∧τ} - J_{s∧τ})] = ∫ a θ X σ dμT` for the representing integrand `a` of `f` (O3, dB part). -/

namespace StochCalcO4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcO4M
/-! O5 drift identity (8c066573 relay 19; append after O4M_tail.lean in the model dev file).
Triple stop `τ = hitR X R ∧ hitR σ R' ∧ hitR μ R''` bounds both integrands `θ X σ` and `θ X μ`.
KEY (relay 19): no conditional expectation `f_u` is needed for the drift: Fubini alone gives
`E[f ∫_0^T θ X μ du] = ∫ (θ X μ)(u,ω) f(ω) dμT`.  With O4 and `f ⊥ χ_T`:
`O5_gain : ∫ a θ X σ dμT + ∫ θ X μ f dμT = 0` for every triple-stopped simple strategy. -/

namespace StochCalcO5

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO5
/-! O6a (8c066573 relay 19): Pred-membership of bounded step-approximable integrands.
Append after O56_tail.lean.  `pred_approx` = the L²(μT) half of O4step (no stochastic integral):
any bounded jointly measurable `H` whose dyadic step approximants `a0` (adapted, NOT necessarily
bounded) have integrated squared error → 0 in probability is an `L²(μT)` limit of elementary
combinations; `pred_mem` states it as membership of the class of `H` in the closure of `range eL`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}



end StochCalcO3

/-! O6b (8c066573 relay 20): left-point sampling.  Append after O6a_tail.lean.
`pred_left`: a bounded, jointly measurable, adapted process that is left-continuous in time at
a.e. `u ∈ (0,T]` (for every `ω`) has its class in the closure of `range eL` (dyadic left-point
approximants `a0 n k = H (k T / 2^n)`, dominated convergence, a.e. ⇒ in measure). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}




end StochCalcO3

/-! O6c (8c066573 relay 20): generic Hilbert pieces of O6.  Append after O6b_tail.lean.
`O6_core`: an `L²(μT)` function in the closure of `range eL` orthogonal to every elementary
`efun` vanishes a.e.;  `perp_all`: orthogonality to elementaries with `v < T` suffices;
`proj_fun`: predictable projection `c` of any `F ∈ L²(μT)` (`∫ c ψ = ∫ F ψ` for predictable `ψ`);
`pred_mul`: predictable × bounded adapted a.e.-left-continuous is predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}

















end StochCalcO3

/-! O6M (8c066573 relay 20): model instance of O6.  Append after O6c_tail.lean in the model dev
file (O6a.lean + O6b_tail + O6c_tail).  With `a' = proj a`, `c = proj (f ∘ snd)` (predictable
projections), every triple stop `τ_N` gives `w_N = a' (Xσ 1[·<τ_N]) + c (Xμ 1[·<τ_N]) ⊥ elementaries`
(O5_gain + proj_fun) and `w_N` predictable (pred_mul), so `w_N = 0` (O6_core); `τ_N = T`
eventually (continuous paths are bounded on `[0,T]`), hence `a' Xσ + c Xμ = 0` μT-a.e. -/

namespace StochCalcO6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open StochCalcO5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO6M



/-! O7.1 [U1] energy uniqueness, bounded-coefficient core.  Restriction `resF s` of elementary
combinations to `[0,s)`, its orthogonality to `m s`, and the restricted-norm bound
`‖E[θ | m s]‖ ≤ ‖a 1_{[0,s)}‖` for a stochastic integral `θ` with integrand `a`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.1 localization, part L0.  `Rep θ b` : `θ` is the stochastic integral of the predictable
integrand `b` (isometric extension of `TL`).  Basic calculus of `Rep` (distance identity, limits,
existence, uniqueness, orthogonality to `L²(m s)` when `b` vanishes before `s`) and the locality
lemma `L0`: for `A ∈ m t` and `b` vanishing before `t`, `Rep θ b → Rep (1_A θ) (1_A b)`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


























end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L1: grid stopping times.  For `τ` with finitely many values `t ∈ S` (`{τ = t} ∈ m t`) and
`δ = I(1_{τ ≤ r} a)`, `δ ⊥ ξ 1_{u < τ}` for bounded `m u`-measurable `ξ`. -/












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L2: general stopping times `τ ≤ T`, by the dyadic ceilings `gc T n τ ↓ τ`. -/


















end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! (B1) cutting a predictable integrand at a stopping time keeps it predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3
-- O7B2 tail (8c066573 relay 24): append after probe/8c066573_B.lean (= L0.lean + O7B_tail).

/-! (B2) the cut-off integral `δ = I(1_{τ ≤ r} a)` is orthogonal to `1_{r<τ} ψ`, and
(B3) the projections of `θ` and of `θ - δ` agree before `τ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! O7.1 (U1, general): energy uniqueness for `a = -η c` with `η` continuous adapted. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.2 (8c066573 relay 25): K-projection.  Two filtrations `mK ≤ mF` for which the same process
`W` satisfies `IncrHyp`, plus the conditional-independence hypothesis
`H1 : E[Y | mK T] = E[Y | mK u]` for bounded `mF u`-measurable `Y` (`u ≤ T`).  If `θ = I_F(a)`
then `φ = E[θ | mK T]` is a K-stochastic integral `I_K(b)`, where `b` is the orthogonal projection
of `a` onto the K-predictable subspace: `⟪b, ψ⟫ = ⟪a, ψ⟫` for every K-predictable `ψ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

/-! O7.4a (8c066573 relay 25): identification of an integrand from localized weak pairings.
If `b, c'` are predictable and `⟪b, 1_{r<τ_R} e⟫ = -⟪c', η 1_{r<τ_R} e⟫` for every elementary `e`
and every hitting level `R ∈ ℕ` of the continuous adapted `η`, then `b = -η c'` a.e.  (This turns the
K-projection `Kproj` of `a = -η c` into the hypothesis `hac` of `U1` without assuming `η` bounded.) -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}






end StochCalcO3

/-! O7.4b (8c066573 relay 25): `Kshift`.  If `θ = I_F(a)` with `a = -η c`, `c` the F-projection of
`θ`, and `η` continuous and K-adapted, then `φ = E[θ | mK T]` satisfies `φ = I_K(b)` with
`b = -η c_φ`, `c_φ` the K-projection of `φ` (the hypothesis shape of `U1` in the filtration K). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! O7.4c (8c066573 relay 25): `U1_diff` -- two integrals `θ₁ = I(-η c₁)`, `θ₂ = I(-η c₂)` (each `cᵢ`
the predictable projection of `θᵢ`, integrands vanishing before `v`) coincide.  O7.4 applies it in
the filtration K to `θ₁ = E[f | K_T] - f_t` (from `Kshift`) and `θ₂ = f_t (Z_T / Z_t - 1)` (from O7.3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7.3 generic part (Z1): `Rep` is closed under `L²` limits of integrands (`rep_of_tendsto`),
and the truncation limit `rep_trunc`: integrands `1_{S n} f` (`S n` increasing, covering a.e.)
with `Rep θ_n (1_{S n} f)` and `‖θ_n‖ ≤ C` force `f ∈ L²(μT)` and `Rep θ f` for the `L²`
limit `θ` of `θ_n`.  Used for `Z_T - 1 = I(-Z η)` from the stopped identities. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z6 (8c066573 relay 27, O7.3): L² optional-sampling bound for a right-continuous martingale
closed by `Z T`: `‖Z_{τ∧T}‖₂ ≤ ‖Z_T‖₂` for every stopping time `τ`.  Finite-valued case by
conditional Jensen on `{σ = t} ∈ m t` (`eLpNorm_condExp_le_eLpNorm`), general case by the
dyadic ceilings `gc T n τ ↓ τ ∧ T` and Fatou. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}









end StochCalcO3

/-! Z4 (8c066573 relay 27, O7.3): Rep form of an EK Ito integral of a bounded integrand
(copy of O4step's approximation argument ending in `rep_exists`/`rep_conv`). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! Z4t (8c066573 relay 27, O7.3): transfer of `Rep` from a larger filtration `m'` (e.g. the completed
Brownian past) to a smaller one `m ≤ m'` (e.g. `M.F`) when every `m' t`-measurable variable has an
a.e.-equal `m t`-measurable version: the elementary integrals and time-space classes agree. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z5 (8c066573 relay 28, O7.3): stopped identification.  If `Rep θ a` and `K t =ᵐ E[θ | m t]`
(t ≤ T) with right-continuous paths, then for a stopping time `τ ≤ T` the variable `K_τ` is the
integral of `1_{s<τ} a`.  Route: (rep_aesm) integrals of integrands vanishing after `s` are
`m s`-measurable; (rep_ce) `E[θ|m t]` integrates `1_{s<t} a`; (Z5fin) finite-valued `τ` via `L0`;
(Z5) grid `gc T n τ ↓ τ`, `L²` limit + a.e. subsequence + right-continuity. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}








end StochCalcO3

/-! Z4m-a (8c066573 relay 28, O7.3): completed-Brownian-past measurable variables have
`M.F t`-measurable a.e. versions (append after Br.lean; needs `import Solutions.Sol_pv_1558a108`
for `ItoLib.aeClosure` / `completedBrownianPast_const_le`). -/

namespace StochCalcZ4m

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib StochCalcBr
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

section Gen
variable {Ω' : Type*}



end Gen






end StochCalcZ4m

/-! Z4m-b (8c066573 relay 29, O7.3): a bounded library Ito integral (filtration `cBP`, driver
`W · · 0`) of the HedgePSNV model is represented (`Rep`, filtration `M.F`, driver `M.B`) by its
integrand.  `M.F`-measurable a.e. versions of the library approximants (hmod_cBP), clamped to keep
the per-level bounds, then `StochCalcO3.O4rep`. Append after the combined dev base (O6M + generic
Z chain + O7Z4m_tail). -/

namespace StochCalcZ4mb

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ4mb


/-! Z2 (8c066573 relay 29, O7.3): a continuous, `cBP`-adapted version `Ic` of the Ito integral of
`η' s = η (s ∧ T)`, glued from the continuous Ito integrals of the clamped integrands `clamp n η'`
(platform theorem 1c98c8e0, conjunct 3, as the hypothesis `ContHyp M`).  Gluing index: the least
`n` with `sup |η'| ≤ n` (whole horizon) for the paths, and the least `n` with `sup_{[0,t]} |η'| ≤ n`
for the `cBP t`-measurable version at time `t` (completeness of `cBP t`).  Append after
O7Z4mb_tail. -/

namespace StochCalcZ2

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcZ2



/-! Z3 (8c066573 relay 29, O7.3): Ito formula for `Zc = exp(-Ic - ½∫η'²)`: for a continuous,
`cBP`-adapted Ito integral `Ic` of `η'` (Z2), `Zc t = 1 + K t` a.s. for each `t`, where `K` is the
Ito integral of `-Zc η'` (ItoLib `ito_formula` with `e = 1`, `X = Ic + ½∫η'²`, `f x = exp(-x₀)`).
Append after O7Z2_tail. -/

namespace StochCalcZ3

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2
open scoped NNReal ENNReal

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end line

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcZ3

/-! Z7a (8c066573 relay 30, O7.3): horizon change for `Rep` (an integrand on `[0,t)` represents
the same variable at any later horizon `T`), hence the conditional expectation of a represented
variable at time `t` is represented at horizon `t`; model corollary `Jmart`: a bounded library Ito
integral is an `M.F`-martingale.  Append after O7Z3_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}













end StochCalcO3

namespace StochCalcZ7a

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m StochCalcZ4mb
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcZ7a

/-! Z7b/Z7c (8c066573 relay 30, O7.3): `Zc` is continuous, `M.F`-adapted, a.e. equal to `M.Z`
on `[0,T]` and an `M.F`-martingale closed by `Zc T` (Assumption5); stopping at the hitting time
`τ R` of `|Zc η'| ≥ R`, the library Ito integral `J` of the clamped integrand `Hcl R` equals
`Zc - 1` at `τ R` (locality at dyadic `t < τ R` + path continuity).  Append after O7Z7a_tail. -/

namespace StochCalcZ7b

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






variable {Ic : ℝ≥0 → Ω → ℝ}
















end StochCalcZ7b

/-! Z7d (8c066573 relay 30, O7.3 assembly): `Zc T - 1` is represented (`Rep`, filtration `M.F`,
driver `M.B`) by the integrand `-Zc η'` on `[0,T)`, which is in `L²(dt × dP)`.  Per level `n`:
ContHyp integral `J n` of `Hcl n`, Z4m representative, Jmart (Z5's martingale hypothesis), Z5 at
`tau n`, locality `loc`, Z6 bound; then rep_trunc over `S n = {s < tau n}` and the a.e. limit
(`tau n = T` eventually).  Append after O7Z7b_tail. -/

namespace StochCalcZ7d

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ7d


/-! O7ZM (8c066573 relay 31, O7.3 remainder): multiplication of a stochastic integral by a
bounded `m t`-measurable factor `ζ` (generalizes `L0`, where `ζ = 1_A`), and the tail
representation `θ - E[θ | m t] = I(a 1_[t,T))`.  Generic `StochCalcO3`; append after O7Z7d. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}








end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


end StochCalcO3

/-! O7ZK (8c066573 relay 32, O7.3 model instance in a sub-filtration `mK`): generic
`rep_restrict` (an `mF`-representation of an `mK T`-measurable `θ` by an `mK`-predictable integrand
is an `mK`-representation), `mart_restrict` (tower property), and the model instance `zK` of `ztail`
for `ZT = Zc (· ∧ T)` in any filtration `cBP ≤ mK ≤ M.F` with `IncrHyp mK M.B` and `H1`.
Generic `StochCalcO3` part + `StochCalcZK`; append after O7ZM_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

namespace StochCalcZK

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcZK

/-! O7KF (8c066573 relay 32, model K + H1 for O7.4): the filtration
`Kf t s = F_s (s < t), F_t ⊔ G_s (s ≥ t)`, with `Kf ≤ F`, `IncrHyp (Kf t) M.B`, `Zc` and `η`
`Kf`-adapted on `[0,T]`, and the conditional-independence hypothesis `H1` of `Kproj`/`Kshift`.
Generic part: `ce_sup_indep` (`E[Y | A ⊔ D] = E[Y | A]` for `Y ∈ F' ⊇ A`, `F' ⊥ D`) and
`meas_of_ae_eq_nulls`.  Append after O7ZK_tail. -/

namespace StochCalcCE

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} {A F' D K : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]




end StochCalcCE

namespace StochCalcKF

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcKF

/-! O7Q1 (8c066573 relay 32, O7.4 generic core): if `θ = I_F(a)` with `a = -η c` (`c` the
F-projection of `θ`, `η` continuous `mK`-adapted) and `Θ = E[θ | mK T]` is orthogonal to `L∞(mK t)`,
then `Θ = 0`.  Kshift (Θ = I_K(-η cΘ)), perp_tail (cΘ = 0 before t), U1.  Append after O7KF_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7Q1M (8c066573 relay 33, O7.4 model): `E[θ | F_t ⊔ G_T] = E[θ|F_t] Z_T / Z_t` for `θ = I_F(-η c)`.
Generic: `int_mul_ce`, `proj_tailA` (F-projection of `1_A (θ - f_t)`).  Model: `Q1R` (fixed `R`), `Q1model`.
Append after O7Q1_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω}


end StochCalcO3

namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedge

open HedgePSNV







end StochCalcHedge

/-! S8 tail (8c066573 relay 1, 2026-11-06): `0 ≤ Z_t/Z^M_t ≤ 1` a.s. and the three elementary
conjuncts of theorem_1_ii (everything except the value formula (21)).
Appended after S8.lean (namespace StochCalcHedge provides I_zero_ae, Z_pos, Z_T_measurable,
ZM0_eq, one_lt_ZM0). -/

namespace StochCalcS8b

open HedgePSNV StochCalcHedge









end StochCalcS8b
/-! K2a (8c066573 relay 2, 2026-11-06): base change `P → P^M` for the `B~`-tilt machinery.
`dP^M/dP = Z_T` is `G_T`-measurable, so every independence `F_u ⊔ G_T ⊥ (B~ increments after u)`
and the Gaussian laws of the increments survive under `P^M`; the exponential `B~`-tilts of `P^M`
are in `M_X` once `X` is a `P^M`-martingale (no L² assumption on `X`).
Append after cc6d45ce_P4.lean + S8.lean + S8b_tail.lean (imports stripped). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM

section generic

variable {Ω : Type*}





end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2
/-! K2b (8c066573 relay 2): orthogonality `E^M[Y ξ χ_T] = 0` and the Stein identity under `P^M`.
Append after K2a_tail.lean. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcOrth

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}


end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcK2
/-! K2c (8c066573 relay 2): Bessel inequality for two orthogonal test variables, and the
`Z_T`-weighted martingale-difference sums `S = Σ_{k<N} Y_k ξ_k` on the grid `gr p n`
(`E_P[Z_T² S²] = Σ E_P[Z_T² Y_k²] T/n`, `E_P[Z_T² S] = E_P[Z_T S] = 0`) via the auxiliary
measure `Q2 = (Z_T²/c)·P`, under which the grid increments keep their independence and laws.
Append after K2b_tail.lean (needs D2_tail's `gr`, `V_gr`; i.e. a dev file containing D2). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcP6S

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]



end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcK2


/-! O7Q2 (8c066573 relay 34, O7.5 glue hQb): Bayes formula for the tilted measure
`Q = (Z²/c)·P` and the Q2 form of O7.4: with `g = θ / Z_T`,
`E_Q[g | m] = E_P[θ|F_t] / Z_t` for every `F_t ≤ m ≤ F_t ⊔ G_T`; hence
`E_Q[g | F_t ⊔ G_T] = E_Q[g | F_t]` (the `hQb` hypothesis of `StochCalcE2.E2_bound`).
Generic: `StochCalcQ2.bayes_ce`.  Model: `StochCalcQ2.Q2ce`, `StochCalcQ2.Q2_hQb`.
Append after O7Q1M_tail (inside the dev file's `namespace StochCalcP6`). -/

namespace StochCalcQ2

open MeasureTheory ProbabilityTheory Filter Topology
open StochCalcTilt
open scoped NNReal ENNReal

section generic

variable {Ω : Type*} {m mH : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]


end generic

end StochCalcQ2

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ2M


/-! O7.5 piece (relay 21): one-cell identity of the E2 error argument (pure Mathlib).
F-filtration (F k) ≤ (F (k + 1)), enlarged H-filtration (H k) ≤ (H (k + 1)) ((F k) ≤ (H k), (F (k + 1)) ≤ (H (k + 1))), increment w ((F (k + 1))-measurable,
"independent of (H k) with mean 0" in the form `hind`), g with E[g|(H (k + 1))] = E[g|(F (k + 1))] (Q1), NC for (F k)-multipliers.
Then for a bounded (H k)-measurable y:  E[g y w] = E[(gb - ga) w (yb - ya)]. -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcE2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]



end StochCalcE2

-- O7E3 tail (8c066573 relay 24): append after lib/stochcalc/O7E2.lean (pure Mathlib).

/-! O7.5 (E2 n-cell sum): splitting a cell into `n` pieces, the NC orthogonality gives
`|E[g y ΣΔW]| ≤ l/2 E g² + (1/2l)(μ/2 Σ E w_k⁴ + 2 Cy⁴/μ)` for all `l, μ > 0`; with `Σ E w_k⁴ = O(1/n)`
this forces `E[g y ΣΔW] = 0`. -/

namespace StochCalcE2

open MeasureTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]









end StochCalcE2


/-! O7G4 (8c066573 relay 24, for the O7.5 model instance): fourth moments of centred Gaussians
scale like `v²`: `∫ x⁴ dN(0,v) = v² ∫ x⁴ dN(0,1)`, and a random variable with law `N(0,v)` has
`E w⁴ = v² K₄`, `K₄ := ∫ x⁴ dN(0,1)` (finite). Pure Mathlib. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochCalcG4




end StochCalcG4

/-! O7E5 (8c066573 relay 34, O7.5 model glue): under `Q2 = (Z_T²/c)·P`, if `g = f/Z_T` has the
Q1 property `E_Q2[g | F_t ⊔ G_T] = E_Q2[g | F_t]` (`StochCalcQ2M.Q2ce`) and `f` is orthogonal to
the grid class `NC` (expanded form `hfN`), then `E_Q2[g y (B~_{t_{j+1}} - B~_{t_j})] = 0` for every
bounded `F_{t_j} ⊔ G_T`-measurable `y` (cell split in `r` pieces + `StochCalcE2.E2_bound` +
`StochCalcE2.zero_of_bounds`).  Append after E2G4_block (dev base M15). -/

namespace StochCalcE5M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcE2 StochCalcG4
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcE5M

end StochCalcP6
-- ===== slice of RUmod (probe/slice8c/cuts/r_k2.lean.src/RUmod.lean): 0/17 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! RU (8c066573 relay 44): Elem-free ("unpacked") forms of `Rep`, `closure (range eL)`, `closure (range TL)`
and `IncrHyp`, so that cut statements become Definitions-only after unfolding. -/

namespace StochCalcRU

open StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}














end StochCalcRU

namespace StochCalcQ2U

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcZ2 StochCalcZ3 StochCalcO3
open StochCalcZK
open StochCalcRU
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcQ2U

end StochCalcP6

-- ===== slice of P8c066573M16c (probe/slice8c/cuts/r_k2.lean.src/P8c066573M16c.lean): 64/865 top-level decls kept =====

/-! Bridge from the HedgePSNV model to the ItoLib library (Solutions/Sol_pv_1558a108.lean):
a standard 2-d Brownian motion `W = (B, B~)` (modified on a null set so that every path is
continuous), with `F t ≤ completedBrownianPast P W 0 t`, and the transfer of
`HasBrownianItoIntegral` from `(F, B)` / `(F, B~)` to `(cBP, W · · 0)` / `(cBP, W · · 1)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcBr

open HedgePSNV EthierKurtz

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



































end StochCalcBr

/-! D1a (pathwise half): if an Ito integral `I` equals `-(1/2) ∫_0^· g` at all dyadic grid points
(`g = η²` continuous) and its quadratic-variation sums converge in measure to `∫_0^T g`
(ItoLib.qvJ_tendsto with `B := 1`, `H1 = H2 = η`), then `∫_0^T g = 0` a.s.
The QV sums of a continuous finite-variation path vanish: `∑ (∫_cell g)^2 ≤ M^2 T^2 / 2^n`. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

namespace StochCalcD1a

variable {Ω : Type*} [MeasurableSpace Ω]






end StochCalcD1a

/-! D1a wiring (relay 6): in the degenerate case `Z_T = 1` a.s., the drift `μ` vanishes
`dt`-a.e. on `[0,T]`, so `X_t = x₀ + J_t` for `t ≤ T`. The quadratic-variation input is the
hypothesis `hQV` = statement of the planned platform child C_QV (ItoLib.qvJ_tendsto with
`B := 1`, `j = j'`, `H1 = H2`). -/

namespace StochCalcD1aW

open HedgePSNV EthierKurtz StochCalcBr

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcD1aW

/-! LA / D1b (relay 6 start): an Ito integral `J = ∫ H dW^j` of a continuous adapted integrand with
`E ∫_0^T H² < ∞` (and a.s. continuous paths on `[0,T]`) is square integrable and satisfies the
martingale property in set-integral form for every `A ∈ completedBrownianPast s`, `A` measurable.
(`completedBrownianPast` contains non-measurable null subsets, so `condExp` wrt it is junk;
the model side converts the set-integral form into `IsMartingaleOn` for `F`.)
Dev file: imports the accepted ItoLib (Sol_pv_1558a108); the platform child pastes the prefix. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcL2M

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}










/-! Lemma B (relay 7): martingale property of the Ito integral of a BOUNDED continuous adapted
integrand at dyadic grid times, set-integral form. -/





/-! Lemma C (relay 7): unbounded continuous adapted integrands with `E ∫_0^t H² < ∞`. -/






/-! Lemma D (relay 7): `L²` bound and martingale property at arbitrary times `s ≤ t`. -/



end StochCalcL2M

/-! D1b (relay 7): the model's `dB`-integral `J = ∫ Xσ dB` is a `P`-martingale on `[0,T]` (set-integral
form for `F`), and in the degenerate case `Z_T = 1` the price `X` is a `P`-martingale on `[0,T]`. -/

namespace StochCalcD1b

open HedgePSNV EthierKurtz StochCalcBr StochCalcL2M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcD1b

/-! P1 for D2 (relay 7): the future increments of one Brownian coordinate `j` after `t₀` are
independent of the joint family {all coordinates up to `t₀`} ∪ {the other coordinates at all
times}. Used for the exponential tilts `Q_λ ∈ M_X` (D2) and Gaussian integration by parts. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology

namespace StochCalcIndep

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}




end StochCalcIndep

/-! P1b (relay 7): the model σ-algebras `F_c ⊔ G_T'` sit inside the a.e. closure of the
past-of-`B~`/all-of-`B` σ-algebra of the library Brownian motion `W M`; hence the `B~`
increments after `c` are independent of `F_c ⊔ G_T'`. -/

namespace StochCalcHs

open HedgePSNV EthierKurtz StochCalcBr StochCalcIndep ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcHs

/-! P2 for D2 (relay 8): Gaussian facts for a centred Gaussian `ξ ~ N(0, v)`:
exponential moments, the tilt `L c = exp(c ξ - v c²/2)` (mean one, in L²), and the
derivative-at-zero limit `E[ξ Y] = 0` from `E[(L c - 1) Y] = 0` for small `c ≠ 0` (DCT). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcGauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : Ω → ℝ} {v : ℝ≥0}


















end StochCalcGauss

/-! P3 generic part (relay 8): change of measure by a positive mean-one L² density `D`,
set integrals / integrability under `Q = P.withDensity (ofReal ∘ D)`, the martingale property
under `Q` from set-integral identities under `P`, and the one-step tilt identity
`∫_A E R X_v = ∫_A E R X_s` (E `𝓕`-measurable, R independent of `𝓗 ⊇ 𝓕`, mean one). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace StochCalcTilt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]












end StochCalcTilt
/-! P3 model part (relay 8): the exponential `B~`-increment tilts
`Q_c = P.withDensity (exp(c (B~_{t'} - B~_t) - c²(t'-t)/2))` belong to `M_X` whenever `X` is an
L² `P`-martingale on `[0, T]` (degenerate case). -/

namespace StochCalcTiltM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



















end StochCalcTiltM
/-! P4 (relay 8): every admissible gains process is orthogonal to the future `B~` increments:
`E[Y ξ χ_T] = 0` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y` (degenerate case,
`X` an L² `P`-martingale), via the tilts `Q_c ∈ M_X` and `d/dc|₀`. -/

namespace StochCalcOrth

open HedgePSNV EthierKurtz StochCalcBr StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcOrth

/-! P5 for D2 (relay 9): Gaussian integration by parts (Stein) for the hinge
`x ↦ max (k - s x) 0`, and its independent-conditioning form
`E[ξ (k0 - a (R - (U + s ξ))^+) Y] = a s v E[Y 1{U + s ξ ≤ R}]` for `ξ ~ N(0, v)` independent of `(U, Y)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcStein








end StochCalcStein
/-! P5 model part (relay 9): Stein identity for the production payoff against a `B~` increment:
`E[ξ H Y] = (P - s) σ~ (t' - t) E[Y 1{A_T ≤ R}]` for `ξ = B~_{t'} - B~_t` and bounded `F_t`-measurable `Y`
(no degeneracy needed: `ξ` is independent of `F_t ⊔ G_T ⊔ σ(B~_T - B~_{t'})`). -/

namespace StochCalcSteinM

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcTiltM StochCalcStein

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcSteinM

/-! P6 generic pieces (relay 9): (A) a variance lower bound from a test variable `D` with
`E D = 0` and `E[D U] = E[D²]`; (B) left Riemann sums of a monotone function on a uniform grid. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6




/-! P6 generic (relay 10): martingale-difference sums `S n = Σ_{k<n} Y k * ξ k` with `ξ k`
independent of `m k`, centred, in `L²`, `m (k+1)`-measurable, and `Y k` bounded `m k`-measurable:
`E S = 0`, `S ∈ L²`, `E S² = Σ E[Y k²] E[ξ k²]`. Plus Gaussian moments. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochCalcP6S

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]




variable (m : ℕ → MeasurableSpace Ω) (ξ Y : ℕ → Ω → ℝ)



end StochCalcP6S

/-! Degenerate case `Z_T = 1` a.s. of Theorem 1(ii) (child `HedgePSNV.theorem_1_ii_degenerate` of
proposition_5 cc6d45ce): reduction of the child to three stochastic obligations
  (D1) `X` is a `P`-martingale on `[0,T]`,
  (D2) lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
  (D3) approximate attainment `∃ (θ,χ) ∈ A_X, Var[H + χ_T] ≤ Psi + ε`,
plus the elementary degenerate facts (`P^M = P`, `Z_t = Z^M_t = 1` a.s., `E χ_T = 0`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedgeDeg

open HedgePSNV

variable {p : Params} {Ω : Type*} [MeasurableSpace Ω]











end StochCalcHedgeDeg

/-! D2 (relay 10): the degenerate lower bound `Psi ≤ Var[H + χ_T]` for every admissible strategy,
via the test variables `D_n = Σ_k σ~(P-s) c_{t_k} ξ_k` (P4 orthogonality, P5 Stein, P6 Riemann sums). -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg StochCalcGauss

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




















end StochCalcD2

/-! D2 limit (relay 10): Riemann sums of the monotone `u ↦ E[δ_u²]` and `Psi_deg`. -/

namespace StochCalcD2

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcHedgeDeg

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcD2
/-! D3 reduction (relay 11): approximate attainment `Var[H + χ_T] ≤ Psi + ε` from ONE
L²-density statement (`hdens` of `StochCalcD3.D3_of_density`): for every `η > 0` some
admissible `χ`, constant `c` and simple `dB̃`-sum `K = Σ Z_k ξ_k` on a uniform grid have
`E[(H + χ_T − c − K)²] ≤ η`.  Proof: `D = Σ σ̃(P−s) Yc_{t_k} ξ_k` is the projection of
`U = H + χ_T − c` onto the simple `dB̃`-sums of the grid (Stein + polarized isometry), so
`E U² ≤ E D² + E (U − K)²`, and `E D²` is a left Riemann sum of the monotone `u ↦ E δ_u²`. -/

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
/-! D3 split (relay 11): `hdens` of `D3_of_density` from
  (R)  representation density: `H ≈ c + Σ Y_k ΔB_k + Σ Z_k ΔB̃_k` in L² on a uniform grid;
  (XS) hedging of a simple `dB`-sum by an admissible strategy: `χ_T ≈ −Σ Y_k ΔB_k` in L².
Grid refinement `n → n*m` is exact (telescoping). -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace StochCalcD3

open HedgePSNV StochCalcBr StochCalcTiltM StochCalcSteinM StochCalcOrth StochCalcHedgeDeg
  StochCalcGauss StochCalcD2

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcD3

/-! R1 generic (relay 13): telescoping-product approximation of `exp (i Σ x_k)` by a constant
plus an adapted "stochastic sum" `Σ A_k (i x_k)`, for a discrete filtration `m` and increments
`x k` that are `m (k+1)`-measurable, independent of `m k`, centred, with `E x_k⁴ ≤ D`.
Error in `L²`: `≤ 16 n D`.  Mathlib only. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace StochCalcR1



variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]









end StochCalcR1

/-! R1 model (relay 13): `exp (i Σ_k (λ_k ΔB_k + μ_k ΔB~_k))` on a uniform grid is `L²`-close to a
constant plus an adapted fine-grid sum `Σ_l A_l · i (a_l ΔB_l + b_l ΔB~_l)`.  Needs the joint
independence of `(ΔB, ΔB~)` on `[u, w]` from `F_u` (new: `indep_B_incr`, `indep_pair`). -/

namespace StochCalcR1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcIndep ItoLib StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcD2 StochCalcD3 StochCalcGauss StochCalcP6S Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






















end StochCalcR1M

/-! R4 (relay 13): the class `IsGS` of grid sums `c + Σ Y_k ΔB_k + Σ Z_k ΔB~_k` (bounded adapted
coefficients on a uniform grid) is a vector space of `F_T`-measurable `L²` functions. -/

namespace StochCalcR4

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcGauss Finset

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







end StochCalcR4

/-! R2a (relay 12): characteristic-function identification.  If an integrable `V` is orthogonal to
`cos ⟪Δ, t⟫` and `sin ⟪Δ, t⟫` for every `t`, then `∫_A V = 0` for every `A ∈ σ(Δ)`.
Mathlib only. -/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal

namespace StochCalcR2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [mE : MeasurableSpace E] [BorelSpace E]



end StochCalcR2

/-! R2b (relay 12): π-λ extension of vanishing set integrals from an increasing sequence of
σ-algebras to their supremum joined with the `P`-null sets, and the a.e.-limit criterion that
puts a variable's σ-algebra below it.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace StochCalcR2








end StochCalcR2

/-! R2c (relay 12): the generic identification theorem. -/

namespace StochCalcR2

open MeasureTheory


end StochCalcR2

/-! R3 (relay 12): Hilbert-space glue.  A subspace (given as a predicate on functions) of `L²`
whose orthogonal complement is trivial is `L²`-dense.  Mathlib only. -/

open MeasureTheory Filter
open scoped ENNReal

namespace StochCalcR3


end StochCalcR3

/-! R6 generic (relay 13): orthogonality passes to `L²`-limits.  Mathlib only. -/

set_option autoImplicit false

open MeasureTheory

namespace StochCalcR6



end StochCalcR6

/-! R5 (relay 14): the grid-`2^j` increment vectors `Δ_j` of `(B, B~)`, the monotonicity of
their σ-algebras, `F_T ≤ aug (⨆ σ(Δ_j))`, and `⟪Δ_j, t⟫` as a grid sum. -/

namespace StochCalcR5

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR2 Finset Filter
open scoped Topology



variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





















end StochCalcR5

/-! R7 (relay 14): trigonometric functions of `Δ_j` are `L²`-limits of grid sums; hence the
grid sums are dense in `L²(F_T)` (hsep + R3), which is the hypothesis `hR` of `dens_of_rep`. -/

namespace StochCalcR7

open HedgePSNV StochCalcTiltM StochCalcD2 StochCalcD3 StochCalcR4 StochCalcR5 StochCalcR1M
  Finset Filter




variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcR7

/-! TC (relay 15 of cc6d45ce): truncation consistency of the Ito integral at an ARBITRARY time
`r ≤ t`.  The clamped left-point sums of the horizon-`t` dyadic grid, masked to the cells that
start before `r`, converge in probability to `J r`, given that `J` is continuous in probability
along the dyadic floors `r_n ↑ r`.  Three-term argument: dyadic floor `r_n` (ItoLib M7a
`partialSum_tendsto_of_hasBrownianItoIntegral`), the cells in `[r_n, r)` (Lenglart bound
`itoStepSum_local_chebyshev`, at most `2^m` cells of length `t/2^(n+m)`), and `J r_n → J r`.
Use: hXS step S1 (Ito integral of a simple-in-time strategy times `Xσ`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped NNReal ENNReal Topology BigOperators

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
















/-! S1b preparation (relay 15): one cell for every coefficient family; `thetaS` bounds. -/





end StochCalcTC

/-! TC2 (relay 16 of cc6d45ce): S1b, the integrated-squared-error clause for the
`thetaS · clamp_N H` approximants. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcTC

/-! TC3 (relay 16 of cc6d45ce): S1 assembly.  The Ito integral of the simple-in-time weight
`thetaS s θ n'` times a continuous adapted `H` is `Σ_i θ_i (J(s_{i+1} ∧ t) − J(s_i ∧ t))`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! TC4 (relay 16 of cc6d45ce): variant of S1c needing `J`-continuity only at the jump times;
dyadic floors converge; clause 1 of the Ito relation for `thetaS · H`. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}





end StochCalcTC

/-! Mart (relay 16 of cc6d45ce): simple stochastic integrals of a martingale are martingales.
`θ (X(b ∧ t) − X(a ∧ t))` with `θ` bounded `F a`-measurable is an `IsMartingaleOn` martingale;
finite sums too.  Generic (any filtration, any finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcMart

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcMart

/-! S1M (relay 16 of cc6d45ce): in the degenerate model, a simple-in-time strategy
`thetaS s θ n'` (jump times `s_i ≤ T`, `θ_i` bounded `F(s_i)`-measurable) with gains
`chiS = Σ θ_i (X(s_{i+1} ∧ t) − X(s_i ∧ t))` is admissible: `(thetaS, chiS) ∈ A_X`. -/

namespace StochCalcS1M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1M

/-! TCR (8c066573 relay 15, O2 core): truncation consistency at a RANDOM cutoff `ρ ≤ t` that is a
stopping time of the completed Brownian past.  Same three-term argument as `truncSum_tendsto`,
with the dyadic CEILING `ρ^n = dyTime t n ⌈ρ/t·2^n⌉` (a stopping time, finitely many values):
masked sums up to `ρ^n` are finitely many deterministic truncations (`trunc_dy_tendsto`), the
cells in `[ρ, ρ^n)` are adapted (Lenglart), and `J (ρ^n) → J ρ` is a hypothesis. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}











end StochCalcTC

/-! S1b with RANDOM jump times `s ω` (8c066573 relay 15): the argument is pathwise. -/

namespace StochCalcTC

open ItoLib

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}



end StochCalcTC

/-! S1RM (8c066573 relay 15, O2b): the Ito relation for a STOPPED simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}` in the model, with `K_t = Y (J(s'∧τ∧t) − J(s∧τ∧t))`.
Append after probe/cc6d45ce_S1M.lean + lib/stochcalc/TCR_tail.lean + lib/stochcalc/S1bR_tail.lean.
Hypothesis `hJc` (J along dyadic ceilings of a random time) is discharged separately (needs s' < T). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcS1R
/-! S1RJ (8c066573 relay 16, O2c): discharge `hJc` of `S1R_model` for random times bounded by
`s' < T`, giving `S1R_modelT` (no `hJc` hypothesis).
Append after probe/8c066573_S1R.lean (= cc6d45ce_S1M + TCR_tail + S1bR_tail + S1RM_tail). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcS1R

/-! OS (8c066573 relay 14): continuous-time optional stopping for `IsMartingaleOn`.
A continuous martingale on `[0,T]` stopped at a stopping time is again a martingale on `[0,T]`.
Proof: grid stopping times `jn` on `s + k (t-s)/(N+1)` (Mathlib discrete optional sampling gives
`X(grid ceiling of ρ) = E[X t | F_ρN]`), uniform integrability of conditional expectations,
pointwise convergence by path continuity, Vitali.  Generic (any filtration, finite measure). -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcOS

open HedgePSNV

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]



























end StochCalcOS

/-! Hit (8c066573 relay 16, O2a): the hitting time of the closed set `{R ≤ |x|}` by a process
with continuous paths, capped at `T`, is a stopping time of any filtration to which the
process is adapted (no right-continuity of the filtration needed: closed set + continuous paths).
Also: the stopped process is bounded by `R` when it starts inside. Mathlib only. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace StochCalcHit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcHit
/-! S1RA (8c066573 relay 16, O2d): the stopped simple strategy
`θ = Y 1{s∧τ ≤ u < s'∧τ}`, `χ_t = Y (X_{s'∧τ∧t} − X_{s∧τ∧t})` is admissible (`∈ M.AX`) when
`s ≤ s' < T`, `τ` is a stopping time and the stopped price is bounded (e.g. `τ = hitR`).
Append after probe/8c066573_S1RJ.lean + the body of lib/stochcalc/Hit.lean (no import line). -/

namespace StochCalcS1R

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC StochCalcMart
  StochCalcS1M ItoLib StochCalcOS StochCalcHit

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcS1R

/-! RieszIso (8c066573 relay 16, O3 core): if a linear map `T : S → F` into a Hilbert space is
isometric for a seminorm given by a linear map `e : S → E` into another Hilbert space
(`‖T s‖ = ‖e s‖`), then every `f ∈ F` has a "representing integrand" `a ∈ E` with
`⟪f, T s⟫ = ⟪a, e s⟫` for all `s`.  (Use: `S` = simple adapted processes, `e` = their class in
`L²(dt ⊗ dP)`, `T` = the elementary stochastic integral into `L²(P)`.)  Mathlib only; no quotient
by null processes is needed. -/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace StochCalcRiesz

variable {S E F : Type*} [AddCommGroup S] [Module ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]




end StochCalcRiesz

/-! O3gen (8c066573 relay 17, O3 instantiation, generic; append after RieszIso.lean, Mathlib only).
For a real process `W` with independent centred increments of variance `v - u` w.r.t. a monotone family
`m t` of σ-algebras, every `f ∈ L²(P)` has a representing integrand `a ∈ L²(dt|[0,T] ⊗ P)` (in the closure of
the adapted simple processes) with `E[f · Y (W_v - W_u)] = ∫∫ a · 1_[u,v) Y` for all bounded `m u`-measurable `Y`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}
































end StochCalcO3

/-! O3M (8c066573 relay 17, O3 model instantiation): `B` and `B~` satisfy `StochCalcO3.IncrHyp` w.r.t. `M.F`,
so every `f ∈ L²(P)` has representing integrands `a, b ∈ L²(dt|[0,T) ⊗ P)` (in the closure of adapted simple processes):
`E[f Y (B_v - B_u)] = ∫∫ a 1_[u,v) Y` and `E[f Y (B~_v - B~_u)] = ∫∫ b 1_[u,v) Y`.
Append after probe/8c066573_S1RA.lean + RieszIso.lean body + O3gen_tail.lean (no import lines). -/

namespace StochCalcO3M

open HedgePSNV StochCalcBr StochCalcO3 StochCalcD3 StochCalcR1M StochCalcTiltM StochCalcSteinM
  StochCalcGauss StochCalcP6S

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcO3M

/-! O4gen (8c066573 relay 17, O4 generic part; append after O3gen_tail.lean, Mathlib only).
If elementary combinations `s n` have time-space classes `eL (s n) → ψ` in `L²(μT)` and elementary integrals
`TL (s n) → J` in measure, then `J` has an `L²` version `K` with `‖K‖ = ‖ψ‖` (isometry) and `⟪f, K⟫ = ⟪a, ψ⟫`
for the representing integrand `a` of `f` (O3).  Plus pointwise formulas `coe_TL` / `coe_eL` for combinations. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

/-! O4step (8c066573 relay 18, O4 generic step-approximation part).  Append after O4gen_tail.lean.
Needs `Definitions.Def_EthierKurtz_itoStepValue`, `Definitions.Def_EthierKurtz_itoStepSum` and
`Solutions.Sol_pv_1558a108` (ItoLib) imported.
`O4fun`: function form of O4gen.  `O4step`: given EK approximants `a0` of a BOUNDED jointly measurable
integrand `H` (integrated squared error → 0 in probability, step sums → `J` in probability) and the ItoLib
"zero lemma" for step sums, the approximants clamped at the bound of `H` are elementary combinations whose
time-space classes converge to `H` in `L²(μT)` and whose integrals still converge to `J`; hence
`∫ f J dP = ∫ a H dμT` for the representing integrand `a` of `f` (O3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



/-! Clamping and step values. -/








/-! The clamped approximants as elementary combinations. -/











end StochCalcO3

/-! O4 model (8c066573 relay 18; append after O4step_tail.lean in the model dev file).
The doubly stopped simple strategy `θ = Y 1{s∧τ ≤ u < s'∧τ}`, `τ = hitR X R ∧ hitR σ R'`, is admissible
(`dblSimple_mem_AX`) and its Itô integrand `θ X σ` is bounded by `C R R'`, so `O4step` gives
`E[f · Y (J_{s'∧τ} - J_{s∧τ})] = ∫ a θ X σ dμT` for the representing integrand `a` of `f` (O3, dB part). -/

namespace StochCalcO4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]











end StochCalcO4M
/-! O5 drift identity (8c066573 relay 19; append after O4M_tail.lean in the model dev file).
Triple stop `τ = hitR X R ∧ hitR σ R' ∧ hitR μ R''` bounds both integrands `θ X σ` and `θ X μ`.
KEY (relay 19): no conditional expectation `f_u` is needed for the drift: Fubini alone gives
`E[f ∫_0^T θ X μ du] = ∫ (θ X μ)(u,ω) f(ω) dμT`.  With O4 and `f ⊥ χ_T`:
`O5_gain : ∫ a θ X σ dμT + ∫ θ X μ f dμT = 0` for every triple-stopped simple strategy. -/

namespace StochCalcO5

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO5
/-! O6a (8c066573 relay 19): Pred-membership of bounded step-approximable integrands.
Append after O56_tail.lean.  `pred_approx` = the L²(μT) half of O4step (no stochastic integral):
any bounded jointly measurable `H` whose dyadic step approximants `a0` (adapted, NOT necessarily
bounded) have integrated squared error → 0 in probability is an `L²(μT)` limit of elementary
combinations; `pred_mem` states it as membership of the class of `H` in the closure of `range eL`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}



end StochCalcO3

/-! O6b (8c066573 relay 20): left-point sampling.  Append after O6a_tail.lean.
`pred_left`: a bounded, jointly measurable, adapted process that is left-continuous in time at
a.e. `u ∈ (0,T]` (for every `ω`) has its class in the closure of `range eL` (dyadic left-point
approximants `a0 n k = H (k T / 2^n)`, dominated convergence, a.e. ⇒ in measure). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}




end StochCalcO3

/-! O6c (8c066573 relay 20): generic Hilbert pieces of O6.  Append after O6b_tail.lean.
`O6_core`: an `L²(μT)` function in the closure of `range eL` orthogonal to every elementary
`efun` vanishes a.e.;  `perp_all`: orthogonality to elementaries with `v < T` suffices;
`proj_fun`: predictable projection `c` of any `F ∈ L²(μT)` (`∫ c ψ = ∫ F ψ` for predictable `ψ`);
`pred_mul`: predictable × bounded adapted a.e.-left-continuous is predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}

















end StochCalcO3

/-! O6M (8c066573 relay 20): model instance of O6.  Append after O6c_tail.lean in the model dev
file (O6a.lean + O6b_tail + O6c_tail).  With `a' = proj a`, `c = proj (f ∘ snd)` (predictable
projections), every triple stop `τ_N` gives `w_N = a' (Xσ 1[·<τ_N]) + c (Xμ 1[·<τ_N]) ⊥ elementaries`
(O5_gain + proj_fun) and `w_N` predictable (pred_mul), so `w_N = 0` (O6_core); `τ_N = T`
eventually (continuous paths are bounded on `[0,T]`), hence `a' Xσ + c Xμ = 0` μT-a.e. -/

namespace StochCalcO6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open StochCalcO5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcO6M



/-! O7.1 [U1] energy uniqueness, bounded-coefficient core.  Restriction `resF s` of elementary
combinations to `[0,s)`, its orthogonality to `m s`, and the restricted-norm bound
`‖E[θ | m s]‖ ≤ ‖a 1_{[0,s)}‖` for a stochastic integral `θ` with integrand `a`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}











end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.1 localization, part L0.  `Rep θ b` : `θ` is the stochastic integral of the predictable
integrand `b` (isometric extension of `TL`).  Basic calculus of `Rep` (distance identity, limits,
existence, uniqueness, orthogonality to `L²(m s)` when `b` vanishes before `s`) and the locality
lemma `L0`: for `A ∈ m t` and `b` vanishing before `t`, `Rep θ b → Rep (1_A θ) (1_A b)`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


























end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L1: grid stopping times.  For `τ` with finitely many values `t ∈ S` (`{τ = t} ∈ m t`) and
`δ = I(1_{τ ≤ r} a)`, `δ ⊥ ξ 1_{u < τ}` for bounded `m u`-measurable `ξ`. -/












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-! L2: general stopping times `τ ≤ T`, by the dyadic ceilings `gc T n τ ↓ τ`. -/


















end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! (B1) cutting a predictable integrand at a stopping time keeps it predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcO3
-- O7B2 tail (8c066573 relay 24): append after probe/8c066573_B.lean (= L0.lean + O7B_tail).

/-! (B2) the cut-off integral `δ = I(1_{τ ≤ r} a)` is orthogonal to `1_{r<τ} ψ`, and
(B3) the projections of `θ` and of `θ - δ` agree before `τ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}






end StochCalcO3

/-! O7.1 (U1, general): energy uniqueness for `a = -η c` with `η` continuous adapted. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! O7.2 (8c066573 relay 25): K-projection.  Two filtrations `mK ≤ mF` for which the same process
`W` satisfies `IncrHyp`, plus the conditional-independence hypothesis
`H1 : E[Y | mK T] = E[Y | mK u]` for bounded `mF u`-measurable `Y` (`u ≤ T`).  If `θ = I_F(a)`
then `φ = E[θ | mK T]` is a K-stochastic integral `I_K(b)`, where `b` is the orthogonal projection
of `a` onto the K-predictable subspace: `⟪b, ψ⟫ = ⟪a, ψ⟫` for every K-predictable `ψ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

/-! O7.4a (8c066573 relay 25): identification of an integrand from localized weak pairings.
If `b, c'` are predictable and `⟪b, 1_{r<τ_R} e⟫ = -⟪c', η 1_{r<τ_R} e⟫` for every elementary `e`
and every hitting level `R ∈ ℕ` of the continuous adapted `η`, then `b = -η c'` a.e.  (This turns the
K-projection `Kproj` of `a = -η c` into the hypothesis `hac` of `U1` without assuming `η` bounded.) -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}






end StochCalcO3

/-! O7.4b (8c066573 relay 25): `Kshift`.  If `θ = I_F(a)` with `a = -η c`, `c` the F-projection of
`θ`, and `η` continuous and K-adapted, then `φ = E[θ | mK T]` satisfies `φ = I_K(b)` with
`b = -η c_φ`, `c_φ` the K-projection of `φ` (the hypothesis shape of `U1` in the filtration K). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! O7.4c (8c066573 relay 25): `U1_diff` -- two integrals `θ₁ = I(-η c₁)`, `θ₂ = I(-η c₂)` (each `cᵢ`
the predictable projection of `θᵢ`, integrands vanishing before `v`) coincide.  O7.4 applies it in
the filtration K to `θ₁ = E[f | K_T] - f_t` (from `Kshift`) and `θ₂ = f_t (Z_T / Z_t - 1)` (from O7.3). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7.3 generic part (Z1): `Rep` is closed under `L²` limits of integrands (`rep_of_tendsto`),
and the truncation limit `rep_trunc`: integrands `1_{S n} f` (`S n` increasing, covering a.e.)
with `Rep θ_n (1_{S n} f)` and `‖θ_n‖ ≤ C` force `f ∈ L²(μT)` and `Rep θ f` for the `L²`
limit `θ` of `θ_n`.  Used for `Z_T - 1 = I(-Z η)` from the stopped identities. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z6 (8c066573 relay 27, O7.3): L² optional-sampling bound for a right-continuous martingale
closed by `Z T`: `‖Z_{τ∧T}‖₂ ≤ ‖Z_T‖₂` for every stopping time `τ`.  Finite-valued case by
conditional Jensen on `{σ = t} ∈ m t` (`eLpNorm_condExp_le_eLpNorm`), general case by the
dyadic ceilings `gc T n τ ↓ τ ∧ T` and Fatou. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}









end StochCalcO3

/-! Z4 (8c066573 relay 27, O7.3): Rep form of an EK Ito integral of a bounded integrand
(copy of O4step's approximation argument ending in `rep_exists`/`rep_conv`). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology EthierKurtz ItoLib
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3

/-! Z4t (8c066573 relay 27, O7.3): transfer of `Rep` from a larger filtration `m'` (e.g. the completed
Brownian past) to a smaller one `m ≤ m'` (e.g. `M.F`) when every `m' t`-measurable variable has an
a.e.-equal `m t`-measurable version: the elementary integrals and time-space classes agree. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

/-! Z5 (8c066573 relay 28, O7.3): stopped identification.  If `Rep θ a` and `K t =ᵐ E[θ | m t]`
(t ≤ T) with right-continuous paths, then for a stopping time `τ ≤ T` the variable `K_τ` is the
integral of `1_{s<τ} a`.  Route: (rep_aesm) integrals of integrands vanishing after `s` are
`m s`-measurable; (rep_ce) `E[θ|m t]` integrates `1_{s<t} a`; (Z5fin) finite-valued `τ` via `L0`;
(Z5) grid `gc T n τ ↓ τ`, `L²` limit + a.e. subsequence + right-continuity. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}








end StochCalcO3

/-! Z4m-a (8c066573 relay 28, O7.3): completed-Brownian-past measurable variables have
`M.F t`-measurable a.e. versions (append after Br.lean; needs `import Solutions.Sol_pv_1558a108`
for `ItoLib.aeClosure` / `completedBrownianPast_const_le`). -/

namespace StochCalcZ4m

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib StochCalcBr
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

section Gen
variable {Ω' : Type*}



end Gen






end StochCalcZ4m

/-! Z4m-b (8c066573 relay 29, O7.3): a bounded library Ito integral (filtration `cBP`, driver
`W · · 0`) of the HedgePSNV model is represented (`Rep`, filtration `M.F`, driver `M.B`) by its
integrand.  `M.F`-measurable a.e. versions of the library approximants (hmod_cBP), clamped to keep
the per-level bounds, then `StochCalcO3.O4rep`. Append after the combined dev base (O6M + generic
Z chain + O7Z4m_tail). -/

namespace StochCalcZ4mb

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ4mb


/-! Z2 (8c066573 relay 29, O7.3): a continuous, `cBP`-adapted version `Ic` of the Ito integral of
`η' s = η (s ∧ T)`, glued from the continuous Ito integrals of the clamped integrands `clamp n η'`
(platform theorem 1c98c8e0, conjunct 3, as the hypothesis `ContHyp M`).  Gluing index: the least
`n` with `sup |η'| ≤ n` (whole horizon) for the paths, and the least `n` with `sup_{[0,t]} |η'| ≤ n`
for the `cBP t`-measurable version at time `t` (completeness of `cBP t`).  Append after
O7Z4mb_tail. -/

namespace StochCalcZ2

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcZ2



/-! Z3 (8c066573 relay 29, O7.3): Ito formula for `Zc = exp(-Ic - ½∫η'²)`: for a continuous,
`cBP`-adapted Ito integral `Ic` of `η'` (Z2), `Zc t = 1 + K t` a.s. for each `t`, where `K` is the
Ito integral of `-Zc η'` (ItoLib `ito_formula` with `e = 1`, `X = Ic + ½∫η'²`, `f x = exp(-x₀)`).
Append after O7Z2_tail. -/

namespace StochCalcZ3

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2
open scoped NNReal ENNReal

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end line

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]












end StochCalcZ3

/-! Z7a (8c066573 relay 30, O7.3): horizon change for `Rep` (an integrand on `[0,t)` represents
the same variable at any later horizon `T`), hence the conditional expectation of a represented
variable at time `t` is represented at horizon `t`; model corollary `Jmart`: a bounded library Ito
integral is an `M.F`-martingale.  Append after O7Z3_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}













end StochCalcO3

namespace StochCalcZ7a

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcO3 StochCalcO3M StochCalcZ4m StochCalcZ4mb
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcZ7a

/-! Z7b/Z7c (8c066573 relay 30, O7.3): `Zc` is continuous, `M.F`-adapted, a.e. equal to `M.Z`
on `[0,T]` and an `M.F`-martingale closed by `Zc T` (Assumption5); stopping at the hitting time
`τ R` of `|Zc η'| ≥ R`, the library Ito integral `J` of the clamped integrand `Hcl R` equals
`Zc - 1` at `τ R` (locality at dyadic `t < τ R` + path continuity).  Append after O7Z7a_tail. -/

namespace StochCalcZ7b

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcHit
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






variable {Ic : ℝ≥0 → Ω → ℝ}
















end StochCalcZ7b

/-! Z7d (8c066573 relay 30, O7.3 assembly): `Zc T - 1` is represented (`Rep`, filtration `M.F`,
driver `M.B`) by the integrand `-Zc η'` on `[0,T)`, which is in `L²(dt × dP)`.  Per level `n`:
ContHyp integral `J n` of `Hcl n`, Z4m representative, Jmart (Z5's martingale hypothesis), Z5 at
`tau n`, locality `loc`, Z6 bound; then rep_trunc over `S n = {s < tau n}` and the a.e. limit
(`tau n = T` eventually).  Append after O7Z7b_tail. -/

namespace StochCalcZ7d

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcZ7d


/-! O7ZM (8c066573 relay 31, O7.3 remainder): multiplication of a stochastic integral by a
bounded `m t`-measurable factor `ζ` (generalizes `L0`, where `ζ = 1_A`), and the tail
representation `θ - E[θ | m t] = I(a 1_[t,T))`.  Generic `StochCalcO3`; append after O7Z7d. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}












end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω}








end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


end StochCalcO3

/-! O7ZK (8c066573 relay 32, O7.3 model instance in a sub-filtration `mK`): generic
`rep_restrict` (an `mF`-representation of an `mK T`-measurable `θ` by an `mK`-predictable integrand
is an `mK`-representation), `mart_restrict` (tower property), and the model instance `zK` of `ztail`
for `ZT = Zc (· ∧ T)` in any filtration `cBP ≤ mK ≤ M.F` with `IncrHyp mK M.B` and `H1`.
Generic `StochCalcO3` part + `StochCalcZK`; append after O7ZM_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}




end StochCalcO3

namespace StochCalcZK

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcZK

/-! O7KF (8c066573 relay 32, model K + H1 for O7.4): the filtration
`Kf t s = F_s (s < t), F_t ⊔ G_s (s ≥ t)`, with `Kf ≤ F`, `IncrHyp (Kf t) M.B`, `Zc` and `η`
`Kf`-adapted on `[0,T]`, and the conditional-independence hypothesis `H1` of `Kproj`/`Kshift`.
Generic part: `ce_sup_indep` (`E[Y | A ⊔ D] = E[Y | A]` for `Y ∈ F' ⊇ A`, `F' ⊥ D`) and
`meas_of_ae_eq_nulls`.  Append after O7ZK_tail. -/

namespace StochCalcCE

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} {A F' D K : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]




end StochCalcCE

namespace StochCalcKF

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcKF

/-! O7Q1 (8c066573 relay 32, O7.4 generic core): if `θ = I_F(a)` with `a = -η c` (`c` the
F-projection of `θ`, `η` continuous `mK`-adapted) and `Θ = E[θ | mK T]` is orthogonal to `L∞(mK t)`,
then `Θ = 0`.  Kshift (Θ = I_K(-η cΘ)), perp_tail (cΘ = 0 before t), U1.  Append after O7KF_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}


end StochCalcO3

/-! O7Q1M (8c066573 relay 33, O7.4 model): `E[θ | F_t ⊔ G_T] = E[θ|F_t] Z_T / Z_t` for `θ = I_F(-η c)`.
Generic: `int_mul_ce`, `proj_tailA` (F-projection of `1_A (θ - f_t)`).  Model: `Q1R` (fixed `R`), `Q1model`.
Append after O7Q1_tail. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


variable {m : ℝ≥0 → MeasurableSpace Ω}


end StochCalcO3

namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology


set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StochCalcHedge

open HedgePSNV

lemma I_zero_ae {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) : M.I 0 =ᵐ[M.P] fun _ => (0 : ℝ) := by
  obtain ⟨a, -, -, -, hlim⟩ := hM.I_ito.2 0
  have hsum : ∀ n, EthierKurtz.itoStepSum M.B 0 n (a n) = fun _ => (0 : ℝ) := by
    intro n
    funext ω
    unfold EthierKurtz.itoStepSum
    simp
  have h0 : TendstoInMeasure M.P (fun n => EthierKurtz.itoStepSum M.B 0 n (a n)) Filter.atTop
      (fun _ => (0 : ℝ)) := by
    intro ε hε
    simp [hsum, not_le.mpr hε]
  exact tendstoInMeasure_ae_unique hlim h0

/-- `E[Z_T] = 1` (Assumption 5 martingale property and `Z_0 = 1` a.s.). -/
lemma integral_Z_T {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) : ∫ ω, M.Z p.T ω ∂M.P = 1 := by
  have := hM.prob
  have hZ0 : M.Z 0 =ᵐ[M.P] fun _ => (1 : ℝ) := by
    filter_upwards [I_zero_ae M hM] with ω hω
    simp [Model.Z, hω]
  have hce := h5.1.2.2 0 p.T zero_le le_rfl
  rw [← integral_condExp (M.F.le 0)]
  rw [integral_congr_ae (hce.trans hZ0)]
  simp

lemma Z_pos {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) (t : ℝ≥0) (ω : Ω) :
    0 < M.Z t ω := Real.exp_pos _

lemma Z_T_measurable {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) : Measurable (M.Z p.T) :=
  ((h5.1.1 p.T le_rfl).mono (M.F.le p.T)).measurable

/-- `Z^M_0 = E^M[Z_T] = E[Z_T^2]` (Theorem 1(ii), p.15). -/
lemma ZM0_eq {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) : M.ZM0 = ∫ ω, M.Z p.T ω ^ 2 ∂M.P := by
  have hm : Measurable (fun ω => (M.Z p.T ω).toNNReal) :=
    (Z_T_measurable M h5).real_toNNReal
  unfold Model.ZM0 Model.PM
  have hden : (fun ω => ENNReal.ofReal (M.Z p.T ω)) =
      (fun ω => (((M.Z p.T ω).toNNReal : ℝ≥0) : ℝ≥0∞)) := rfl
  rw [hden, integral_withDensity_eq_integral_smul hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Z_pos M p.T ω).le]
  ring

/-- `Z^M_0 > 1` when `Z_T` is not a.s. `1` (strict Jensen). -/
lemma one_lt_ZM0 {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5)
    (hne : ¬ (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ))) : 1 < M.ZM0 := by
  have := hM.prob
  rw [ZM0_eq M h5]
  have hL2 : MemLp (M.Z p.T) 2 M.P := h5.2 p.T le_rfl
  have hint : Integrable (M.Z p.T) M.P := h5.1.2.1 p.T le_rfl
  have hsq : Integrable (fun ω => M.Z p.T ω ^ 2) M.P := hL2.integrable_sq
  have hE := integral_Z_T M hM h5
  have hvar_int : Integrable (fun ω => (M.Z p.T ω - 1) ^ 2) M.P := by
    have : (fun ω => (M.Z p.T ω - 1) ^ 2) =
        fun ω => M.Z p.T ω ^ 2 - 2 * M.Z p.T ω + 1 := by
      funext ω; ring
    rw [this]
    exact (hsq.sub (hint.const_mul 2)).add (integrable_const 1)
  have hvar : ∫ ω, (M.Z p.T ω - 1) ^ 2 ∂M.P = ∫ ω, M.Z p.T ω ^ 2 ∂M.P - 1 := by
    have : (fun ω => (M.Z p.T ω - 1) ^ 2) =
        fun ω => M.Z p.T ω ^ 2 - 2 * M.Z p.T ω + 1 := by
      funext ω; ring
    rw [this]
    have h1 : ∫ ω, (M.Z p.T ω ^ 2 - 2 * M.Z p.T ω + 1) ∂M.P =
        ∫ ω, (M.Z p.T ω ^ 2 - 2 * M.Z p.T ω) ∂M.P + ∫ _ω, (1 : ℝ) ∂M.P :=
      integral_add (hsq.sub (hint.const_mul 2)) (integrable_const 1)
    have h2 : ∫ ω, (M.Z p.T ω ^ 2 - 2 * M.Z p.T ω) ∂M.P =
        ∫ ω, M.Z p.T ω ^ 2 ∂M.P - ∫ ω, 2 * M.Z p.T ω ∂M.P :=
      integral_sub hsq (hint.const_mul 2)
    rw [h1, h2, integral_const_mul, hE]
    simp
    ring
  have hnn : 0 ≤ᵐ[M.P] fun ω => (M.Z p.T ω - 1) ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hpos : 0 < ∫ ω, (M.Z p.T ω - 1) ^ 2 ∂M.P := by
    rcases (integral_nonneg_of_ae hnn).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hne
      have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn hvar_int).1 h.symm
      filter_upwards [h0] with ω hω
      have : (M.Z p.T ω - 1) ^ 2 = 0 := hω
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      simpa using (sub_eq_zero.1 this)
  linarith

end StochCalcHedge

/-! S8 tail (8c066573 relay 1, 2026-11-06): `0 ≤ Z_t/Z^M_t ≤ 1` a.s. and the three elementary
conjuncts of theorem_1_ii (everything except the value formula (21)).
Appended after S8.lean (namespace StochCalcHedge provides I_zero_ae, Z_pos, Z_T_measurable,
ZM0_eq, one_lt_ZM0). -/

namespace StochCalcS8b

open HedgePSNV StochCalcHedge

lemma PM_prob {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) : IsProbabilityMeasure M.PM := by
  have := hM.prob
  have hint : Integrable (M.Z p.T) M.P := (h5.1.2.1 p.T le_rfl)
  constructor
  unfold Model.PM
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le), integral_Z_T M hM h5,
    ENNReal.ofReal_one]

lemma P_ac_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) : M.P ≪ M.PM := by
  exact withDensity_absolutelyContinuous' (Z_T_measurable M h5).ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun ω => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _)

/-- `∫ Z_T g dP = ∫ g dP^M` (density `Z_T`). -/
lemma integral_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) (g : Ω → ℝ) :
    ∫ ω, M.Z p.T ω * g ω ∂M.P = ∫ ω, g ω ∂M.PM := by
  have hm : Measurable (fun ω => (M.Z p.T ω).toNNReal) :=
    (Z_T_measurable M h5).real_toNNReal
  unfold Model.PM
  have hden : (fun ω => ENNReal.ofReal (M.Z p.T ω)) =
      (fun ω => (((M.Z p.T ω).toNNReal : ℝ≥0) : ℝ≥0∞)) := rfl
  rw [hden, integral_withDensity_eq_integral_smul hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Z_pos M p.T ω).le]

/-- `g` is `P^M`-integrable when `Z_T g` is `P`-integrable. -/
lemma int_PM_of {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) (g : Ω → ℝ) (hg : Integrable (fun ω => M.Z p.T ω * g ω) M.P) :
    Integrable g M.PM := by
  have hm : Measurable (fun ω => (M.Z p.T ω).toNNReal) :=
    (Z_T_measurable M h5).real_toNNReal
  unfold Model.PM
  have hden : (fun ω => ENNReal.ofReal (M.Z p.T ω)) =
      (fun ω => (((M.Z p.T ω).toNNReal : ℝ≥0) : ℝ≥0∞)) := rfl
  rw [hden, integrable_withDensity_iff_integrable_smul hm]
  refine hg.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Z_pos M p.T ω).le]

/-- `Z_t ≤ Z^M_t` `P^M`-a.s. for `t ≤ T`: for `s ∈ F_t`,
`∫_s Z^M_t dP^M = ∫_s Z_T² dP ≥ ∫_s Z_t² dP = ∫_s Z_t Z_T dP = ∫_s Z_t dP^M`. -/
lemma Z_le_ZM_PM {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) (t : ℝ≥0) (ht : t ≤ p.T) :
    ∀ᵐ ω ∂M.PM, M.Z t ω ≤ M.ZM t ω := by
  have := hM.prob
  haveI := PM_prob M hM h5
  have hT2 : MemLp (M.Z p.T) 2 M.P := h5.2 p.T le_rfl
  have ht2 : MemLp (M.Z t) 2 M.P := h5.2 t ht
  have hTT : Integrable (fun ω => M.Z p.T ω * M.Z p.T ω) M.P := hT2.integrable_mul hT2
  have hTt : Integrable (fun ω => M.Z p.T ω * M.Z t ω) M.P := hT2.integrable_mul ht2
  have htt : Integrable (fun ω => M.Z t ω * M.Z t ω) M.P := ht2.integrable_mul ht2
  have hZTPM : Integrable (M.Z p.T) M.PM := int_PM_of M h5 _ hTT
  have hZtPM : Integrable (M.Z t) M.PM := int_PM_of M h5 _ hTt
  have hZMPM : Integrable (M.ZM t) M.PM := integrable_condExp
  have hmt : StronglyMeasurable[M.F t] (M.Z t) := h5.1.1 t ht
  have hmart : condExp (M.F t) M.P (M.Z p.T) =ᵐ[M.P] M.Z t := h5.1.2.2 t p.T ht le_rfl
  set f : Ω → ℝ := fun ω => M.ZM t ω - M.Z t ω with hf
  have hfm : StronglyMeasurable[M.F t] f :=
    (stronglyMeasurable_condExp (m := M.F t) (μ := M.PM) (f := M.Z p.T)).sub hmt
  have hfi : Integrable f M.PM := hZMPM.sub hZtPM
  have key : ∀ s, MeasurableSet[M.F t] s → 0 ≤ ∫ ω in s, f ω ∂M.PM := by
    intro s hs
    have hs' : MeasurableSet s := M.F.le t s hs
    -- set integrals under P^M as P-integrals
    have e1 : ∫ ω in s, M.ZM t ω ∂M.PM = ∫ ω in s, M.Z p.T ω * M.Z p.T ω ∂M.P := by
      unfold Model.ZM
      rw [setIntegral_condExp (M.F.le t) hZTPM hs, ← integral_indicator hs',
        ← integral_indicator hs', ← integral_PM M h5]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      by_cases h : ω ∈ s <;> simp [h]
    have e2 : ∫ ω in s, M.Z t ω ∂M.PM = ∫ ω in s, M.Z p.T ω * M.Z t ω ∂M.P := by
      rw [← integral_indicator hs', ← integral_indicator hs', ← integral_PM M h5]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      by_cases h : ω ∈ s <;> simp [h]
    -- pull-out: ∫_s Z_T Z_t dP = ∫_s Z_t Z_t dP
    have e3 : ∫ ω in s, M.Z p.T ω * M.Z t ω ∂M.P = ∫ ω in s, M.Z t ω * M.Z t ω ∂M.P := by
      rw [← integral_indicator hs', ← integral_indicator hs']
      have q1 : s.indicator (fun ω => M.Z p.T ω * M.Z t ω) =
          (s.indicator (M.Z t)) * (M.Z p.T) := by
        funext ω; by_cases h : ω ∈ s <;> simp [h, mul_comm]
      have q2 : s.indicator (fun ω => M.Z t ω * M.Z t ω) =
          (s.indicator (M.Z t)) * (M.Z t) := by
        funext ω; by_cases h : ω ∈ s <;> simp [h]
      have hsm : StronglyMeasurable[M.F t] (s.indicator (M.Z t)) := hmt.indicator hs
      have hint : Integrable ((s.indicator (M.Z t)) * (M.Z p.T)) M.P := by
        rw [← q1]; exact hTt.indicator hs' |>.congr (Filter.Eventually.of_forall fun ω => by
          by_cases h : ω ∈ s <;> simp [h, mul_comm])
      rw [q1, q2, ← integral_condExp (M.F.le t)]
      refine integral_congr_ae ?_
      filter_upwards [condExp_mul_of_stronglyMeasurable_left hsm hint (h5.1.2.1 p.T le_rfl),
        hmart] with ω h1 h2
      rw [h1]; simp only [Pi.mul_apply, h2]
    have hsq : 0 ≤ ∫ ω in s, (M.Z p.T ω - M.Z t ω) ^ 2 ∂M.P :=
      setIntegral_nonneg hs' (fun ω _ => sq_nonneg _)
    have hexp : ∫ ω in s, (M.Z p.T ω - M.Z t ω) ^ 2 ∂M.P =
        ∫ ω in s, M.Z p.T ω * M.Z p.T ω ∂M.P - 2 * ∫ ω in s, M.Z p.T ω * M.Z t ω ∂M.P +
          ∫ ω in s, M.Z t ω * M.Z t ω ∂M.P := by
      have i1 : Integrable (fun ω => M.Z p.T ω * M.Z p.T ω - 2 * (M.Z p.T ω * M.Z t ω))
          (M.P.restrict s) := (hTT.sub (hTt.const_mul 2)).restrict
      have a1 : ∫ ω in s, (M.Z p.T ω - M.Z t ω) ^ 2 ∂M.P =
          ∫ ω in s, ((M.Z p.T ω * M.Z p.T ω - 2 * (M.Z p.T ω * M.Z t ω)) +
            M.Z t ω * M.Z t ω) ∂M.P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        simp only; ring
      have a2 : ∫ ω in s, ((M.Z p.T ω * M.Z p.T ω - 2 * (M.Z p.T ω * M.Z t ω)) +
            M.Z t ω * M.Z t ω) ∂M.P =
          ∫ ω in s, (M.Z p.T ω * M.Z p.T ω - 2 * (M.Z p.T ω * M.Z t ω)) ∂M.P +
            ∫ ω in s, M.Z t ω * M.Z t ω ∂M.P := integral_add i1 htt.restrict
      have a3 : ∫ ω in s, (M.Z p.T ω * M.Z p.T ω - 2 * (M.Z p.T ω * M.Z t ω)) ∂M.P =
          ∫ ω in s, M.Z p.T ω * M.Z p.T ω ∂M.P - ∫ ω in s, 2 * (M.Z p.T ω * M.Z t ω) ∂M.P :=
        integral_sub hTT.restrict (hTt.const_mul 2).restrict
      rw [a1, a2, a3, integral_const_mul]
    have hsub : ∫ ω in s, f ω ∂M.PM =
        ∫ ω in s, M.ZM t ω ∂M.PM - ∫ ω in s, M.Z t ω ∂M.PM :=
      integral_sub hZMPM.restrict hZtPM.restrict
    rw [hsub, e1, e2]
    linarith
  have htr : 0 ≤ᵐ[M.PM.trim (M.F.le t)] f := by
    refine ae_nonneg_of_forall_setIntegral_nonneg (hfi.trim (M.F.le t) hfm) ?_
    intro s hs _
    rw [← setIntegral_trim (M.F.le t) hfm hs]
    exact key s hs
  filter_upwards [ae_of_ae_trim (M.F.le t) htr] with ω hω
  have : 0 ≤ M.ZM t ω - M.Z t ω := hω
  linarith

lemma Z_div_ZM_nonneg {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (h5 : M.Assumption5) (t : ℝ≥0) : ∀ᵐ ω ∂M.P, 0 ≤ M.Z t ω / M.ZM t ω := by
  have h : 0 ≤ᵐ[M.PM] M.ZM t := by
    unfold Model.ZM
    exact condExp_nonneg (Filter.Eventually.of_forall fun ω => by
      show (0 : ℝ) ≤ M.Z p.T ω
      simp only [Model.Z]; exact (Real.exp_pos _).le)
  filter_upwards [P_ac_PM M h5 h] with ω hω
  exact div_nonneg (Z_pos M t ω).le hω

lemma Z_div_ZM_le_one {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h5 : M.Assumption5) (t : ℝ≥0) (ht : t ≤ p.T) :
    ∀ᵐ ω ∂M.P, M.Z t ω / M.ZM t ω ≤ 1 := by
  filter_upwards [P_ac_PM M h5 (Z_le_ZM_PM M hM h5 t ht)] with ω hω
  rcases le_or_gt (M.ZM t ω) 0 with h0 | h0
  · exact (div_nonpos_of_nonneg_of_nonpos (Z_pos M t ω).le h0).trans zero_le_one
  · exact (div_le_one h0).2 hω


end StochCalcS8b
/-! K2a (8c066573 relay 2, 2026-11-06): base change `P → P^M` for the `B~`-tilt machinery.
`dP^M/dP = Z_T` is `G_T`-measurable, so every independence `F_u ⊔ G_T ⊥ (B~ increments after u)`
and the Gaussian laws of the increments survive under `P^M`; the exponential `B~`-tilts of `P^M`
are in `M_X` once `X` is a `P^M`-martingale (no L² assumption on `X`).
Append after cc6d45ce_P4.lean + S8.lean + S8b_tail.lean (imports stripped). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM

section generic

variable {Ω : Type*}

/-- A density measurable for `𝓖` factorizes against sets independent of `𝓖`. -/
lemma Qd_inter {𝓖 m2 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℝ} (hD : Measurable[𝓖] D) (hind : Indep 𝓖 m2 P) (h𝓖 : 𝓖 ≤ mΩ) (hm2 : m2 ≤ mΩ)
    {A B : Set Ω} (hA : MeasurableSet[𝓖] A) (hB : MeasurableSet[m2] B) :
    Qd P D (A ∩ B) = Qd P D A * P B := by
  have hA' : MeasurableSet[mΩ] A := h𝓖 _ hA
  have hB' : MeasurableSet[mΩ] B := hm2 _ hB
  rw [withDensity_apply _ (hA'.inter hB'), withDensity_apply _ hA',
    ← lintegral_indicator (hA'.inter hB'), ← lintegral_indicator hA']
  have heq : ∀ ω, (A ∩ B).indicator (fun ω => ENNReal.ofReal (D ω)) ω =
      A.indicator (fun ω => ENNReal.ofReal (D ω)) ω * B.indicator (1 : Ω → ℝ≥0∞) ω := by
    intro ω
    by_cases h1 : ω ∈ A <;> by_cases h2 : ω ∈ B <;> simp [h1, h2]
  simp_rw [heq]
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace h𝓖 hm2 hind
    ((hD.ennreal_ofReal).indicator hA) (Measurable.indicator (m := m2) (f := (1 : Ω → ℝ≥0∞)) measurable_const hB),
    lintegral_indicator_one hB']

/-- Sets of the independent σ-algebra keep their mass. -/
lemma Qd_eq {𝓖 m2 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℝ} (hD : Measurable[𝓖] D) (hind : Indep 𝓖 m2 P) (h𝓖 : 𝓖 ≤ mΩ) (hm2 : m2 ≤ mΩ)
    (h1 : Qd P D Set.univ = 1) {B : Set Ω} (hB : MeasurableSet[m2] B) :
    Qd P D B = P B := by
  have := Qd_inter (mΩ := mΩ) hD hind h𝓖 hm2 (@MeasurableSet.univ Ω 𝓖) hB
  rwa [Set.univ_inter, h1, one_mul] at this

/-- Independence survives the change of measure. -/
lemma indep_Qd {𝓖 m2 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℝ} (hD : Measurable[𝓖] D) (hind : Indep 𝓖 m2 P) (h𝓖 : 𝓖 ≤ mΩ) (hm2 : m2 ≤ mΩ)
    (h1 : Qd P D Set.univ = 1) : Indep 𝓖 m2 (Qd P D) := by
  rw [Indep_iff]
  intro A B hA hB
  rw [Qd_inter (mΩ := mΩ) hD hind h𝓖 hm2 hA hB, Qd_eq (mΩ := mΩ) hD hind h𝓖 hm2 h1 hB]

/-- One martingale step against an `𝓕`-measurable weight, assuming only integrability. -/
lemma setIntegral_mul_step' [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : MeasurableSpace Ω} (h𝓕 : 𝓕 ≤ mΩ) {E Xv Xs : Ω → ℝ}
    (hE : StronglyMeasurable[𝓕] E) (hint : Integrable (fun ω => E ω * Xv ω) P)
    (hXv : Integrable Xv P) (hmart : condExp 𝓕 P Xv =ᵐ[P] Xs) {A : Set Ω}
    (hA : MeasurableSet[𝓕] A) :
    ∫ ω in A, E ω * Xv ω ∂P = ∫ ω in A, E ω * Xs ω ∂P := by
  have hA' : MeasurableSet[mΩ] A := h𝓕 _ hA
  have hY : StronglyMeasurable[𝓕] (A.indicator E) := hE.indicator hA
  have hint' : Integrable (A.indicator E * Xv) P := by
    refine (hint.indicator hA').congr (Eventually.of_forall fun ω => ?_)
    by_cases h : ω ∈ A <;> simp [h]
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
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hY hint' hXv, hmart] with ω h1 h2
  rw [h1, Pi.mul_apply, h2, Pi.mul_apply]

end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma meas_ii (g : ℝ → Ω → ℝ)
    (hc : ∀ ω, Continuous fun u => g u ω) (hm : ∀ u, Measurable (g u)) (a b : ℝ) :
    Measurable fun ω => ∫ u in a..b, g u ω := by
  have hj : Measurable (Function.uncurry g) := measurable_uncurry_of_continuous_of_measurable hc hm
  have hj' : StronglyMeasurable (Function.uncurry fun ω u => g u ω) :=
    (hj.comp measurable_swap).stronglyMeasurable
  have h1 : StronglyMeasurable fun ω => ∫ u, g u ω ∂(volume.restrict (Set.Ioc a b)) :=
    hj'.integral_prod_right
  have h2 : StronglyMeasurable fun ω => ∫ u, g u ω ∂(volume.restrict (Set.Ioc b a)) :=
    hj'.integral_prod_right
  simp_rw [intervalIntegral]
  exact h1.measurable.sub h2.measurable

lemma ZformK (μ σ : ℝ≥0 → Ω → ℝ) (I : Ω → ℝ) (T : ℝ≥0)
    (hμc : ∀ ω, Continuous fun t => μ t ω) (hσc : ∀ ω, Continuous fun t => σ t ω)
    (hσ : ∀ t ω, 0 < σ t ω) (hμm : ∀ s, s ≤ T → Measurable (μ s))
    (hσm : ∀ s, s ≤ T → Measurable (σ s)) (hI : Measurable I) :
    Measurable fun ω => Real.exp (-(I ω) - (1 / 2) *
      ∫ u in (0 : ℝ)..(T : ℝ), (μ u.toNNReal ω / σ u.toNNReal ω) ^ 2) := by
  let k : ℝ → ℝ≥0 := fun u => min u.toNNReal T
  have hk : Continuous k := continuous_real_toNNReal.min continuous_const
  have hkT : ∀ u, k u ≤ T := fun u => min_le_right _ _
  have heq : ∀ ω, (∫ u in (0 : ℝ)..(T : ℝ), (μ u.toNNReal ω / σ u.toNNReal ω) ^ 2) =
      ∫ u in (0 : ℝ)..(T : ℝ), (μ (k u) ω / σ (k u) ω) ^ 2 := by
    intro ω
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu' : u ≤ (T : ℝ) := by
      rcases Set.mem_uIcc.1 hu with h | h
      · exact h.2
      · linarith [h.1, h.2, T.coe_nonneg]
    have : u.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hu'
    simp only [k, min_eq_left this]
  simp_rw [heq]
  refine Real.measurable_exp.comp (hI.neg.sub (measurable_const.mul ?_))
  refine meas_ii (fun u ω => (μ (k u) ω / σ (k u) ω) ^ 2) (fun ω => ?_) (fun u => ?_) 0 T
  · exact (((hμc ω).comp hk).div ((hσc ω).comp hk) fun u => (hσ _ _).ne').pow 2
  · exact ((hμm _ (hkT u)).div (hσm _ (hkT u))).pow_const 2

/-- `Z_T` is `G_T`-measurable. -/
lemma Z_measG (M : Model p Ω) (hM : M.Standing) : Measurable[M.G p.T] (M.Z p.T) :=
  @ZformK Ω (M.G p.T) M.μ M.σ (M.I p.T) p.T hM.μ_cont hM.σ_cont hM.σ_pos
    (fun s hs => ((hM.μ_adapted s).measurable.mono (M.G.mono hs) le_rfl))
    (fun s hs => ((hM.σ_adapted s).measurable.mono (M.G.mono hs) le_rfl))
    (hM.I_adapted p.T).measurable

lemma Z_measFG (M : Model p Ω) (hM : M.Standing) (u : ℝ≥0) :
    Measurable[M.F u ⊔ M.G p.T] (M.Z p.T) :=
  (Z_measG M hM).mono le_sup_right le_rfl

lemma PM_eq (M : Model p Ω) : M.PM = Qd M.P (M.Z p.T) := rfl

lemma PM_univ (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) :
    Qd M.P (M.Z p.T) Set.univ = 1 := by
  have := StochCalcS8b.PM_prob M hM h5
  rw [← PM_eq]; exact measure_univ

lemma FGle (M : Model p Ω) (u : ℝ≥0) : M.F u ⊔ M.G p.T ≤ mΩ :=
  sup_le (M.F.le u) (M.G.le p.T)

/-- The `B~`-tilt version `Lw` stays independent of `F_u ⊔ G_T` under `P^M`. -/
lemma indep_Lw_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) {u w : ℝ≥0}
    (huw : u ≤ w) (c : ℝ) :
    Indep (M.F u ⊔ M.G p.T) (MeasurableSpace.comap (Lw M u w c) inferInstance) M.PM := by
  have := hM.prob
  exact indep_Qd (mΩ := mΩ) (Z_measFG M hM u) (indep_Lw M hM huw c p.T) (FGle M u)
    (Lw_meas M hM u w c).comap_le (PM_univ M hM h5)

/-- `ξ = B~_w - B~_u` stays independent of `F_u ⊔ G_T` under `P^M`. -/
lemma indep_ξ_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) {u w : ℝ≥0}
    (huw : u ≤ w) :
    Indep (M.F u ⊔ M.G p.T) (MeasurableSpace.comap (ξ M u w) inferInstance) M.PM := by
  have := hM.prob
  exact indep_Qd (mΩ := mΩ) (Z_measFG M hM u) (indep_ξ M hM huw p.T) (FGle M u)
    (ξ_meas M hM u w).comap_le (PM_univ M hM h5)

/-- The `B~` increments keep their Gaussian law under `P^M`. -/
lemma ξ_law_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) {u w : ℝ≥0}
    (huw : u ≤ w) : HasLaw (ξ M u w) (gaussianReal 0 (V u w)) M.PM := by
  have := hM.prob
  have hm := ξ_meas M hM u w
  refine ⟨hm.aemeasurable, ?_⟩
  rw [← (ξ_law M hM u w).map_eq]
  ext S hS
  rw [Measure.map_apply hm hS, Measure.map_apply hm hS, PM_eq]
  exact Qd_eq (mΩ := mΩ) (Z_measFG M hM u) (indep_ξ M hM huw p.T) (FGle M u)
    hm.comap_le (PM_univ M hM h5) ⟨S, hS, rfl⟩

lemma PM_ac (M : Model p Ω) : M.PM ≪ M.P := withDensity_absolutelyContinuous _ _

lemma Lm_ae_PM (M : Model p Ω) (hM : M.Standing) (u w : ℝ≥0) (c : ℝ) :
    Lm M u w c =ᵐ[M.PM] Lw M u w c :=
  (PM_ac M).ae_le (Lm_ae M hM u w c)

lemma integral_Lm_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) {u w : ℝ≥0}
    (huw : u ≤ w) (c : ℝ) : ∫ ω, Lm M u w c ω ∂M.PM = 1 := by
  have := StochCalcS8b.PM_prob M hM h5
  exact integral_L (ξ_law_PM M hM h5 huw) c

lemma memLp_Lm_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) {u w : ℝ≥0}
    (huw : u ≤ w) (c : ℝ) : MemLp (Lm M u w c) 2 M.PM := by
  have := StochCalcS8b.PM_prob M hM h5
  exact memLp_L (ξ_meas M hM u w) (ξ_law_PM M hM h5 huw) c

lemma X_measFG (M : Model p Ω) (hM : M.Standing) (u : ℝ≥0) {v : ℝ≥0} (hv : v ≤ p.T) :
    Measurable[M.F u ⊔ M.G p.T] (M.X v) :=
  (X_measH M hM u hv).measurable

/-- `Lm · X_v` is `P^M`-integrable (independence under `P^M`). -/
lemma int_Lm_X (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hXM : IsMartingaleOn p.T M.F M.PM M.X) {u w : ℝ≥0} (huw : u ≤ w) (c : ℝ)
    {v : ℝ≥0} (hv : v ≤ p.T) :
    Integrable (fun ω => Lm M u w c ω * M.X v ω) M.PM := by
  have := StochCalcS8b.PM_prob M hM h5
  have hind : IndepFun (Lw M u w c) (M.X v) M.PM := by
    rw [IndepFun_iff_Indep]
    exact (indep_of_indep_of_le_left (indep_Lw_PM M hM h5 huw c)
      (X_measFG M hM u hv).comap_le).symm
  have hLw : Integrable (Lw M u w c) M.PM :=
    ((memLp_Lm_PM M hM h5 huw c).integrable one_le_two).congr (Lm_ae_PM M hM u w c)
  have h := hind.integrable_mul hLw (hXM.2.1 v hv)
  refine h.congr ?_
  filter_upwards [Lm_ae_PM M hM u w c] with ω hω
  simp [hω]

/-- The tilt identity under `P^M`. -/
theorem setIntegral_tilt_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hXM : IsMartingaleOn p.T M.F M.PM M.X)
    {t t' : ℝ≥0} (htt : t ≤ t') (c : ℝ) (s v : ℝ≥0) (hsv : s ≤ v) (hv : v ≤ p.T)
    (A : Set Ω) (hA : MeasurableSet[M.F s] A) :
    ∫ ω in A, Lm M t t' c ω * M.X v ω ∂M.PM = ∫ ω in A, Lm M t t' c ω * M.X s ω ∂M.PM := by
  have := StochCalcS8b.PM_prob M hM h5
  have hmart := hXM.2.2 s v hsv hv
  have hs : s ≤ p.T := hsv.trans hv
  rcases le_total t' s with h1 | h1
  · exact setIntegral_mul_step' (M.F.le s) (Lm_measF M hM (htt.trans h1) h1 c)
      (int_Lm_X M hM h5 hXM htt c hv) (hXM.2.1 v hv) hmart hA
  rcases le_total s t with h2 | h2
  · have e : ∀ r, r ≤ p.T → ∫ ω in A, Lm M t t' c ω * M.X r ω ∂M.PM = ∫ ω in A, M.X r ω ∂M.PM := by
      intro r hr
      have := setIntegral_indep (mΩ := mΩ) (P := M.PM) (𝓗 := M.F t ⊔ M.G p.T) (FGle M t)
        (E := fun _ => (1 : ℝ)) stronglyMeasurable_const (X_measH M hM t hr)
        (Lw_meas M hM t t' c) (Lm_ae_PM M hM t t' c) (integral_Lm_PM M hM h5 htt c)
        (indep_Lw_PM M hM h5 htt c) (A := A) (((M.F.mono h2).trans (le_sup_left : M.F t ≤ M.F t ⊔ M.G p.T)) A hA)
      simpa using this
    rw [e v hv, e s hs]
    have := setIntegral_mul_step' (P := M.PM) (M.F.le s) (E := fun _ => (1 : ℝ))
      stronglyMeasurable_const (by simpa using hXM.2.1 v hv) (hXM.2.1 v hv) hmart hA
    simpa using this
  · have e : ∀ r, r ≤ p.T → ∫ ω in A, Lm M t s c ω * Lm M s t' c ω * M.X r ω ∂M.PM =
        ∫ ω in A, Lm M t s c ω * M.X r ω ∂M.PM := by
      intro r hr
      exact setIntegral_indep (mΩ := mΩ) (P := M.PM) (𝓗 := M.F s ⊔ M.G p.T) (FGle M s)
        ((Lm_measF M hM h2 le_rfl c).mono le_sup_left) (X_measH M hM s hr)
        (Lw_meas M hM s t' c) (Lm_ae_PM M hM s t' c) (integral_Lm_PM M hM h5 h1 c)
        (indep_Lw_PM M hM h5 h1 c) (A := A) ((le_sup_left : M.F s ≤ M.F s ⊔ M.G p.T) A hA)
    have hsplit : ∀ r, ∫ ω in A, Lm M t t' c ω * M.X r ω ∂M.PM =
        ∫ ω in A, Lm M t s c ω * Lm M s t' c ω * M.X r ω ∂M.PM := by
      intro r
      refine setIntegral_congr_fun (M.F.le s _ hA) fun ω _ => ?_
      rw [Lm_mul M h2 h1]
    rw [hsplit v, hsplit s, e v hv, e s hs]
    exact setIntegral_mul_step' (M.F.le s) (Lm_measF M hM h2 le_rfl c)
      (int_Lm_X M hM h5 hXM h2 c hv) (hXM.2.1 v hv) hmart hA

/-- `Z_T · Lm ∈ L²(P)` (independent factors). -/
lemma memLp_Z_Lm (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) {u w : ℝ≥0}
    (huw : u ≤ w) (c : ℝ) : MemLp (fun ω => M.Z p.T ω * Lm M u w c ω) 2 M.P := by
  have := hM.prob
  have hZm : Measurable (M.Z p.T) := StochCalcHedge.Z_T_measurable M h5
  have hLm : Measurable (Lw M u w c) := Lw_meas M hM u w c
  have hind : IndepFun (fun ω => M.Z p.T ω ^ 2) (fun ω => Lw M u w c ω ^ 2) M.P := by
    have h0 : IndepFun (M.Z p.T) (Lw M u w c) M.P := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left (indep_Lw M hM huw c p.T) (Z_measFG M hM u).comap_le
    exact h0.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hZ2 : Integrable (fun ω => M.Z p.T ω ^ 2) M.P := (h5.2 p.T le_rfl).integrable_sq
  have hL2 : Integrable (fun ω => Lw M u w c ω ^ 2) M.P :=
    ((memLp_Lm M hM u w c).ae_eq (Lm_ae M hM u w c)).integrable_sq
  have hprod := hind.integrable_mul hZ2 hL2
  have hmeas : AEStronglyMeasurable (fun ω => M.Z p.T ω * Lm M u w c ω) M.P :=
    (hZm.mul (L_measurable (ξ_meas M hM u w) c)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).2 (hprod.congr ?_)
  filter_upwards [Lm_ae M hM u w c] with ω hω
  simp only [Pi.mul_apply, hω]; ring

/-- The exponential `B~`-tilts of `P^M` belong to `M_X`. -/
theorem tilt_mem_MX_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hXM : IsMartingaleOn p.T M.F M.PM M.X) {t t' : ℝ≥0} (htt : t ≤ t') (c : ℝ) :
    Qd M.PM (Lm M t t' c) ∈ M.MX := by
  have := hM.prob
  have := StochCalcS8b.PM_prob M hM h5
  have hm : Measurable (Lm M t t' c) := L_measurable (ξ_meas M hM t t') c
  have hpos : ∀ ω, 0 < Lm M t t' c ω := fun ω => L_pos c ω
  have hint : Integrable (Lm M t t' c) M.PM := (memLp_Lm_PM M hM h5 htt c).integrable one_le_two
  have hZm : Measurable (M.Z p.T) := StochCalcHedge.Z_T_measurable M h5
  have hD : Measurable (fun ω => M.Z p.T ω * Lm M t t' c ω) := hZm.mul hm
  have hDpos : ∀ ω, 0 < M.Z p.T ω * Lm M t t' c ω := fun ω =>
    mul_pos (StochCalcHedge.Z_pos M p.T ω) (hpos ω)
  have hQ : Qd M.PM (Lm M t t' c) = Qd M.P (fun ω => M.Z p.T ω * Lm M t t' c ω) := by
    rw [PM_eq, Qd, Qd, Qd, ← withDensity_mul _ hZm.ennreal_ofReal hm.ennreal_ofReal]
    congr 1
    funext ω
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (StochCalcHedge.Z_pos M p.T ω).le]
  refine ⟨Qd_prob hint hpos (integral_Lm_PM M hM h5 htt c), ?_, ?_, ?_, ?_⟩
  · exact (Qd_ac _).trans (PM_ac M)
  · exact (StochCalcS8b.P_ac_PM M h5).trans (ac_Qd hm hpos)
  · rw [hQ]; exact memLp_rnDeriv hD hDpos (memLp_Z_Lm M hM h5 htt c)
  · exact martingale_Qd hm hpos hint (integral_Lm_PM M hM h5 htt c) p.T M.F M.X hXM.1
      (fun u hu => int_Lm_X M hM h5 hXM htt c hu)
      (fun s v hsv hv A hA => setIntegral_tilt_PM M hM h5 hXM htt c s v hsv hv A hA)

end StochCalcK2
/-! K2b (8c066573 relay 2): orthogonality `E^M[Y ξ χ_T] = 0` and the Stein identity under `P^M`.
Append after K2a_tail.lean. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcStein StochCalcOrth

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- `E[ξ Y] = 0` from the tilt identities, assuming only `G·Y ∈ L¹`. -/
theorem integral_mul_eq_zero' {ξ : Ω → ℝ} {v : ℝ≥0} (hm : Measurable ξ)
    {Y : Ω → ℝ} (hYm : AEStronglyMeasurable Y P)
    (hGY : Integrable (fun ω => G ξ v ω * Y ω) P)
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

end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `Z_T · f(ξ) ∈ L²(P)` for any `f(ξ) ∈ L²(P)` (independent factors). -/
lemma memLp_Z_fξ (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) {u w : ℝ≥0}
    (huw : u ≤ w) (f : ℝ → ℝ) (hf : Measurable f)
    (hf2 : MemLp (fun ω => f (ξ M u w ω)) 2 M.P) :
    MemLp (fun ω => M.Z p.T ω * f (ξ M u w ω)) 2 M.P := by
  have := hM.prob
  have hZm : Measurable (M.Z p.T) := StochCalcHedge.Z_T_measurable M h5
  have hξm := ξ_meas M hM u w
  have h0 : IndepFun (M.Z p.T) (ξ M u w) M.P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left (indep_ξ M hM huw p.T) (Z_measFG M hM u).comap_le
  have hind : IndepFun (fun ω => M.Z p.T ω ^ 2) (fun ω => f (ξ M u w ω) ^ 2) M.P :=
    h0.comp (measurable_id.pow_const 2) (hf.pow_const 2)
  have hZ2 : Integrable (fun ω => M.Z p.T ω ^ 2) M.P := (h5.2 p.T le_rfl).integrable_sq
  have hprod := hind.integrable_mul hZ2 hf2.integrable_sq
  have hmeas : AEStronglyMeasurable (fun ω => M.Z p.T ω * f (ξ M u w ω)) M.P :=
    (hZm.mul (hf.comp hξm)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).2 (hprod.congr (Eventually.of_forall fun ω => ?_))
  simp only [Pi.mul_apply]; ring

/-- `P^M ∈ M_X` once `X` is a `P^M`-martingale. -/
lemma PM_mem_MX (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hXM : IsMartingaleOn p.T M.F M.PM M.X) : M.PM ∈ M.MX := by
  have := hM.prob
  have hZm : Measurable (M.Z p.T) := StochCalcHedge.Z_T_measurable M h5
  refine ⟨StochCalcS8b.PM_prob M hM h5, PM_ac M, StochCalcS8b.P_ac_PM M h5, ?_, hXM⟩
  rw [PM_eq]
  exact memLp_rnDeriv hZm (StochCalcHedge.Z_pos M p.T) (h5.2 p.T le_rfl)

/-- `Z_T · g ∈ L¹(P)` for `Z_T`-weighted L² products. -/
lemma int_PM_mul (M : Model p Ω) (h5 : M.Assumption5) {a b : Ω → ℝ}
    (ha : MemLp (fun ω => M.Z p.T ω * a ω) 2 M.P) (hb : MemLp b 2 M.P) :
    Integrable (fun ω => a ω * b ω) M.PM := by
  refine StochCalcS8b.int_PM_of M h5 _ ((ha.integrable_mul hb).congr
    (Eventually.of_forall fun ω => ?_))
  simp only [Pi.mul_apply]; ring

theorem setIntegral_xi_chi_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hXM : IsMartingaleOn p.T M.F M.PM M.X)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX)
    {t t' : ℝ≥0} (htt : t ≤ t') (ht : t ≤ p.T) (A : Set Ω) (hA : MeasurableSet[M.F t] A) :
    ∫ ω in A, ξ M t t' ω * θχ.2 p.T ω ∂M.PM = 0 := by
  have := hM.prob
  have := StochCalcS8b.PM_prob M hM h5
  obtain ⟨-, hχad, -, hχ2, hmart⟩ := hθ
  have hA' : MeasurableSet A := M.F.le t _ hA
  have hP := setIntegral_mart M (hmart M.PM (PM_mem_MX M hM h5 hXM)) ht hA
  have hZ1 : MemLp (fun ω => M.Z p.T ω * (fun _ => (1 : ℝ)) ω) 2 M.P := by
    simpa using h5.2 p.T le_rfl
  have hint2 : Integrable (θχ.2 p.T) M.PM := by
    have := int_PM_mul M h5 hZ1 hχ2; simpa using this
  have hc : ∀ c : ℝ, ∫ ω, (Lm M t t' c ω - 1) * A.indicator (θχ.2 p.T) ω ∂M.PM = 0 := by
    intro c
    have hQ := tilt_mem_MX_PM M hM h5 hXM htt c
    haveI : IsProbabilityMeasure (Qd M.PM (Lm M t t' c)) := hQ.1
    have hm : Measurable (Lm M t t' c) := L_measurable (ξ_meas M hM t t') c
    have hpos : ∀ ω, 0 < Lm M t t' c ω := fun ω => L_pos c ω
    have h1 := setIntegral_mart M (hmart _ hQ) ht hA
    rw [setIntegral_Qd hm hpos _ hA', setIntegral_Qd hm hpos _ hA'] at h1
    have h2 : ∫ ω in A, Lm M t t' c ω * θχ.2 t ω ∂M.PM = ∫ ω in A, θχ.2 t ω ∂M.PM := by
      have := setIntegral_indep (mΩ := mΩ) (P := M.PM) (𝓗 := M.F t ⊔ M.G p.T)
        (FGle M t) (E := fun _ => (1 : ℝ)) stronglyMeasurable_const
        ((hχad t).mono le_sup_left) (Lw_meas M hM t t' c) (Lm_ae_PM M hM t t' c)
        (integral_Lm_PM M hM h5 htt c) (indep_Lw_PM M hM h5 htt c)
        (A := A) ((le_sup_left : M.F t ≤ M.F t ⊔ M.G p.T) A hA)
      simpa using this
    have hint1 : Integrable (fun ω => Lm M t t' c ω * θχ.2 p.T ω) M.PM :=
      int_PM_mul M h5 (memLp_Z_Lm M hM h5 htt c) hχ2
    calc ∫ ω, (Lm M t t' c ω - 1) * A.indicator (θχ.2 p.T) ω ∂M.PM
        = ∫ ω in A, (Lm M t t' c ω * θχ.2 p.T ω - θχ.2 p.T ω) ∂M.PM := by
          rw [← integral_indicator hA']
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          by_cases h : ω ∈ A <;> simp [h]; ring
      _ = ∫ ω in A, Lm M t t' c ω * θχ.2 p.T ω ∂M.PM - ∫ ω in A, θχ.2 p.T ω ∂M.PM :=
          integral_sub hint1.integrableOn hint2.integrableOn
      _ = 0 := by rw [h1, h2, hP]; ring
  have hgf : Measurable (fun x : ℝ => (|x| + (V t t' : ℝ)) * Real.exp (|x| + (V t t' : ℝ))) := by
    fun_prop
  have hG2 : MemLp (fun ω => (fun x : ℝ => (|x| + (V t t' : ℝ)) * Real.exp (|x| + (V t t' : ℝ)))
      (ξ M t t' ω)) 2 M.P := memLp_G (ξ_meas M hM t t') (ξ_law M hM t t')
  have hZG := memLp_Z_fξ M hM h5 htt _ hgf hG2
  have hGY : Integrable (fun ω => G (ξ M t t') (V t t') ω * A.indicator (θχ.2 p.T) ω) M.PM :=
    int_PM_mul M h5 hZG (hχ2.indicator hA')
  have key := integral_mul_eq_zero' (P := M.PM) (ξ_meas M hM t t')
    ((hχ2.indicator hA').aestronglyMeasurable.mono_ac (PM_ac M)) hGY (fun c _ _ => hc c)
  rw [← key, ← integral_indicator hA']
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  by_cases h : ω ∈ A <;> simp [h]

/-- Orthogonality under `P^M`: `E^M[Y ξ χ_T] = 0` for bounded `F_t`-measurable `Y`. -/
theorem integral_Y_xi_chi_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hXM : IsMartingaleOn p.T M.F M.PM M.X)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX)
    {t t' : ℝ≥0} (htt : t ≤ t') (ht : t ≤ p.T) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[M.F t] Y) {C : ℝ} (hYb : ∀ ω, |Y ω| ≤ C) :
    ∫ ω, Y ω * (ξ M t t' ω * θχ.2 p.T ω) ∂M.PM = 0 := by
  have := hM.prob
  have := StochCalcS8b.PM_prob M hM h5
  have hχ2 : MemLp (θχ.2 p.T) 2 M.P := hθ.2.2.2.1
  have hZξ := memLp_Z_fξ M hM h5 htt id measurable_id
    (memLp_xi (ξ_meas M hM t t') (ξ_law M hM t t'))
  have hint : Integrable (fun ω => ξ M t t' ω * θχ.2 p.T ω) M.PM :=
    int_PM_mul M h5 hZξ hχ2
  have hYint : Integrable (fun ω => Y ω * (ξ M t t' ω * θχ.2 p.T ω)) M.PM :=
    hint.bdd_mul (hY.mono (M.F.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hYb ω)
  have hce : condExp (M.F t) M.PM (fun ω => ξ M t t' ω * θχ.2 p.T ω) =ᵐ[M.PM] 0 :=
    (ae_eq_condExp_of_forall_setIntegral_eq (M.F.le t) hint
      (fun _ _ _ => integrableOn_zero)
      (fun A hA _ => by
        rw [setIntegral_xi_chi_PM M hM h5 hXM θχ hθ htt ht A hA]; simp)
      stronglyMeasurable_zero.aestronglyMeasurable).symm
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := M.F t) (μ := M.PM) hY hYint hint
  have h0 : condExp (M.F t) M.PM (fun ω => Y ω * (ξ M t t' ω * θχ.2 p.T ω)) =ᵐ[M.PM] 0 := by
    refine hpull.trans ?_
    filter_upwards [hce] with ω h
    simp [h]
  rw [← integral_condExp (M.F.le t), integral_congr_ae h0]
  simp

/-- Stein identity under `P^M`. -/
theorem stein_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) {t t' : ℝ≥0}
    (htt : t ≤ t') (ht'T : t' ≤ p.T) (P R : ℝ) {Y : Ω → ℝ} (hYm : Measurable[M.F t] Y) (K : ℝ)
    (hYb : ∀ ω, |Y ω| ≤ K)
    (hint : Integrable (fun ω => ξ M t t' ω * (M.H P R ω * Y ω)) M.PM) :
    ∫ ω, ξ M t t' ω * (M.H P R ω * Y ω) ∂M.PM =
      (P - p.s) * p.σt * (StochCalcTiltM.V t t' : ℝ) *
        ∫ ω, Set.indicator {ω | M.AT ω ≤ R} Y ω ∂M.PM := by
  have := hM.prob
  have := StochCalcS8b.PM_prob M hM h5
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
  have hind1 : Indep (M.F t ⊔ M.G p.T) (MeasurableSpace.comap ξ1 inferInstance) M.PM :=
    indep_ξ_PM M hM h5 htt
  have hind2 : Indep (MeasurableSpace.comap ξ1 inferInstance ⊔ (M.F t ⊔ M.G p.T))
      (MeasurableSpace.comap η inferInstance) M.PM := by
    have h0 := indep_ξ_PM M hM h5 ht'T
    refine indep_of_indep_of_le_left h0 ?_
    exact sup_le ((ξ_measF M hM htt).comap_le.trans le_sup_left)
      (sup_le ((M.F.mono htt).trans le_sup_left) le_sup_right)
  have hind : Indep (MeasurableSpace.comap ξ1 inferInstance) (Ksig M t t') M.PM :=
    indep_sup_of_triple _ _ _ hξm.comap_le (sup_le (M.F.le t) (M.G.le p.T)) hηm.comap_le
      hind1 hind2
  have hindF : IndepFun (fun ω => (U ω, Y ω)) ξ1 M.PM := by
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
  rw [hset, stein_indep hξm hUm hY0 (ξ_law_PM M hM h5 htt) hindF p.hσt _ _ R K hYb hint]

end StochCalcK2
/-! K2c (8c066573 relay 2): Bessel inequality for two orthogonal test variables, and the
`Z_T`-weighted martingale-difference sums `S = Σ_{k<N} Y_k ξ_k` on the grid `gr p n`
(`E_P[Z_T² S²] = Σ E_P[Z_T² Y_k²] T/n`, `E_P[Z_T² S] = E_P[Z_T S] = 0`) via the auxiliary
measure `Q2 = (Z_T²/c)·P`, under which the grid increments keep their independence and laws.
Append after K2b_tail.lean (needs D2_tail's `gr`, `V_gr`; i.e. a dev file containing D2). -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
  StochCalcSteinM StochCalcP6S

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

lemma scal_id (b B : ℝ) : -2 * (b / B) * b + (b / B) ^ 2 * B = -(b ^ 2 / B) := by
  rcases eq_or_ne B 0 with h | h
  · simp [h]
  · field_simp; ring

/-- Bessel's inequality for two orthogonal test variables (`D0` nondegenerate). -/
theorem bessel2 {U D0 D1 : Ω → ℝ} (hU : MemLp U 2 P) (hD0 : MemLp D0 2 P) (hD1 : MemLp D1 2 P)
    (horth : ∫ ω, D0 ω * D1 ω ∂P = 0) (hA : 0 < ∫ ω, D0 ω ^ 2 ∂P) :
    (∫ ω, U ω * D0 ω ∂P) ^ 2 / (∫ ω, D0 ω ^ 2 ∂P) +
      (∫ ω, U ω * D1 ω ∂P) ^ 2 / (∫ ω, D1 ω ^ 2 ∂P) ≤ ∫ ω, U ω ^ 2 ∂P := by
  set a := ∫ ω, U ω * D0 ω ∂P with ha
  set b := ∫ ω, U ω * D1 ω ∂P with hb
  set A := ∫ ω, D0 ω ^ 2 ∂P with hAd
  set B := ∫ ω, D1 ω ^ 2 ∂P with hBd
  set α := a / A
  set β := b / B
  have i1 : Integrable (fun ω => U ω ^ 2) P := hU.integrable_sq
  have i2 : Integrable (fun ω => U ω * D0 ω) P := hU.integrable_mul hD0
  have i3 : Integrable (fun ω => U ω * D1 ω) P := hU.integrable_mul hD1
  have i4 : Integrable (fun ω => D0 ω ^ 2) P := hD0.integrable_sq
  have i5 : Integrable (fun ω => D1 ω ^ 2) P := hD1.integrable_sq
  have i6 : Integrable (fun ω => D0 ω * D1 ω) P := hD0.integrable_mul hD1
  have e : (fun ω => (U ω - α * D0 ω - β * D1 ω) ^ 2) = fun ω =>
      U ω ^ 2 + (-2 * α) * (U ω * D0 ω) + (-2 * β) * (U ω * D1 ω) + α ^ 2 * D0 ω ^ 2 +
        β ^ 2 * D1 ω ^ 2 + (2 * α * β) * (D0 ω * D1 ω) := by
    funext ω; ring
  have h0 : 0 ≤ ∫ ω, (U ω - α * D0 ω - β * D1 ω) ^ 2 ∂P :=
    integral_nonneg fun ω => sq_nonneg _
  have j2 : Integrable (fun ω => -2 * α * (U ω * D0 ω)) P := i2.const_mul _
  have j3 : Integrable (fun ω => -2 * β * (U ω * D1 ω)) P := i3.const_mul _
  have j4 : Integrable (fun ω => α ^ 2 * D0 ω ^ 2) P := i4.const_mul _
  have j5 : Integrable (fun ω => β ^ 2 * D1 ω ^ 2) P := i5.const_mul _
  have j6 : Integrable (fun ω => 2 * α * β * (D0 ω * D1 ω)) P := i6.const_mul _
  have s1 : Integrable (fun ω => U ω ^ 2 + -2 * α * (U ω * D0 ω)) P := i1.add j2
  have s2 : Integrable (fun ω => U ω ^ 2 + -2 * α * (U ω * D0 ω) + -2 * β * (U ω * D1 ω)) P :=
    s1.add j3
  have s3 : Integrable (fun ω => U ω ^ 2 + -2 * α * (U ω * D0 ω) + -2 * β * (U ω * D1 ω) +
      α ^ 2 * D0 ω ^ 2) P := s2.add j4
  have s4 : Integrable (fun ω => U ω ^ 2 + -2 * α * (U ω * D0 ω) + -2 * β * (U ω * D1 ω) +
      α ^ 2 * D0 ω ^ 2 + β ^ 2 * D1 ω ^ 2) P := s3.add j5
  rw [e, integral_add s4 j6, integral_add s3 j5, integral_add s2 j4, integral_add s1 j3,
    integral_add i1 j2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, horth, mul_zero] at h0
  have hα : -2 * α * a + α ^ 2 * A = -(a ^ 2 / A) := scal_id a A
  have hβ : -2 * β * b + β ^ 2 * B = -(b ^ 2 / B) := scal_id b B
  rw [← ha, ← hb, ← hAd, ← hBd] at h0
  linarith [hα, hβ]

end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `c = E_P[Z_T²]`. -/
noncomputable def cZ (M : Model p Ω) : ℝ := ∫ ω, M.Z p.T ω ^ 2 ∂M.P

lemma cZ_pos (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) : 0 < cZ M := by
  have := hM.prob
  have hi : Integrable (fun ω => M.Z p.T ω ^ 2) M.P := (h5.2 p.T le_rfl).integrable_sq
  rw [cZ, integral_pos_iff_support_of_nonneg (fun ω => sq_nonneg _) hi]
  have : Function.support (fun ω => M.Z p.T ω ^ 2) = Set.univ := by
    ext ω; simp [(StochCalcHedge.Z_pos M p.T ω).ne']
  rw [this, measure_univ]; exact one_pos

/-- The weight `Z_T²/c`. -/
noncomputable def wZ (M : Model p Ω) (ω : Ω) : ℝ := M.Z p.T ω ^ 2 / cZ M

lemma wZ_pos (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (ω : Ω) : 0 < wZ M ω :=
  div_pos (pow_pos (StochCalcHedge.Z_pos M p.T ω) 2) (cZ_pos M hM h5)

lemma wZ_measFG (M : Model p Ω) (hM : M.Standing) (u : ℝ≥0) :
    Measurable[M.F u ⊔ M.G p.T] (wZ M) :=
  ((Z_measFG M hM u).pow_const 2).div_const _

lemma wZ_meas (M : Model p Ω) (hM : M.Standing) : Measurable (wZ M) :=
  (wZ_measFG M hM 0).mono (FGle M 0) le_rfl

lemma wZ_int (M : Model p Ω) (h5 : M.Assumption5) : Integrable (wZ M) M.P :=
  ((h5.2 p.T le_rfl).integrable_sq).div_const _

lemma wZ_one (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) :
    ∫ ω, wZ M ω ∂M.P = 1 := by
  unfold wZ; rw [integral_div]; exact div_self (cZ_pos M hM h5).ne'

lemma Q2_univ (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) :
    Qd M.P (wZ M) Set.univ = 1 := by
  have := hM.prob
  have := Qd_prob (wZ_int M h5) (wZ_pos M hM h5) (wZ_one M hM h5)
  exact measure_univ

lemma Q2_prob (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) :
    IsProbabilityMeasure (Qd M.P (wZ M)) := by
  have := hM.prob
  exact Qd_prob (wZ_int M h5) (wZ_pos M hM h5) (wZ_one M hM h5)

lemma integral_Q2 (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (g : Ω → ℝ) :
    ∫ ω, g ω ∂(Qd M.P (wZ M)) = ∫ ω, wZ M ω * g ω ∂M.P := by
  have := hM.prob
  have h := setIntegral_Qd (P := M.P) (wZ_meas M hM) (wZ_pos M hM h5) g MeasurableSet.univ
  simpa only [Measure.restrict_univ] using h

/-- grid increment `ξ_k = B~(t_{k+1}) - B~(t_k)`. -/
noncomputable def xg (M : Model p Ω) (n k : ℕ) : Ω → ℝ :=
  ξ M (StochCalcD2.gr p n k) (StochCalcD2.gr p n (k + 1))

/-- grid σ-algebras `F_{t_k} ⊔ G_T`. -/
noncomputable def mg (M : Model p Ω) (n k : ℕ) : MeasurableSpace Ω :=
  M.F (StochCalcD2.gr p n k) ⊔ M.G p.T

lemma mg_mono (M : Model p Ω) (n : ℕ) : Monotone (mg M n) := fun i j hij =>
  sup_le_sup_right (M.F.mono (StochCalcD2.gr_mono p n hij)) _

lemma xg_measm (M : Model p Ω) (hM : M.Standing) (n k : ℕ) : Measurable[mg M n (k + 1)] (xg M n k) :=
  (ξ_measF M hM (StochCalcD2.gr_mono p n k.le_succ)).mono le_sup_left le_rfl

lemma indep_xg (M : Model p Ω) (hM : M.Standing) (n k : ℕ) :
    Indep (mg M n k) (MeasurableSpace.comap (xg M n k) inferInstance) M.P :=
  indep_ξ M hM (StochCalcD2.gr_mono p n k.le_succ) p.T

lemma indep_xg_Q2 (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (n k : ℕ) :
    Indep (mg M n k) (MeasurableSpace.comap (xg M n k) inferInstance) (Qd M.P (wZ M)) := by
  have := hM.prob
  exact indep_Qd (mΩ := mΩ) (wZ_measFG M hM _) (indep_xg M hM n k) (FGle M _)
    (ξ_meas M hM _ _).comap_le (Q2_univ M hM h5)

lemma xg_law_Q2 (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (n k : ℕ) :
    HasLaw (xg M n k) (gaussianReal 0 (V (StochCalcD2.gr p n k) (StochCalcD2.gr p n (k + 1))))
      (Qd M.P (wZ M)) := by
  have := hM.prob
  have hm := ξ_meas M hM (StochCalcD2.gr p n k) (StochCalcD2.gr p n (k + 1))
  refine ⟨hm.aemeasurable, ?_⟩
  rw [← (ξ_law M hM _ _).map_eq]
  ext S hS
  rw [xg, Measure.map_apply hm hS, Measure.map_apply hm hS]
  exact Qd_eq (mΩ := mΩ) (wZ_measFG M hM _) (indep_xg M hM n k) (FGle M _)
    hm.comap_le (Q2_univ M hM h5) ⟨S, hS, rfl⟩

/-- The weighted sum identities. -/
theorem wsum (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (n : ℕ)
    (Y : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable[M.F (StochCalcD2.gr p n k)] (Y k)) (C : ℝ)
    (hYb : ∀ k ω, |Y k ω| ≤ C) (N : ℕ) :
    MemLp (fun ω => M.Z p.T ω * ∑ k ∈ Finset.range N, Y k ω * xg M n k ω) 2 M.P ∧
    ∫ ω, (M.Z p.T ω * ∑ k ∈ Finset.range N, Y k ω * xg M n k ω) ^ 2 ∂M.P =
      ∑ k ∈ Finset.range N, (∫ ω, M.Z p.T ω ^ 2 * Y k ω ^ 2 ∂M.P) * ((p.T : ℝ) / n) ∧
    ∫ ω, M.Z p.T ω ^ 2 * ∑ k ∈ Finset.range N, Y k ω * xg M n k ω ∂M.P = 0 ∧
    ∫ ω, M.Z p.T ω * ∑ k ∈ Finset.range N, Y k ω * xg M n k ω ∂M.P = 0 := by
  have := hM.prob
  have := Q2_prob M hM h5
  have := StochCalcS8b.PM_prob M hM h5
  have hc := cZ_pos M hM h5
  have hYm' : ∀ k, Measurable[mg M n k] (Y k) := fun k => (hYm k).mono le_sup_left le_rfl
  have hξ2 : ∀ k, MemLp (xg M n k) 2 (Qd M.P (wZ M)) := fun k =>
    memLp_xi (ξ_meas M hM _ _) (xg_law_Q2 M hM h5 n k)
  have hξ0 : ∀ k, ∫ ω, xg M n k ω ∂(Qd M.P (wZ M)) = 0 := fun k =>
    integral_gauss (xg_law_Q2 M hM h5 n k)
  obtain ⟨hSm, hS2, hSsq⟩ := sum_props (P := Qd M.P (wZ M)) (mg M n) (xg M n) Y (mg_mono M n)
    (fun k => FGle M _) (xg_measm M hM n) (indep_xg_Q2 M hM h5 n) hξ2 hξ0 hYm' C hYb N
  set S : Ω → ℝ := fun ω => ∑ k ∈ Finset.range N, Y k ω * xg M n k ω with hS
  have hSm' : Measurable S := hSm.mono (FGle M _) le_rfl
  have hZm : Measurable (M.Z p.T) := StochCalcHedge.Z_T_measurable M h5
  -- E_P[Z² f] = c E_Q2[f]
  have hconv : ∀ g : Ω → ℝ, ∫ ω, M.Z p.T ω ^ 2 * g ω ∂M.P = cZ M * ∫ ω, g ω ∂(Qd M.P (wZ M)) := by
    intro g
    rw [integral_Q2 M hM h5, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [wZ]; field_simp
  have hint2 : Integrable (fun ω => M.Z p.T ω ^ 2 * S ω ^ 2) M.P := by
    have h := (integrable_Qd_iff (P := M.P) (wZ_meas M hM) (wZ_pos M hM h5) _).1 hS2.integrable_sq
    refine (h.const_mul (cZ M)).congr (Eventually.of_forall fun ω => ?_)
    simp only [wZ]; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (memLp_two_iff_integrable_sq (hZm.mul hSm').aestronglyMeasurable).2
      (hint2.congr (Eventually.of_forall fun ω => ?_))
    simp only [Pi.mul_apply]; ring
  · have e1 : (fun ω => (M.Z p.T ω * S ω) ^ 2) = fun ω => M.Z p.T ω ^ 2 * S ω ^ 2 := by
      funext ω; ring
    rw [e1, hconv, hSsq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_sq_gauss (xg_law_Q2 M hM h5 n k), StochCalcD2.V_gr, hconv]
    ring
  · rw [hconv, integral_sum_eq_zero (P := Qd M.P (wZ M)) (mg M n) (xg M n) Y (fun k => FGle M _)
      (indep_xg_Q2 M hM h5 n) (fun k => ξ_meas M hM _ _) hξ2 hξ0 hYm' C hYb N, mul_zero]
  · rw [StochCalcS8b.integral_PM M h5]
    exact integral_sum_eq_zero (P := M.PM) (mg M n) (xg M n) Y (fun k => FGle M _)
      (fun k => indep_ξ_PM M hM h5 (StochCalcD2.gr_mono p n k.le_succ))
      (fun k => ξ_meas M hM _ _)
      (fun k => memLp_xi (ξ_meas M hM _ _) (ξ_law_PM M hM h5 (StochCalcD2.gr_mono p n k.le_succ)))
      (fun k => integral_gauss (ξ_law_PM M hM h5 (StochCalcD2.gr_mono p n k.le_succ))) hYm' C hYb N

end StochCalcK2


/-! O7Q2 (8c066573 relay 34, O7.5 glue hQb): Bayes formula for the tilted measure
`Q = (Z²/c)·P` and the Q2 form of O7.4: with `g = θ / Z_T`,
`E_Q[g | m] = E_P[θ|F_t] / Z_t` for every `F_t ≤ m ≤ F_t ⊔ G_T`; hence
`E_Q[g | F_t ⊔ G_T] = E_Q[g | F_t]` (the `hQb` hypothesis of `StochCalcE2.E2_bound`).
Generic: `StochCalcQ2.bayes_ce`.  Model: `StochCalcQ2.Q2ce`, `StochCalcQ2.Q2_hQb`.
Append after O7Q1M_tail (inside the dev file's `namespace StochCalcP6`). -/

namespace StochCalcQ2

open MeasureTheory ProbabilityTheory Filter Topology
open StochCalcTilt
open scoped NNReal ENNReal

section generic

variable {Ω : Type*} {m mH : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]


end generic

end StochCalcQ2

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ2M


/-! O7.5 piece (relay 21): one-cell identity of the E2 error argument (pure Mathlib).
F-filtration (F k) ≤ (F (k + 1)), enlarged H-filtration (H k) ≤ (H (k + 1)) ((F k) ≤ (H k), (F (k + 1)) ≤ (H (k + 1))), increment w ((F (k + 1))-measurable,
"independent of (H k) with mean 0" in the form `hind`), g with E[g|(H (k + 1))] = E[g|(F (k + 1))] (Q1), NC for (F k)-multipliers.
Then for a bounded (H k)-measurable y:  E[g y w] = E[(gb - ga) w (yb - ya)]. -/

set_option autoImplicit false

open MeasureTheory Filter
open scoped NNReal

namespace StochCalcE2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]



end StochCalcE2

-- O7E3 tail (8c066573 relay 24): append after lib/stochcalc/O7E2.lean (pure Mathlib).

/-! O7.5 (E2 n-cell sum): splitting a cell into `n` pieces, the NC orthogonality gives
`|E[g y ΣΔW]| ≤ l/2 E g² + (1/2l)(μ/2 Σ E w_k⁴ + 2 Cy⁴/μ)` for all `l, μ > 0`; with `Σ E w_k⁴ = O(1/n)`
this forces `E[g y ΣΔW] = 0`. -/

namespace StochCalcE2

open MeasureTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]









end StochCalcE2


/-! O7G4 (8c066573 relay 24, for the O7.5 model instance): fourth moments of centred Gaussians
scale like `v²`: `∫ x⁴ dN(0,v) = v² ∫ x⁴ dN(0,1)`, and a random variable with law `N(0,v)` has
`E w⁴ = v² K₄`, `K₄ := ∫ x⁴ dN(0,1)` (finite). Pure Mathlib. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochCalcG4




end StochCalcG4

/-! O7E5 (8c066573 relay 34, O7.5 model glue): under `Q2 = (Z_T²/c)·P`, if `g = f/Z_T` has the
Q1 property `E_Q2[g | F_t ⊔ G_T] = E_Q2[g | F_t]` (`StochCalcQ2M.Q2ce`) and `f` is orthogonal to
the grid class `NC` (expanded form `hfN`), then `E_Q2[g y (B~_{t_{j+1}} - B~_{t_j})] = 0` for every
bounded `F_{t_j} ⊔ G_T`-measurable `y` (cell split in `r` pieces + `StochCalcE2.E2_bound` +
`StochCalcE2.zero_of_bounds`).  Append after E2G4_block (dev base M15). -/

namespace StochCalcE5M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcE2 StochCalcG4
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcE5M

end StochCalcP6
-- ===== slice of P8c066573M17 (probe/slice8c/cuts/r_k2.lean.src/P8c066573M17.lean): 0/73 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

/-! O7E6 (8c066573 relay 35, O7.6): conclusion of the completeness argument.  Under
`Q2 = (Z_T²/c)·P`, let `g = f/Z_T`.  If `g ⊥_Q2 L∞(G_T)` (`hG`, from `Q2ce` at `t = 0`) and
`g ⊥_Q2 y·ΔB~_cell` for bounded `F_{t_j} ⊔ G_T`-measurable `y` (`hE`, the conclusion of
`StochCalcE5M.E5`), then `E_P[f Z_T ζ e^{i Σ μ_k ΔB~_k}] = 0` for bounded `G_T`-measurable `ζ`
(`StochCalcR1.core` under `Q2`: exponentials of `B~`-grid sums are `L²(Q2)`-limits of constants
plus `F_{t_l} ⊔ G_T`-weighted `B~`-grid sums), hence `f Z_T` is orthogonal to every
`cos/sin ⟪Δ_j, t⟫` (`StochCalcR5.inner_Δ`, `cos (a + b)` split with `a` the `B`-part) and
`StochCalcR2.ae_eq_zero_of_trig` gives `f Z_T = 0`, so `f = 0`.  Append after O7E5_tail (dev base M16). -/

namespace StochCalcE6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV Finset
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcD3 StochCalcE2 StochCalcG4 StochCalcR5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]









end StochCalcE6M

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

/-! O7HG (8c066573 relay 36): the `hG` input of `StochCalcE6M.E6` from `Q2ce` at `t = 0`.
`F_0` (augmented natural filtration of `(B, B~)` at time `0`) is `P`-trivial since `B_0 = B~_0 = 0`
a.s., so `E_P[f | F_0] = ∫ f = 0`; `Q2ce` at `t = 0` gives `E_Q2[f/Z_T | F_0 ⊔ G_T] = 0`, hence
`∫ f/Z_T · ζ dQ2 = 0` for bounded `G_T`-measurable `ζ`.  Append after O7E5_tail (dev base M16). -/

namespace StochCalcHGM

open MeasureTheory ProbabilityTheory Filter HedgePSNV Set
open StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM StochCalcSteinM StochCalcP6S
open StochCalcK2 StochCalcD2 StochCalcD3 StochCalcZ3
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcHGM

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

/-! O70 support (copied from the accepted cc6d45ce library: StochCalcS2 clR + hasIto_add, StochCalcS3 hasIto_tail,
StochCalcS3M ext_hasIto, StochCalcFe). -/

namespace StochCalcS2

open ItoLib StochCalcTC StochCalcL2M

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]














end StochCalcS2
namespace StochCalcS3

open EthierKurtz ItoLib StochCalcTC StochCalcS2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcS3
namespace StochCalcS3M

open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS3

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcS3M
namespace StochCalcFe

open Real

section line
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




end line










end StochCalcFe

/-! O7.0 (8c066573 relay 36): `X_t ≠ 0` a.s. in the NON-degenerate model (no `hdeg`, no `QVStatement`):
Ito formula for `f_ε(x) = ½ log(x² + ε)` on `X` frozen at `T` and continued with its drift and
Brownian increments, localized on `σ ≤ Rσ`, `μ ≤ Rμ`; then `μT`-a.e. via Tonelli, and the `hac`
input of `Q2ce`: `a' Xσ + c Xμ = 0 ⇒ a' = -η c`. -/

namespace StochCalcX0

open MeasureTheory ProbabilityTheory Filter Set
open HedgePSNV EthierKurtz StochCalcBr StochCalcD1b StochCalcD1aW StochCalcTC ItoLib
  StochCalcS1M StochCalcS2 StochCalcS3 StochCalcS3M StochCalcFe
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




























end StochCalcX0

end StochCalcP6

-- ===== slice of P8c066573M18 (probe/slice8c/cuts/r_k2.lean.src/P8c066573M18.lean): 0/23 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

/-! GQ (8c066573 relay 37): the O7.4 chain for a GENERAL `θ = θB + θ⊥` (relay 37 found that
`Q1model`/`Q2ce` assume `θ` is a pure `B`-integral, but the completeness argument applies them to `f`,
which also has a `B~`-part).  `KshiftG`/`Q1coreG`: `Rep θB a` for the `B`-part only, `hproj` for the
full `θ`, and `E[θ - θB | K_T] = 0`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}



end StochCalcO3


namespace StochCalcQ1M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcQ1M

namespace StochCalcQ2M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcQ2M

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

/-! G3/G5 (8c066573 relay 38).  G5: `O6_modelP` = `O6_model` also exporting that `a'` is
predictable (in the closure of the elementaries).  G3: for `θ` in the closure of the elementary
`B~`-integrals, `E[θ | F_t ⊔ G_T] = E[θ | F_t]` (the `B~` increments after `u` are independent of
`F_u ⊔ G_T`). -/

namespace StochCalcO6M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1b StochCalcO3 StochCalcO3M StochCalcS1R StochCalcHit StochCalcO4M
open StochCalcO5
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcO6M

namespace StochCalcG3

open MeasureTheory ProbabilityTheory Filter Topology StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} {m1 m2 mG n : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]




end StochCalcG3

namespace StochCalcG3M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcO3 StochCalcO3M StochCalcKF StochCalcSteinM
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcG3M


namespace StochCalcG4

open MeasureTheory ProbabilityTheory Filter Topology StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]





variable {mF : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}





end StochCalcG4


namespace StochCalcG4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcO3 StochCalcO3M StochCalcG3M StochCalcG4 StochCalcR1M StochCalcR4 StochCalcR7 StochCalcD2
  StochCalcD3 StochCalcTiltM
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]




end StochCalcG4M

end StochCalcP6

namespace StochCalcP6

set_option autoImplicit false

/-! HC (8c066573 relay 38): **M6 hcomp** (completeness) from O3_model, O6_modelP, O70, G4, G3, Z2, Z3,
Q2ceG, E5, hG_glue, E6.  `ContHyp M` (conj 3 of platform theorem 1c98c8e0) is kept as a hypothesis. -/

namespace StochCalcHC

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcO3 StochCalcO3M StochCalcO6M StochCalcG3M StochCalcG4 StochCalcG4M StochCalcKF
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


end StochCalcHC

end StochCalcP6

-- ===== slice of RUb (probe/slice8c/cuts/r_k2.lean.src/RUb.lean): 0/17 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! RU (8c066573 relay 44): Elem-free ("unpacked") forms of `Rep`, `closure (range eL)`, `closure (range TL)`
and `IncrHyp`, so that cut statements become Definitions-only after unfolding. -/

namespace StochCalcRU

open StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}














end StochCalcRU

namespace StochCalcQ2U

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV EthierKurtz ItoLib
open StochCalcBr StochCalcD1aW StochCalcZ2 StochCalcZ3 StochCalcZ4m StochCalcZ4mb StochCalcHit
open StochCalcO3 StochCalcO3M StochCalcZ7a StochCalcZ7b StochCalcZ7d StochCalcCE StochCalcR1M
open StochCalcZK StochCalcKF StochCalcTilt StochCalcQ2 StochCalcRU
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcQ2U

end StochCalcP6

-- ===== slice of __current__ (probe/slice8c/cuts/r_k2.lean.src/__current__.lean): 41/98 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! K2d (relay 3): the finite-grid lower bound under `P^M`, tests `D0 = Z_T - 1`, `D1 = Z_T S`. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- Bessel with the linearised second term: `a²/A + (2b - B) ≤ E U²`. -/
theorem bessel_lin {U D0 D1 : Ω → ℝ} (hU : MemLp U 2 P) (hD0 : MemLp D0 2 P)
    (hD1 : MemLp D1 2 P) (horth : ∫ ω, D0 ω * D1 ω ∂P = 0) (hA : 0 < ∫ ω, D0 ω ^ 2 ∂P) :
    (∫ ω, U ω * D0 ω ∂P) ^ 2 / (∫ ω, D0 ω ^ 2 ∂P) +
      (2 * (∫ ω, U ω * D1 ω ∂P) - ∫ ω, D1 ω ^ 2 ∂P) ≤ ∫ ω, U ω ^ 2 ∂P := by
  have hb := bessel2 hU hD0 hD1 horth hA
  have hlin : 2 * (∫ ω, U ω * D1 ω ∂P) - ∫ ω, D1 ω ^ 2 ∂P ≤
      (∫ ω, U ω * D1 ω ∂P) ^ 2 / (∫ ω, D1 ω ^ 2 ∂P) := by
    rcases (integral_nonneg (fun ω => sq_nonneg (D1 ω)) : 0 ≤ ∫ ω, D1 ω ^ 2 ∂P).eq_or_lt
      with h | h
    · have hz := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (D1 ω))
        hD1.integrable_sq).1 h.symm
      have h0 : ∫ ω, U ω * D1 ω ∂P = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hz] with ω hω
        have : D1 ω = 0 := by simpa using hω
        simp [this]
      rw [h0, ← h]; simp
    · rw [le_div_iff₀ h]
      nlinarith [sq_nonneg ((∫ ω, U ω * D1 ω ∂P) - ∫ ω, D1 ω ^ 2 ∂P)]
  linarith

end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `E^M[χ_T] = 0` for admissible strategies (`P^M ∈ M_X`, `χ_0 = 0`). -/
lemma integral_chi_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5)
    (hXM : IsMartingaleOn p.T M.F M.PM M.X)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX) :
    ∫ ω, θχ.2 p.T ω ∂M.PM = 0 := by
  have := hM.prob
  have := StochCalcS8b.PM_prob M hM h5
  obtain ⟨-, -, hg, -, hmart⟩ := hθ
  have hm := hmart M.PM (PM_mem_MX M hM h5 hXM)
  obtain ⟨K, hK, hχ⟩ := hg.2
  have hK0 := StochCalcHedgeDeg.ito_zero_ae M.P (fun t => M.F t) M.B _ K hK
  have hχ0 : θχ.2 0 =ᵐ[M.PM] fun _ => (0 : ℝ) := by
    refine (PM_ac M).ae_le ?_
    filter_upwards [hχ, hK0] with ω h1 h2
    rw [h1 0 zero_le, h2]; simp
  rw [← integral_condExp (M.F.le 0),
    integral_congr_ae ((hm.2.2 0 p.T zero_le le_rfl).trans hχ0)]
  simp

/-- `L²(P)` variables are `P^M`-integrable. -/
lemma int_PM_L2 (M : Model p Ω) (h5 : M.Assumption5) {b : Ω → ℝ} (hb : MemLp b 2 M.P) :
    Integrable b M.PM :=
  StochCalcS8b.int_PM_of M h5 b ((h5.2 p.T le_rfl).integrable_mul hb)

/-- One grid term: `E^M[(Y ξ)(H + χ_T)] = (P-s)σ̃ Δ E^M[Y 1{A_T ≤ R}]`. -/
theorem termPM (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2) (h5 : M.Assumption5)
    (hXM : IsMartingaleOn p.T M.F M.PM M.X)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX) (P R : ℝ)
    {t t' : ℝ≥0} (htt : t ≤ t') (ht'T : t' ≤ p.T) {Y : Ω → ℝ} (hYm : Measurable[M.F t] Y)
    {C : ℝ} (hYb : ∀ ω, |Y ω| ≤ C) :
    ∫ ω, (Y ω * ξ M t t' ω) * (M.H P R ω + θχ.2 p.T ω) ∂M.PM =
      (P - p.s) * p.σt * (V t t' : ℝ) * ∫ ω, Set.indicator {ω | M.AT ω ≤ R} Y ω ∂M.PM := by
  have := hM.prob
  have := StochCalcS8b.PM_prob M hM h5
  have hYa : Measurable Y := hYm.mono (M.F.le t) le_rfl
  have hZξ := memLp_Z_fξ M hM h5 htt id measurable_id
    (memLp_xi (ξ_meas M hM t t') (ξ_law M hM t t'))
  have hZYξ : MemLp (fun ω => M.Z p.T ω * (Y ω * ξ M t t' ω)) 2 M.P := by
    refine (StochCalcP6S.memLp_bdd_mul hZξ hYa.aestronglyMeasurable hYb).congr_norm
      ((StochCalcHedge.Z_T_measurable M h5).mul (hYa.mul (ξ_meas M hM t t'))).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    simp only [id]; ring_nf
  have hH := StochCalcHedgeDeg.H_memLp M hM hL2 P R
  have hχ : MemLp (θχ.2 p.T) 2 M.P := hθ.2.2.2.1
  have i1 : Integrable (fun ω => (Y ω * ξ M t t' ω) * M.H P R ω) M.PM := int_PM_mul M h5 hZYξ hH
  have i2 : Integrable (fun ω => (Y ω * ξ M t t' ω) * θχ.2 p.T ω) M.PM :=
    int_PM_mul M h5 hZYξ hχ
  have e1 : (fun ω => (Y ω * ξ M t t' ω) * (M.H P R ω + θχ.2 p.T ω)) =
      fun ω => (Y ω * ξ M t t' ω) * M.H P R ω + (Y ω * ξ M t t' ω) * θχ.2 p.T ω := by
    funext ω; ring
  rw [e1, integral_add i1 i2]
  have h0 : ∫ ω, (Y ω * ξ M t t' ω) * θχ.2 p.T ω ∂M.PM = 0 := by
    have h := integral_Y_xi_chi_PM M hM h5 hXM θχ hθ htt (htt.trans ht'T)
      hYm.stronglyMeasurable hYb
    rw [← h]; congr 1; funext ω; ring
  have hint : Integrable (fun ω => ξ M t t' ω * (M.H P R ω * Y ω)) M.PM := by
    refine i1.congr (Eventually.of_forall fun ω => ?_); simp only; ring
  have hs := stein_PM M hM h5 htt ht'T P R hYm C hYb hint
  rw [h0, add_zero, ← hs]
  congr 1; funext ω; ring

/-- The finite-grid lower bound for arbitrary bounded adapted grid weights `Y_k`. -/
theorem low_nY (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2) (h5 : M.Assumption5)
    (hne : ¬ (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)))
    (hXM : IsMartingaleOn p.T M.F M.PM M.X)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX) (P R m : ℝ)
    (hmean : ∫ ω, (M.H P R ω + θχ.2 p.T ω) ∂M.P = m) (n : ℕ)
    (Y : ℕ → Ω → ℝ) (hYm : ∀ k, Measurable[M.F (StochCalcD2.gr p n k)] (Y k)) (C : ℝ)
    (hYb : ∀ k ω, |Y k ω| ≤ C) :
    (M.V0 P R - m) ^ 2 / (M.ZM0 - 1) +
      ∑ k ∈ Finset.range n, ((p.T : ℝ) / n) *
        (2 * ((P - p.s) * p.σt * ∫ ω, Set.indicator {ω | M.AT ω ≤ R} (Y k) ω ∂M.PM) -
          ∫ ω, M.Z p.T ω ^ 2 * Y k ω ^ 2 ∂M.P) ≤
      ∫ ω, (M.H P R ω + θχ.2 p.T ω - m) ^ 2 ∂M.P := by
  have := hM.prob
  have := StochCalcS8b.PM_prob M hM h5
  obtain ⟨hS2, hSsq, hZ2S, hZS⟩ := wsum M hM h5 n Y hYm C hYb n
  let S : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, Y k ω * xg M n k ω
  have hS2' : MemLp (fun ω => M.Z p.T ω * S ω) 2 M.P := hS2
  have hSsq' : ∫ ω, (M.Z p.T ω * S ω) ^ 2 ∂M.P =
      ∑ k ∈ Finset.range n, (∫ ω, M.Z p.T ω ^ 2 * Y k ω ^ 2 ∂M.P) * ((p.T : ℝ) / n) := hSsq
  have hZ2S' : ∫ ω, M.Z p.T ω ^ 2 * S ω ∂M.P = 0 := hZ2S
  have hZS' : ∫ ω, M.Z p.T ω * S ω ∂M.P = 0 := hZS
  have hZ2 : MemLp (M.Z p.T) 2 M.P := h5.2 p.T le_rfl
  have hH := StochCalcHedgeDeg.H_memLp M hM hL2 P R
  have hχ : MemLp (θχ.2 p.T) 2 M.P := hθ.2.2.2.1
  have hHχ : MemLp (fun ω => M.H P R ω + θχ.2 p.T ω) 2 M.P := hH.add hχ
  have hU : MemLp (fun ω => M.H P R ω + θχ.2 p.T ω - m) 2 M.P := hHχ.sub (memLp_const m)
  have hD0 : MemLp (fun ω => M.Z p.T ω - 1) 2 M.P := hZ2.sub (memLp_const 1)
  have iZ : Integrable (M.Z p.T) M.P := hZ2.integrable one_le_two
  -- orthogonality of the tests
  have horth : ∫ ω, (M.Z p.T ω - 1) * (M.Z p.T ω * S ω) ∂M.P = 0 := by
    have e : (fun ω => (M.Z p.T ω - 1) * (M.Z p.T ω * S ω)) =
        fun ω => M.Z p.T ω * (M.Z p.T ω * S ω) - M.Z p.T ω * S ω := by funext ω; ring
    have i1 : Integrable (fun ω => M.Z p.T ω * (M.Z p.T ω * S ω)) M.P := hZ2.integrable_mul hS2'
    rw [e, integral_sub i1 (hS2'.integrable one_le_two), hZS', sub_zero, ← hZ2S']
    congr 1; funext ω; ring
  -- A = ZM0 - 1
  have hA : ∫ ω, (M.Z p.T ω - 1) ^ 2 ∂M.P = M.ZM0 - 1 := by
    have e : (fun ω => (M.Z p.T ω - 1) ^ 2) = fun ω => (M.Z p.T ω ^ 2 - 2 * M.Z p.T ω) + 1 := by
      funext ω; ring
    have j1 : Integrable (fun ω => M.Z p.T ω ^ 2 - 2 * M.Z p.T ω) M.P :=
      hZ2.integrable_sq.sub (iZ.const_mul 2)
    rw [e, integral_add j1 (integrable_const 1),
      integral_sub hZ2.integrable_sq (iZ.const_mul 2), integral_const_mul,
      StochCalcHedge.integral_Z_T M hM h5, StochCalcHedge.ZM0_eq M h5]
    simp; ring
  have hApos : 0 < ∫ ω, (M.Z p.T ω - 1) ^ 2 ∂M.P := by
    rw [hA]; linarith [StochCalcHedge.one_lt_ZM0 M hM h5 hne]
  -- a = V0 - m
  have ha : ∫ ω, (M.H P R ω + θχ.2 p.T ω - m) * (M.Z p.T ω - 1) ∂M.P = M.V0 P R - m := by
    have e : (fun ω => (M.H P R ω + θχ.2 p.T ω - m) * (M.Z p.T ω - 1)) =
        fun ω => (M.Z p.T ω * (M.H P R ω + θχ.2 p.T ω) - (M.H P R ω + θχ.2 p.T ω)) -
          m * (M.Z p.T ω - 1) := by funext ω; ring
    have i1 : Integrable (fun ω => M.Z p.T ω * (M.H P R ω + θχ.2 p.T ω)) M.P :=
      hZ2.integrable_mul hHχ
    have i2 : Integrable (fun ω => M.H P R ω + θχ.2 p.T ω) M.P := hHχ.integrable one_le_two
    have i3 : Integrable (fun ω => M.Z p.T ω - 1) M.P := iZ.sub (integrable_const 1)
    have j1 : Integrable (fun ω => M.Z p.T ω * (M.H P R ω + θχ.2 p.T ω) -
        (M.H P R ω + θχ.2 p.T ω)) M.P := i1.sub i2
    have j2 : Integrable (fun ω => m * (M.Z p.T ω - 1)) M.P := i3.const_mul m
    rw [e, integral_sub j1 j2, integral_sub i1 i2, integral_const_mul,
      integral_sub iZ (integrable_const 1), StochCalcHedge.integral_Z_T M hM h5, hmean,
      StochCalcS8b.integral_PM M h5,
      integral_add (int_PM_L2 M h5 hH) (int_PM_L2 M h5 hχ), integral_chi_PM M hM h5 hXM θχ hθ]
    have hV0 : M.V0 P R = ∫ ω, M.H P R ω ∂M.PM := rfl
    rw [hV0]; simp
  -- b = Σ Δ (P-s)σ̃ E^M[Y_k 1{A ≤ R}]
  have hb : ∫ ω, (M.H P R ω + θχ.2 p.T ω - m) * (M.Z p.T ω * S ω) ∂M.P =
      ∑ k ∈ Finset.range n, ((p.T : ℝ) / n) *
        ((P - p.s) * p.σt * ∫ ω, Set.indicator {ω | M.AT ω ≤ R} (Y k) ω ∂M.PM) := by
    have e : (fun ω => (M.H P R ω + θχ.2 p.T ω - m) * (M.Z p.T ω * S ω)) =
        fun ω => M.Z p.T ω * (S ω * (M.H P R ω + θχ.2 p.T ω)) - m * (M.Z p.T ω * S ω) := by
      funext ω; ring
    have i1 : Integrable (fun ω => M.Z p.T ω * (S ω * (M.H P R ω + θχ.2 p.T ω))) M.P :=
      (hS2'.integrable_mul hHχ).congr (Eventually.of_forall fun ω => by
        simp only [Pi.mul_apply]; ring)
    rw [e, integral_sub i1 ((hS2'.integrable one_le_two).const_mul m), integral_const_mul, hZS',
      mul_zero, sub_zero, StochCalcS8b.integral_PM M h5]
    have hterm : ∀ k ∈ Finset.range n,
        ∫ ω, (Y k ω * xg M n k ω) * (M.H P R ω + θχ.2 p.T ω) ∂M.PM =
          ((p.T : ℝ) / n) *
            ((P - p.s) * p.σt * ∫ ω, Set.indicator {ω | M.AT ω ≤ R} (Y k) ω ∂M.PM) := by
      intro k hk
      have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
      rw [xg, termPM M hM hL2 h5 hXM θχ hθ P R (StochCalcD2.gr_mono p n k.le_succ)
        (StochCalcD2.gr_le_T p hk') (hYm k) (hYb k), StochCalcD2.V_gr]
      ring
    have hint : ∀ k ∈ Finset.range n,
        Integrable (fun ω => (Y k ω * xg M n k ω) * (M.H P R ω + θχ.2 p.T ω)) M.PM := by
      intro k _
      have hYa : Measurable (Y k) := (hYm k).mono (M.F.le _) le_rfl
      have hZξ := memLp_Z_fξ M hM h5 (StochCalcD2.gr_mono p n k.le_succ) id measurable_id
        (memLp_xi (ξ_meas M hM _ _) (ξ_law M hM _ _))
      have hZYξ : MemLp (fun ω => M.Z p.T ω * (Y k ω * xg M n k ω)) 2 M.P := by
        refine (StochCalcP6S.memLp_bdd_mul hZξ hYa.aestronglyMeasurable (hYb k)).congr_norm
          ((StochCalcHedge.Z_T_measurable M h5).mul
            (hYa.mul (ξ_meas M hM _ _))).aestronglyMeasurable
          (Eventually.of_forall fun ω => ?_)
        simp only [id, xg]; rw [mul_left_comm]
      exact int_PM_mul M h5 hZYξ hHχ
    have e2 : (fun ω => S ω * (M.H P R ω + θχ.2 p.T ω)) =
        fun ω => ∑ k ∈ Finset.range n, (Y k ω * xg M n k ω) * (M.H P R ω + θχ.2 p.T ω) := by
      funext ω; simp only [S, Finset.sum_mul]
    rw [e2, integral_finsetSum _ hint]
    exact Finset.sum_congr rfl hterm
  have key := bessel_lin hU hD0 hS2' horth hApos
  rw [ha, hA, hb, hSsq'] at key
  convert key using 2
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end StochCalcK2

/-! K2e (relay 3): the grid weights `Y = a·ĉ_t / max(Z^M_t, ε)` and the bracket bound. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `c^M_t = P^M(A_T ≤ R | F_t)`. -/
noncomputable def cAM (M : Model p Ω) (R : ℝ) (t : ℝ≥0) : Ω → ℝ :=
  condExp (M.F t) M.PM (Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)))

/-- An everywhere `[0,1]`-valued version. -/
noncomputable def YcM (M : Model p Ω) (R : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max 0 (min 1 (cAM M R t ω))

/-- `max(Z^M_t, ε)`. -/
noncomputable def mxe (M : Model p Ω) (ε : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := max (M.ZM t ω) ε

/-- The grid weight. -/
noncomputable def Ye (M : Model p Ω) (P R ε : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  p.σt * (P - p.s) * YcM M R t ω / mxe M ε t ω

/-- `g_ε(t) = E^M[(a ĉ_t)² / max(Z^M_t, ε)]`. -/
noncomputable def ge (M : Model p Ω) (P R ε : ℝ) (t : ℝ≥0) : ℝ :=
  ∫ ω, (p.σt * (P - p.s) * YcM M R t ω) ^ 2 / mxe M ε t ω ∂M.PM

lemma ind_int_PM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (R : ℝ) :
    Integrable (Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ))) M.PM := by
  have := StochCalcS8b.PM_prob M hM h5
  exact (integrable_const 1).indicator
    (measurableSet_le (StochCalcD2.AT_meas M hM) measurable_const)

lemma cAM_bounds (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (R : ℝ) (t : ℝ≥0) :
    ∀ᵐ ω ∂M.PM, 0 ≤ cAM M R t ω ∧ cAM M R t ω ≤ 1 := by
  have := StochCalcS8b.PM_prob M hM h5
  have hi := ind_int_PM M hM h5 R
  have h0 : 0 ≤ᵐ[M.PM] cAM M R t :=
    condExp_nonneg (Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have h1 : cAM M R t ≤ᵐ[M.PM] condExp (M.F t) M.PM (fun _ => (1 : ℝ)) :=
    condExp_mono hi (integrable_const 1) (Eventually.of_forall fun ω =>
      Set.indicator_le_self' (fun _ _ => zero_le_one) ω)
  rw [condExp_const (M.F.le t)] at h1
  filter_upwards [h0, h1] with ω a b
  exact ⟨a, b⟩

lemma YcM_ae (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (R : ℝ) (t : ℝ≥0) :
    YcM M R t =ᵐ[M.PM] cAM M R t := by
  filter_upwards [cAM_bounds M hM h5 R t] with ω h
  simp only [YcM, min_eq_right h.2, max_eq_right h.1]

lemma YcM_meas (M : Model p Ω) (R : ℝ) (t : ℝ≥0) : Measurable[M.F t] (YcM M R t) := by
  have h : Measurable[M.F t] (cAM M R t) := stronglyMeasurable_condExp.measurable
  exact measurable_const.max (measurable_const.min h)

lemma YcM_bdd (M : Model p Ω) (R : ℝ) (t : ℝ≥0) (ω : Ω) : |YcM M R t ω| ≤ 1 := by
  unfold YcM
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (min_le_left _ _)

lemma mxe_meas (M : Model p Ω) (ε : ℝ) (t : ℝ≥0) : Measurable[M.F t] (mxe M ε t) :=
  (stronglyMeasurable_condExp.measurable : Measurable[M.F t] (M.ZM t)).max measurable_const

lemma mxe_ge {M : Model p Ω} {ε : ℝ} (t : ℝ≥0) (ω : Ω) : ε ≤ mxe M ε t ω := le_max_right _ _

lemma Ye_meas (M : Model p Ω) (P R ε : ℝ) (t : ℝ≥0) : Measurable[M.F t] (Ye M P R ε t) :=
  (measurable_const.mul (YcM_meas M R t)).div (mxe_meas M ε t)

lemma Ye_bdd (M : Model p Ω) (P R : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ≥0) (ω : Ω) :
    |Ye M P R ε t ω| ≤ |p.σt * (P - p.s)| / ε := by
  have hm : 0 < mxe M ε t ω := hε.trans_le (mxe_ge t ω)
  unfold Ye
  rw [abs_div, abs_mul, abs_of_pos hm]
  calc |p.σt * (P - p.s)| * |YcM M R t ω| / mxe M ε t ω ≤ |p.σt * (P - p.s)| / mxe M ε t ω :=
        div_le_div_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) (YcM_bdd M R t ω))
          hm.le
    _ ≤ |p.σt * (P - p.s)| / ε := div_le_div_of_nonneg_left (abs_nonneg _) hε (mxe_ge t ω)

/-- Pull-out under `P^M`. -/
lemma pullPM (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (R : ℝ) (t : ℝ≥0)
    {Y : Ω → ℝ} (hY : StronglyMeasurable[M.F t] Y) {C : ℝ} (hYb : ∀ ω, |Y ω| ≤ C) :
    ∫ ω, Set.indicator {ω | M.AT ω ≤ R} Y ω ∂M.PM = ∫ ω, Y ω * cAM M R t ω ∂M.PM := by
  have := StochCalcS8b.PM_prob M hM h5
  have hi := ind_int_PM M hM h5 R
  have e2 : (fun ω => Set.indicator {ω | M.AT ω ≤ R} Y ω) =
      fun ω => Y ω * Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)) ω := by
    funext ω; by_cases h : M.AT ω ≤ R <;> simp [Set.indicator, h]
  have hYi : Integrable (fun ω => Y ω * Set.indicator {x | M.AT x ≤ R} (fun _ => (1 : ℝ)) ω)
      M.PM :=
    hi.bdd_mul (hY.mono (M.F.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hYb ω)
  have h1 := condExp_mul_of_stronglyMeasurable_left (m := M.F t) (μ := M.PM) hY hYi hi
  rw [e2, ← integral_condExp (M.F.le t)]
  exact integral_congr_ae h1

/-- The bracket of `low_nY` dominates `g_ε(t)`. -/
theorem bracket_ge (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (P R : ℝ)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ≥0) :
    ge M P R ε t ≤
      2 * ((P - p.s) * p.σt * ∫ ω, Set.indicator {ω | M.AT ω ≤ R} (Ye M P R ε t) ω ∂M.PM) -
        ∫ ω, M.Z p.T ω ^ 2 * Ye M P R ε t ω ^ 2 ∂M.P := by
  have := hM.prob
  have := StochCalcS8b.PM_prob M hM h5
  set a := p.σt * (P - p.s) with ha
  have hYm := Ye_meas M P R ε t
  have hYb := Ye_bdd M P R hε t
  have hYa : Measurable (Ye M P R ε t) := hYm.mono (M.F.le t) le_rfl
  have hmxa : Measurable (mxe M ε t) := (mxe_meas M ε t).mono (M.F.le t) le_rfl
  have hYca : Measurable (YcM M R t) := (YcM_meas M R t).mono (M.F.le t) le_rfl
  have hmpos : ∀ ω, 0 < mxe M ε t ω := fun ω => hε.trans_le (mxe_ge t ω)
  -- g integrable (bounded)
  have hgi : Integrable (fun ω => (a * YcM M R t ω) ^ 2 / mxe M ε t ω) M.PM := by
    refine Integrable.of_bound (C := a ^ 2 / ε)
      (((measurable_const.mul hYca).pow_const 2).div hmxa).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hmpos ω).le)]
    have h1 : (a * YcM M R t ω) ^ 2 ≤ a ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_right (sq_nonneg a) (by
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (YcM_bdd M R t ω))
    calc (a * YcM M R t ω) ^ 2 / mxe M ε t ω ≤ a ^ 2 / mxe M ε t ω :=
          div_le_div_of_nonneg_right h1 (hmpos ω).le
      _ ≤ a ^ 2 / ε := div_le_div_of_nonneg_left (sq_nonneg a) hε (mxe_ge t ω)
  -- first term
  have h1 : (P - p.s) * p.σt * ∫ ω, Set.indicator {ω | M.AT ω ≤ R} (Ye M P R ε t) ω ∂M.PM =
      ge M P R ε t := by
    rw [pullPM M hM h5 R t hYm.stronglyMeasurable hYb, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [YcM_ae M hM h5 R t] with ω hω
    simp only [Ye]
    rw [← hω]
    have h0 := (hmpos ω).ne'
    field_simp
    try ring
  -- second term
  have hZ2 : MemLp (M.Z p.T) 2 M.P := h5.2 p.T le_rfl
  have hZi : Integrable (M.Z p.T) M.PM := int_PM_L2 M h5 hZ2
  have hY2m : StronglyMeasurable[M.F t] (fun ω => Ye M P R ε t ω ^ 2) :=
    (hYm.pow_const 2).stronglyMeasurable
  have hY2b : ∀ ω, ‖Ye M P R ε t ω ^ 2‖ ≤ (|a| / ε) ^ 2 := fun ω => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hYb ω) 2
  have hYZi : Integrable (fun ω => Ye M P R ε t ω ^ 2 * M.Z p.T ω) M.PM :=
    hZi.bdd_mul (hYa.pow_const 2).aestronglyMeasurable (Eventually.of_forall hY2b)
  have hYZMi : Integrable (fun ω => Ye M P R ε t ω ^ 2 * M.ZM t ω) M.PM :=
    integrable_condExp.bdd_mul (hYa.pow_const 2).aestronglyMeasurable (Eventually.of_forall hY2b)
  have h2 : ∫ ω, M.Z p.T ω ^ 2 * Ye M P R ε t ω ^ 2 ∂M.P =
      ∫ ω, Ye M P R ε t ω ^ 2 * M.ZM t ω ∂M.PM := by
    have e : (fun ω => M.Z p.T ω ^ 2 * Ye M P R ε t ω ^ 2) =
        fun ω => M.Z p.T ω * (Ye M P R ε t ω ^ 2 * M.Z p.T ω) := by funext ω; ring
    rw [e, StochCalcS8b.integral_PM M h5, ← integral_condExp (M.F.le t)]
    exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hY2m hYZi hZi)
  have h3 : ∫ ω, Ye M P R ε t ω ^ 2 * M.ZM t ω ∂M.PM ≤ ge M P R ε t := by
    refine integral_mono hYZMi hgi (fun ω => ?_)
    have hm := hmpos ω
    have hz : M.ZM t ω ≤ mxe M ε t ω := le_max_left _ _
    simp only [Ye, ← ha]
    rw [div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hm]
    have : (a * YcM M R t ω) ^ 2 * M.ZM t ω * mxe M ε t ω ≤
        (a * YcM M R t ω) ^ 2 * mxe M ε t ω * mxe M ε t ω :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (sq_nonneg _)) hm.le
    nlinarith [this]
  rw [h1, h2]
  linarith

end StochCalcK2

/-! K2f (relay 3): `ε ↓ 0` in the grid bound; `Z^M_t > 0` `P^M`-a.s. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The grid bound with the weights `Ye`. -/
theorem low_ne (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2) (h5 : M.Assumption5)
    (hne : ¬ (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)))
    (hXM : IsMartingaleOn p.T M.F M.PM M.X)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX) (P R m : ℝ)
    (hmean : ∫ ω, (M.H P R ω + θχ.2 p.T ω) ∂M.P = m) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (M.V0 P R - m) ^ 2 / (M.ZM0 - 1) +
      ∑ k ∈ Finset.range n, ((p.T : ℝ) / n) * ge M P R ε (StochCalcD2.gr p n k) ≤
      ∫ ω, (M.H P R ω + θχ.2 p.T ω - m) ^ 2 ∂M.P := by
  refine le_trans ?_ (low_nY M hM hL2 h5 hne hXM θχ hθ P R m hmean n
    (fun k => Ye M P R ε (StochCalcD2.gr p n k)) (fun k => Ye_meas M P R ε _)
    (|p.σt * (P - p.s)| / ε) (fun k ω => Ye_bdd M P R hε _ ω))
  refine add_le_add le_rfl (Finset.sum_le_sum fun k _ => ?_)
  exact mul_le_mul_of_nonneg_left (bracket_ge M hM h5 P R hε _) (by positivity)

lemma ge_int (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (P R : ℝ)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ≥0) :
    Integrable (fun ω => (p.σt * (P - p.s) * YcM M R t ω) ^ 2 / mxe M ε t ω) M.PM := by
  have := StochCalcS8b.PM_prob M hM h5
  set a := p.σt * (P - p.s)
  have hmxa : Measurable (mxe M ε t) := (mxe_meas M ε t).mono (M.F.le t) le_rfl
  have hYca : Measurable (YcM M R t) := (YcM_meas M R t).mono (M.F.le t) le_rfl
  have hmpos : ∀ ω, 0 < mxe M ε t ω := fun ω => hε.trans_le (mxe_ge t ω)
  refine Integrable.of_bound (C := a ^ 2 / ε)
    (((measurable_const.mul hYca).pow_const 2).div hmxa).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hmpos ω).le)]
  have h1 : (a * YcM M R t ω) ^ 2 ≤ a ^ 2 := by
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg a) (by
      rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (YcM_bdd M R t ω))
  calc (a * YcM M R t ω) ^ 2 / mxe M ε t ω ≤ a ^ 2 / mxe M ε t ω :=
        div_le_div_of_nonneg_right h1 (hmpos ω).le
    _ ≤ a ^ 2 / ε := div_le_div_of_nonneg_left (sq_nonneg a) hε (mxe_ge t ω)

lemma ge_nonneg (M : Model p Ω) (P R : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ≥0) :
    0 ≤ ge M P R ε t :=
  integral_nonneg fun ω => div_nonneg (sq_nonneg _) (hε.le.trans (mxe_ge t ω))

/-- `Z^M_t > 0` `P^M`-a.s. -/
lemma ZM_pos (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (t : ℝ≥0) :
    ∀ᵐ ω ∂M.PM, 0 < M.ZM t ω := by
  have := StochCalcS8b.PM_prob M hM h5
  have hZi : Integrable (M.Z p.T) M.PM := int_PM_L2 M h5 (h5.2 p.T le_rfl)
  have hmeas : StronglyMeasurable[M.F t] (M.ZM t) := stronglyMeasurable_condExp
  have hA : MeasurableSet[M.F t] {ω | M.ZM t ω ≤ 0} :=
    measurableSet_le hmeas.measurable measurable_const
  have hA' : MeasurableSet {ω | M.ZM t ω ≤ 0} := M.F.le t _ hA
  have h : ∫ x in {ω | M.ZM t ω ≤ 0}, M.ZM t x ∂M.PM =
      ∫ x in {ω | M.ZM t ω ≤ 0}, M.Z p.T x ∂M.PM := setIntegral_condExp (M.F.le t) hZi hA
  have h1 : ∫ x in {ω | M.ZM t ω ≤ 0}, M.ZM t x ∂M.PM ≤ 0 :=
    setIntegral_nonpos hA' (fun x hx => hx)
  have h2 : 0 ≤ ∫ x in {ω | M.ZM t ω ≤ 0}, M.Z p.T x ∂M.PM :=
    setIntegral_nonneg hA' (fun x _ => (StochCalcHedge.Z_pos M p.T x).le)
  have h0 : ∫ x in {ω | M.ZM t ω ≤ 0}, M.Z p.T x ∂M.PM = 0 := by linarith
  have hz := (setIntegral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun x => (StochCalcHedge.Z_pos M p.T x).le) hZi.integrableOn).1 h0
  rw [EventuallyEq, ae_restrict_iff' hA'] at hz
  filter_upwards [hz] with ω hω
  by_contra hc
  push_neg at hc
  exact (StochCalcHedge.Z_pos M p.T ω).ne' (by simpa using hω hc)

/-- `G(t) = E^M[(a c^M_t)² / Z^M_t]` (extended). -/
noncomputable def Gt (M : Model p Ω) (P R : ℝ) (t : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((p.σt * (P - p.s) * cAM M R t ω) ^ 2 / M.ZM t ω) ∂M.PM

lemma tendsto_ge (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (P R : ℝ) (t : ℝ≥0) :
    Tendsto (fun N : ℕ => ENNReal.ofReal (ge M P R (1 / ((N : ℝ) + 1)) t)) atTop
      (𝓝 (Gt M P R t)) := by
  have := StochCalcS8b.PM_prob M hM h5
  set a := p.σt * (P - p.s) with ha
  have hεN : ∀ N : ℕ, (0 : ℝ) < 1 / ((N : ℝ) + 1) := fun N => by positivity
  have e : (fun N : ℕ => ENNReal.ofReal (ge M P R (1 / ((N : ℝ) + 1)) t)) =
      fun N : ℕ => ∫⁻ ω, ENNReal.ofReal
        ((a * YcM M R t ω) ^ 2 / mxe M (1 / ((N : ℝ) + 1)) t ω) ∂M.PM := by
    funext N
    exact ofReal_integral_eq_lintegral_ofReal (ge_int M hM h5 P R (hεN N) t)
      (Eventually.of_forall fun ω => div_nonneg (sq_nonneg _) ((hεN N).le.trans (mxe_ge t ω)))
  rw [e]
  have hYca : Measurable (YcM M R t) := (YcM_meas M R t).mono (M.F.le t) le_rfl
  refine lintegral_tendsto_of_tendsto_of_monotone (fun N => ?_) ?_ ?_
  · have hmxa : Measurable (mxe M (1 / ((N : ℝ) + 1)) t) :=
      (mxe_meas M _ t).mono (M.F.le t) le_rfl
    exact (((measurable_const.mul hYca).pow_const 2).div hmxa).ennreal_ofReal.aemeasurable
  · refine Eventually.of_forall fun ω N N' hNN' => ?_
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (sq_nonneg _)
      ((hεN N').trans_le (mxe_ge t ω)) (max_le_max le_rfl ?_))
    exact one_div_le_one_div_of_le (by positivity) (by linarith [(Nat.cast_le (α := ℝ)).2 hNN'])
  · filter_upwards [YcM_ae M hM h5 R t, ZM_pos M hM h5 t] with ω h1 h2
    rw [← h1]
    refine ENNReal.tendsto_ofReal (tendsto_const_nhds.div ?_ h2.ne')
    have := (tendsto_const_nhds (x := M.ZM t ω)).max tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [max_eq_left h2.le] at this

/-- The grid bound with `G` (extended reals). -/
theorem low_nG (M : Model p Ω) (hM : M.Standing) (hL2 : M.NegPartL2) (h5 : M.Assumption5)
    (hne : ¬ (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)))
    (hXM : IsMartingaleOn p.T M.F M.PM M.X)
    (θχ : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hθ : θχ ∈ M.AX) (P R m : ℝ)
    (hmean : ∫ ω, (M.H P R ω + θχ.2 p.T ω) ∂M.P = m) (n : ℕ) :
    ENNReal.ofReal ((M.V0 P R - m) ^ 2 / (M.ZM0 - 1)) +
      ∑ k ∈ Finset.range n, ENNReal.ofReal ((p.T : ℝ) / n) * Gt M P R (StochCalcD2.gr p n k) ≤
      ENNReal.ofReal (∫ ω, (M.H P R ω + θχ.2 p.T ω - m) ^ 2 ∂M.P) := by
  have hc0 : 0 ≤ (M.V0 P R - m) ^ 2 / (M.ZM0 - 1) :=
    div_nonneg (sq_nonneg _) (by linarith [StochCalcHedge.one_lt_ZM0 M hM h5 hne])
  have hN : ∀ N : ℕ, ENNReal.ofReal ((M.V0 P R - m) ^ 2 / (M.ZM0 - 1)) +
      ∑ k ∈ Finset.range n, ENNReal.ofReal ((p.T : ℝ) / n) *
        ENNReal.ofReal (ge M P R (1 / ((N : ℝ) + 1)) (StochCalcD2.gr p n k)) ≤
      ENNReal.ofReal (∫ ω, (M.H P R ω + θχ.2 p.T ω - m) ^ 2 ∂M.P) := by
    intro N
    have hε : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    have h := low_ne M hM hL2 h5 hne hXM θχ hθ P R m hmean n hε
    have hT : (0 : ℝ) ≤ (p.T : ℝ) / n := by positivity
    simp_rw [← ENNReal.ofReal_mul hT]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg hT (ge_nonneg M P R hε _)),
      ← ENNReal.ofReal_add hc0 (Finset.sum_nonneg fun k _ => mul_nonneg hT (ge_nonneg M P R hε _))]
    exact ENNReal.ofReal_le_ofReal h
  refine le_of_tendsto' (tendsto_const_nhds.add (tendsto_finset_sum _ fun k _ =>
    ENNReal.Tendsto.const_mul (tendsto_ge M hM h5 P R _) (Or.inr ENNReal.ofReal_ne_top))) hN

end StochCalcK2

/-! K2g (relay 3): `G(u) = E_P[Z_u/Z^M_u δ_u²]`, `G` monotone and bounded. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

lemma ofReal_int_le {f : Ω → ℝ} (hf : Integrable f μ) :
    ENNReal.ofReal (∫ ω, f ω ∂μ) ≤ ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
  calc ENNReal.ofReal (∫ ω, f ω ∂μ) ≤ ENNReal.ofReal (∫ ω, max (f ω) 0 ∂μ) :=
        ENNReal.ofReal_le_ofReal (integral_mono hf hf.pos_part fun ω => le_max_left _ _)
    _ = ∫⁻ ω, ENNReal.ofReal (max (f ω) 0) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hf.pos_part
          (Eventually.of_forall fun ω => le_max_right _ _)
    _ = ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
        congr 1; funext ω; simp [ENNReal.ofReal_max]

/-- `E[c · E[X|m]] = E[c X]` for bounded `m`-measurable `c`. -/
lemma int_mul_condExp {m : MeasurableSpace Ω} (hm : m ≤ mΩ) [IsFiniteMeasure μ]
    {c X : Ω → ℝ} (hc : StronglyMeasurable[m] c) {C : ℝ} (hcb : ∀ ω, |c ω| ≤ C)
    (hX : Integrable X μ) :
    ∫ ω, c ω * condExp m μ X ω ∂μ = ∫ ω, c ω * X ω ∂μ := by
  have hcX : Integrable (fun ω => c ω * X ω) μ :=
    hX.bdd_mul (hc.mono hm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hcb ω)
  rw [← integral_condExp hm (f := fun ω => c ω * X ω)]
  exact (integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hc hcX hX)).symm

end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Lebesgue form of the `P`-martingale property of `Z`. -/
lemma lint_mart (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) {u : ℝ≥0}
    (hu : u ≤ p.T) {g : Ω → ℝ≥0∞} (hg : Measurable[M.F u] g) :
    ∫⁻ ω, ENNReal.ofReal (M.Z p.T ω) * g ω ∂M.P =
      ∫⁻ ω, ENNReal.ofReal (M.Z u ω) * g ω ∂M.P := by
  have := hM.prob
  have hle := M.F.le u
  have hZT : Measurable (M.Z p.T) := StochCalcHedge.Z_T_measurable M h5
  have hZu : Measurable (M.Z u) := ((h5.1.1 u hu).mono hle).measurable
  have hg' : Measurable g := hg.mono hle le_rfl
  have hiT : Integrable (M.Z p.T) M.P := h5.1.2.1 p.T le_rfl
  have hiu : Integrable (M.Z u) M.P := h5.1.2.1 u hu
  have key : (M.P.withDensity fun ω => ENNReal.ofReal (M.Z p.T ω)).trim hle =
      (M.P.withDensity fun ω => ENNReal.ofReal (M.Z u ω)).trim hle := by
    refine @Measure.ext Ω (M.F u) _ _ fun s hs => ?_
    rw [trim_measurableSet_eq hle hs, trim_measurableSet_eq hle hs,
      withDensity_apply _ (hle _ hs), withDensity_apply _ (hle _ hs),
      ← ofReal_integral_eq_lintegral_ofReal hiT.integrableOn
        (Eventually.of_forall fun ω => (StochCalcHedge.Z_pos M _ ω).le),
      ← ofReal_integral_eq_lintegral_ofReal hiu.integrableOn
        (Eventually.of_forall fun ω => (StochCalcHedge.Z_pos M _ ω).le)]
    congr 1
    rw [← setIntegral_condExp hle hiT hs]
    exact setIntegral_congr_ae (hle _ hs)
      (by filter_upwards [h5.1.2.2 u p.T hu le_rfl] with ω h _; exact h)
  calc ∫⁻ ω, ENNReal.ofReal (M.Z p.T ω) * g ω ∂M.P
        = ∫⁻ ω, g ω ∂(M.P.withDensity fun ω => ENNReal.ofReal (M.Z p.T ω)) :=
          (lintegral_withDensity_eq_lintegral_mul _ hZT.ennreal_ofReal hg').symm
    _ = ∫⁻ ω, g ω ∂((M.P.withDensity fun ω => ENNReal.ofReal (M.Z p.T ω)).trim hle) :=
          (lintegral_trim hle hg).symm
    _ = ∫⁻ ω, g ω ∂((M.P.withDensity fun ω => ENNReal.ofReal (M.Z u ω)).trim hle) := by
          rw [key]
    _ = ∫⁻ ω, g ω ∂(M.P.withDensity fun ω => ENNReal.ofReal (M.Z u ω)) := lintegral_trim hle hg
    _ = ∫⁻ ω, ENNReal.ofReal (M.Z u ω) * g ω ∂M.P :=
          lintegral_withDensity_eq_lintegral_mul _ hZu.ennreal_ofReal hg'

lemma delta_eq_cAM (M : Model p Ω) (P R : ℝ) (t : ℝ≥0) (ω : Ω) :
    M.delta P R t ω = p.σt * (P - p.s) * cAM M R t ω := rfl

/-- `G(u) = E_P[(Z_u / Z^M_u) δ_u²]` for `u ≤ T`. -/
theorem Gt_eq (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (P R : ℝ) {u : ℝ≥0}
    (hu : u ≤ p.T) :
    Gt M P R u = ∫⁻ ω, ENNReal.ofReal (M.Z u ω / M.ZM u ω * M.delta P R u ω ^ 2) ∂M.P := by
  have hZT : Measurable (M.Z p.T) := StochCalcHedge.Z_T_measurable M h5
  have hc : Measurable[M.F u] (cAM M R u) := stronglyMeasurable_condExp.measurable
  have hz : Measurable[M.F u] (M.ZM u) := stronglyMeasurable_condExp.measurable
  have hf : Measurable[M.F u] (fun ω => ENNReal.ofReal
      ((p.σt * (P - p.s) * cAM M R u ω) ^ 2 / M.ZM u ω)) :=
    (((measurable_const.mul hc).pow_const 2).div hz).ennreal_ofReal
  unfold Gt Model.PM
  rw [lintegral_withDensity_eq_lintegral_mul _ hZT.ennreal_ofReal (hf.mono (M.F.le u) le_rfl)]
  refine (lint_mart M hM h5 hu hf).trans ?_
  congr 1; funext ω
  rw [← ENNReal.ofReal_mul (StochCalcHedge.Z_pos M u ω).le, delta_eq_cAM]
  congr 1; ring

/-- `G(u) ≤ (σ̃(P-s))²`. -/
theorem Gt_le (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (P R : ℝ) {u : ℝ≥0}
    (hu : u ≤ p.T) : Gt M P R u ≤ ENNReal.ofReal ((p.σt * (P - p.s)) ^ 2) := by
  have := hM.prob
  rw [Gt_eq M hM h5 P R hu]
  calc ∫⁻ ω, ENNReal.ofReal (M.Z u ω / M.ZM u ω * M.delta P R u ω ^ 2) ∂M.P
      ≤ ∫⁻ _, ENNReal.ofReal ((p.σt * (P - p.s)) ^ 2) ∂M.P := by
        refine lintegral_mono_ae ?_
        filter_upwards [StochCalcS8b.Z_div_ZM_nonneg M h5 u, StochCalcS8b.Z_div_ZM_le_one M hM h5 u hu,
          (StochCalcS8b.P_ac_PM M h5).ae_le (cAM_bounds M hM h5 R u)] with ω h1 h2 h3
        refine ENNReal.ofReal_le_ofReal ?_
        rw [delta_eq_cAM, mul_pow]
        have hc2 : cAM M R u ω ^ 2 ≤ 1 := by nlinarith [h3.1, h3.2]
        have hd : (p.σt * (P - p.s)) ^ 2 * cAM M R u ω ^ 2 ≤ (p.σt * (P - p.s)) ^ 2 :=
          mul_le_of_le_one_right (sq_nonneg _) hc2
        nlinarith [mul_nonneg (sq_nonneg (p.σt * (P - p.s))) (sq_nonneg (cAM M R u ω))]
    _ = ENNReal.ofReal ((p.σt * (P - p.s)) ^ 2) := by simp

/-- `G` is monotone on `[0, T]`. -/
theorem Gt_mono (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (P R : ℝ) {s t : ℝ≥0}
    (hst : s ≤ t) (ht : t ≤ p.T) : Gt M P R s ≤ Gt M P R t := by
  have := hM.prob
  have := StochCalcS8b.PM_prob M hM h5
  set a := p.σt * (P - p.s) with ha
  refine le_of_tendsto' (tendsto_ge M hM h5 P R s) fun N => ?_
  have hε : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  set ε := 1 / ((N : ℝ) + 1)
  set c := Ye M P R ε s with hcdef
  have hcm : Measurable[M.F s] c := Ye_meas M P R ε s
  have hcb : ∀ ω, |c ω| ≤ |a| / ε := Ye_bdd M P R hε s
  have hcmt : StronglyMeasurable[M.F t] c := (hcm.mono (M.F.mono hst) le_rfl).stronglyMeasurable
  have hca : Measurable c := hcm.mono (M.F.le s) le_rfl
  have hc2b : ∀ ω, |c ω ^ 2| ≤ (|a| / ε) ^ 2 := fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hcb ω) 2
  have hc2t : StronglyMeasurable[M.F t] (fun ω => c ω ^ 2) :=
    ((hcm.pow_const 2).mono (M.F.mono hst) le_rfl).stronglyMeasurable
  have hind := ind_int_PM M hM h5 R
  have hZi : Integrable (M.Z p.T) M.PM := int_PM_L2 M h5 (h5.2 p.T le_rfl)
  have i1 : Integrable (fun ω => c ω * cAM M R t ω) M.PM :=
    integrable_condExp.bdd_mul hca.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hcb ω)
  have i2 : Integrable (fun ω => c ω ^ 2 * M.ZM t ω) M.PM :=
    integrable_condExp.bdd_mul (hca.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hc2b ω)
  have hlin : Integrable (fun ω => 2 * a * (c ω * cAM M R t ω) - c ω ^ 2 * M.ZM t ω) M.PM :=
    (i1.const_mul (2 * a)).sub i2
  -- the linear lower bound
  have hval : ∫ ω, (2 * a * (c ω * cAM M R t ω) - c ω ^ 2 * M.ZM t ω) ∂M.PM =
      2 * ((P - p.s) * p.σt * ∫ ω, Set.indicator {ω | M.AT ω ≤ R} c ω ∂M.PM) -
        ∫ ω, M.Z p.T ω ^ 2 * c ω ^ 2 ∂M.P := by
    rw [integral_sub (i1.const_mul (2 * a)) i2, integral_const_mul]
    have e1 : ∫ ω, c ω * cAM M R t ω ∂M.PM = ∫ ω, Set.indicator {ω | M.AT ω ≤ R} c ω ∂M.PM := by
      rw [cAM, int_mul_condExp (M.F.le t) hcmt hcb hind]
      congr 1; funext ω; by_cases h : M.AT ω ≤ R <;> simp [Set.indicator, h]
    have e2 : ∫ ω, c ω ^ 2 * M.ZM t ω ∂M.PM = ∫ ω, M.Z p.T ω ^ 2 * c ω ^ 2 ∂M.P := by
      rw [Model.ZM, int_mul_condExp (M.F.le t) hc2t hc2b hZi, ← StochCalcS8b.integral_PM M h5]
      congr 1; funext ω; ring
    rw [e1, e2, ha]; ring
  have hbr := bracket_ge M hM h5 P R hε s
  rw [← hval] at hbr
  calc ENNReal.ofReal (ge M P R ε s)
      ≤ ENNReal.ofReal (∫ ω, (2 * a * (c ω * cAM M R t ω) - c ω ^ 2 * M.ZM t ω) ∂M.PM) :=
        ENNReal.ofReal_le_ofReal hbr
    _ ≤ ∫⁻ ω, ENNReal.ofReal (2 * a * (c ω * cAM M R t ω) - c ω ^ 2 * M.ZM t ω) ∂M.PM :=
        ofReal_int_le hlin
    _ ≤ Gt M P R t := by
        refine lintegral_mono_ae ?_
        filter_upwards [ZM_pos M hM h5 t] with ω hy
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ hy]
        nlinarith [sq_nonneg (a * cAM M R t ω - c ω * M.ZM t ω)]

end StochCalcK2

/-! K2h (relay 3): Riemann sums and the assembled lower bound K2. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `u ↦ G(min(u⁺, T))` as a real function (globally monotone). -/
noncomputable def fK (M : Model p Ω) (P R : ℝ) (u : ℝ) : ℝ :=
  (Gt M P R (min u.toNNReal p.T)).toReal

lemma Gt_ne_top (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (P R : ℝ) {u : ℝ≥0}
    (hu : u ≤ p.T) : Gt M P R u ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (Gt_le M hM h5 P R hu)

lemma fK_mono (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (P R : ℝ) :
    Monotone (fK M P R) := fun u v huv => by
  unfold fK
  refine ENNReal.toReal_mono (Gt_ne_top M hM h5 P R (min_le_right _ _)) ?_
  exact Gt_mono M hM h5 P R (min_le_min_right _ (Real.toNNReal_le_toNNReal huv)) (min_le_right _ _)

lemma fK_nonneg (M : Model p Ω) (P R u : ℝ) : 0 ≤ fK M P R u := ENNReal.toReal_nonneg

lemma fK_le (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) (P R u : ℝ) :
    fK M P R u ≤ (p.σt * (P - p.s)) ^ 2 :=
  ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) (Gt_le M hM h5 P R (min_le_right _ _))

/-- K2: the lower bound of (21). -/
theorem K2 (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hne : ¬ (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)))
    (hXM : IsMartingaleOn p.T M.F M.PM M.X) (m P R : ℝ) :
    ENNReal.ofReal ((m - M.V0 P R) ^ 2 / (M.ZM0 - 1)) +
        ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ∫⁻ ω,
          ENNReal.ofReal (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * M.delta P R u.toNNReal ω ^ 2)
            ∂M.P ≤ M.Bval m P R := by
  have := hM.prob
  unfold Model.Bval
  refine le_iInf₂ fun θχ hθ => le_iInf fun hmean => ?_
  set a := p.σt * (P - p.s) with ha
  have hin : ∀ u ∈ Set.Icc (0 : ℝ) (p.T : ℝ), ∫⁻ ω, ENNReal.ofReal
      (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * M.delta P R u.toNNReal ω ^ 2) ∂M.P =
      ENNReal.ofReal (fK M P R u) := by
    intro u hu
    have huT : u.toNNReal ≤ p.T := Real.toNNReal_le_iff_le_coe.2 hu.2
    unfold fK
    rw [min_eq_left huT, ENNReal.ofReal_toReal (Gt_ne_top M hM h5 P R huT), Gt_eq M hM h5 P R huT]
  rw [lintegral_congr_ae ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hin))]
  have hmono := fK_mono M hM h5 P R
  have hFint : IntegrableOn (fK M P R) (Set.Icc 0 (p.T : ℝ)) :=
    (hmono.monotoneOn _).integrableOn_isCompact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hFint (ae_of_all _ fun u => fK_nonneg M P R u)]
  have hTpos : (0 : ℝ) < p.T := by exact_mod_cast p.hT
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hTpos.le]
  -- the variance
  have hU : MemLp (fun ω => M.H P R ω + θχ.2 p.T ω) 2 M.P :=
    (StochCalcHedgeDeg.H_memLp M hM hL2 P R).add hθ.2.2.2.1
  have hvar : evariance (fun ω => M.H P R ω + θχ.2 p.T ω) M.P =
      ENNReal.ofReal (∫ ω, (M.H P R ω + θχ.2 p.T ω - m) ^ 2 ∂M.P) := by
    rw [← hU.ofReal_variance_eq, variance_eq_integral hU.aestronglyMeasurable.aemeasurable, hmean]
  rw [hvar]
  have hsq : (m - M.V0 P R) ^ 2 = (M.V0 P R - m) ^ 2 := by ring
  rw [hsq]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨n, hn⟩ := exists_nat_gt ((p.T : ℝ) * a ^ 2 / ε)
  have hn0 : 0 < n := by
    have : (0 : ℝ) ≤ (p.T : ℝ) * a ^ 2 / ε := by positivity
    exact_mod_cast this.trans_lt hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have h1 := StochCalcP6.integral_le_left_sum hTpos (hmono.monotoneOn _) n hn0
  have hT0 : (0 : ℝ) ≤ (p.T : ℝ) / n := by positivity
  have h2 : ENNReal.ofReal (∑ i ∈ Finset.range n, ((p.T : ℝ) / n) * fK M P R (i * ((p.T : ℝ) / n))) =
      ∑ k ∈ Finset.range n, ENNReal.ofReal ((p.T : ℝ) / n) * Gt M P R (StochCalcD2.gr p n k) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg hT0 (fK_nonneg M P R _))]
    refine Finset.sum_congr rfl fun k hkm => ?_
    have hc : ((StochCalcD2.gr p n k : ℝ≥0) : ℝ) = (k : ℝ) * ((p.T : ℝ) / n) := by
      unfold StochCalcD2.gr; push_cast; ring
    have hk : ((k : ℝ) * ((p.T : ℝ) / n)).toNNReal = StochCalcD2.gr p n k := by
      rw [← hc, Real.toNNReal_coe]
    have hkT : StochCalcD2.gr p n k ≤ p.T :=
      StochCalcD2.gr_le_T p (Finset.mem_range.1 hkm).le
    rw [ENNReal.ofReal_mul hT0, fK, hk, min_eq_left hkT,
      ENNReal.ofReal_toReal (Gt_ne_top M hM h5 P R hkT)]
  have h3 : ((p.T : ℝ) / n) * (fK M P R p.T - fK M P R 0) ≤ ε := by
    have hb := fK_le M hM h5 P R p.T
    have hb0 := fK_nonneg M P R 0
    calc ((p.T : ℝ) / n) * (fK M P R p.T - fK M P R 0)
        ≤ ((p.T : ℝ) / n) * a ^ 2 := mul_le_mul_of_nonneg_left (by linarith) hT0
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hnr]
          have := (div_lt_iff₀ hεr).1 hn
          linarith
  have h4 := low_nG M hM hL2 h5 hne hXM θχ hθ P R m hmean n
  rw [← h2] at h4
  calc ENNReal.ofReal ((M.V0 P R - m) ^ 2 / (M.ZM0 - 1)) +
        ENNReal.ofReal (∫ x in (0 : ℝ)..p.T, fK M P R x)
      ≤ ENNReal.ofReal ((M.V0 P R - m) ^ 2 / (M.ZM0 - 1)) +
        (ENNReal.ofReal (∑ i ∈ Finset.range n, ((p.T : ℝ) / n) * fK M P R (i * ((p.T : ℝ) / n)))
          + ENNReal.ofReal ε) := by
        gcongr
        exact (ENNReal.ofReal_le_ofReal (h1.trans (by linarith))).trans ENNReal.ofReal_add_le
    _ = (ENNReal.ofReal ((M.V0 P R - m) ^ 2 / (M.ZM0 - 1)) +
        ENNReal.ofReal (∑ i ∈ Finset.range n, ((p.T : ℝ) / n) * fK M P R (i * ((p.T : ℝ) / n))))
          + ENNReal.ofReal ε := by rw [add_assoc]
    _ ≤ ENNReal.ofReal (∫ ω, (M.H P R ω + θχ.2 p.T ω - m) ^ 2 ∂M.P) + ε := by
        rw [ENNReal.ofReal_coe_nnreal]; gcongr

end StochCalcK2

/-! K3H (8c066573 relay 11): abstract Hilbert-space glue for the upper bound K3 of HedgePSNV.theorem_1_ii.
E = L²(F_T, P), one = 1, z = Z_T, h = H, A = admissible gains {χ_T}, N = span{Z_T γ ξ_k} (B̃-part of the
dual space).  Completeness `hcomp` (f ⊥ 1, A, N ⇒ f = 0) is the martingale-representation input. -/

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace StochCalcK3H

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]





section Fn

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]



end Fn

end StochCalcK3H

/-! K3M0 (8c066573 relay 11): model-level glue.  `HedgePSNV.theorem_1_ii_upper_bound`'s conclusion from the
obligations M1-M6 of scratch/decomp/8c066573.K3plan.md, stated on `P` (F_T-measurable functions), via
`StochCalcK3H.fn_upper` on `P.trim (F_T ≤ m)`.  Append after K3H.lean (needs Definitions.Def_HedgePSNV_Hedging). -/

namespace StochCalcK3M0

open MeasureTheory ProbabilityTheory HedgePSNV
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]



end StochCalcK3M0
/-! K3M1 (8c066573 relay 12): the easy obligations of `StochCalcK3M0.K3_of_obl`:
`A_X` contains `0` and is closed under `+` and scalar multiples (linearity of the Ito relation and
of `IsMartingaleOn`), `Z_T`/`H` measurability and `L²`, `E Z_T = 1`, `1 < E Z_T²`, `V0 = E[H Z_T]`,
`E[Z_T χ_T] = 0`.  `K3_of_N` is then K3 from the `N`-class obligations, `hcomp` (M6) and `hbd` (M5).
Append after K3H + K3M0_tail (on top of the K2 dev chain probe/8c066573_K2h.lean). -/

namespace StochCalcK3M1

open MeasureTheory ProbabilityTheory Filter HedgePSNV EthierKurtz ItoLib
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]













variable {p : Params}









end StochCalcK3M1
/-! K3M2 (8c066573 relay 12): the class `N` of `Z_T`-weighted `B~`-grid sums
`n = Z_T * Σ_{k<n} Y_k ξ(t_k, t_{k+1})` (uniform grid `t_k = k T / n` of K2, `Y_k` bounded
`F_{t_k}`-measurable) and its obligations in `StochCalcK3M1.K3_of_N`: `L²`, `F_T`-measurability,
`0`, closure under `+` (common refinement `n * n'`) and scalar multiples, orthogonality to the
gains `χ_T` (under `P^M`), to `1` and to `Z_T`.  `K3_of_M56` = K3 from M5 (`hbd`) and M6 (`hcomp`)
for this class.  Append after K3M1_tail. -/

namespace StochCalcK3M2

open MeasureTheory ProbabilityTheory Filter HedgePSNV
open StochCalcBr StochCalcGauss StochCalcTiltM StochCalcSteinM StochCalcHedge StochCalcS8b
  StochCalcK2 StochCalcD2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]


















end StochCalcK3M2
/-! K3M5 (8c066573 relay 13): obligation M5 of `StochCalcK3M2.K3_of_M56`.  For
`f = Z_T * Σ_k Y_k ξ_k` in the grid class `NC`, `(E_P[H f])² ≤ Ψ E_P[f²]` with
`Ψ = ∫_0^T fK` (= the target `∫ E_P[(Z_u/Z^M_u) δ_u²] du`).  Proof: Stein under `P^M` turns
`E_P[H f]` into `Σ (T/n) E^M[a c^M_{t_k} Y_k]`; the tower property turns `E_P[f²]` into
`Σ (T/n) E^M[Z^M_{t_k} Y_k²]`; a weighted AM-GM bound for every `λ > 0` gives Cauchy-Schwarz;
the left Riemann sum of the monotone `fK` is below its integral.  `K3_of_M6` = K3 from M6
(`hcomp`) only.  Append after K3M2_tail. -/

namespace StochCalcK3M5

open MeasureTheory ProbabilityTheory Filter HedgePSNV
open StochCalcBr StochCalcGauss StochCalcTiltM StochCalcSteinM StochCalcHedge StochCalcS8b
  StochCalcK2 StochCalcD2 StochCalcK3M2
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]










end StochCalcK3M5

/-! K3G (8c066573 relay 39): K3 (upper bound of (21)) from `K3_of_M6` + `hcomp`, with the
continuity hypothesis `ContHyp M` (conjunct 3 of platform theorem 1c98c8e0) kept explicit. -/

namespace StochCalcK3G

open MeasureTheory ProbabilityTheory Filter HedgePSNV
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcK3G

end StochCalcP6


open MeasureTheory ProbabilityTheory HedgePSNV in
open scoped NNReal ENNReal in
theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hne : ¬ (M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)))
    (hXM : IsMartingaleOn p.T M.F M.PM M.X) (m P R : ℝ) :
    ENNReal.ofReal ((m - M.V0 P R) ^ 2 / (M.ZM0 - 1)) +
        ∫⁻ u in Set.Icc (0 : ℝ) (p.T : ℝ), ∫⁻ ω,
          ENNReal.ofReal (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * M.delta P R u.toNNReal ω ^ 2)
            ∂M.P ≤ M.Bval m P R := by
  exact StochCalcP6.StochCalcK2.K2 M hM hL2 h4 h5 hne hXM m P R
