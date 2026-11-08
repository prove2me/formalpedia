-- Prove2me | solution 1 for HedgePSNV.hedging_completeness
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T19:44:07.826069+00:00
-- url     : https://prove2.me/submissions/71be06cb-6e2a-4d27-9a5f-18e9e25b109d

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Theorems.Thm_HedgePSNV_girsanov_density_ito
import Theorems.Thm_HedgePSNV_tilted_orthogonality_vanish
import Theorems.Thm_HedgePSNV_grid_sums_dense_L2
import Theorems.Thm_HedgePSNV_tilted_bayes_conditional_expectation
import Theorems.Thm_HedgePSNV_asset_price_zero_set_null
import Theorems.Thm_HedgePSNV_orthogonal_claim_integrand_relation
import Theorems.Thm_HedgePSNV_eta_ito_integral_continuous_version
import Theorems.Thm_EthierKurtz_brownian_ito_integral_locality_and_continuity

set_option maxHeartbeats 2000000
set_option linter.all false
set_option Elab.async false











-- ===== slice of Solutions.Sol_pv_1558a108 (scratch/probe/slice8c/cuts/gK4c.lean.src/Solutions.Sol_pv_1558a108.lean): 6/153 top-level decls kept =====

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


-- ===== slice of P8c066573M16 (scratch/probe/slice8c/cuts/gK4c.lean.src/P8c066573M16.lean): 177/865 top-level decls kept =====

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

lemma G_le_F (M : Model p Ω) (hM : M.Standing) (t : ℝ≥0) : M.G t ≤ M.F t := by
  rw [hM.filtG t, hM.filtF t]
  refine sup_le_sup_right (iSup₂_mono fun s _ => ?_) _
  have h : M.B s = Prod.fst ∘ (fun ω => (M.B s ω, M.Bt s ω)) := rfl
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_fst.comap_le









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

/-- The integrand `Xσ`. -/
def Hx (M : Model p Ω) (t : ℝ≥0) (ω : Ω) : ℝ := M.X t ω * M.σ t ω











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












end StochCalcR1M

/-! R4 (relay 13): the class `IsGS` of grid sums `c + Σ Y_k ΔB_k + Σ Z_k ΔB~_k` (bounded adapted
coefficients on a uniform grid) is a vector space of `F_T`-measurable `L²` functions. -/

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



lemma memLp_trim_of {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure[m0] Ω} (hm : m ≤ m0)
    {f : Ω → ℝ} (hf : StronglyMeasurable[m] f) (h : MemLp f 2 μ) : MemLp f 2 (μ.trim hm) :=
  ⟨hf.aestronglyMeasurable, by rw [eLpNorm_trim hm hf]; exact h.2⟩

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







/-- **R7b (hsep).** On `(Ω, F_T, P)`, an `L²` variable orthogonal to all grid sums vanishes. -/
theorem hsep (M : Model p Ω) (hM : M.Standing) (V : Ω → ℝ)
    (hV : MemLp V 2 (M.P.trim (M.F.le p.T)))
    (horth : ∀ f, IsGS M f → ∫ ω, V ω * f ω ∂(M.P.trim (M.F.le p.T)) = 0) :
    V =ᵐ[M.P.trim (M.F.le p.T)] 0 := by
  exact HedgePSNV.grid_sums_dense_L2 M hM V hV horth





























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


lemma X_measF (M : Model p Ω) (hM : M.Standing) (u : ℝ≥0) : StronglyMeasurable[M.F u] (M.X u) :=
  (hM.X_adapted u).mono (G_le_F M hM u)









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

omit [CompleteSpace E] [CompleteSpace F] in
lemma inner_map_eq (e : S →ₗ[ℝ] E) (T : S →ₗ[ℝ] F) (hT : ∀ s, ‖T s‖ = ‖e s‖) (s t : S) :
    ⟪T s, T t⟫_ℝ = ⟪e s, e t⟫_ℝ := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← map_add, ← map_add, hT, hT, hT]

/-- **O3 core (Riesz via isometry).** -/
theorem riesz_isom (e : S →ₗ[ℝ] E) (T : S →ₗ[ℝ] F) (hT : ∀ s, ‖T s‖ = ‖e s‖) (f : F) :
    ∃ a : E, ∀ s : S, ⟪f, T s⟫_ℝ = ⟪a, e s⟫_ℝ := by
  set K : Submodule ℝ F := (LinearMap.range T).topologicalClosure with hK
  have : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set f' : F := K.starProjection f with hf'
  have hperp : ∀ s, ⟪f, T s⟫_ℝ = ⟪f', T s⟫_ℝ := by
    intro s
    have hmem : T s ∈ K := Submodule.le_topologicalClosure _ (LinearMap.mem_range_self T s)
    have h0 := (Submodule.mem_orthogonal' K _).1 (K.sub_starProjection_mem_orthogonal f) (T s) hmem
    rw [inner_sub_left] at h0
    linarith
  have hf'mem : f' ∈ closure (Set.range T) := by
    have h : f' ∈ K := K.starProjection_apply_mem f
    rw [hK, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range] at h
    exact h
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hf'mem
  choose v hv using hu
  have hc : CauchySeq fun n => e (v n) := by
    have hcu : CauchySeq u := hlim.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm, ← map_sub, ← hT, map_sub, hv, hv, ← dist_eq_norm]
    exact hN m hm n hn
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨a, fun s => ?_⟩
  rw [hperp]
  have h1 : Tendsto (fun n => ⟪u n, T s⟫_ℝ) atTop (𝓝 ⟪f', T s⟫_ℝ) :=
    hlim.inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪e (v n), e s⟫_ℝ) atTop (𝓝 ⟪a, e s⟫_ℝ) :=
    ha.inner tendsto_const_nhds
  have h3 : (fun n => ⟪u n, T s⟫_ℝ) = fun n => ⟪e (v n), e s⟫_ℝ := by
    funext n; rw [← hv, inner_map_eq e T hT]
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- `a` can be taken in the closure of the range of `e` (uniqueness of the integrand there). -/
theorem riesz_isom_mem (e : S →ₗ[ℝ] E) (T : S →ₗ[ℝ] F) (hT : ∀ s, ‖T s‖ = ‖e s‖) (f : F) :
    ∃ a : E, a ∈ (LinearMap.range e).topologicalClosure ∧ ∀ s : S, ⟪f, T s⟫_ℝ = ⟪a, e s⟫_ℝ := by
  obtain ⟨a, ha⟩ := riesz_isom e T hT f
  set L : Submodule ℝ E := (LinearMap.range e).topologicalClosure with hL
  have : CompleteSpace L := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  refine ⟨L.starProjection a, L.starProjection_apply_mem a, fun s => ?_⟩
  rw [ha s]
  have hmem : e s ∈ L := Submodule.le_topologicalClosure _ (LinearMap.mem_range_self e s)
  have h0 := (Submodule.mem_orthogonal' L _).1 (L.sub_starProjection_mem_orthogonal a) (e s) hmem
  rw [inner_sub_left] at h0
  linarith

end StochCalcRiesz

/-! O3gen (8c066573 relay 17, O3 instantiation, generic; append after RieszIso.lean, Mathlib only).
For a real process `W` with independent centred increments of variance `v - u` w.r.t. a monotone family
`m t` of σ-algebras, every `f ∈ L²(P)` has a representing integrand `a ∈ L²(dt|[0,T] ⊗ P)` (in the closure of
the adapted simple processes) with `E[f · Y (W_v - W_u)] = ∫∫ a · 1_[u,v) Y` for all bounded `m u`-measurable `Y`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Increment hypotheses on a real process `W` w.r.t. a family of σ-algebras `m`. -/
structure IncrHyp (m : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop where
  mono : Monotone m
  le : ∀ t, m t ≤ mΩ
  adapt : ∀ t, Measurable[m t] (W t)
  indep : ∀ u v, u ≤ v →
    Indep (m u) (MeasurableSpace.comap (fun ω => W v ω - W u ω) inferInstance) P
  mem2 : ∀ u v, MemLp (fun ω => W v ω - W u ω) 2 P
  mean : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ∂P = 0
  var : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ^ 2 ∂P = (v : ℝ) - u

variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

lemma dW_meas (hW : IncrHyp m W P) {u v : ℝ≥0} (huv : u ≤ v) :
    Measurable[m v] (fun ω => W v ω - W u ω) :=
  (hW.adapt v).sub ((hW.adapt u).mono (hW.mono huv) le_rfl)

lemma dW_measAmb (hW : IncrHyp m W P) (u v : ℝ≥0) : Measurable (fun ω => W v ω - W u ω) :=
  ((hW.adapt v).mono (hW.le v) le_rfl).sub ((hW.adapt u).mono (hW.le u) le_rfl)

lemma int_mul_dW (hW : IncrHyp m W P) {c d : ℝ≥0} (hcd : c ≤ d) {g : Ω → ℝ}
    (hg : Measurable[m c] g) : ∫ ω, g ω * (W d ω - W c ω) ∂P = 0 := by
  have hind : IndepFun g (fun ω => W d ω - W c ω) P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left (hW.indep c d hcd) hg.comap_le
  rw [hind.integral_fun_mul_eq_mul_integral (hg.mono (hW.le c) le_rfl).aestronglyMeasurable
    (dW_measAmb hW c d).aestronglyMeasurable, hW.mean c d hcd, mul_zero]

lemma int_mul_dW_sq (hW : IncrHyp m W P) {c d : ℝ≥0} (hcd : c ≤ d) {g : Ω → ℝ}
    (hg : Measurable[m c] g) :
    ∫ ω, g ω * (W d ω - W c ω) ^ 2 ∂P = (∫ ω, g ω ∂P) * ((d : ℝ) - c) := by
  have hind : IndepFun g (fun ω => (W d ω - W c ω) ^ 2) P := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (hW.indep c d hcd) hg.comap_le) ?_
    exact ((comap_measurable (fun ω => W d ω - W c ω)).pow_const 2).comap_le
  rw [hind.integral_fun_mul_eq_mul_integral (hg.mono (hW.le c) le_rfl).aestronglyMeasurable
    ((dW_measAmb hW c d).pow_const 2).aestronglyMeasurable, hW.var c d hcd]

lemma int_mul_dW_dW (hW : IncrHyp m W P) {c x y : ℝ≥0} (hcx : c ≤ x) (hxy : x ≤ y) {g : Ω → ℝ}
    (hg : Measurable[m c] g) {C : ℝ} (hC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * ((W x ω - W c ω) * (W y ω - W c ω)) ∂P = (∫ ω, g ω ∂P) * ((x : ℝ) - c) := by
  have hga : AEStronglyMeasurable g P := (hg.mono (hW.le c) le_rfl).aestronglyMeasurable
  have hgb : ∀ᵐ ω ∂P, ‖g ω‖ ≤ C :=
    Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω
  have i1 : Integrable (fun ω => g ω * (W x ω - W c ω) ^ 2) P :=
    (hW.mem2 c x).integrable_sq.bdd_mul hga hgb
  have i2 : Integrable (fun ω => g ω * ((W x ω - W c ω) * (W y ω - W x ω))) P :=
    ((hW.mem2 c x).integrable_mul (hW.mem2 x y)).bdd_mul hga hgb
  have i2' : Integrable (fun ω => g ω * (W x ω - W c ω) * (W y ω - W x ω)) P := by
    simpa only [mul_assoc] using i2
  have e : (fun ω => g ω * ((W x ω - W c ω) * (W y ω - W c ω))) =
      fun ω => g ω * (W x ω - W c ω) ^ 2 + g ω * (W x ω - W c ω) * (W y ω - W x ω) := by
    funext ω; ring
  have hg2 : Measurable[m x] (fun ω => g ω * (W x ω - W c ω)) :=
    (hg.mono (hW.mono hcx) le_rfl).mul (dW_meas hW hcx)
  rw [e, integral_add i1 i2', int_mul_dW_sq hW hcx hg, int_mul_dW hW hxy hg2, add_zero]

/-- Overlap length of `[u,v)` and `[u',v')`. -/
noncomputable def ov (u v u' v' : ℝ≥0) : ℝ := max (min (v : ℝ) v' - max (u : ℝ) u') 0

lemma ov_comm (u v u' v' : ℝ≥0) : ov u v u' v' = ov u' v' u v := by
  unfold ov; rw [min_comm, max_comm (u : ℝ)]

/-- Covariance of two elementary increments (case `u ≤ u'`). -/
lemma cov_le (hW : IncrHyp m W P) {u v u' v' : ℝ≥0} (huv : u ≤ v) (hu'v' : u' ≤ v')
    (huu' : u ≤ u') {Y Y' : Ω → ℝ} (hY : Measurable[m u] Y) (hY' : Measurable[m u'] Y')
    {C C' : ℝ} (hC : ∀ ω, |Y ω| ≤ C) (hC' : ∀ ω, |Y' ω| ≤ C') :
    ∫ ω, (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω)) ∂P =
      (∫ ω, Y ω * Y' ω ∂P) * ov u v u' v' := by
  have hYu' : Measurable[m u'] Y := hY.mono (hW.mono huu') le_rfl
  have hYY' : Measurable[m u'] (fun ω => Y ω * Y' ω) := hYu'.mul hY'
  have hbd : ∀ ω, |Y ω * Y' ω| ≤ C * C' := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hC ω) (hC' ω) (abs_nonneg _) ((abs_nonneg _).trans (hC ω))
  have hu'r : (u : ℝ) ≤ u' := by exact_mod_cast huu'
  rcases le_or_gt v u' with hvu | hu'v
  · have hvu' : (v : ℝ) ≤ u' := by exact_mod_cast hvu
    have hov : ov u v u' v' = 0 := by
      unfold ov
      exact max_eq_right (by linarith [min_le_left (v : ℝ) v', le_max_right (u : ℝ) u'])
    have e : (fun ω => (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω))) =
        fun ω => (Y ω * (W v ω - W u ω) * Y' ω) * (W v' ω - W u' ω) := by
      funext ω; ring
    have hg : Measurable[m u'] (fun ω => Y ω * (W v ω - W u ω) * Y' ω) :=
      (hYu'.mul ((dW_meas hW huv).mono (hW.mono hvu) le_rfl)).mul hY'
    rw [e, int_mul_dW hW hu'v' hg, hov, mul_zero]
  · have hu'v'' : (u' : ℝ) < v := by exact_mod_cast hu'v
    have hu'v1 : u' ≤ v := hu'v.le
    have hga : AEStronglyMeasurable (fun ω => Y ω * Y' ω) P :=
      (hYY'.mono (hW.le u') le_rfl).aestronglyMeasurable
    have hgb : ∀ᵐ ω ∂P, ‖Y ω * Y' ω‖ ≤ C * C' :=
      Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd ω
    have i1 : Integrable (fun ω => Y ω * Y' ω * ((W u' ω - W u ω) * (W v' ω - W u' ω))) P :=
      ((hW.mem2 u u').integrable_mul (hW.mem2 u' v')).bdd_mul hga hgb
    have i2 : Integrable (fun ω => Y ω * Y' ω * ((W v ω - W u' ω) * (W v' ω - W u' ω))) P :=
      ((hW.mem2 u' v).integrable_mul (hW.mem2 u' v')).bdd_mul hga hgb
    have i1' : Integrable (fun ω => Y ω * Y' ω * (W u' ω - W u ω) * (W v' ω - W u' ω)) P := by
      simpa only [mul_assoc] using i1
    have e : (fun ω => (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω))) =
        fun ω => Y ω * Y' ω * (W u' ω - W u ω) * (W v' ω - W u' ω) +
          Y ω * Y' ω * ((W v ω - W u' ω) * (W v' ω - W u' ω)) := by
      funext ω; ring
    have hg1 : Measurable[m u'] (fun ω => Y ω * Y' ω * (W u' ω - W u ω)) :=
      hYY'.mul (dW_meas hW huu')
    rw [e, integral_add i1' i2, int_mul_dW hW hu'v' hg1, zero_add]
    rcases le_total v v' with hvv | hvv
    · rw [int_mul_dW_dW hW hu'v1 hvv hYY' hbd]
      congr 1
      unfold ov
      have hvv' : (v : ℝ) ≤ v' := by exact_mod_cast hvv
      rw [min_eq_left hvv', max_eq_right hu'r, max_eq_left (by linarith)]
    · have e2 : (fun ω => Y ω * Y' ω * ((W v ω - W u' ω) * (W v' ω - W u' ω))) =
          fun ω => Y ω * Y' ω * ((W v' ω - W u' ω) * (W v ω - W u' ω)) := by
        funext ω; ring
      rw [e2, int_mul_dW_dW hW hu'v' hvv hYY' hbd]
      congr 1
      unfold ov
      have hvv' : (v' : ℝ) ≤ v := by exact_mod_cast hvv
      have hu'v'r : (u' : ℝ) ≤ v' := by exact_mod_cast hu'v'
      rw [min_eq_right hvv', max_eq_right hu'r, max_eq_left (by linarith)]

lemma cov (hW : IncrHyp m W P) {u v u' v' : ℝ≥0} (huv : u ≤ v) (hu'v' : u' ≤ v')
    {Y Y' : Ω → ℝ} (hY : Measurable[m u] Y) (hY' : Measurable[m u'] Y')
    {C C' : ℝ} (hC : ∀ ω, |Y ω| ≤ C) (hC' : ∀ ω, |Y' ω| ≤ C') :
    ∫ ω, (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω)) ∂P =
      (∫ ω, Y ω * Y' ω ∂P) * ov u v u' v' := by
  rcases le_total u u' with h | h
  · exact cov_le hW huv hu'v' h hY hY' hC hC'
  · have := cov_le hW hu'v' huv h hY' hY hC' hC
    have e1 : (fun ω => (Y ω * (W v ω - W u ω)) * (Y' ω * (W v' ω - W u' ω))) =
        fun ω => (Y' ω * (W v' ω - W u' ω)) * (Y ω * (W v ω - W u ω)) := by
      funext ω; ring
    have e2 : (fun ω => Y ω * Y' ω) = fun ω => Y' ω * Y ω := by funext ω; ring
    rw [e1, e2, this, ov_comm]

/-- Time indicator of `[u, v)`. -/
noncomputable def ind (u v : ℝ≥0) (r : ℝ) : ℝ := (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) r

lemma ind_mul (u v u' v' : ℝ≥0) (r : ℝ) :
    ind u v r * ind u' v' r =
      (Set.Ico (max (u : ℝ) u') (min (v : ℝ) v')).indicator (fun _ => (1 : ℝ)) r := by
  simp only [ind, Set.indicator_apply, Set.mem_Ico, max_le_iff, lt_min_iff]
  split_ifs <;> simp_all

lemma ind_abs_le (u v : ℝ≥0) (r : ℝ) : |ind u v r| ≤ 1 := by
  unfold ind; rw [Set.indicator_apply]; split_ifs <;> simp

lemma ind_meas (u v : ℝ≥0) : Measurable (ind u v) :=
  (measurable_const.indicator measurableSet_Ico)

/-- The time-space measure `dt|[0,T) ⊗ P`. -/
noncomputable def μT (P : Measure Ω) (T : ℝ≥0) : Measure (ℝ × Ω) :=
  (volume.restrict (Set.Ico (0 : ℝ) T)).prod P

instance (T : ℝ≥0) : IsFiniteMeasure (μT P T) := by unfold μT; infer_instance

lemma int_time (T : ℝ≥0) {u v u' v' : ℝ≥0} (hvT : v ≤ T) :
    ∫ r, ind u v r * ind u' v' r ∂(volume.restrict (Set.Ico (0 : ℝ) T)) = ov u v u' v' := by
  unfold ov
  simp_rw [ind_mul]
  have hsub : Set.Ico (max (u : ℝ) u') (min (v : ℝ) v') ⊆ Set.Ico 0 T := fun r hr =>
    ⟨le_trans (le_trans (NNReal.coe_nonneg u) (le_max_left _ _)) hr.1,
      lt_of_lt_of_le hr.2 (le_trans (min_le_left _ _) (by exact_mod_cast hvT))⟩
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico, measureReal_restrict_apply measurableSet_Ico,
    Set.inter_eq_left.2 hsub, Real.volume_real_Ico, smul_eq_mul, mul_one]

/-- Elementary adapted processes `Y 1_[u,v)` on `[0,T]`. -/
structure Elem (m : ℝ≥0 → MeasurableSpace Ω) (T : ℝ≥0) where
  u : ℝ≥0
  v : ℝ≥0
  huv : u ≤ v
  hvT : v ≤ T
  Y : Ω → ℝ
  hY : Measurable[m u] Y
  C : ℝ
  hC : ∀ ω, |Y ω| ≤ C

/-- The time-space function of an elementary process. -/
noncomputable def efun {T : ℝ≥0} (i : Elem m T) (z : ℝ × Ω) : ℝ := ind i.u i.v z.1 * i.Y z.2

/-- The elementary stochastic integral. -/
noncomputable def ifun {T : ℝ≥0} (W : ℝ≥0 → Ω → ℝ) (i : Elem m T) (ω : Ω) : ℝ :=
  i.Y ω * (W i.v ω - W i.u ω)

lemma memLp_efun (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (i : Elem m T) :
    MemLp (efun i) 2 (μT P T) := by
  have hm : Measurable (efun i) :=
    ((ind_meas i.u i.v).comp measurable_fst).mul ((i.hY.mono (hle i.u) le_rfl).comp measurable_snd)
  refine MemLp.of_bound hm.aestronglyMeasurable i.C (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, efun, abs_mul]
  calc |ind i.u i.v z.1| * |i.Y z.2| ≤ 1 * |i.Y z.2| :=
        mul_le_mul_of_nonneg_right (ind_abs_le _ _ _) (abs_nonneg _)
    _ ≤ i.C := by rw [one_mul]; exact i.hC z.2

lemma memLp_ifun (hW : IncrHyp m W P) {T : ℝ≥0} (i : Elem m T) : MemLp (ifun W i) 2 P := by
  refine ((hW.mem2 i.u i.v).const_mul i.C).of_le
    ((i.hY.mono (hW.le i.u) le_rfl).aestronglyMeasurable.mul (hW.mem2 i.u i.v).aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  simp only [ifun, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right ((i.hC ω).trans (le_abs_self _)) (abs_nonneg _)

noncomputable def eE (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (i : Elem m T) : Lp ℝ 2 (μT P T) :=
  (memLp_efun (P := P) hle i).toLp _

noncomputable def eI (hW : IncrHyp m W P) (T : ℝ≥0) (i : Elem m T) : Lp ℝ 2 P :=
  (memLp_ifun hW i).toLp _

lemma inner_eE (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (i j : Elem m T) :
    ⟪eE (P := P) hle T i, eE hle T j⟫_ℝ = ov i.u i.v j.u j.v * ∫ ω, i.Y ω * j.Y ω ∂P := by
  unfold eE
  rw [L2.inner_def]
  have h1 := (memLp_efun (P := P) hle i).coeFn_toLp
  have h2 := (memLp_efun (P := P) hle j).coeFn_toLp
  have hc : ∫ z, ⟪((memLp_efun (P := P) hle i).toLp _ : ℝ × Ω → ℝ) z,
      ((memLp_efun (P := P) hle j).toLp _ : ℝ × Ω → ℝ) z⟫_ℝ ∂(μT P T) =
      ∫ z, (ind i.u i.v z.1 * ind j.u j.v z.1) * (i.Y z.2 * j.Y z.2) ∂(μT P T) := by
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2, RCLike.inner_apply', conj_trivial, efun, efun]
    ring
  rw [hc, μT, integral_prod_mul (fun r => ind i.u i.v r * ind j.u j.v r)
    (fun ω => i.Y ω * j.Y ω), int_time T i.hvT]

lemma inner_eI (hW : IncrHyp m W P) {T : ℝ≥0} (i j : Elem m T) :
    ⟪eI hW T i, eI hW T j⟫_ℝ = ov i.u i.v j.u j.v * ∫ ω, i.Y ω * j.Y ω ∂P := by
  unfold eI
  rw [L2.inner_def]
  have h1 := (memLp_ifun hW i).coeFn_toLp
  have h2 := (memLp_ifun hW j).coeFn_toLp
  have hc : ∫ ω, ⟪((memLp_ifun hW i).toLp _ : Ω → ℝ) ω, ((memLp_ifun hW j).toLp _ : Ω → ℝ) ω⟫_ℝ ∂P =
      ∫ ω, (i.Y ω * (W i.v ω - W i.u ω)) * (j.Y ω * (W j.v ω - W j.u ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2, RCLike.inner_apply', conj_trivial, ifun, ifun]
  rw [hc, cov hW i.huv j.huv i.hY j.hY i.hC j.hC, mul_comm]

noncomputable def eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    (Elem m T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (μT P T) :=
  Finsupp.linearCombination ℝ (eE hle T)

noncomputable def TL (hW : IncrHyp m W P) (T : ℝ≥0) : (Elem m T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 P :=
  Finsupp.linearCombination ℝ (eI hW T)

lemma inner_TL (hW : IncrHyp m W P) (T : ℝ≥0) (s t : Elem m T →₀ ℝ) :
    ⟪TL hW T s, TL hW T t⟫_ℝ = ⟪eL (P := P) hW.le T s, eL hW.le T t⟫_ℝ := by
  induction s using Finsupp.induction_linear with
  | zero => simp
  | add s1 s2 h1 h2 => simp only [map_add, inner_add_left, h1, h2]
  | single i a =>
    induction t using Finsupp.induction_linear with
    | zero => simp
    | add t1 t2 h1 h2 => simp only [map_add, inner_add_right, h1, h2]
    | single j b =>
      simp only [TL, eL, Finsupp.linearCombination_single, real_inner_smul_left,
        real_inner_smul_right, inner_eI, inner_eE]

lemma norm_TL (hW : IncrHyp m W P) (T : ℝ≥0) (s : Elem m T →₀ ℝ) :
    ‖TL hW T s‖ = ‖eL (P := P) hW.le T s‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_TL]

/-- **O3 (representing integrand, one Brownian component).** -/
theorem O3 (hW : IncrHyp m W P) (T : ℝ≥0) (f : Lp ℝ 2 P) :
    ∃ a : Lp ℝ 2 (μT P T), a ∈ (LinearMap.range (eL (P := P) hW.le T)).topologicalClosure ∧
      ∀ i : Elem m T, ∫ ω, f ω * ifun W i ω ∂P = ∫ z, a z * efun i z ∂(μT P T) := by
  obtain ⟨a, ha, h⟩ := StochCalcRiesz.riesz_isom_mem (eL hW.le T) (TL hW T) (norm_TL hW T) f
  refine ⟨a, ha, fun i => ?_⟩
  have hi := h (Finsupp.single i 1)
  simp only [TL, eL, Finsupp.linearCombination_single, one_smul] at hi
  unfold eI eE at hi
  rw [L2.inner_def, L2.inner_def] at hi
  have h1 : ∫ ω, f ω * ifun W i ω ∂P =
      ∫ ω, ⟪f ω, ((memLp_ifun hW i).toLp _ : Ω → ℝ) ω⟫_ℝ ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_ifun hW i).coeFn_toLp] with ω hω
    rw [hω, RCLike.inner_apply', conj_trivial]
  have h2 : ∫ z, a z * efun i z ∂(μT P T) =
      ∫ z, ⟪a z, ((memLp_efun (P := P) hW.le i).toLp _ : ℝ × Ω → ℝ) z⟫_ℝ ∂(μT P T) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_efun (P := P) hW.le i).coeFn_toLp] with z hz
    rw [hz, RCLike.inner_apply', conj_trivial]
  rw [h1, h2, hi]

/-- Function form. -/
theorem O3_fun (hW : IncrHyp m W P) (T : ℝ≥0) {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∃ a : ℝ × Ω → ℝ, MemLp a 2 (μT P T) ∧
      ∀ i : Elem m T, ∫ ω, f ω * ifun W i ω ∂P = ∫ z, a z * efun i z ∂(μT P T) := by
  obtain ⟨a, -, ha⟩ := O3 hW T (hf.toLp f)
  refine ⟨a, Lp.memLp a, fun i => ?_⟩
  rw [← ha i]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with ω hω
  rw [hω]

end StochCalcO3

/-! O3M (8c066573 relay 17, O3 model instantiation): `B` and `B~` satisfy `StochCalcO3.IncrHyp` w.r.t. `M.F`,
so every `f ∈ L²(P)` has representing integrands `a, b ∈ L²(dt|[0,T) ⊗ P)` (in the closure of adapted simple processes):
`E[f Y (B_v - B_u)] = ∫∫ a 1_[u,v) Y` and `E[f Y (B~_v - B~_u)] = ∫∫ b 1_[u,v) Y`.
Append after probe/8c066573_S1RA.lean + RieszIso.lean body + O3gen_tail.lean (no import lines). -/

namespace StochCalcO3M

open HedgePSNV StochCalcBr StochCalcO3 StochCalcD3 StochCalcR1M StochCalcTiltM StochCalcSteinM
  StochCalcGauss StochCalcP6S

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma V_eq {u w : ℝ≥0} (huw : u ≤ w) : ((V u w : ℝ≥0) : ℝ) = (w : ℝ) - u := by
  rw [V, coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast huw))]

theorem incr_B (M : Model p Ω) (hM : M.Standing) : IncrHyp M.F M.B M.P := by
  have := hM.prob
  exact
  { mono := fun _ _ h => M.F.mono h
    le := M.F.le
    adapt := fun t => B_measF M hM le_rfl
    indep := fun u v huv => indep_dB M hM huv
    mem2 := fun u v => memLp_xi (dB_meas M hM u v) (dB_law M hM u v)
    mean := fun u v _ => integral_gauss (dB_law M hM u v)
    var := fun u v huv => by
      have h := integral_sq_gauss (dB_law M hM u v)
      rw [V_eq huv] at h
      exact h }

theorem incr_Bt (M : Model p Ω) (hM : M.Standing) : IncrHyp M.F M.Bt M.P := by
  have := hM.prob
  exact
  { mono := fun _ _ h => M.F.mono h
    le := M.F.le
    adapt := fun t => Bt_measF M hM le_rfl
    indep := fun u v huv => indep_of_indep_of_le_left (indep_ξ M hM huv v) le_sup_left
    mem2 := fun u v => memLp_xi (ξ_meas M hM u v) (ξ_law M hM u v)
    mean := fun u v _ => integral_gauss (ξ_law M hM u v)
    var := fun u v huv => by
      have h := integral_sq_gauss (ξ_law M hM u v)
      rw [V_eq huv] at h
      exact h }

/-- **O3 (model form).** Representing integrands of `f ∈ L²(P)` for both Brownian motions. -/
theorem O3_model (M : Model p Ω) (hM : M.Standing) {f : Ω → ℝ} (hf : MemLp f 2 M.P) :
    ∃ a b : ℝ × Ω → ℝ, MemLp a 2 (μT M.P p.T) ∧ MemLp b 2 (μT M.P p.T) ∧
      (∀ i : Elem M.F p.T, ∫ ω, f ω * ifun M.B i ω ∂M.P = ∫ z, a z * efun i z ∂(μT M.P p.T)) ∧
      (∀ i : Elem M.F p.T, ∫ ω, f ω * ifun M.Bt i ω ∂M.P = ∫ z, b z * efun i z ∂(μT M.P p.T)) := by
  have := hM.prob
  obtain ⟨a, ha2, ha⟩ := O3_fun (incr_B M hM) p.T hf
  obtain ⟨b, hb2, hb⟩ := O3_fun (incr_Bt M hM) p.T hf
  exact ⟨a, b, ha2, hb2, ha, hb⟩

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












/-- The predictable subspace of `L²(μT)`. -/
noncomputable def Pred (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) : Submodule ℝ (Lp ℝ 2 (μT P T)) :=
  (LinearMap.range (eL (P := P) hle T)).topologicalClosure

lemma mem_Pred_iff (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (x : Lp ℝ 2 (μT P T)) :
    x ∈ Pred (P := P) hle T ↔ x ∈ closure (Set.range (eL (P := P) hle T)) := by
  rw [Pred, ← SetLike.mem_coe, Submodule.topologicalClosure_coe, LinearMap.coe_range]

theorem proj_fun (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) {F : ℝ × Ω → ℝ} (hF : MemLp F 2 (μT P T)) :
    ∃ c : ℝ × Ω → ℝ, ∃ hc : MemLp c 2 (μT P T),
      hc.toLp c ∈ closure (Set.range (eL (P := P) hle T)) ∧
      ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
        hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hle T)) →
        ∫ z, c z * ψ z ∂(μT P T) = ∫ z, F z * ψ z ∂(μT P T) := by
  let K := Pred (P := P) hle T
  haveI : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let C : Lp ℝ 2 (μT P T) := K.starProjection (hF.toLp F)
  have hCm : C ∈ K := by
    simp only [C, Submodule.starProjection_apply]
    exact (K.orthogonalProjection _).2
  refine ⟨C, Lp.memLp C, ?_, fun ψ hψ hψK => ?_⟩
  · rw [Lp.toLp_coeFn]; exact (mem_Pred_iff hle T C).1 hCm
  · have hψK' : hψ.toLp ψ ∈ K := (mem_Pred_iff hle T _).2 hψK
    have e1 : ⟪C, hψ.toLp ψ⟫_ℝ = ⟪hF.toLp F, hψ.toLp ψ⟫_ℝ := by
      simp only [C]
      rw [Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.2 hψK']
    rw [L2.inner_def, L2.inner_def] at e1
    have l1 : ∫ z, ⟪(C : ℝ × Ω → ℝ) z, (hψ.toLp ψ : ℝ × Ω → ℝ) z⟫_ℝ ∂(μT P T) =
        ∫ z, C z * ψ z ∂(μT P T) := by
      refine integral_congr_ae ?_
      filter_upwards [hψ.coeFn_toLp] with z h1
      rw [h1, RCLike.inner_apply', conj_trivial]
    have l2 : ∫ z, ⟪(hF.toLp F : ℝ × Ω → ℝ) z, (hψ.toLp ψ : ℝ × Ω → ℝ) z⟫_ℝ ∂(μT P T) =
        ∫ z, F z * ψ z ∂(μT P T) := by
      refine integral_congr_ae ?_
      filter_upwards [hF.coeFn_toLp, hψ.coeFn_toLp] with z h0 h1
      rw [h0, h1, RCLike.inner_apply', conj_trivial]
    rw [← l1, ← l2]
    exact e1



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

/-- `θ` is the stochastic integral of the predictable integrand `b`. -/
def Rep (hW : IncrHyp m W P) (T : ℝ≥0) (θ : Lp ℝ 2 P) (b : Lp ℝ 2 (μT P T)) : Prop :=
  θ ∈ closure (Set.range (TL hW T)) ∧ b ∈ closure (Set.range (eL (P := P) hW.le T)) ∧
    ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪b, eL (P := P) hW.le T x⟫_ℝ


lemma rep_lim (hW : IncrHyp m W P) (T : ℝ≥0) {x : ℕ → (Elem m T →₀ ℝ)} {θ : Lp ℝ 2 P}
    {b : Lp ℝ 2 (μT P T)} (hx : Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ))
    (hb : Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 b)) : Rep hW T θ b := by
  refine ⟨mem_closure_of_tendsto hx (Eventually.of_forall fun n => ⟨x n, rfl⟩),
    mem_closure_of_tendsto hb (Eventually.of_forall fun n => ⟨x n, rfl⟩), fun y => ?_⟩
  have h1 : Tendsto (fun n => ⟪TL hW T (x n), TL hW T y⟫_ℝ) atTop (𝓝 ⟪θ, TL hW T y⟫_ℝ) :=
    hx.inner tendsto_const_nhds
  have h2 : Tendsto (fun n => ⟪eL (P := P) hW.le T (x n), eL (P := P) hW.le T y⟫_ℝ) atTop
      (𝓝 ⟪b, eL (P := P) hW.le T y⟫_ℝ) := hb.inner tendsto_const_nhds
  simp only [inner_TL] at h1
  exact tendsto_nhds_unique h1 h2

lemma rep_exists (hW : IncrHyp m W P) (T : ℝ≥0) {b : Lp ℝ 2 (μT P T)}
    (hb : b ∈ closure (Set.range (eL (P := P) hW.le T))) : ∃ θ, Rep hW T θ b := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hb
  choose y hy using hxr
  have hx' : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b) := by
    simp_rw [hy]; exact hx
  have hc : CauchySeq fun n => TL hW T (y n) := by
    have hcu : CauchySeq fun n => eL (P := P) hW.le T (y n) := hx'.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm, ← map_sub, norm_TL hW T, map_sub, ← dist_eq_norm]
    exact hN i hi j hj
  obtain ⟨θ, hθ⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨θ, rep_lim hW T hθ hx'⟩






















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

/-- Conjunct 3 of `EthierKurtz.brownian_ito_integral_locality_and_continuity` (platform theorem
1c98c8e0) for the model's 2-d Brownian motion `W M`, coordinate 0. -/
def ContHyp (M : Model p Ω) : Prop :=
  ∀ H : ℝ≥0 → Ω → ℝ,
    (∀ s, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) s] (H s)) →
    (∀ s, Measurable (H s)) → (∀ ω, Continuous fun s => H s ω) →
    ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
    ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
      (∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Jc t)) ∧
      (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
      HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
        (fun s ω => W M s ω 0) H Jc

/-- `η` frozen at the horizon. -/
noncomputable def etaT (M : Model p Ω) (s : ℝ≥0) (ω : Ω) : ℝ := M.η (min s p.T) ω














/-- **Z2.** -/
theorem Z2 (M : Model p Ω) (hM : M.Standing) (hC : ContHyp M) :
    ∃ Ic : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Ic t ω) ∧
      (∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t)) ∧
      (∀ t, Measurable (Ic t)) ∧ (∀ ω, Ic 0 ω = 0) ∧
      HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
        (fun s ω => W M s ω 0) (etaT M) Ic ∧
      (∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) := by
  exact HedgePSNV.eta_ito_integral_continuous_version M hM (StochCalcBr.W M) (fun _ _ => rfl) hC
































































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










/-- `Zc = exp(-Ic - ½∫_0^s η'²)`. -/
noncomputable def Zc (M : Model p Ω) (Ic : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(Ic s ω) - (1 / 2) * ∫ u in (0 : ℝ)..s.val, etaT M u.toNNReal ω ^ 2)

/-- **Z3.** -/
theorem Z3 (M : Model p Ω) (hM : M.Standing) {Ic : ℝ≥0 → Ω → ℝ}
    (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (hI0 : ∀ ω, Ic 0 ω = 0)
    (hIi : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (etaT M) Ic) :
    ∃ K : ℝ≥0 → Ω → ℝ,
      HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
        (fun s ω => W M s ω 0) (fun s ω => -(Zc M Ic s ω * etaT M s ω)) K ∧
      ∀ t, ∀ᵐ ω ∂M.P, Zc M Ic t ω = 1 + K t ω := by
  exact HedgePSNV.girsanov_density_ito M hM (StochCalcBr.W M) (fun _ _ => rfl) hIc hIa hIm hI0 hIi


































































































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


lemma joint_meas {X : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun s => X s ω)
    (hm : ∀ s, Measurable (X s)) : Measurable (fun z : ℝ × Ω => X z.1.toNNReal z.2) := by
  have h := measurable_uncurry_of_continuous_of_measurable hc hm
  exact h.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)




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

/-- The filtration `K^t`. -/
noncomputable def Kf (M : Model p Ω) (t s : ℝ≥0) : MeasurableSpace Ω :=
  if s < t then M.F s else M.F t ⊔ M.G s


lemma Kf_ge (M : Model p Ω) {t s : ℝ≥0} (h : t ≤ s) : Kf M t s = M.F t ⊔ M.G s :=
  if_neg (not_lt.2 h)














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



lemma Z_pos {p : Params} {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω) (t : ℝ≥0) (ω : Ω) :
    0 < M.Z t ω := Real.exp_pos _




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



lemma FGle (M : Model p Ω) (u : ℝ≥0) : M.F u ⊔ M.G p.T ≤ mΩ :=
  sup_le (M.F.le u) (M.G.le p.T)













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

/-- Pull-out: `∫ c · E[X|m] = ∫ c X` for `m`-measurable `c` with `c X` integrable. -/
lemma l1_pull {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {c X : Ω → ℝ}
    (hc : StronglyMeasurable[m] c) (hX : Integrable X Q)
    (hcX : Integrable (fun ω => c ω * X ω) Q) :
    ∫ ω, c ω * condExp m Q X ω ∂Q = ∫ ω, c ω * X ω ∂Q := by
  rw [← integral_condExp hm (f := fun ω => c ω * X ω)]
  exact (integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hc hcX hX)).symm

theorem cell_id {F H : ℕ → MeasurableSpace Ω} {k : ℕ} (hFab : F k ≤ F (k + 1)) (hFHa : F k ≤ H k)
    (hHab : H k ≤ H (k + 1)) (hFHb : F (k + 1) ≤ H (k + 1)) (hHb : H (k + 1) ≤ mΩ)
    {g w y : Ω → ℝ} (hg : MemLp g 2 Q) (hw : MemLp w 2 Q) (hwm : StronglyMeasurable[(F (k + 1))] w)
    {Cy : ℝ≥0} (hym : StronglyMeasurable[(H k)] y) (hyb : ∀ ω, |y ω| ≤ Cy)
    (hQb : condExp (H (k + 1)) Q g =ᵐ[Q] condExp (F (k + 1)) Q g)
    (hind : ∀ h : Ω → ℝ, StronglyMeasurable[(H k)] h → ∫ ω, h ω * w ω ∂Q = 0)
    (hNC : ∀ z : Ω → ℝ, StronglyMeasurable[(F k)] z → (∀ᵐ ω ∂Q, |z ω| ≤ Cy) →
      ∫ ω, g ω * z ω * w ω ∂Q = 0) :
    ∫ ω, g ω * y ω * w ω ∂Q =
      ∫ ω, (condExp (F (k + 1)) Q g ω - condExp (F k) Q g ω) * w ω *
        (condExp (F (k + 1)) Q y ω - condExp (F k) Q y ω) ∂Q := by
  have hFb : (F (k + 1)) ≤ mΩ := hFHb.trans hHb
  have hFa : (F k) ≤ mΩ := hFab.trans hFb
  set gb := condExp (F (k + 1)) Q g with hgb
  set ga := condExp (F k) Q g with hga
  set yb := condExp (F (k + 1)) Q y with hyb'
  set ya := condExp (F k) Q y with hya'
  have hgb2 : MemLp gb 2 Q := MemLp.condExp (m := (F (k + 1))) one_le_two hg
  have hga2 : MemLp ga 2 Q := MemLp.condExp (m := (F k)) one_le_two hg
  have hgbm : StronglyMeasurable[(F (k + 1))] gb := stronglyMeasurable_condExp
  have hgam : StronglyMeasurable[(F k)] ga := stronglyMeasurable_condExp
  have hybm : StronglyMeasurable[(F (k + 1))] yb := stronglyMeasurable_condExp
  have hyam : StronglyMeasurable[(F k)] ya := stronglyMeasurable_condExp
  have hyae : AEStronglyMeasurable[mΩ] y Q := (hym.mono (hHab.trans hHb)).aestronglyMeasurable
  have hyb_ae : ∀ᵐ ω ∂Q, |yb ω| ≤ Cy := ae_bdd_abs_condExp_of_ae_bdd_abs (R := (Cy : ℝ)) (Eventually.of_forall hyb)
  have hya_ae : ∀ᵐ ω ∂Q, |ya ω| ≤ Cy := ae_bdd_abs_condExp_of_ae_bdd_abs (R := (Cy : ℝ)) (Eventually.of_forall hyb)
  have hyi : Integrable y Q :=
    (integrable_const (Cy : ℝ)).mono' hyae (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hyb ω)
  have hgi : Integrable g Q := hg.integrable one_le_two
  -- integrability of `a * w * b` for `a ∈ L²`, `b` bounded
  have T : ∀ a b : Ω → ℝ, MemLp a 2 Q → AEStronglyMeasurable[mΩ] b Q → (∀ᵐ ω ∂Q, |b ω| ≤ Cy) →
      Integrable (fun ω => a ω * w ω * b ω) Q := by
    intro a b ha hb hbb
    have h1 := (ha.integrable_mul hw).bdd_mul hb (c := (Cy : ℝ))
      (by filter_upwards [hbb] with ω h; rwa [Real.norm_eq_abs])
    refine h1.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply]; ring
  have hyA : ∀ᵐ ω ∂Q, |y ω| ≤ Cy := Eventually.of_forall hyb
  have hybA : AEStronglyMeasurable[mΩ] yb Q := (hybm.mono hFb).aestronglyMeasurable
  have hyaA : AEStronglyMeasurable[mΩ] ya Q := (hyam.mono hFa).aestronglyMeasurable
  -- E1: ∫ g y w = ∫ gb w y
  have E1 : ∫ ω, g ω * y ω * w ω ∂Q = ∫ ω, gb ω * w ω * y ω ∂Q := by
    have hc : StronglyMeasurable[(H (k + 1))] (fun ω => y ω * w ω) :=
      (hym.mono hHab).mul (hwm.mono hFHb)
    have hI : Integrable (fun ω => (y ω * w ω) * g ω) Q :=
      (T g y hg hyae hyA).congr (Eventually.of_forall fun ω => by ring)
    have := l1_pull hHb hc hgi hI
    have h2 : ∫ ω, (y ω * w ω) * condExp (H (k + 1)) Q g ω ∂Q = ∫ ω, (y ω * w ω) * gb ω ∂Q :=
      integral_congr_ae (hQb.mono fun ω h => congrArg (fun x => y ω * w ω * x) h)
    calc ∫ ω, g ω * y ω * w ω ∂Q = ∫ ω, (y ω * w ω) * g ω ∂Q :=
          integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = ∫ ω, (y ω * w ω) * condExp (H (k + 1)) Q g ω ∂Q := this.symm
      _ = ∫ ω, (y ω * w ω) * gb ω ∂Q := h2
      _ = ∫ ω, gb ω * w ω * y ω ∂Q := integral_congr_ae (Eventually.of_forall fun ω => by ring)
  -- E2: ∫ gb w y = ∫ gb w yb
  have E2 : ∫ ω, gb ω * w ω * yb ω ∂Q = ∫ ω, gb ω * w ω * y ω ∂Q :=
    l1_pull hFb (hgbm.mul hwm) hyi (T gb y hgb2 hyae hyA)
  -- E3: ∫ gb w ya = 0
  have E3 : ∫ ω, gb ω * w ω * ya ω ∂Q = 0 := by
    have hc : StronglyMeasurable[(F (k + 1))] (fun ω => ya ω * w ω) := (hyam.mono hFab).mul hwm
    have hI : Integrable (fun ω => (ya ω * w ω) * g ω) Q :=
      (T g ya hg hyaA hya_ae).congr (Eventually.of_forall fun ω => by ring)
    have := l1_pull hFb hc hgi hI
    calc ∫ ω, gb ω * w ω * ya ω ∂Q = ∫ ω, (ya ω * w ω) * gb ω ∂Q :=
          integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = ∫ ω, (ya ω * w ω) * g ω ∂Q := this
      _ = ∫ ω, g ω * ya ω * w ω ∂Q := integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = 0 := hNC ya hyam hya_ae
  -- E4: ∫ ga w yb = 0
  have E4 : ∫ ω, ga ω * w ω * yb ω ∂Q = 0 := by
    have e4 : ∫ ω, ga ω * w ω * yb ω ∂Q = ∫ ω, ga ω * w ω * y ω ∂Q :=
      l1_pull hFb ((hgam.mono hFab).mul hwm) hyi (T ga y hga2 hyae hyA)
    calc ∫ ω, ga ω * w ω * yb ω ∂Q = ∫ ω, ga ω * w ω * y ω ∂Q := e4
      _ = ∫ ω, (ga ω * y ω) * w ω ∂Q :=
          integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = 0 := hind _ ((hgam.mono hFHa).mul hym)
  -- E5: ∫ ga w ya = 0
  have E5 : ∫ ω, ga ω * w ω * ya ω ∂Q = 0 := by
    calc ∫ ω, ga ω * w ω * ya ω ∂Q = ∫ ω, (ga ω * ya ω) * w ω ∂Q :=
          integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = 0 := hind _ ((hgam.mul hyam).mono hFHa)
  -- expand
  have i1 := T gb yb hgb2 hybA hyb_ae
  have i2 := T gb ya hgb2 hyaA hya_ae
  have i3 := T ga yb hga2 hybA hyb_ae
  have i4 := T ga ya hga2 hyaA hya_ae
  have hexp : ∫ ω, (gb ω - ga ω) * w ω * (yb ω - ya ω) ∂Q =
      (∫ ω, gb ω * w ω * yb ω ∂Q - ∫ ω, gb ω * w ω * ya ω ∂Q) -
        (∫ ω, ga ω * w ω * yb ω ∂Q - ∫ ω, ga ω * w ω * ya ω ∂Q) := by
    have e := integral_sub' (i1.sub i2) (i3.sub i4)
    rw [integral_sub' i1 i2, integral_sub' i3 i4] at e
    refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans e
    simp only [Pi.sub_apply]; ring
  rw [hexp]; linarith [E1, E2, E3, E4, E5]

end StochCalcE2

-- O7E3 tail (8c066573 relay 24): append after lib/stochcalc/O7E2.lean (pure Mathlib).

/-! O7.5 (E2 n-cell sum): splitting a cell into `n` pieces, the NC orthogonality gives
`|E[g y ΣΔW]| ≤ l/2 E g² + (1/2l)(μ/2 Σ E w_k⁴ + 2 Cy⁴/μ)` for all `l, μ > 0`; with `Σ E w_k⁴ = O(1/n)`
this forces `E[g y ΣΔW] = 0`. -/

namespace StochCalcE2

open MeasureTheory Filter Topology
open scoped NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

lemma amgm {l : ℝ} (hl : 0 < l) (x y : ℝ) : x * y ≤ l / 2 * x ^ 2 + y ^ 2 / (2 * l) := by
  have key : l / 2 * x ^ 2 + y ^ 2 / (2 * l) - x * y = (l * x - y) ^ 2 / (2 * l) := by
    field_simp; ring
  nlinarith [div_nonneg (sq_nonneg (l * x - y)) (by positivity : (0 : ℝ) ≤ 2 * l)]

lemma pt_bound {l μ C : ℝ} (hl : 0 < l) (hμ : 0 < μ) (a b c : ℝ) (hc : |c| ≤ 2 * C) :
    |a * b * c| ≤ l / 2 * a ^ 2 + 1 / (2 * l) * (μ / 2 * b ^ 4 + 2 * C ^ 2 / μ * c ^ 2) := by
  have h1 := amgm hl |a| |b * c|
  have h2 := amgm hμ (b ^ 2) (c ^ 2)
  have hc2 : c ^ 2 ≤ (2 * C) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg c) hc 2
  have h3 : (c ^ 2) ^ 2 ≤ 4 * C ^ 2 * c ^ 2 := by
    have := mul_le_mul_of_nonneg_right hc2 (sq_nonneg c)
    nlinarith
  calc |a * b * c| = |a| * |b * c| := by rw [mul_assoc, abs_mul]
    _ ≤ l / 2 * |a| ^ 2 + |b * c| ^ 2 / (2 * l) := h1
    _ = l / 2 * a ^ 2 + (b ^ 2 * c ^ 2) / (2 * l) := by rw [sq_abs, sq_abs, mul_pow]
    _ ≤ l / 2 * a ^ 2 + (μ / 2 * (b ^ 2) ^ 2 + (c ^ 2) ^ 2 / (2 * μ)) / (2 * l) := by gcongr
    _ ≤ l / 2 * a ^ 2 + (μ / 2 * (b ^ 2) ^ 2 + (4 * C ^ 2 * c ^ 2) / (2 * μ)) / (2 * l) := by
        gcongr
    _ = l / 2 * a ^ 2 + 1 / (2 * l) * (μ / 2 * b ^ 4 + 2 * C ^ 2 / μ * c ^ 2) := by
        field_simp; ring

lemma sq_sub_expand {a b : Ω → ℝ} (ha : MemLp a 2 Q) (hb : MemLp b 2 Q)
    (hab : ∫ ω, a ω * b ω ∂Q = ∫ ω, a ω * a ω ∂Q) :
    ∫ ω, (b ω - a ω) ^ 2 ∂Q = ∫ ω, b ω ^ 2 ∂Q - ∫ ω, a ω ^ 2 ∂Q := by
  have i1 : Integrable (fun ω => b ω ^ 2) Q := hb.integrable_sq
  have i2 : Integrable (fun ω => a ω * b ω) Q := ha.integrable_mul hb
  have i3 : Integrable (fun ω => a ω ^ 2) Q := ha.integrable_sq
  have e : (fun ω => (b ω - a ω) ^ 2) = fun ω => (b ω ^ 2 - 2 * (a ω * b ω)) + a ω ^ 2 := by
    funext ω; ring
  have e2 : ∫ ω, a ω * a ω ∂Q = ∫ ω, a ω ^ 2 ∂Q :=
    integral_congr_ae (Eventually.of_forall fun ω => by simp [sq])
  have i4 : Integrable (fun ω => b ω ^ 2 - 2 * (a ω * b ω)) Q := i1.sub (i2.const_mul 2)
  rw [e, integral_add i4 i3, integral_sub i1 (i2.const_mul 2),
    integral_const_mul, hab, e2]
  ring

lemma condExp_sq_le {F : ℕ → MeasurableSpace Ω} {k : ℕ} (hm : F k ≤ mΩ) {g : Ω → ℝ}
    (hg : MemLp g 2 Q) :
    ∫ ω, (condExp (F k) Q g ω) ^ 2 ∂Q ≤ ∫ ω, g ω ^ 2 ∂Q := by
  have hc2 : MemLp (condExp (F k) Q g) 2 Q := MemLp.condExp (m := F k) one_le_two hg
  have hab : ∫ ω, condExp (F k) Q g ω * g ω ∂Q =
      ∫ ω, condExp (F k) Q g ω * condExp (F k) Q g ω ∂Q :=
    (l1_pull hm stronglyMeasurable_condExp (hg.integrable one_le_two)
      (hc2.integrable_mul hg)).symm
  have := sq_sub_expand hc2 hg hab
  have h0 : 0 ≤ ∫ ω, (g ω - condExp (F k) Q g ω) ^ 2 ∂Q := integral_nonneg fun ω => sq_nonneg _
  linarith

lemma incr_sq {F : ℕ → MeasurableSpace Ω} {j k : ℕ} (h12 : F j ≤ F k) (hm₂ : F k ≤ mΩ)
    {g : Ω → ℝ} (hg : MemLp g 2 Q) :
    ∫ ω, (condExp (F k) Q g ω - condExp (F j) Q g ω) ^ 2 ∂Q =
      ∫ ω, (condExp (F k) Q g ω) ^ 2 ∂Q - ∫ ω, (condExp (F j) Q g ω) ^ 2 ∂Q := by
  have ha : MemLp (condExp (F j) Q g) 2 Q := MemLp.condExp (m := F j) one_le_two hg
  have hb : MemLp (condExp (F k) Q g) 2 Q := MemLp.condExp (m := F k) one_le_two hg
  refine sq_sub_expand ha hb ?_
  have h1 := l1_pull (h12.trans hm₂) (stronglyMeasurable_condExp (m := F j) (f := g) (μ := Q))
    (hb.integrable one_le_two) (ha.integrable_mul hb)
  rw [← h1]
  refine integral_congr_ae ?_
  filter_upwards [condExp_condExp_of_le (μ := Q) (f := g) h12 hm₂] with ω hω
  simp only [hω]

lemma tele {F : ℕ → MeasurableSpace Ω} (hF : Monotone F) (hle : ∀ k, F k ≤ mΩ) {g : Ω → ℝ}
    (hg : MemLp g 2 Q) (n : ℕ) :
    ∑ k ∈ Finset.range n, ∫ ω, (condExp (F (k + 1)) Q g ω - condExp (F k) Q g ω) ^ 2 ∂Q ≤
      ∫ ω, g ω ^ 2 ∂Q := by
  rw [Finset.sum_congr rfl fun k _ => incr_sq (hF (Nat.le_succ k)) (hle _) hg,
    Finset.sum_range_sub (fun k => ∫ ω, (condExp (F k) Q g ω) ^ 2 ∂Q)]
  have h1 := condExp_sq_le (hle n) hg
  have h0 : 0 ≤ ∫ ω, (condExp (F 0) Q g ω) ^ 2 ∂Q := integral_nonneg fun ω => sq_nonneg _
  linarith

/-- O7.5, quantitative form for one subdivision into `n` pieces. -/
theorem E2_bound {F H : ℕ → MeasurableSpace Ω} (hF : Monotone F) (hH : Monotone H)
    (hFH : ∀ k, F k ≤ H k) (hHle : ∀ k, H k ≤ mΩ)
    {g y : Ω → ℝ} {w : ℕ → Ω → ℝ} (n : ℕ) (hg : MemLp g 2 Q)
    (hw : ∀ k < n, MemLp (w k) 2 Q) (hw4 : ∀ k < n, Integrable (fun ω => w k ω ^ 4) Q)
    (hwm : ∀ k < n, StronglyMeasurable[F (k + 1)] (w k))
    {Cy : ℝ≥0} (hym : StronglyMeasurable[H 0] y) (hyb : ∀ ω, |y ω| ≤ Cy)
    (hQb : ∀ k < n, condExp (H (k + 1)) Q g =ᵐ[Q] condExp (F (k + 1)) Q g)
    (hind : ∀ k < n, ∀ h : Ω → ℝ, StronglyMeasurable[H k] h → ∫ ω, h ω * w k ω ∂Q = 0)
    (hNC : ∀ k < n, ∀ z : Ω → ℝ, StronglyMeasurable[F k] z → (∀ᵐ ω ∂Q, |z ω| ≤ Cy) →
      ∫ ω, g ω * z ω * w k ω ∂Q = 0)
    {l μ : ℝ} (hl : 0 < l) (hμ : 0 < μ) :
    |∫ ω, g ω * y ω * ∑ k ∈ Finset.range n, w k ω ∂Q| ≤
      l / 2 * ∫ ω, g ω ^ 2 ∂Q + 1 / (2 * l) *
        (μ / 2 * ∑ k ∈ Finset.range n, ∫ ω, w k ω ^ 4 ∂Q + 2 * (Cy : ℝ) ^ 4 / μ) := by
  set C : ℝ := (Cy : ℝ) with hCdef
  have hC0 : 0 ≤ C := Cy.2
  have hym' : StronglyMeasurable y := hym.mono (hHle 0)
  have hy2 : MemLp y 2 Q :=
    MemLp.of_bound hym'.aestronglyMeasurable C (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hyb ω)
  have hFle : ∀ k, F k ≤ mΩ := fun k => (hFH k).trans (hHle k)
  -- abbreviations
  let dg : ℕ → Ω → ℝ := fun k ω => condExp (F (k + 1)) Q g ω - condExp (F k) Q g ω
  let dy : ℕ → Ω → ℝ := fun k ω => condExp (F (k + 1)) Q y ω - condExp (F k) Q y ω
  have hdg : ∀ k, MemLp (dg k) 2 Q := fun k =>
    (MemLp.condExp (m := F (k + 1)) one_le_two hg).sub (MemLp.condExp (m := F k) one_le_two hg)
  have hdy : ∀ k, MemLp (dy k) 2 Q := fun k =>
    (MemLp.condExp (m := F (k + 1)) one_le_two hy2).sub (MemLp.condExp (m := F k) one_le_two hy2)
  have hdyb : ∀ k, ∀ᵐ ω ∂Q, |dy k ω| ≤ 2 * C := by
    intro k
    have hb : ∀ᵐ ω ∂Q, |y ω| ≤ Cy := Eventually.of_forall hyb
    filter_upwards [ae_bdd_condExp_of_ae_bdd (m := F (k + 1)) hb,
      ae_bdd_condExp_of_ae_bdd (m := F k) hb] with ω h1 h2
    calc |dy k ω| ≤ |condExp (F (k + 1)) Q y ω| + |condExp (F k) Q y ω| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  -- step 1: split the sum
  have hint : ∀ k < n, Integrable (fun ω => g ω * y ω * w k ω) Q := by
    intro k hk
    refine (((hg.integrable_mul (hw k hk)).norm).const_mul C).mono'
      ((hg.aestronglyMeasurable.mul hym'.aestronglyMeasurable).mul (hw k hk).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    have := hyb ω
    have h0 : 0 ≤ |g ω| * |w k ω| := by positivity
    nlinarith [abs_nonneg (g ω), abs_nonneg (w k ω)]
  have e1 : ∫ ω, g ω * y ω * ∑ k ∈ Finset.range n, w k ω ∂Q =
      ∑ k ∈ Finset.range n, ∫ ω, dg k ω * w k ω * dy k ω ∂Q := by
    rw [show (fun ω => g ω * y ω * ∑ k ∈ Finset.range n, w k ω) =
        fun ω => ∑ k ∈ Finset.range n, g ω * y ω * w k ω from funext fun ω => Finset.mul_sum _ _ _,
      integral_finset_sum _ fun k hk => hint k (Finset.mem_range.1 hk)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    exact cell_id (hF (Nat.le_succ k)) (hFH k) (hH (Nat.le_succ k)) (hFH (k + 1)) (hHle (k + 1))
      hg (hw k hk') (hwm k hk') (hym.mono (hH (Nat.zero_le k))) hyb (hQb k hk') (hind k hk')
      (hNC k hk')
  -- step 2: bound each cell
  have hcell : ∀ k < n, |∫ ω, dg k ω * w k ω * dy k ω ∂Q| ≤
      l / 2 * ∫ ω, dg k ω ^ 2 ∂Q + 1 / (2 * l) *
        (μ / 2 * ∫ ω, w k ω ^ 4 ∂Q + 2 * C ^ 2 / μ * ∫ ω, dy k ω ^ 2 ∂Q) := by
    intro k hk
    have iB : Integrable (fun ω => l / 2 * dg k ω ^ 2 + 1 / (2 * l) *
        (μ / 2 * w k ω ^ 4 + 2 * C ^ 2 / μ * dy k ω ^ 2)) Q :=
      ((hdg k).integrable_sq.const_mul _).add
        ((((hw4 k hk).const_mul _).add ((hdy k).integrable_sq.const_mul _)).const_mul _)
    refine abs_integral_le_integral_abs.trans ((integral_mono_of_nonneg
      (Eventually.of_forall fun ω => abs_nonneg _) iB ?_).trans (le_of_eq ?_))
    · filter_upwards [hdyb k] with ω hω
      exact pt_bound hl hμ _ _ _ hω
    · have j1 : Integrable (fun ω => dg k ω ^ 2) Q := (hdg k).integrable_sq
      have j2 : Integrable (fun ω => w k ω ^ 4) Q := hw4 k hk
      have j3 : Integrable (fun ω => dy k ω ^ 2) Q := (hdy k).integrable_sq
      have j23 : Integrable (fun ω => μ / 2 * w k ω ^ 4 + 2 * C ^ 2 / μ * dy k ω ^ 2) Q :=
        (j2.const_mul _).add (j3.const_mul _)
      rw [integral_add (j1.const_mul (l / 2)) (j23.const_mul (1 / (2 * l))),
        integral_const_mul, integral_const_mul,
        integral_add (j2.const_mul (μ / 2)) (j3.const_mul (2 * C ^ 2 / μ)),
        integral_const_mul, integral_const_mul]
  -- step 3: sum up
  have hG := tele hF hFle hg n
  have hY := tele hF hFle hy2 n
  have hy2C : ∫ ω, y ω ^ 2 ∂Q ≤ C ^ 2 := by
    calc ∫ ω, y ω ^ 2 ∂Q ≤ ∫ _ω, C ^ 2 ∂Q :=
          integral_mono hy2.integrable_sq (integrable_const _) fun ω => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hyb ω) 2
      _ = C ^ 2 := by simp
  rw [e1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k hk =>
    hcell k (Finset.mem_range.1 hk)).trans ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hA : ∑ k ∈ Finset.range n, ∫ ω, dg k ω ^ 2 ∂Q ≤ ∫ ω, g ω ^ 2 ∂Q := hG
  have hB : ∑ k ∈ Finset.range n, ∫ ω, dy k ω ^ 2 ∂Q ≤ C ^ 2 := hY.trans hy2C
  have hl2 : 0 ≤ 1 / (2 * l) := by positivity
  have hμ2 : 0 ≤ 2 * C ^ 2 / μ := by positivity
  have e4 : 2 * C ^ 4 / μ = 2 * C ^ 2 / μ * C ^ 2 := by ring
  rw [e4]
  gcongr

/-- O7.5 conclusion: bounds of `E2_bound` shape with `Σ E w⁴ ≤ K/n` force zero. -/
theorem zero_of_bounds {V G D K : ℝ}
    (h : ∀ n : ℕ, 0 < n → ∀ l μ : ℝ, 0 < l → 0 < μ →
      |V| ≤ l / 2 * G + 1 / (2 * l) * (μ / 2 * (K / n) + D / μ)) : V = 0 := by
  have h1 : ∀ l μ : ℝ, 0 < l → 0 < μ → |V| ≤ l / 2 * G + 1 / (2 * l) * (D / μ) := by
    intro l μ hl hμ
    have ht : Tendsto (fun n : ℕ => l / 2 * G + 1 / (2 * l) * (μ / 2 * (K / n) + D / μ)) atTop
        (𝓝 (l / 2 * G + 1 / (2 * l) * (μ / 2 * 0 + D / μ))) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul ((tendsto_const_nhds.mul
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)).add tendsto_const_nhds))
    have := ge_of_tendsto ht (eventually_atTop.2 ⟨1, fun n hn => h n hn l μ hl hμ⟩)
    simpa using this
  have h2 : ∀ l : ℝ, 0 < l → |V| ≤ l / 2 * G := by
    intro l hl
    have ht : Tendsto (fun μ : ℝ => l / 2 * G + 1 / (2 * l) * (D / μ)) atTop
        (𝓝 (l / 2 * G + 1 / (2 * l) * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.div_atTop tendsto_id))
    have := ge_of_tendsto ht ((eventually_gt_atTop 0).mono fun μ hμ => h1 l μ hl hμ)
    simpa using this
  have ht : Tendsto (fun l : ℝ => l / 2 * G) (𝓝[>] 0) (𝓝 (0 / 2 * G)) :=
    (((continuous_id.div_const 2).mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  have h3 := ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun l hl => h2 l hl)
  simp only [zero_div, zero_mul] at h3
  exact abs_nonpos_iff.1 h3

end StochCalcE2


/-! O7G4 (8c066573 relay 24, for the O7.5 model instance): fourth moments of centred Gaussians
scale like `v²`: `∫ x⁴ dN(0,v) = v² ∫ x⁴ dN(0,1)`, and a random variable with law `N(0,v)` has
`E w⁴ = v² K₄`, `K₄ := ∫ x⁴ dN(0,1)` (finite). Pure Mathlib. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StochCalcG4

lemma gauss4 (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) = (v : ℝ) ^ 2 * ∫ x, x ^ 4 ∂(gaussianReal 0 1) := by
  have hmap : (gaussianReal 0 1).map (Real.sqrt v * ·) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h := Real.sq_sqrt (NNReal.coe_nonneg v)
  calc (Real.sqrt v * x) ^ 4 = ((Real.sqrt v) ^ 2) ^ 2 * x ^ 4 := by ring
    _ = (v : ℝ) ^ 2 * x ^ 4 := by rw [h]

lemma integrable_pow4 (v : ℝ≥0) : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 v) := by
  have h := (memLp_id_gaussianReal (μ := 0) (v := v) 4).integrable_norm_pow (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Real.norm_eq_abs, pow_abs, Even.pow_abs (by decide : Even 4)]

/-- A random variable with law `N(0,v)` has fourth moment `v² K₄`. -/
theorem moment4 {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {w : Ω → ℝ} (hw : Measurable w)
    {v : ℝ≥0} (hlaw : Q.map w = gaussianReal 0 v) :
    Integrable (fun ω => w ω ^ 4) Q ∧
      ∫ ω, w ω ^ 4 ∂Q = (v : ℝ) ^ 2 * ∫ x, x ^ 4 ∂(gaussianReal 0 1) := by
  have hi := integrable_pow4 v
  rw [← hlaw] at hi
  refine ⟨(integrable_map_measure (by fun_prop) hw.aemeasurable).1 hi, ?_⟩
  rw [← gauss4 v, ← hlaw, integral_map hw.aemeasurable (by fun_prop)]

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

lemma V_gr (n a : ℕ) : (V (gr p n a) (gr p n (a + 1)) : ℝ) = (p.T : ℝ) / n := by
  rw [V_eq (gr_mono p n (Nat.le_succ a))]
  unfold gr
  push_cast
  ring

lemma sum_xg (M : Model p Ω) {N r : ℕ} (hr : 0 < r) (j : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range r, xg M (N * r) (j * r + k) ω = xg M N j ω := by
  have h : ∑ k ∈ Finset.range r, (M.Bt (gr p (N * r) (j * r + k + 1)) ω -
      M.Bt (gr p (N * r) (j * r + k)) ω) =
      M.Bt (gr p (N * r) (j * r + r)) ω - M.Bt (gr p (N * r) (j * r + 0)) ω :=
    Finset.sum_range_sub (fun k => M.Bt (gr p (N * r) (j * r + k)) ω) r
  simp only [xg, ξ]
  rw [h, show j * r + r = (j + 1) * r by ring, add_zero, StochCalcD3.gr_mul p hr,
    StochCalcD3.gr_mul p hr]

/-- **O7.5 (model).** -/
theorem E5 (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] (h5 : M.Assumption5)
    {f : Ω → ℝ} (hf2 : MemLp f 2 M.P)
    (hQb : ∀ t : ℝ≥0, t ≤ p.T →
      condExp (M.F t ⊔ M.G p.T) (Qd M.P (wZ M)) (fun ω => f ω / M.Z p.T ω) =ᵐ[Qd M.P (wZ M)]
        condExp (M.F t) (Qd M.P (wZ M)) (fun ω => f ω / M.Z p.T ω))
    (hfN : ∀ n : ℕ, 0 < n → ∀ Y : ℕ → Ω → ℝ, (∀ k, Measurable[M.F (gr p n k)] (Y k)) →
      (∃ C : ℝ, ∀ k ω, |Y k ω| ≤ C) →
      ∫ ω, f ω * (M.Z p.T ω * ∑ k ∈ Finset.range n, Y k ω * xg M n k ω) ∂M.P = 0)
    {N j : ℕ} (hj : j < N) {y : Ω → ℝ} (hym : Measurable[M.F (gr p N j) ⊔ M.G p.T] y)
    {Cy : ℝ≥0} (hyb : ∀ ω, |y ω| ≤ Cy) :
    ∫ ω, f ω / M.Z p.T ω * y ω * xg M N j ω ∂(Qd M.P (wZ M)) = 0 := by
  haveI := Q2_prob M hM h5
  set Q := Qd M.P (wZ M) with hQdef
  set g : Ω → ℝ := fun ω => f ω / M.Z p.T ω with hgdef
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le j) hj
  have hZpos : ∀ ω, 0 < M.Z p.T ω := fun ω => Real.exp_pos _
  have hZm : Measurable (M.Z p.T) := ((h5.1.1 p.T le_rfl).mono (M.F.le p.T)).measurable
  have hc := cZ_pos M hM h5
  -- g ∈ L²(Q)
  have hg : MemLp g 2 Q := by
    have hae : AEStronglyMeasurable g Q :=
      ((hf2.1.aemeasurable.div hZm.aemeasurable).aestronglyMeasurable).mono_ac (Qd_ac _)
    refine (memLp_two_iff_integrable_sq hae).2 ?_
    rw [integrable_Qd_iff (wZ_meas M hM) (wZ_pos M hM h5)]
    refine (hf2.integrable_sq.div_const (cZ M)).congr (Eventually.of_forall fun ω => ?_)
    have hz : M.Z p.T ω ≠ 0 := (hZpos ω).ne'
    simp only [hgdef, wZ]
    field_simp
  -- the r-piece bound
  set κ : ℝ := ∫ x, x ^ 4 ∂(gaussianReal 0 1) with hκ
  refine zero_of_bounds (G := ∫ ω, g ω ^ 2 ∂Q) (K := ((p.T : ℝ) / N) ^ 2 * κ)
    (D := 2 * (Cy : ℝ) ^ 4) fun r hr l μ hl hμ => ?_
  set F : ℕ → MeasurableSpace Ω := fun k => M.F (gr p (N * r) (j * r + k)) with hFdef
  set H : ℕ → MeasurableSpace Ω := fun k => M.F (gr p (N * r) (j * r + k)) ⊔ M.G p.T with hHdef
  set w : ℕ → Ω → ℝ := fun k => xg M (N * r) (j * r + k) with hwdef
  have hFm : Monotone F := fun a b hab => M.F.mono (gr_mono p (N * r) (by omega))
  have hHm : Monotone H := fun a b hab => sup_le_sup_right (hFm hab) _
  have hlaw : ∀ k, HasLaw (w k) (gaussianReal 0 (V (gr p (N * r) (j * r + k))
      (gr p (N * r) (j * r + k + 1)))) Q := fun k => xg_law_Q2 M hM h5 (N * r) (j * r + k)
  have hwmeas : ∀ k, Measurable (w k) := fun k => ξ_meas M hM _ _
  have hm4 : ∀ k, Integrable (fun ω => w k ω ^ 4) Q ∧
      ∫ ω, w k ω ^ 4 ∂Q = ((p.T : ℝ) / (N * r : ℕ)) ^ 2 * κ := by
    intro k
    obtain ⟨h1, h2⟩ := moment4 (hwmeas k) (hlaw k).map_eq
    refine ⟨h1, ?_⟩
    rw [h2, V_gr]
  have hy0 : StronglyMeasurable[H 0] y := by
    have e : gr p (N * r) (j * r + 0) = gr p N j := by rw [add_zero, StochCalcD3.gr_mul p hr]
    show StronglyMeasurable[M.F (gr p (N * r) (j * r + 0)) ⊔ M.G p.T] y
    rw [e]; exact hym.stronglyMeasurable
  have hle : ∀ k < r, j * r + k + 1 ≤ N * r := by
    intro k hk
    have : (j + 1) * r ≤ N * r := Nat.mul_le_mul_right r hj
    nlinarith
  have hB := E2_bound (Q := Q) (F := F) (H := H) hFm hHm (fun k => le_sup_left)
    (fun k => FGle M _) (g := g) (y := y) (w := w) r hg
    (fun k _ => memLp_xi (hwmeas k) (hlaw k)) (fun k _ => (hm4 k).1)
    (fun k _ => (ξ_measF M hM (gr_mono p (N * r) (Nat.le_succ _))).stronglyMeasurable)
    hy0 hyb
    (fun k hk => hQb _ (gr_le_T p (hle k hk)))
    (fun k _ h hh => by
      have hind : IndepFun h (w k) Q := by
        rw [IndepFun_iff_Indep]
        exact indep_of_indep_of_le_left (indep_xg_Q2 M hM h5 (N * r) (j * r + k))
          hh.measurable.comap_le
      have hmul := hind.integral_mul_eq_mul_integral (hh.mono (FGle M _)).aestronglyMeasurable
        (hwmeas k).aestronglyMeasurable
      simp only [Pi.mul_apply] at hmul
      rw [hmul, integral_gauss (hlaw k), mul_zero])
    (fun k hk z hz hzb => by
      set z' : Ω → ℝ := fun ω => max (-(Cy : ℝ)) (min (Cy : ℝ) (z ω)) with hz'
      have hz'm : Measurable[F k] z' :=
        measurable_const.max (measurable_const.min hz.measurable)
      have hz'b : ∀ ω, |z' ω| ≤ Cy := fun ω => by
        rw [abs_le]; constructor
        · exact le_max_left _ _
        · exact max_le (by linarith [Cy.2]) (min_le_left _ _)
      have hzz : ∀ᵐ ω ∂Q, z ω = z' ω := by
        filter_upwards [hzb] with ω hω
        rw [abs_le] at hω
        simp only [hz', min_eq_right hω.2, max_eq_right hω.1]
      rw [integral_congr_ae (show (fun ω => g ω * z ω * w k ω) =ᵐ[Q]
          (fun ω => g ω * z' ω * w k ω) from hzz.mono fun ω hω => by simp only [hω])]
      let Y : ℕ → Ω → ℝ := fun i => if i = j * r + k then z' else fun _ => 0
      have hYm : ∀ i, Measurable[M.F (gr p (N * r) i)] (Y i) := by
        intro i
        by_cases hi : i = j * r + k
        · subst hi; simp only [Y, if_true]; exact hz'm
        · simp only [Y, hi, if_false]; exact measurable_const
      have hYb : ∃ C : ℝ, ∀ i ω, |Y i ω| ≤ C := ⟨Cy, fun i ω => by
        by_cases hi : i = j * r + k
        · simp only [Y, hi, if_true]; exact hz'b ω
        · simp only [Y, hi, if_false, abs_zero]; exact Cy.2⟩
      have hNr : 0 < N * r := Nat.mul_pos hN hr
      have h0 := hfN (N * r) hNr Y hYm hYb
      have hsum : ∀ ω, ∑ i ∈ Finset.range (N * r), Y i ω * xg M (N * r) i ω =
          z' ω * w k ω := by
        intro ω
        rw [Finset.sum_eq_single (j * r + k)]
        · simp [Y, hwdef]
        · intro i _ hi; simp [Y, hi]
        · intro hn; exact absurd (Finset.mem_range.2 (by have := hle k hk; omega)) hn
      simp only [hsum] at h0
      rw [integral_Q2 M hM h5]
      have e : (fun ω => wZ M ω * (g ω * z' ω * w k ω)) =
          fun ω => (f ω * (M.Z p.T ω * (z' ω * w k ω))) / cZ M := by
        funext ω
        have hz : M.Z p.T ω ≠ 0 := (hZpos ω).ne'
        simp only [wZ, hgdef]
        field_simp
      rw [e, integral_div, h0, zero_div])
    hl hμ
  have hsumw : ∀ ω, ∑ k ∈ Finset.range r, w k ω = xg M N j ω := sum_xg M hr j
  simp only [hsumw] at hB
  have hS : ∑ k ∈ Finset.range r, ∫ ω, w k ω ^ 4 ∂Q = ((p.T : ℝ) / N) ^ 2 * κ / r := by
    rw [Finset.sum_congr rfl fun k _ => (hm4 k).2, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp
  rw [hS] at hB
  simpa only [hgdef] using hB

end StochCalcE5M

end StochCalcP6
-- ===== slice of P8c066573M17 (scratch/probe/slice8c/cuts/gK4c.lean.src/P8c066573M17.lean): 8/73 top-level decls kept =====

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








/-- **O7.6 (model).** -/
theorem E6 (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) {f : Ω → ℝ}
    (hfm : StronglyMeasurable[M.F p.T] f) (hf2 : MemLp f 2 M.P)
    (hG : ∀ ζ : Ω → ℝ, Measurable[M.G p.T] ζ → ∀ C : ℝ, (∀ ω, |ζ ω| ≤ C) →
      ∫ ω, f ω / M.Z p.T ω * ζ ω ∂(Qd M.P (wZ M)) = 0)
    (hE : ∀ N j : ℕ, j < N → ∀ y : Ω → ℝ, Measurable[M.F (gr p N j) ⊔ M.G p.T] y →
      ∀ Cy : ℝ≥0, (∀ ω, |y ω| ≤ Cy) →
      ∫ ω, f ω / M.Z p.T ω * y ω * xg M N j ω ∂(Qd M.P (wZ M)) = 0) :
    f =ᵐ[M.P] 0 := by
  exact HedgePSNV.tilted_orthogonality_vanish M hM h5 hfm hf2 hG hE





































































































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

/-- The σ-algebra of `P`-trivial sets (a.e. empty or a.e. full). -/
def trivMS (P : Measure Ω) : MeasurableSpace Ω where
  MeasurableSet' s := s =ᵐ[P] (∅ : Set Ω) ∨ s =ᵐ[P] (univ : Set Ω)
  measurableSet_empty := Or.inl EventuallyEq.rfl
  measurableSet_compl s hs := by
    rcases hs with h | h
    · right; simpa using h.compl
    · left; simpa using h.compl
  measurableSet_iUnion f hf := by
    by_cases h : ∀ i, f i =ᵐ[P] (∅ : Set Ω)
    · left
      exact ae_eq_empty.2 (measure_iUnion_null fun i => ae_eq_empty.1 (h i))
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      have hu := (hf i).resolve_left hi
      right
      rw [ae_eq_univ] at hu ⊢
      exact measure_mono_null (compl_subset_compl.2 (subset_iUnion f i)) hu

lemma F0_le_triv (M : Model p Ω) (hM : M.Standing) : M.F 0 ≤ trivMS M.P := by
  rw [hM.filtF 0]
  refine sup_le (iSup₂_le fun s hs => ?_) (MeasurableSpace.generateFrom_le fun N hN =>
    Or.inl (ae_eq_empty.2 hN.2))
  have hs0 : s = 0 := nonpos_iff_eq_zero.1 hs
  subst hs0
  intro t ht
  obtain ⟨A, -, rfl⟩ := ht
  have hB0 := hM.brownB.eval_zero_ae_eq_zero
  have hBt0 := hM.brownBt.eval_zero_ae_eq_zero
  have hg : (fun ω => (M.B 0 ω, M.Bt 0 ω)) =ᵐ[M.P] fun _ => ((0 : ℝ), (0 : ℝ)) := by
    filter_upwards [hB0, hBt0] with ω h1 h2
    simp [h1, h2]
  have hpre := hg.preimage A
  by_cases hA : ((0 : ℝ), (0 : ℝ)) ∈ A
  · right
    refine hpre.trans ?_
    simp [hA]
  · left
    refine hpre.trans ?_
    simp [hA]

/-- `E_P[f | F_0] = ∫ f dP`. -/
lemma condExp_F0 (M : Model p Ω) (hM : M.Standing) {f : Ω → ℝ} (hf : Integrable f M.P) :
    condExp (M.F 0) M.P f =ᵐ[M.P] fun _ => ∫ ω, f ω ∂M.P := by
  haveI := hM.prob
  refine (ae_eq_condExp_of_forall_setIntegral_eq (M.F.le 0) hf
    (fun s _ _ => integrableOn_const) (fun s hs _ => ?_)
    stronglyMeasurable_const.aestronglyMeasurable).symm
  rcases F0_le_triv M hM s hs with h | h
  · rw [setIntegral_congr_set h, setIntegral_congr_set h]
    simp
  · rw [setIntegral_congr_set h, setIntegral_congr_set h, setIntegral_univ, setIntegral_univ]
    simp

/-- **hG glue.**  The `hG` hypothesis of `StochCalcE6M.E6` from the first conjunct of
`Q2ce` at `t = 0` (with `cc := cZ M`) and `∫ f dP = 0`. -/
theorem hG_glue (M : Model p Ω) (hM : M.Standing) (h5 : M.Assumption5) {f : Ω → ℝ}
    (hf2 : MemLp f 2 M.P) (hf0 : ∫ ω, f ω ∂M.P = 0) {Ic : ℝ≥0 → Ω → ℝ}
    (hq : condExp (M.F 0 ⊔ M.G p.T) (Qd M.P (wZ M))
        (fun ω => (hf2.toLp f : Ω → ℝ) ω / M.Z p.T ω) =ᵐ[Qd M.P (wZ M)]
      (fun ω => condExp (M.F 0) M.P (hf2.toLp f : Ω → ℝ) ω / Zc M Ic 0 ω)) :
    ∀ ζ : Ω → ℝ, Measurable[M.G p.T] ζ → ∀ C : ℝ, (∀ ω, |ζ ω| ≤ C) →
      ∫ ω, f ω / M.Z p.T ω * ζ ω ∂(Qd M.P (wZ M)) = 0 := by
  intro ζ hζ C hζb
  have := hM.prob
  have := Q2_prob M hM h5
  set Q := Qd M.P (wZ M) with hQdef
  have hac : Q ≪ M.P := Qd_ac _
  set θ : Ω → ℝ := (hf2.toLp f : Ω → ℝ) with hθdef
  have hθf : θ =ᵐ[M.P] f := hf2.coeFn_toLp
  have hθ2 : MemLp θ 2 M.P := (MemLp.ae_eq hθf.symm hf2)
  have hZpos : ∀ ω, 0 < M.Z p.T ω := fun ω => Real.exp_pos _
  have hZsm : StronglyMeasurable[M.F p.T] (M.Z p.T) := h5.1.1 p.T le_rfl
  have hZm : Measurable (M.Z p.T) := (hZsm.mono (M.F.le p.T)).measurable
  set g : Ω → ℝ := fun ω => θ ω / M.Z p.T ω with hgdef
  have hg : MemLp g 2 Q := by
    have hae : AEStronglyMeasurable g Q :=
      ((hθ2.1.aemeasurable.div hZm.aemeasurable).aestronglyMeasurable).mono_ac (Qd_ac _)
    refine (memLp_two_iff_integrable_sq hae).2 ?_
    rw [integrable_Qd_iff (wZ_meas M hM) (wZ_pos M hM h5)]
    refine (hθ2.integrable_sq.div_const (cZ M)).congr (Eventually.of_forall fun ω => ?_)
    have hz : M.Z p.T ω ≠ 0 := (hZpos ω).ne'
    simp only [hgdef, wZ]
    field_simp
  have hgi : Integrable g Q := hg.integrable one_le_two
  have hm : M.F 0 ⊔ M.G p.T ≤ mΩ := sup_le (M.F.le 0) (M.G.le p.T)
  have hζm : Measurable[M.F 0 ⊔ M.G p.T] ζ := hζ.mono le_sup_right le_rfl
  have hζsm : StronglyMeasurable[M.F 0 ⊔ M.G p.T] ζ := hζm.stronglyMeasurable
  have hζmeas : Measurable ζ := hζm.mono hm le_rfl
  have hζg : Integrable (ζ * g) Q := by
    refine (hgi.bdd_mul (c := C) hζmeas.aestronglyMeasurable ?_)
    exact Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hζb ω
  -- step 1: replace f by θ
  have h1 : ∫ ω, f ω / M.Z p.T ω * ζ ω ∂Q = ∫ ω, (ζ * g) ω ∂Q := by
    refine integral_congr_ae ?_
    filter_upwards [hac.ae_le hθf] with ω hω
    simp only [Pi.mul_apply, hgdef, hω]
    ring
  -- step 2: pull out ζ
  have h2 : ∫ ω, (ζ * g) ω ∂Q = ∫ ω, (ζ * condExp (M.F 0 ⊔ M.G p.T) Q g) ω ∂Q := by
    rw [← integral_condExp hm (f := ζ * g)]
    exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hζsm hζg hgi)
  -- step 3: the conditional expectation vanishes
  have hc0 : condExp (M.F 0) M.P θ =ᵐ[M.P] 0 := by
    filter_upwards [condExp_F0 M hM (hθ2.integrable one_le_two)] with ω hω
    rw [hω, Pi.zero_apply, integral_congr_ae hθf, hf0]
  have h3 : condExp (M.F 0 ⊔ M.G p.T) Q g =ᵐ[Q] 0 := by
    filter_upwards [hq, hac.ae_le hc0] with ω hω hω0
    rw [hω, hω0]
    simp
  rw [h1, h2]
  have h4 : (ζ * condExp (M.F 0 ⊔ M.G p.T) Q g) =ᵐ[Q] fun _ => (0 : ℝ) := by
    filter_upwards [h3] with ω hω
    simp [hω]
  rw [integral_congr_ae h4]
  simp

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

























/-- **O7.0a**: `X_t ≠ 0` a.s. for `0 < t ≤ T` (non-degenerate model). -/
theorem X_ne_zero (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) {t : ℝ≥0}
    (ht0 : 0 < t) (htT : t ≤ p.T) : M.P {ω | M.X t ω = 0} = 0 := by
  exact HedgePSNV.asset_price_zero_set_null M hM h4 ht0 htT





























/-- `X ≠ 0` `μT`-a.e. -/
theorem X_ne_zero_μT (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) :
    ∀ᵐ z ∂(StochCalcO3.μT M.P p.T), M.X z.1.toNNReal z.2 ≠ 0 := by
  have := hM.prob
  have hXm : Measurable fun z : ℝ × Ω => M.X z.1.toNNReal z.2 :=
    StochCalcZ7b.joint_meas hM.X_cont fun s => ((X_measF M hM s).mono (M.F.le s)).measurable
  have hS : MeasurableSet {z : ℝ × Ω | M.X z.1.toNNReal z.2 = 0} :=
    hXm (measurableSet_singleton 0)
  rw [ae_iff]
  simp only [ne_eq, not_not]
  unfold StochCalcO3.μT
  rw [Measure.prod_apply hS]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  show M.P (Prod.mk u ⁻¹' {z : ℝ × Ω | M.X z.1.toNNReal z.2 = 0}) = 0
  have hpre : Prod.mk u ⁻¹' {z : ℝ × Ω | M.X z.1.toNNReal z.2 = 0} =
      {ω | M.X u.toNNReal ω = 0} := rfl
  rw [hpre]
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    have : {ω | M.X (0 : ℝ).toNNReal ω = 0} = ∅ := by
      ext ω; simp [hM.X_zero, p.hx₀.ne']
    rw [this, measure_empty]
  · refine X_ne_zero M hM h4 (Real.toNNReal_pos.2 hpos) ?_
    exact Real.toNNReal_le_iff_le_coe.2 hu.2.le

/-- **O7.0**: the `hac` input of `Q2ce` from the `O6_model` relation. -/
theorem O70 (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) {a' c : ℝ × Ω → ℝ}
    (hrel : ∀ᵐ z ∂(StochCalcO3.μT M.P p.T), a' z * Hx M z.1.toNNReal z.2 +
        c z * (M.X z.1.toNNReal z.2 * M.μ z.1.toNNReal z.2) = 0) :
    ∀ᵐ z ∂(StochCalcO3.μT M.P p.T), a' z = -(StochCalcZ2.etaT M z.1.toNNReal z.2) * c z := by
  have := hM.prob
  have hfst : ∀ᵐ z ∂(StochCalcO3.μT M.P p.T), z.1 ∈ Set.Ico (0 : ℝ) p.T := by
    unfold StochCalcO3.μT
    rw [ae_iff]
    have e : {z : ℝ × Ω | ¬ z.1 ∈ Set.Ico (0 : ℝ) p.T} = (Set.Ico (0 : ℝ) p.T)ᶜ ×ˢ Set.univ := by
      ext z; simp
    rw [e, Measure.prod_prod, Measure.restrict_apply' measurableSet_Ico]
    simp
  filter_upwards [hrel, X_ne_zero_μT M hM h4, hfst] with z h hX hz
  have hle : z.1.toNNReal ≤ p.T := Real.toNNReal_le_iff_le_coe.2 hz.2.le
  have hσ : 0 < M.σ z.1.toNNReal z.2 := hM.σ_pos _ _
  unfold StochCalcZ2.etaT
  rw [min_eq_left hle]
  unfold HedgePSNV.Model.η
  unfold Hx at h
  have h' : M.X z.1.toNNReal z.2 * (a' z * M.σ z.1.toNNReal z.2 +
      c z * M.μ z.1.toNNReal z.2) = 0 := by rw [← h]; ring
  have h2 := (mul_eq_zero.1 h').resolve_left hX
  field_simp
  linarith

end StochCalcX0

end StochCalcP6

-- ===== slice of RUmod (scratch/probe/slice8c/cuts/gK4c.lean.src/RUmod.lean): 11/17 top-level decls kept =====

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

/-- Elementary time-space functions `1_[u,v) Y`, Elem-free. -/
def SE (m : ℝ≥0 → MeasurableSpace Ω) (P : Measure Ω) (T : ℝ≥0) : Set (Lp ℝ 2 (μT P T)) :=
  {g | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧ ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
    ∃ h : MemLp (fun z : ℝ × Ω => ind u v z.1 * Y z.2) 2 (μT P T), g = h.toLp _}

/-- Elementary stochastic integrals `Y (W_v - W_u)`, Elem-free. -/
def SI (m : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (T : ℝ≥0) : Set (Lp ℝ 2 P) :=
  {g | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧ ∃ Y : Ω → ℝ, Measurable[m u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
    ∃ h : MemLp (fun ω => Y ω * (W v ω - W u ω)) 2 P, g = h.toLp _}

/-- `Rep`, Elem-free. -/
def RepU (m : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (T : ℝ≥0)
    (θ : Lp ℝ 2 P) (b : Lp ℝ 2 (μT P T)) : Prop :=
  θ ∈ closure (Submodule.span ℝ (SI m W P T) : Set (Lp ℝ 2 P)) ∧
    b ∈ closure (Submodule.span ℝ (SE m P T) : Set (Lp ℝ 2 (μT P T))) ∧
    ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[m u] Y → (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
      ∫ ω, (θ : Ω → ℝ) ω * (Y ω * (W v ω - W u ω)) ∂P =
        ∫ z, (b : ℝ × Ω → ℝ) z * (ind u v z.1 * Y z.2) ∂(μT P T)



lemma range_eE (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    Set.range (eE (P := P) hle T) = SE m P T := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.u, i.v, i.huv, i.hvT, i.Y, i.hY, ⟨i.C, i.hC⟩, memLp_efun hle i, rfl⟩
  · rintro ⟨u, v, huv, hvT, Y, hY, ⟨C, hC⟩, h, rfl⟩
    exact ⟨⟨u, v, huv, hvT, Y, hY, C, hC⟩, rfl⟩

lemma range_eI (hW : IncrHyp m W P) (T : ℝ≥0) :
    Set.range (eI hW T) = SI m W P T := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.u, i.v, i.huv, i.hvT, i.Y, i.hY, ⟨i.C, i.hC⟩, memLp_ifun hW i, rfl⟩
  · rintro ⟨u, v, huv, hvT, Y, hY, ⟨C, hC⟩, h, rfl⟩
    exact ⟨⟨u, v, huv, hvT, Y, hY, C, hC⟩, rfl⟩

lemma range_eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    Set.range (eL (P := P) hle T) = (Submodule.span ℝ (SE m P T) : Set (Lp ℝ 2 (μT P T))) := by
  rw [← LinearMap.coe_range]
  unfold eL
  rw [Finsupp.range_linearCombination, range_eE]

lemma range_TL (hW : IncrHyp m W P) (T : ℝ≥0) :
    Set.range (TL hW T) = (Submodule.span ℝ (SI m W P T) : Set (Lp ℝ 2 P)) := by
  rw [← LinearMap.coe_range]
  unfold TL
  rw [Finsupp.range_linearCombination, range_eI]

lemma closure_eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) :
    closure (Set.range (eL (P := P) hle T)) =
      closure (Submodule.span ℝ (SE m P T) : Set (Lp ℝ 2 (μT P T))) := by
  rw [range_eL]

lemma int_eI (hW : IncrHyp m W P) {T : ℝ≥0} (θ : Lp ℝ 2 P) (i : Elem m T) :
    ∫ ω, (θ : Ω → ℝ) ω * (i.Y ω * (W i.v ω - W i.u ω)) ∂P = ⟪θ, eI hW T i⟫_ℝ := by
  unfold eI
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_ifun hW i).coeFn_toLp] with ω hω
  rw [hω, ifun, RCLike.inner_apply, conj_trivial, mul_comm]

lemma int_eE (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (b : Lp ℝ 2 (μT P T)) (i : Elem m T) :
    ∫ z, (b : ℝ × Ω → ℝ) z * (ind i.u i.v z.1 * i.Y z.2) ∂(μT P T) = ⟪b, eE (P := P) hle T i⟫_ℝ := by
  unfold eE
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_efun (P := P) hle i).coeFn_toLp] with z hz
  rw [hz, efun, RCLike.inner_apply, conj_trivial, mul_comm]

lemma rep_iff (hW : IncrHyp m W P) (T : ℝ≥0) (θ : Lp ℝ 2 P) (b : Lp ℝ 2 (μT P T)) :
    StochCalcO3.Rep hW T θ b ↔ RepU m W P T θ b := by
  unfold StochCalcO3.Rep RepU
  rw [range_TL, range_eL]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩)
  · intro u v huv hvT Y hY hC
    obtain ⟨C, hC⟩ := hC
    let i : Elem m T := ⟨u, v, huv, hvT, Y, hY, C, hC⟩
    have h1 := h (Finsupp.single i 1)
    simp only [TL, eL, Finsupp.linearCombination_single, one_smul] at h1
    rw [int_eI hW θ i, int_eE hW.le b i]
    exact h1
  · intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add s1 s2 h1 h2 => simp only [map_add, inner_add_right, h1, h2]
    | single i a =>
      simp only [TL, eL, Finsupp.linearCombination_single, real_inner_smul_right]
      rw [← int_eI hW θ i, ← int_eE hW.le b i, h i.u i.v i.huv i.hvT i.Y i.hY ⟨i.C, i.hC⟩]

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

-- ===== slice of P8c066573M18 (scratch/probe/slice8c/cuts/gK4c.lean.src/P8c066573M18.lean): 19/23 top-level decls kept =====

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

theorem Q2ceG (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] (h5 : M.Assumption5)
    (hC : ContHyp M) {Ic : ℝ≥0 → Ω → ℝ}
    (hIc : ∀ ω, Continuous fun t => Ic t ω)
    (hIa : ∀ t, Measurable[completedBrownianPast M.P (W M) (fun _ => 0) t] (Ic t))
    (hIm : ∀ t, Measurable (Ic t)) (hI0 : ∀ ω, Ic 0 ω = 0)
    (hIe : ∀ t, t ≤ p.T → Ic t =ᵐ[M.P] M.I t) {Kj : ℝ≥0 → Ω → ℝ}
    (hKj : HasBrownianItoIntegral M.P (completedBrownianPast M.P (W M) (fun _ => 0))
      (fun s ω => W M s ω 0) (fun s ω => -(Zc M Ic s ω * etaT M s ω)) Kj)
    (hKz : ∀ t, ∀ᵐ ω ∂M.P, Zc M Ic t ω = 1 + Kj t ω)
    {θ θB : Lp ℝ 2 M.P} {a : Lp ℝ 2 (μT M.P p.T)} (h : Rep (incr_B M hM) p.T θB a)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT M.P p.T))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT M.P p.T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := M.P) (incr_B M hM).le p.T)) →
      ∫ z, c z * ψ z ∂(μT M.P p.T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T))
    (hac : ∀ᵐ z ∂(μT M.P p.T), a z = -(etaT M z.1.toNNReal z.2) * c z)
    {t : ℝ≥0} (htT : t ≤ p.T)
    (hperp : condExp (Kf M t p.T) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω) =ᵐ[M.P]
      condExp (M.F t) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω)) {cc : ℝ} (hcc : 0 < cc)
    [IsFiniteMeasure (Qd M.P fun ω => M.Z p.T ω ^ 2 / cc)] :
    condExp (M.F t ⊔ M.G p.T) (Qd M.P fun ω => M.Z p.T ω ^ 2 / cc)
        (fun ω => (θ : Ω → ℝ) ω / M.Z p.T ω) =ᵐ[Qd M.P fun ω => M.Z p.T ω ^ 2 / cc]
      (fun ω => condExp (M.F t) M.P θ ω / Zc M Ic t ω) ∧
    condExp (M.F t) (Qd M.P fun ω => M.Z p.T ω ^ 2 / cc)
        (fun ω => (θ : Ω → ℝ) ω / M.Z p.T ω) =ᵐ[Qd M.P fun ω => M.Z p.T ω ^ 2 / cc]
      (fun ω => condExp (M.F t) M.P θ ω / Zc M Ic t ω) := by
  exact HedgePSNV.tilted_bayes_conditional_expectation M hM h5 (StochCalcBr.W M) (fun _ _ => rfl) hC hIc hIa hIm hI0 hIe (StochCalcP6.StochCalcZ3.Zc M Ic) (fun _ _ => rfl) hKj hKz (StochCalcP6.StochCalcO3.μT M.P p.T) rfl ((StochCalcP6.StochCalcRU.rep_iff (incr_B M hM) p.T θB a).1 h).1 ((StochCalcP6.StochCalcRU.rep_iff (incr_B M hM) p.T θB a).1 h).2.1 ((StochCalcP6.StochCalcRU.rep_iff (incr_B M hM) p.T θB a).1 h).2.2 hc (fun ψ hψ hm => hproj ψ hψ (by rw [StochCalcP6.StochCalcRU.closure_eL]; exact hm)) hac htT (by rw [← StochCalcP6.StochCalcKF.Kf_ge M htT]; exact hperp) hcc (Qd M.P fun ω => M.Z p.T ω ^ 2 / cc) rfl





















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

theorem O6_modelP (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P]
    (h4 : M.Assumption4) {f : Ω → ℝ}
    (hf : MemLp f 2 M.P) {a : ℝ × Ω → ℝ} (ha2 : MemLp a 2 (μT M.P p.T))
    (ha : ∀ i : Elem M.F p.T,
      ∫ ω, f ω * ifun M.B i ω ∂M.P = ∫ z, a z * efun i z ∂(μT M.P p.T))
    (hfA : ∀ θχ ∈ M.AX, ∫ ω, f ω * θχ.2 p.T ω ∂M.P = 0) :
    ∃ a' c : ℝ × Ω → ℝ, MemLp a' 2 (μT M.P p.T) ∧ MemLp c 2 (μT M.P p.T) ∧
      (∀ h : MemLp a' 2 (μT M.P p.T),
        h.toLp a' ∈ closure (Set.range (eL (P := M.P) M.F.le p.T))) ∧
      (∀ i : Elem M.F p.T,
        ∫ ω, f ω * ifun M.B i ω ∂M.P = ∫ z, a' z * efun i z ∂(μT M.P p.T)) ∧
      (∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT M.P p.T),
        hψ.toLp ψ ∈ closure (Set.range (eL (P := M.P) M.F.le p.T)) →
        ∫ z, c z * ψ z ∂(μT M.P p.T) = ∫ z, f z.2 * ψ z ∂(μT M.P p.T)) ∧
      ∀ᵐ z ∂(μT M.P p.T), a' z * Hx M z.1.toNNReal z.2 +
        c z * (M.X z.1.toNNReal z.2 * M.μ z.1.toNNReal z.2) = 0 := by
  exact (by obtain ⟨a', c, h1, h2, h3, h4', h5', h6⟩ := HedgePSNV.orthogonal_claim_integrand_relation M hM h4 _ rfl hf ha2 (fun u v huv hvT Y hY hC => by obtain ⟨C, hC⟩ := hC; exact ha ⟨u, v, huv, hvT, Y, hY, C, hC⟩) hfA; exact ⟨a', c, h1, h2, (fun h => by rw [StochCalcP6.StochCalcRU.closure_eL]; exact h3 h), (fun i => h4' i.u i.v i.huv i.hvT i.Y i.hY ⟨i.C, i.hC⟩), (fun ψ hψ hm => h5' ψ hψ (by rw [StochCalcP6.StochCalcRU.closure_eL] at hm; exact hm)), h6⟩)













































































































end StochCalcO6M

namespace StochCalcG3

open MeasureTheory ProbabilityTheory Filter Topology StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} {m1 m2 mG n : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- Two conditional expectations that agree on a family `e i ⊆ L²` agree on the closed span. -/
theorem ce_eq_closure (h1 : m1 ≤ mΩ) (h2 : m2 ≤ mΩ)
    {ι : Type*} (e : ι → Lp ℝ 2 P)
    (he : ∀ i, condExp m1 P (e i : Ω → ℝ) =ᵐ[P] condExp m2 P (e i : Ω → ℝ))
    {θ : Lp ℝ 2 P} (hθ : θ ∈ closure (Set.range (Finsupp.linearCombination ℝ e))) :
    condExp m1 P (θ : Ω → ℝ) =ᵐ[P] condExp m2 P (θ : Ω → ℝ) := by
  set Φ : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
    (lpMeas ℝ ℝ m1 2 P).subtypeL.comp (condExpL2 ℝ ℝ h1) -
      (lpMeas ℝ ℝ m2 2 P).subtypeL.comp (condExpL2 ℝ ℝ h2) with hΦ
  have key : ∀ y : Lp ℝ 2 P, Φ y = 0 ↔
      condExp m1 P (y : Ω → ℝ) =ᵐ[P] condExp m2 P (y : Ω → ℝ) := by
    intro y
    have e1 := (Lp.memLp y).condExpL2_ae_eq_condExp (𝕜 := ℝ) h1
    have e2 := (Lp.memLp y).condExpL2_ae_eq_condExp (𝕜 := ℝ) h2
    simp only [Lp.toLp_coeFn] at e1 e2
    have hΦy : Φ y = ((condExpL2 ℝ ℝ h1 y : lpMeas ℝ ℝ m1 2 P) : Lp ℝ 2 P) -
        ((condExpL2 ℝ ℝ h2 y : lpMeas ℝ ℝ m2 2 P) : Lp ℝ 2 P) := rfl
    have hc : (Φ y : Ω → ℝ) =ᵐ[P]
        fun ω => condExp m1 P (y : Ω → ℝ) ω - condExp m2 P (y : Ω → ℝ) ω := by
      rw [hΦy]
      filter_upwards [Lp.coeFn_sub ((condExpL2 ℝ ℝ h1 y : lpMeas ℝ ℝ m1 2 P) : Lp ℝ 2 P)
        ((condExpL2 ℝ ℝ h2 y : lpMeas ℝ ℝ m2 2 P) : Lp ℝ 2 P), e1, e2] with ω h h1' h2'
      rw [h, Pi.sub_apply, h1', h2']
    rw [Lp.eq_zero_iff_ae_eq_zero]
    constructor
    · intro h0
      filter_upwards [hc, h0] with ω h h'
      have := h.symm.trans h'
      simpa only [Pi.zero_apply, sub_eq_zero] using this
    · intro h0
      filter_upwards [hc, h0] with ω h h'
      rw [h, h', sub_self, Pi.zero_apply]
  have hclosed : IsClosed {y : Lp ℝ 2 P | Φ y = 0} := isClosed_eq Φ.continuous continuous_const
  have hsub : Set.range (Finsupp.linearCombination ℝ e) ⊆ {y | Φ y = 0} := by
    rintro _ ⟨x, rfl⟩
    show Φ _ = 0
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x1 x2 hx1 hx2 => rw [map_add, map_add, hx1, hx2, add_zero]
    | single i a => rw [Finsupp.linearCombination_single, map_smul, (key _).2 (he i), smul_zero]
  exact (key θ).1 (hclosed.closure_subset_iff.2 hsub hθ)

/-- A `W`-increment after `c`, weighted by a bounded `mF c`-variable, has zero conditional
expectation given any `n ≤ mF c ⊔ mG`, when the increments are independent of `mF c ⊔ mG`. -/
lemma ce_zero {mF : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}
    (hFG : IncrHyp (fun u => mF u ⊔ mG) W P) {c d : ℝ≥0} (hcd : c ≤ d)
    (hn : n ≤ mF c ⊔ mG) {g : Ω → ℝ} (hg : Measurable[mF c] g) {C : ℝ}
    (hC : ∀ ω, |g ω| ≤ C) :
    condExp n P (fun ω => g ω * (W d ω - W c ω)) =ᵐ[P] 0 := by
  have hn0 : n ≤ mΩ := hn.trans (hFG.le c)
  have hgG : Measurable[mF c ⊔ mG] g := hg.mono le_sup_left le_rfl
  have hga : AEStronglyMeasurable g P := (hgG.mono (hFG.le c) le_rfl).aestronglyMeasurable
  have hint : Integrable (fun ω => g ω * (W d ω - W c ω)) P :=
    ((hFG.mem2 c d).integrable one_le_two).bdd_mul hga
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hn0 hint (fun s _ _ => integrableOn_zero)
    (fun s hs _ => ?_) stronglyMeasurable_zero.aestronglyMeasurable).symm
  rw [integral_zero, ← integral_indicator (hn0 s hs)]
  have e : s.indicator (fun ω => g ω * (W d ω - W c ω)) =
      fun ω => s.indicator g ω * (W d ω - W c ω) := by
    funext ω; by_cases h : ω ∈ s <;> simp [Set.indicator, h]
  rw [e]
  exact (int_mul_dW hFG hcd (hgG.indicator (hn s hs))).symm

/-- Elementary case of G3. -/
theorem ce_elem {mF : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ} (hF : IncrHyp mF W P)
    (hFG : IncrHyp (fun u => mF u ⊔ mG) W P) {T : ℝ≥0}
    (i : Elem mF T) (t : ℝ≥0) :
    condExp (mF t ⊔ mG) P (ifun W i) =ᵐ[P] condExp (mF t) P (ifun W i) := by
  have hle1 : mF t ⊔ mG ≤ mΩ := hFG.le t
  have hle2 : mF t ≤ mΩ := hF.le t
  have hint : Integrable (ifun W i) P := (memLp_ifun hF i).integrable one_le_two
  have hYa : AEStronglyMeasurable i.Y P := (i.hY.mono (hF.le i.u) le_rfl).aestronglyMeasurable
  have hYb : ∀ᵐ ω ∂P, ‖i.Y ω‖ ≤ i.C :=
    Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact i.hC ω
  rcases le_total i.v t with hvt | htv
  · have hm : StronglyMeasurable[mF t] (ifun W i) :=
      ((i.hY.mono (hF.mono (i.huv.trans hvt)) le_rfl).mul
        ((dW_meas hF i.huv).mono (hF.mono hvt) le_rfl)).stronglyMeasurable
    rw [condExp_of_stronglyMeasurable hle1 (hm.mono le_sup_left) hint,
      condExp_of_stronglyMeasurable hle2 hm hint]
  rcases le_total i.u t with hut | htu
  · have hsplit : ifun W i = (fun ω => i.Y ω * (W t ω - W i.u ω)) +
        fun ω => i.Y ω * (W i.v ω - W t ω) := by
      funext ω; simp only [ifun, Pi.add_apply]; ring
    have hYt : Measurable[mF t] i.Y := i.hY.mono (hF.mono hut) le_rfl
    have hm1 : StronglyMeasurable[mF t] (fun ω => i.Y ω * (W t ω - W i.u ω)) :=
      (hYt.mul (dW_meas hF hut)).stronglyMeasurable
    have hi1 : Integrable (fun ω => i.Y ω * (W t ω - W i.u ω)) P :=
      ((hF.mem2 i.u t).integrable one_le_two).bdd_mul hYa hYb
    have hi2 : Integrable (fun ω => i.Y ω * (W i.v ω - W t ω)) P :=
      ((hF.mem2 t i.v).integrable one_le_two).bdd_mul hYa hYb
    rw [hsplit]
    filter_upwards [condExp_add hi1 hi2 (mF t ⊔ mG), condExp_add hi1 hi2 (mF t),
      ce_zero hFG htv (n := mF t ⊔ mG) le_rfl hYt i.hC,
      ce_zero hFG htv (n := mF t) le_sup_left hYt i.hC] with ω h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, Pi.add_apply, h3, h4,
      condExp_of_stronglyMeasurable hle1 (hm1.mono le_sup_left) hi1,
      condExp_of_stronglyMeasurable hle2 hm1 hi1]
  · have hX : ifun W i = fun ω => i.Y ω * (W i.v ω - W i.u ω) := rfl
    rw [hX]
    filter_upwards [ce_zero hFG i.huv (n := mF t ⊔ mG) (sup_le_sup_right (hF.mono htu) _) i.hY i.hC,
      ce_zero hFG i.huv (n := mF t) ((hF.mono htu).trans le_sup_left) i.hY i.hC] with ω h1 h2
    exact h1.trans h2.symm

end StochCalcG3

namespace StochCalcG3M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcO3 StochCalcO3M StochCalcKF StochCalcSteinM
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The `B~` increments with the enlarged filtration `F_u ⊔ G_T'`. -/
theorem incr_BtG (M : Model p Ω) (hM : M.Standing) (T' : ℝ≥0) :
    IncrHyp (fun u => M.F u ⊔ M.G T') M.Bt M.P := by
  have := hM.prob
  have hB := incr_Bt M hM
  exact
  { mono := fun _ _ h => sup_le_sup_right (M.F.mono h) _
    le := fun t => sup_le (M.F.le t) ((StochCalcD1aW.G_le_F M hM T').trans (M.F.le T'))
    adapt := fun t => (hB.adapt t).mono le_sup_left le_rfl
    indep := fun u v huv => indep_ξ M hM huv T'
    mem2 := hB.mem2
    mean := hB.mean
    var := hB.var }

/-- **G3.** For `θ` a `B~`-integral, `E[θ | K^t_T] = E[θ | F_t]`. -/
theorem G3 (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] {T t : ℝ≥0} (htT : t ≤ T) {θ : Lp ℝ 2 M.P}
    (hθ : θ ∈ closure (Set.range (TL (incr_Bt M hM) T))) :
    condExp (Kf M t T) M.P (θ : Ω → ℝ) =ᵐ[M.P] condExp (M.F t) M.P (θ : Ω → ℝ) := by
  have := hM.prob
  rw [Kf_ge M htT]
  have hG := incr_BtG M hM T
  refine StochCalcG3.ce_eq_closure (hG.le t) (M.F.le t) (eI (incr_Bt M hM) T) (fun i => ?_) hθ
  have e : (eI (incr_Bt M hM) T i : Ω → ℝ) =ᵐ[M.P] ifun M.Bt i := (memLp_ifun (incr_Bt M hM) i).coeFn_toLp
  filter_upwards [condExp_congr_ae (m := M.F t ⊔ M.G T) e, condExp_congr_ae (m := M.F t) e,
    StochCalcG3.ce_elem (incr_Bt M hM) hG i t] with ω h1 h2 h3
  rw [h1, h2, h3]

end StochCalcG3M


namespace StochCalcG4

open MeasureTheory ProbabilityTheory Filter Topology StochCalcO3
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

lemma inner_toLp {f : Ω → ℝ} (hf : MemLp f 2 P) (g : Lp ℝ 2 P) :
    ⟪hf.toLp f, g⟫_ℝ = ∫ ω, f ω * g ω ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with ω hω
  rw [hω, RCLike.inner_apply', conj_trivial]

lemma inner_Lp (f g : Lp ℝ 2 P) : ⟪f, g⟫_ℝ = ∫ ω, f ω * g ω ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [RCLike.inner_apply', conj_trivial]

lemma clos_inner_zero {ι : Type*} (e : ι → Lp ℝ 2 P) (v : Lp ℝ 2 P) (h : ∀ i, ⟪v, e i⟫_ℝ = 0)
    {θ : Lp ℝ 2 P} (hθ : θ ∈ closure (Set.range (Finsupp.linearCombination ℝ e))) :
    ⟪v, θ⟫_ℝ = 0 := by
  have hclosed : IsClosed {y : Lp ℝ 2 P | ⟪v, y⟫_ℝ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsub : Set.range (Finsupp.linearCombination ℝ e) ⊆ {y | ⟪v, y⟫_ℝ = 0} := by
    rintro _ ⟨x, rfl⟩
    show ⟪v, _⟫_ℝ = 0
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x1 x2 hx1 hx2 => rw [map_add, inner_add_right, hx1, hx2, add_zero]
    | single i a => rw [Finsupp.linearCombination_single, real_inner_smul_right, h i, mul_zero]
  exact hclosed.closure_subset_iff.2 hsub hθ

lemma clos_aesm {ι : Type*} (e : ι → Lp ℝ 2 P) (hm : m ≤ mΩ)
    (h : ∀ i, AEStronglyMeasurable[m] (e i : Ω → ℝ) P)
    {θ : Lp ℝ 2 P} (hθ : θ ∈ closure (Set.range (Finsupp.linearCombination ℝ e))) :
    AEStronglyMeasurable[m] (θ : Ω → ℝ) P := by
  have hsub : Set.range (Finsupp.linearCombination ℝ e) ⊆
      {f : Lp ℝ 2 P | AEStronglyMeasurable[m] (f : Ω → ℝ) P} := by
    rintro _ ⟨x, rfl⟩
    have hspan : Submodule.span ℝ (Set.range e) ≤ lpMeas ℝ ℝ m 2 P := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact mem_lpMeas_iff_aestronglyMeasurable.2 (h i)
    have hx : Finsupp.linearCombination ℝ e x ∈ lpMeas ℝ ℝ m 2 P :=
      hspan (by rw [← Finsupp.range_linearCombination]; exact ⟨x, rfl⟩)
    exact mem_lpMeas_iff_aestronglyMeasurable.1 hx
  exact (isClosed_aestronglyMeasurable hm).closure_subset_iff.2 hsub hθ

variable {mF : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

lemma ifun_meas (hW : IncrHyp mF W P) {T : ℝ≥0} (i : Elem mF T) :
    Measurable[mF T] (ifun W i) :=
  (i.hY.mono (hW.mono (i.huv.trans i.hvT)) le_rfl).mul ((dW_meas hW i.huv).mono (hW.mono i.hvT) le_rfl)

lemma eI_aesm (hW : IncrHyp mF W P) {T : ℝ≥0} (i : Elem mF T) :
    AEStronglyMeasurable[mF T] (eI hW T i : Ω → ℝ) P :=
  (ifun_meas hW i).stronglyMeasurable.aestronglyMeasurable.congr (memLp_ifun hW i).coeFn_toLp.symm

lemma int_ifun (hW : IncrHyp mF W P) {T : ℝ≥0} (θ : Lp ℝ 2 P) (i : Elem mF T) :
    ∫ ω, θ ω * ifun W i ω ∂P = ⟪θ, eI hW T i⟫_ℝ := by
  rw [inner_Lp]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_ifun hW i).coeFn_toLp] with ω hω
  rw [eI, hω]

lemma TL_mean (hW : IncrHyp mF W P) {T : ℝ≥0} {θ : Lp ℝ 2 P}
    (hθ : θ ∈ closure (Set.range (TL hW T))) : ∫ ω, θ ω ∂P = 0 := by
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 P := memLp_const 1
  have h := clos_inner_zero (eI hW T) (h1.toLp _) (fun i => ?_) hθ
  · rw [inner_toLp] at h
    simpa only [one_mul] using h
  · rw [inner_toLp]
    have e : ∫ ω, (1 : ℝ) * (eI hW T i : Ω → ℝ) ω ∂P = ∫ ω, ifun W i ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [(memLp_ifun hW i).coeFn_toLp] with ω hω
      rw [eI, hω, one_mul]
    rw [e]
    exact int_mul_dW hW i.huv i.hY

end StochCalcG4


namespace StochCalcG4M

open MeasureTheory ProbabilityTheory Filter Topology HedgePSNV
open StochCalcO3 StochCalcO3M StochCalcG3M StochCalcG4 StochCalcR1M StochCalcR4 StochCalcR7 StochCalcD2
  StochCalcD3 StochCalcTiltM
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma YY_bd {T : ℝ≥0} {M : Model p Ω} (i j : Elem M.F T) :
    ∀ᵐ ω ∂M.P, ‖i.Y ω * j.Y ω‖ ≤ i.C * j.C :=
  Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (i.hC ω) (j.hC ω) (abs_nonneg _) ((abs_nonneg _).trans (i.hC ω))

/-- Cross-orthogonality of elementary `B~`- and `B`-integrals. -/
theorem cross (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] {T : ℝ≥0}
    (i j : Elem M.F T) : ∫ ω, ifun M.Bt i ω * ifun M.B j ω ∂M.P = 0 := by
  have hB := incr_B M hM
  have hBt := incr_Bt M hM
  have hG := incr_BtG M hM T
  have hdBG : Measurable[M.G T] (fun ω => M.B j.v ω - M.B j.u ω) :=
    (B_measG M hM j.hvT).sub (B_measG M hM (j.huv.trans j.hvT))
  have hYYa : AEStronglyMeasurable (fun ω => i.Y ω * j.Y ω) M.P :=
    ((i.hY.mono (M.F.le i.u) le_rfl).mul (j.hY.mono (M.F.le j.u) le_rfl)).aestronglyMeasurable
  rcases le_total j.u i.u with hji | hij
  · have hg : Measurable[M.F i.u ⊔ M.G T]
        (fun ω => i.Y ω * (j.Y ω * (M.B j.v ω - M.B j.u ω))) :=
      (i.hY.mono le_sup_left le_rfl).mul
        (((j.hY.mono (M.F.mono hji) le_rfl).mono le_sup_left le_rfl).mul
          (hdBG.mono le_sup_right le_rfl))
    rw [← int_mul_dW hG i.huv hg]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [ifun]; ring
  rcases le_total i.v j.u with hvj | hjv
  · have hg : Measurable[M.F j.u] (fun ω => ifun M.Bt i ω * j.Y ω) :=
      (((i.hY.mono (M.F.mono (i.huv.trans hvj)) le_rfl).mul
        ((dW_meas hBt i.huv).mono (M.F.mono hvj) le_rfl))).mul j.hY
    rw [← int_mul_dW hB j.huv hg]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [ifun]; ring
  · have hg1 : Measurable[M.F j.u] (fun ω => i.Y ω * (M.Bt j.u ω - M.Bt i.u ω) * j.Y ω) :=
      ((i.hY.mono (M.F.mono hij) le_rfl).mul (dW_meas hBt hij)).mul j.hY
    have hg2 : Measurable[M.F j.u ⊔ M.G T]
        (fun ω => i.Y ω * (j.Y ω * (M.B j.v ω - M.B j.u ω))) :=
      ((i.hY.mono (M.F.mono hij) le_rfl).mono le_sup_left le_rfl).mul
        ((j.hY.mono le_sup_left le_rfl).mul (hdBG.mono le_sup_right le_rfl))
    have hi1 : Integrable (fun ω => i.Y ω * (M.Bt j.u ω - M.Bt i.u ω) * j.Y ω *
        (M.B j.v ω - M.B j.u ω)) M.P := by
      refine (((hBt.mem2 i.u j.u).integrable_mul (hB.mem2 j.u j.v)).bdd_mul hYYa
        (YY_bd i j)).congr (Eventually.of_forall fun ω => ?_)
      simp only [Pi.mul_apply]; ring
    have hi2 : Integrable (fun ω => i.Y ω * (j.Y ω * (M.B j.v ω - M.B j.u ω)) *
        (M.Bt i.v ω - M.Bt j.u ω)) M.P := by
      refine (((hB.mem2 j.u j.v).integrable_mul (hBt.mem2 j.u i.v)).bdd_mul hYYa
        (YY_bd i j)).congr (Eventually.of_forall fun ω => ?_)
      simp only [Pi.mul_apply]; ring
    have e : ∫ ω, ifun M.Bt i ω * ifun M.B j ω ∂M.P =
        ∫ ω, (i.Y ω * (M.Bt j.u ω - M.Bt i.u ω) * j.Y ω * (M.B j.v ω - M.B j.u ω) +
          i.Y ω * (j.Y ω * (M.B j.v ω - M.B j.u ω)) * (M.Bt i.v ω - M.Bt j.u ω)) ∂M.P := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [ifun]; ring
    rw [e, integral_add hi1 hi2, int_mul_dW hB j.huv hg1, int_mul_dW hG hjv hg2, add_zero]

/-- **G4.** An `F_T`-measurable centred `f ∈ L²` whose elementary `B`- and `B~`-moments are those
of `θB + θB~` (closed spans of elementary integrals) equals `θB + θB~`. -/
theorem G4 (M : Model p Ω) (hM : M.Standing) [IsProbabilityMeasure M.P] {f : Ω → ℝ}
    (hfm : StronglyMeasurable[M.F p.T] f) (hf2 : MemLp f 2 M.P) (hf1 : ∫ ω, f ω ∂M.P = 0)
    {θB θBt : Lp ℝ 2 M.P}
    (hθB : θB ∈ closure (Set.range (TL (incr_B M hM) p.T)))
    (hθBt : θBt ∈ closure (Set.range (TL (incr_Bt M hM) p.T)))
    (hfB : ∀ i : Elem M.F p.T,
      ∫ ω, f ω * ifun M.B i ω ∂M.P = ∫ ω, θB ω * ifun M.B i ω ∂M.P)
    (hfBt : ∀ i : Elem M.F p.T,
      ∫ ω, f ω * ifun M.Bt i ω ∂M.P = ∫ ω, θBt ω * ifun M.Bt i ω ∂M.P) :
    f =ᵐ[M.P] fun ω => θB ω + θBt ω := by
  have hB := incr_B M hM
  have hBt := incr_Bt M hM
  have hFle := M.F.le p.T
  -- orthogonality facts
  have pB : ∀ i : Elem M.F p.T, ∫ ω, θBt ω * ifun M.B i ω ∂M.P = 0 := fun i => by
    rw [int_ifun hB, real_inner_comm]
    refine clos_inner_zero (eI hBt p.T) _ (fun j => ?_) hθBt
    rw [inner_Lp, ← cross M hM j i]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_ifun hB i).coeFn_toLp, (memLp_ifun hBt j).coeFn_toLp] with ω h1 h2
    rw [eI, eI, h1, h2, mul_comm]
  have pBt : ∀ i : Elem M.F p.T, ∫ ω, θB ω * ifun M.Bt i ω ∂M.P = 0 := fun i => by
    rw [int_ifun hBt, real_inner_comm]
    refine clos_inner_zero (eI hB p.T) _ (fun j => ?_) hθB
    rw [inner_Lp, ← cross M hM i j]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_ifun hBt i).coeFn_toLp, (memLp_ifun hB j).coeFn_toLp] with ω h1 h2
    rw [eI, eI, h1, h2]
  have m1 : ∫ ω, θB ω ∂M.P = 0 := TL_mean hB hθB
  have m2 : ∫ ω, θBt ω ∂M.P = 0 := TL_mean hBt hθBt
  -- measurable versions
  have aB : AEStronglyMeasurable[M.F p.T] (θB : Ω → ℝ) M.P :=
    clos_aesm (eI hB p.T) hFle (fun i => eI_aesm hB i) hθB
  have aBt : AEStronglyMeasurable[M.F p.T] (θBt : Ω → ℝ) M.P :=
    clos_aesm (eI hBt p.T) hFle (fun i => eI_aesm hBt i) hθBt
  set V : Ω → ℝ := fun ω => f ω - θB ω - θBt ω with hVdef
  set V' : Ω → ℝ := fun ω => f ω - aB.mk _ ω - aBt.mk _ ω with hV'def
  have hV'sm : StronglyMeasurable[M.F p.T] V' :=
    (hfm.sub aB.stronglyMeasurable_mk).sub aBt.stronglyMeasurable_mk
  have hVV' : V =ᵐ[M.P] V' := by
    filter_upwards [aB.ae_eq_mk, aBt.ae_eq_mk] with ω h1 h2
    simp only [hVdef, hV'def, h1, h2]
  have hV2 : MemLp V 2 M.P := (hf2.sub (Lp.memLp θB)).sub (Lp.memLp θBt)
  have hV'2 : MemLp V' 2 M.P := hV2.ae_eq hVV'
  -- orthogonality of `V` to constants and elementary integrals
  have oc : ∫ ω, V ω ∂M.P = 0 := by
    have i1 : Integrable f M.P := hf2.integrable one_le_two
    have i2 : Integrable (fun ω => (θB : Ω → ℝ) ω) M.P := (Lp.memLp θB).integrable one_le_two
    have i3 : Integrable (fun ω => (θBt : Ω → ℝ) ω) M.P := (Lp.memLp θBt).integrable one_le_two
    have i12 : Integrable (fun ω => f ω - (θB : Ω → ℝ) ω) M.P := i1.sub i2
    rw [hVdef, integral_sub i12 i3, integral_sub i1 i2, hf1, m1, m2]
    simp
  have oI : ∀ (W : ℝ≥0 → Ω → ℝ) (hW : IncrHyp M.F W M.P) (i : Elem M.F p.T),
      ∫ ω, f ω * ifun W i ω ∂M.P = ∫ ω, θB ω * ifun W i ω ∂M.P + ∫ ω, θBt ω * ifun W i ω ∂M.P →
      ∫ ω, V ω * ifun W i ω ∂M.P = 0 := by
    intro W hW i h
    have hI := memLp_ifun hW i
    have j1 : Integrable (fun ω => f ω * ifun W i ω) M.P := hf2.integrable_mul hI
    have j2 : Integrable (fun ω => (θB : Ω → ℝ) ω * ifun W i ω) M.P :=
      (Lp.memLp θB).integrable_mul hI
    have j3 : Integrable (fun ω => (θBt : Ω → ℝ) ω * ifun W i ω) M.P :=
      (Lp.memLp θBt).integrable_mul hI
    have j12 : Integrable (fun ω => f ω * ifun W i ω - (θB : Ω → ℝ) ω * ifun W i ω) M.P :=
      j1.sub j2
    have e : ∫ ω, V ω * ifun W i ω ∂M.P = ∫ ω, (f ω * ifun W i ω -
        (θB : Ω → ℝ) ω * ifun W i ω - (θBt : Ω → ℝ) ω * ifun W i ω) ∂M.P := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hVdef]; ring
    rw [e, integral_sub j12 j3, integral_sub j1 j2, h]; ring
  have oB : ∀ i : Elem M.F p.T, ∫ ω, V ω * ifun M.B i ω ∂M.P = 0 := fun i =>
    oI M.B hB i (by rw [hfB i, pB i, add_zero])
  have oBt : ∀ i : Elem M.F p.T, ∫ ω, V ω * ifun M.Bt i ω ∂M.P = 0 := fun i =>
    oI M.Bt hBt i (by rw [hfBt i, pBt i, zero_add])
  -- `V' ⊥` grid sums, then `hsep`
  have hV'0 := hsep M hM V' (memLp_trim_of hFle hV'sm hV'2) (fun g hg => by
    obtain ⟨hgm, hg2⟩ := IsGS_props M hM hg
    rw [← integral_trim hFle (f := fun ω => V' ω * g ω) (hV'sm.mul hgm)]
    have e1 : ∫ ω, V' ω * g ω ∂M.P = ∫ ω, V ω * g ω ∂M.P :=
      integral_congr_ae (by filter_upwards [hVV'] with ω h; rw [h])
    rw [e1]
    obtain ⟨n, hn, c, Y, Z, C, hYm, hYb, hZm, hZb, rfl⟩ := hg
    let eY : ∀ k, k < n → Elem M.F p.T := fun k hk =>
      ⟨gr p n k, gr p n (k + 1), gr_mono p n (Nat.le_succ k), gr_le_T p hk, Y k,
        (hYm k).measurable, C, hYb k⟩
    let eZ : ∀ k, k < n → Elem M.F p.T := fun k hk =>
      ⟨gr p n k, gr p n (k + 1), gr_mono p n (Nat.le_succ k), gr_le_T p hk, Z k,
        (hZm k).measurable, C, hZb k⟩
    have iY : ∀ k ∈ Finset.range n, Integrable
        (fun ω => V ω * (Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω)) M.P := fun k hk =>
      hV2.integrable_mul (memLp_ifun hB (eY k (Finset.mem_range.1 hk)))
    have iZ : ∀ k ∈ Finset.range n, Integrable
        (fun ω => V ω * (Z k ω * ξ M (gr p n k) (gr p n (k + 1)) ω)) M.P := fun k hk =>
      hV2.integrable_mul (memLp_ifun hBt (eZ k (Finset.mem_range.1 hk)))
    have e2 : (fun ω => V ω * (c + ∑ k ∈ Finset.range n, Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω +
        ∑ k ∈ Finset.range n, Z k ω * ξ M (gr p n k) (gr p n (k + 1)) ω)) =
        fun ω => (c * V ω + ∑ k ∈ Finset.range n, V ω * (Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω)) +
          ∑ k ∈ Finset.range n, V ω * (Z k ω * ξ M (gr p n k) (gr p n (k + 1)) ω) := by
      funext ω; rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]; ring
    have iC : Integrable (fun ω => c * V ω) M.P := (hV2.integrable one_le_two).const_mul c
    have iSY : Integrable (fun ω => ∑ k ∈ Finset.range n,
        V ω * (Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω)) M.P := integrable_finset_sum _ iY
    have iSZ : Integrable (fun ω => ∑ k ∈ Finset.range n,
        V ω * (Z k ω * ξ M (gr p n k) (gr p n (k + 1)) ω)) M.P := integrable_finset_sum _ iZ
    have iCY : Integrable (fun ω => c * V ω + ∑ k ∈ Finset.range n,
        V ω * (Y k ω * dB M (gr p n k) (gr p n (k + 1)) ω)) M.P := iC.add iSY
    rw [e2, integral_add iCY iSZ, integral_add iC iSY, integral_finset_sum _ iY,
      integral_finset_sum _ iZ, integral_const_mul, oc, mul_zero, zero_add,
      Finset.sum_eq_zero (fun k hk => oB (eY k (Finset.mem_range.1 hk))),
      Finset.sum_eq_zero (fun k hk => oBt (eZ k (Finset.mem_range.1 hk))), add_zero])
  have hV'P : V' =ᵐ[M.P] 0 := ae_eq_of_ae_eq_trim hV'0
  filter_upwards [hVV', hV'P] with ω h1 h2
  have : V ω = 0 := h1.trans h2
  simp only [hVdef] at this
  linarith

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

theorem hcomp (M : Model p Ω) (hM : M.Standing) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hC : StochCalcZ2.ContHyp M)
    (f : Ω → ℝ) (hfm : StronglyMeasurable[M.F p.T] f) (hf2 : MemLp f 2 M.P)
    (hf1 : ∫ ω, f ω ∂M.P = 0)
    (hfA : ∀ θχ ∈ M.AX, ∫ ω, f ω * θχ.2 p.T ω ∂M.P = 0)
    (hfN : ∀ n : ℕ, 0 < n → ∀ Y : ℕ → Ω → ℝ,
      (∀ k : ℕ, Measurable[M.F ((k : ℝ≥0) * (p.T / n))] (Y k)) → (∃ C : ℝ, ∀ (k : ℕ) ω, |Y k ω| ≤ C) →
      ∫ ω, f ω * (M.Z p.T ω * ∑ k ∈ Finset.range n, Y k ω *
        (M.Bt (((k + 1 : ℕ) : ℝ≥0) * (p.T / n)) ω - M.Bt ((k : ℝ≥0) * (p.T / n)) ω)) ∂M.P = 0) :
    f =ᵐ[M.P] 0 := by
  have := hM.prob
  have hB := incr_B M hM
  have hBt := incr_Bt M hM
  have hle : ∀ t, M.F t ≤ mΩ := M.F.le
  have heP : ∀ i : Elem M.F p.T, (memLp_efun (P := M.P) hle i).toLp (efun i) ∈
      closure (Set.range (eL (P := M.P) hle p.T)) := fun i =>
    subset_closure ⟨Finsupp.single i 1, by
      simp only [eL, Finsupp.linearCombination_single, one_smul]; rfl⟩
  obtain ⟨a, b, ha2, hb2, ha, hb⟩ := O3_model M hM hf2
  obtain ⟨a', c, ha'2, hc2, ha'P, ha'E, hc, hrel⟩ := O6_modelP M hM h4 hf2 ha2 ha hfA
  have hac' := StochCalcX0.O70 M hM h4 hrel
  obtain ⟨b', hb'2, hb'P, hb'⟩ := proj_fun (P := M.P) hle p.T hb2
  have hb'E : ∀ i : Elem M.F p.T,
      ∫ ω, f ω * ifun M.Bt i ω ∂M.P = ∫ z, b' z * efun i z ∂(μT M.P p.T) := fun i => by
    rw [hb i, hb' _ (memLp_efun hle i) (heP i)]
  obtain ⟨θB, hθB⟩ := rep_exists hB p.T (ha'P ha'2)
  obtain ⟨θBt, hθBt⟩ := rep_exists hBt p.T hb'P
  have hfB : ∀ i : Elem M.F p.T,
      ∫ ω, f ω * ifun M.B i ω ∂M.P = ∫ ω, θB ω * ifun M.B i ω ∂M.P := fun i => by
    rw [int_ifun hB θB i, ha'E i]
    have h1 := hθB.2.2 (Finsupp.single i 1)
    simp only [TL, eL, Finsupp.linearCombination_single, one_smul] at h1
    rw [h1, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ha'2.coeFn_toLp, (memLp_efun (P := M.P) hle i).coeFn_toLp] with z h1 h2
    rw [eE, h1, h2, RCLike.inner_apply', conj_trivial]
  have hfBt : ∀ i : Elem M.F p.T,
      ∫ ω, f ω * ifun M.Bt i ω ∂M.P = ∫ ω, θBt ω * ifun M.Bt i ω ∂M.P := fun i => by
    rw [int_ifun hBt θBt i, hb'E i]
    have h1 := hθBt.2.2 (Finsupp.single i 1)
    simp only [TL, eL, Finsupp.linearCombination_single, one_smul] at h1
    rw [h1, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hb'2.coeFn_toLp, (memLp_efun (P := M.P) hle i).coeFn_toLp] with z h1 h2
    rw [eE, h1, h2, RCLike.inner_apply', conj_trivial]
  have hfeq := G4 M hM hfm hf2 hf1 hθB.1 hθBt.1 hfB hfBt
  set θ : Lp ℝ 2 M.P := hf2.toLp f with hθdef
  have hd : (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω) =ᵐ[M.P] (θBt : Ω → ℝ) := by
    filter_upwards [hf2.coeFn_toLp, hfeq] with ω h1 h2
    rw [hθdef, h1, h2]; ring
  have hperp : ∀ t : ℝ≥0, t ≤ p.T →
      condExp (Kf M t p.T) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω) =ᵐ[M.P]
        condExp (M.F t) M.P (fun ω => (θ : Ω → ℝ) ω - (θB : Ω → ℝ) ω) := fun t ht =>
    (condExp_congr_ae hd).trans ((G3 M hM ht hθBt.1).trans (condExp_congr_ae hd).symm)
  have hθf : ∀ᵐ z ∂(μT M.P p.T), (θ : Ω → ℝ) z.2 = f z.2 :=
    Measure.quasiMeasurePreserving_snd.ae hf2.coeFn_toLp
  have hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT M.P p.T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := M.P) (incr_B M hM).le p.T)) →
      ∫ z, c z * ψ z ∂(μT M.P p.T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT M.P p.T) := by
    intro ψ hψ hmem
    rw [hc ψ hψ hmem]
    refine integral_congr_ae ?_
    filter_upwards [hθf] with z hz
    rw [hz]
  have hacL : ∀ᵐ z ∂(μT M.P p.T),
      (ha'2.toLp a' : ℝ × Ω → ℝ) z = -(StochCalcZ2.etaT M z.1.toNNReal z.2) * c z := by
    filter_upwards [ha'2.coeFn_toLp, hac'] with z h1 h2
    rw [h1, h2]
  obtain ⟨Ic, hIc, hIa, hIm, hI0, hIi, hIe⟩ := StochCalcZ2.Z2 M hM hC
  obtain ⟨Kj, hKj, hKz⟩ := StochCalcZ3.Z3 M hM hIc hIa hIm hI0 hIi
  have hQp : IsProbabilityMeasure (StochCalcTilt.Qd M.P (StochCalcK2.wZ M)) :=
    StochCalcK2.Q2_prob M hM h5
  have hQp' : IsProbabilityMeasure
      (StochCalcTilt.Qd M.P fun ω => M.Z p.T ω ^ 2 / StochCalcK2.cZ M) :=
    StochCalcK2.Q2_prob M hM h5
  have q := fun (t : ℝ≥0) (ht : t ≤ p.T) =>
    StochCalcQ2M.Q2ceG M hM h5 hC hIc hIa hIm hI0 hIe hKj hKz hθB hc2 hproj hacL ht (hperp t ht)
      (StochCalcK2.cZ_pos M hM h5)
  have hθQ : (fun ω => (θ : Ω → ℝ) ω / M.Z p.T ω) =ᵐ[StochCalcTilt.Qd M.P (StochCalcK2.wZ M)]
      (fun ω => f ω / M.Z p.T ω) := by
    refine (StochCalcTilt.Qd_ac _).ae_le ?_
    filter_upwards [hf2.coeFn_toLp] with ω h
    rw [hθdef, h]
  have hQb : ∀ t : ℝ≥0, t ≤ p.T →
      condExp (M.F t ⊔ M.G p.T) (StochCalcTilt.Qd M.P (StochCalcK2.wZ M))
          (fun ω => f ω / M.Z p.T ω) =ᵐ[StochCalcTilt.Qd M.P (StochCalcK2.wZ M)]
        condExp (M.F t) (StochCalcTilt.Qd M.P (StochCalcK2.wZ M)) (fun ω => f ω / M.Z p.T ω) :=
    fun t ht => (condExp_congr_ae hθQ).symm.trans ((q t ht).1.trans
      ((q t ht).2.symm.trans (condExp_congr_ae hθQ)))
  have hG := StochCalcHGM.hG_glue M hM h5 hf2 hf1 (Ic := Ic) (q 0 (by positivity)).1
  have hfN' : ∀ n : ℕ, 0 < n → ∀ Y : ℕ → Ω → ℝ,
      (∀ k, Measurable[M.F (StochCalcD2.gr p n k)] (Y k)) → (∃ C : ℝ, ∀ k ω, |Y k ω| ≤ C) →
      ∫ ω, f ω * (M.Z p.T ω * ∑ k ∈ Finset.range n, Y k ω * StochCalcK2.xg M n k ω) ∂M.P = 0 :=
    fun n hn Y hY hYb => hfN n hn Y hY hYb
  exact StochCalcE6M.E6 M hM h5 hfm hf2 hG
    (fun N j hj y hym Cy hyb => StochCalcE5M.E5 M hM h5 hf2 hQb hfN' hj hym hyb)

end StochCalcHC

end StochCalcP6

-- ===== slice of __current__ (scratch/probe/slice8c/cuts/gK4c.lean.src/__current__.lean): 2/98 top-level decls kept =====

namespace StochCalcP6

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-! K2d (relay 3): the finite-grid lower bound under `P^M`, tests `D0 = Z_T - 1`, `D1 = Z_T S`. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]


end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcK2

/-! K2e (relay 3): the grid weights `Y = a·ĉ_t / max(Z^M_t, ε)` and the bracket bound. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]

















end StochCalcK2

/-! K2f (relay 3): `ε ↓ 0` in the grid bound; `Z^M_t > 0` `P^M`-a.s. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]








end StochCalcK2

/-! K2g (relay 3): `G(u) = E_P[Z_u/Z^M_u δ_u²]`, `G` monotone and bounded. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

section generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}



end generic

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]






end StochCalcK2

/-! K2h (relay 3): Riemann sums and the assembled lower bound K2. -/

namespace StochCalcK2

open HedgePSNV EthierKurtz StochCalcBr StochCalcHs StochCalcGauss StochCalcTilt StochCalcTiltM
open Filter Topology

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]







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


/-- conjunct 3 of platform theorem 1c98c8e0 (`EthierKurtz.brownian_ito_integral_locality_and_continuity`),
for Brownian motions on the model's probability space. -/
def EKcont (M : Model p Ω) : Prop :=
  ∀ {d : ℕ} {W : ℝ≥0 → Ω → EthierKurtz.SDEState d}, EthierKurtz.IsStandardBrownian M.P W →
    ∀ x₀ : EthierKurtz.SDEState d, ∀ [IsProbabilityMeasure M.P] (j : Fin d) (H : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[EthierKurtz.completedBrownianPast M.P W (fun _ => x₀) s] (H s)) →
      (∀ s, Measurable (H s)) → (∀ ω, Continuous fun s => H s ω) →
      ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
      ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
        (∀ t, Measurable[EthierKurtz.completedBrownianPast M.P W (fun _ => x₀) t] (Jc t)) ∧
        (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
        EthierKurtz.HasBrownianItoIntegral M.P (EthierKurtz.completedBrownianPast M.P W (fun _ => x₀))
          (fun s ω => W s ω j) H Jc

theorem contHyp_of (M : Model p Ω) (hM : M.Standing) (hEK : EKcont M) : StochCalcZ2.ContHyp M := by
  have := hM.prob
  intro H hH hHm hHc C hC
  exact hEK (StochCalcBr.isStandardBrownian M hM) 0 0 H hH hHm hHc C hC


end StochCalcK3G

end StochCalcP6

open MeasureTheory ProbabilityTheory HedgePSNV in
open scoped NNReal ENNReal in
theorem solution (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hXM : IsMartingaleOn p.T M.F M.PM M.X)
    (f : Ω → ℝ) (hfm : StronglyMeasurable[M.F p.T] f) (hf2 : MemLp f 2 M.P)
    (hf1 : ∫ ω, f ω ∂M.P = 0)
    (hfA : ∀ θχ ∈ M.AX, ∫ ω, f ω * θχ.2 p.T ω ∂M.P = 0)
    (hfN : ∀ n : ℕ, 0 < n → ∀ Y : ℕ → Ω → ℝ,
      (∀ k : ℕ, Measurable[M.F ((k : ℝ≥0) * (p.T / n))] (Y k)) → (∃ C : ℝ, ∀ (k : ℕ) ω, |Y k ω| ≤ C) →
      ∫ ω, f ω * (M.Z p.T ω * ∑ k ∈ Finset.range n, Y k ω *
        (M.Bt (((k + 1 : ℕ) : ℝ≥0) * (p.T / n)) ω - M.Bt ((k : ℝ≥0) * (p.T / n)) ω)) ∂M.P = 0) :
    f =ᵐ[M.P] 0 := by
  exact StochCalcP6.StochCalcHC.hcomp M hM h4 h5
    (StochCalcP6.StochCalcK3G.contHyp_of M hM
      (fun hW x₀ => (EthierKurtz.brownian_ito_integral_locality_and_continuity hW x₀).2.2.1))
    f hfm hf2 hf1 hfA hfN
