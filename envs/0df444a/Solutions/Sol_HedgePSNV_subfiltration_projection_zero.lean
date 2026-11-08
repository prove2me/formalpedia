-- Prove2me | solution 1 for HedgePSNV.subfiltration_projection_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T17:16:31.49782+00:00
-- url     : https://prove2.me/submissions/6f77db0b-58f2-437e-a497-43586868be9e

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Theorems.Thm_HedgePSNV_stopped_integrand_representation

set_option maxHeartbeats 2000000
set_option linter.all false
set_option Elab.async false


-- ===== slice of Solutions.Sol_pv_1558a108 (scratch/probe/slice8c/cuts/r_q1.lean.src/Solutions.Sol_pv_1558a108.lean): 6/153 top-level decls kept =====

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






end BM

section AEC
variable {mΩ : MeasurableSpace Ω}




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

theorem tendstoInMeasure_zero_of_abs_le [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {F A B : ι → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hA : TendstoInMeasure P A l (fun _ => 0)) (hB : TendstoInMeasure P B l (fun _ => 0))
    (hF : ∀ i ω, |F i ω| ≤ K * (|A i ω| + |B i ω|)) :
    TendstoInMeasure P F l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hA hB ⊢
  intro ε hε
  have hε' : 0 < ε / (2 * K) := by positivity
  have hsum := (hA _ hε').add (hB _ hε')
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun i => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union, Real.dist_eq, sub_zero] at hω ⊢
  by_contra hcon
  push Not at hcon
  have h1 := hF i ω
  have h2 : K * (|A i ω| + |B i ω|) < K * (ε / (2 * K) + ε / (2 * K)) :=
    mul_lt_mul_of_pos_left (add_lt_add hcon.1 hcon.2) hK
  have h3 : K * (ε / (2 * K) + ε / (2 * K)) = ε := by field_simp; ring
  linarith only [hω, h1, h2, h3]





theorem itoStepValue_eq_sum_indicator (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue t n c u ω = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
  unfold itoStepValue
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Set.indicator_apply, Set.mem_Ioc]

theorem itoStepValue_sq (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    (itoStepValue t n c u ω) ^ 2 = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω ^ 2) u := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have key : ∀ p q : ℕ, p < q →
      ((p : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ (q : ℝ) * t.val / (2 : ℝ) ^ n := by
    intro p q hpq
    have : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hT) h2.le
  unfold itoStepValue
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_eq_single k]
  · simp only [Set.indicator_apply, Set.mem_Ioc]; split_ifs <;> ring
  · intro l _ hlk
    split_ifs with h1 h2 <;> try ring
    exfalso
    rcases lt_or_gt_of_ne hlk with hlt | hgt
    · linarith only [key l k hlt, h1.1, h2.2]
    · linarith only [key k l hgt, h1.2, h2.1]
  · intro hk'; exact absurd hk hk'

theorem intervalIntegrable_indicator_Ioc_const (T a b C : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u => (Set.Ioc a b).indicator (fun _ => C) u) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact (integrableOn_const (by simp)).indicator measurableSet_Ioc


theorem itoStepValue_sq_intervalIntegrable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    IntervalIntegrable (fun u => (itoStepValue t n c u ω) ^ 2) volume 0 t.val := by
  have heq : (fun u => (itoStepValue t n c u ω) ^ 2) = ∑ k ∈ Finset.range (2 ^ n), fun u =>
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω ^ 2) u := by
    funext u; rw [Finset.sum_apply, itoStepValue_sq]
  rw [heq]
  exact IntervalIntegrable.sum _ (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ t.2)


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











/-- Every `u ∈ (0,t]` lies in a cell `(t_k, t_{k+1}]` of the dyadic grid, where the step process
takes the value `c k`. -/
theorem itoStepValue_eq_cell (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) {u : ℝ}
    (hu : u ∈ Set.Ioc 0 t.val) (ω : Ω) :
    ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n ∧
      itoStepValue t n c u ω = c k ω := by
  have ht : (0 : ℝ) < t.val := lt_of_lt_of_le hu.1 hu.2
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hx0 : 0 < u * 2 ^ n / t.val := by have := hu.1; positivity
  have hxle : u * 2 ^ n / t.val ≤ 2 ^ n := by
    rw [div_le_iff₀ ht, mul_comm (2 ^ n : ℝ)]; exact mul_le_mul_of_nonneg_right hu.2 h2.le
  have hc1 : 0 < ⌈u * 2 ^ n / t.val⌉₊ := Nat.ceil_pos.2 hx0
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = ⌈u * 2 ^ n / t.val⌉₊ := ⟨⌈u * 2 ^ n / t.val⌉₊ - 1, by omega⟩
  have hkR : (k : ℝ) + 1 = ⌈u * 2 ^ n / t.val⌉₊ := by exact_mod_cast hk
  have hlt : (k : ℝ) < u * 2 ^ n / t.val := by
    have := Nat.ceil_lt_add_one hx0.le; linarith only [this, hkR]
  have hge : u * 2 ^ n / t.val ≤ (k : ℝ) + 1 := by rw [hkR]; exact Nat.le_ceil _
  have hk2 : k < 2 ^ n := by
    have : ⌈u * 2 ^ n / t.val⌉₊ ≤ 2 ^ n := Nat.ceil_le.2 (by exact_mod_cast hxle)
    omega
  have hlo : (k : ℝ) * t.val / 2 ^ n < u := by
    rw [div_lt_iff₀ h2]; rw [lt_div_iff₀ ht] at hlt; linarith only [hlt]
  have hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n := by
    rw [le_div_iff₀ h2]; rw [div_le_iff₀ ht] at hge; linarith only [hge]
  refine ⟨k, hk2, hlo, hhi, ?_⟩
  unfold itoStepValue
  rw [Finset.sum_eq_single k]
  · rw [if_pos ⟨hlo, hhi⟩]
  · intro l _ hlk
    rw [if_neg]
    rintro ⟨h1, h1'⟩
    rcases lt_or_gt_of_ne hlk with hl | hl
    · have hl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast hl
      have : ((l : ℝ) + 1) * t.val / 2 ^ n ≤ (k : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith only [h1', this, hlo]
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith only [h1, this, hhi]
  · intro hk'; exact absurd (Finset.mem_range.2 hk2) hk'






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


-- ===== slice of P8c066573M16 (scratch/probe/slice8c/cuts/r_q1.lean.src/P8c066573M16.lean): 102/865 top-level decls kept =====

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

/-- Hitting time of `{R ≤ |x|}` on `[0,T]`, equal to `T` if the set is not hit. -/
noncomputable def hitR (X : ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  sInf ({v | v ≤ T ∧ R ≤ |X v ω|} ∪ {T})

lemma hitR_le (X : ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0) (ω : Ω) : hitR X R T ω ≤ T :=
  csInf_le (OrderBot.bddBelow _) (Or.inr rfl)

lemma hitR_le_of {X : ℝ≥0 → Ω → ℝ} {R : ℝ} {T : ℝ≥0} {ω : Ω} {v : ℝ≥0} (hvT : v ≤ T)
    (hv : R ≤ |X v ω|) : hitR X R T ω ≤ v :=
  csInf_le (OrderBot.bddBelow _) (Or.inl ⟨hvT, hv⟩)

lemma hitR_mem {X : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun v => X v ω) (R : ℝ) (T : ℝ≥0)
    (ω : Ω) : hitR X R T ω ∈ ({v | v ≤ T ∧ R ≤ |X v ω|} ∪ {T}) := by
  refine IsClosed.csInf_mem ?_ ⟨T, Or.inr rfl⟩ (OrderBot.bddBelow _)
  refine IsClosed.union ?_ isClosed_singleton
  exact isClosed_le continuous_id continuous_const |>.inter
    (isClosed_le continuous_const (hc ω).abs)

/-- Before the hitting time the process is strictly inside. -/
lemma abs_lt_of_lt_hitR {X : ℝ≥0 → Ω → ℝ} {R : ℝ} {T : ℝ≥0} {ω : Ω} {w : ℝ≥0}
    (hw : w < hitR X R T ω) : |X w ω| < R := by
  by_contra h
  exact absurd (hitR_le_of ((hw.le.trans (hitR_le X R T ω))) (not_lt.1 h)) (not_le.2 hw)

lemma hitR_le_iff {X : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun v => X v ω) (R : ℝ) (T : ℝ≥0)
    (ω : Ω) {u : ℝ≥0} (hu : u < T) :
    hitR X R T ω ≤ u ↔ ∃ v, v ≤ u ∧ R ≤ |X v ω| := by
  constructor
  · intro h
    rcases hitR_mem hc R T ω with hm | hm
    · exact ⟨_, h, hm.2⟩
    · rw [Set.mem_singleton_iff] at hm
      exact absurd (hm ▸ h) (not_le.2 hu)
  · rintro ⟨v, hvu, hv⟩
    exact (hitR_le_of (hvu.trans hu.le) hv).trans hvu

/-- The set "the closed set `{R ≤ |x|}` is hit by time `u`" via countably many times
`min q⁺ u`, `q ∈ ℚ`. -/
lemma hit_set_eq {X : ℝ≥0 → Ω → ℝ} (hc : ∀ ω, Continuous fun v => X v ω) (R : ℝ) (u : ℝ≥0) :
    {ω | ∃ v, v ≤ u ∧ R ≤ |X v ω|} =
      ⋂ k : ℕ, ⋃ q : ℚ, {ω | R - 1 / ((k : ℝ) + 1) < |X (min (Real.toNNReal q) u) ω|} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
  constructor
  · rintro ⟨v, hvu, hv⟩ k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hcv := ((hc ω).abs).continuousAt (x := v)
    rw [Metric.continuousAt_iff] at hcv
    obtain ⟨δ, hδ, hδv⟩ := hcv _ hε
    have key : ∀ w : ℝ≥0, dist w v < δ → R - 1 / ((k : ℝ) + 1) < |X w ω| := by
      intro w hw
      have := hδv hw
      rw [Real.dist_eq] at this
      have h2 := (abs_lt.1 this).1
      linarith
    rcases eq_or_lt_of_le hvu with hvu' | hvu'
    · obtain ⟨n, hn⟩ := exists_nat_ge (u : ℝ)
      refine ⟨n, key _ ?_⟩
      have : min (Real.toNNReal ((n : ℚ) : ℝ)) u = v := by
        rw [hvu', min_eq_right]
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
        exact_mod_cast hn
      rw [this, dist_self]; exact hδ
    · have hlt : (v : ℝ) < min (u : ℝ) ((v : ℝ) + δ) :=
        lt_min (by exact_mod_cast hvu') (by linarith)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have hq0 : (0 : ℝ) ≤ q := v.coe_nonneg.trans hq1.le
      have hqu : Real.toNNReal q ≤ u := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
        exact (hq2.trans_le (min_le_left _ _)).le
      refine ⟨q, key _ ?_⟩
      rw [min_eq_left hqu, NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_lt]
      constructor
      · linarith
      · linarith [hq2.trans_le (min_le_right _ _)]
  · intro h
    choose q hq using h
    set w : ℕ → ℝ≥0 := fun k => min (Real.toNNReal (q k)) u with hw
    have hmem : ∀ k, w k ∈ Set.Icc (0 : ℝ≥0) u := fun k => ⟨zero_le, min_le_right _ _⟩
    obtain ⟨v, hv, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
    refine ⟨v, hv.2, ?_⟩
    have h1 : Tendsto (fun k => |X (w (φ k)) ω| + 1 / ((φ k : ℝ) + 1)) atTop
        (𝓝 (|X v ω| + 0)) :=
      (((hc ω).abs.tendsto v).comp hlim).add
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
    rw [add_zero] at h1
    refine ge_of_tendsto h1 (Eventually.of_forall fun k => ?_)
    have := hq (φ k)
    simp only [hw] at this ⊢
    linarith

/-- **O2a**: the capped hitting time is a stopping time. -/
theorem hitR_isStopping (F : Filtration ℝ≥0 mΩ) {X : ℝ≥0 → Ω → ℝ}
    (hXa : ∀ u, StronglyMeasurable[F u] (X u)) (hc : ∀ ω, Continuous fun v => X v ω)
    (R : ℝ) (T : ℝ≥0) (u : ℝ≥0) : MeasurableSet[F u] {ω | hitR X R T ω ≤ u} := by
  rcases lt_or_ge u T with hu | hu
  · have e : {ω | hitR X R T ω ≤ u} = {ω | ∃ v, v ≤ u ∧ R ≤ |X v ω|} := by
      ext ω; exact hitR_le_iff hc R T ω hu
    rw [e, hit_set_eq hc R u]
    refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun q => ?_
    have hm : Measurable[F u] (X (min (Real.toNNReal q) u)) :=
      ((hXa _).mono (F.mono (min_le_right _ _))).measurable
    exact (continuous_abs.measurable.comp hm) measurableSet_Ioi
  · have e : {ω | hitR X R T ω ≤ u} = Set.univ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact (hitR_le X R T ω).trans hu
    rw [e]; exact MeasurableSet.univ


/-- If the path stays strictly inside on `[0,T]`, the hitting time is `T`. -/
lemma hitR_eq_T {X : ℝ≥0 → Ω → ℝ} {R : ℝ} {T : ℝ≥0} {ω : Ω}
    (h : ∀ v, v ≤ T → |X v ω| < R) : hitR X R T ω = T := by
  have e : ({v | v ≤ T ∧ R ≤ |X v ω|} ∪ {T} : Set ℝ≥0) = {T} := by
    ext v
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, or_iff_right_iff_imp]
    rintro ⟨hv, hR⟩
    exact absurd (h v hv) (not_lt.2 hR)
  unfold hitR; rw [e, csInf_singleton]

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



lemma coe_TL (hW : IncrHyp m W P) (T : ℝ≥0) (s : Elem m T →₀ ℝ) :
    (TL hW T s : Ω → ℝ) =ᵐ[P] fun ω => s.sum (fun i c => c * ifun W i ω) := by
  induction s using Finsupp.induction_linear with
  | zero =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)] with ω h
    rw [map_zero, h]
    simp
  | add s1 s2 h1 h2 =>
    rw [map_add]
    filter_upwards [Lp.coeFn_add (TL hW T s1) (TL hW T s2), h1, h2] with ω h h1 h2
    rw [h, Pi.add_apply, h1, h2,
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  | single i c =>
    simp only [TL, Finsupp.linearCombination_single, Finsupp.sum_single_index, zero_mul]
    filter_upwards [Lp.coeFn_smul c (eI hW T i), (memLp_ifun hW i).coeFn_toLp] with ω h h'
    rw [h, Pi.smul_apply, eI, h', smul_eq_mul]

lemma coe_eL (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) (s : Elem m T →₀ ℝ) :
    (eL (P := P) hle T s : ℝ × Ω → ℝ) =ᵐ[μT P T] fun z => s.sum (fun i c => c * efun i z) := by
  induction s using Finsupp.induction_linear with
  | zero =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μT P T)] with z h
    rw [map_zero, h]
    simp
  | add s1 s2 h1 h2 =>
    rw [map_add]
    filter_upwards [Lp.coeFn_add (eL (P := P) hle T s1) (eL hle T s2), h1, h2] with z h h1 h2
    rw [h, Pi.add_apply, h1, h2,
      Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  | single i c =>
    simp only [eL, Finsupp.linearCombination_single, Finsupp.sum_single_index, zero_mul]
    filter_upwards [Lp.coeFn_smul c (eE (P := P) hle T i),
      (memLp_efun (P := P) hle i).coeFn_toLp] with z h h'
    rw [h, Pi.smul_apply, eE, h', smul_eq_mul]

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

lemma clamp_sub_le {D x y : ℝ} (hy : |y| ≤ D) : |max (-D) (min D x) - y| ≤ |x - y| := by
  have hy' := abs_le.1 hy
  rcases le_total x D with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total (-D) x with h2 | h2
    · exact le_of_eq (by rw [max_eq_right h2])
    · rw [max_eq_left h2, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  · rw [min_eq_left h1, max_eq_right (by linarith), abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith

lemma clamp_abs_le {D x : ℝ} (hD : 0 ≤ D) : |max (-D) (min D x)| ≤ D :=
  abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma cell_uniq {T : ℝ≥0} {n j k : ℕ} {u : ℝ}
    (hj : (j : ℝ) * T.val / (2 : ℝ) ^ n < u ∧ u ≤ ((j : ℝ) + 1) * T.val / (2 : ℝ) ^ n)
    (hk : (k : ℝ) * T.val / (2 : ℝ) ^ n < u ∧ u ≤ ((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n) :
    j = k := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hT : (0 : ℝ) ≤ T.val := T.2
  have e1 : (j : ℝ) * T.val < ((k : ℝ) + 1) * T.val :=
    (div_lt_div_iff_of_pos_right h2).1 (lt_of_lt_of_le hj.1 hk.2)
  have e2 : (k : ℝ) * T.val < ((j : ℝ) + 1) * T.val :=
    (div_lt_div_iff_of_pos_right h2).1 (lt_of_lt_of_le hk.1 hj.2)
  have f1 : (j : ℝ) < (k : ℝ) + 1 := lt_of_mul_lt_mul_right e1 hT
  have f2 : (k : ℝ) < (j : ℝ) + 1 := lt_of_mul_lt_mul_right e2 hT
  have g1 : j < k + 1 := by exact_mod_cast f1
  have g2 : k < j + 1 := by exact_mod_cast f2
  omega

lemma stepValue_comp (T : ℝ≥0) (n : ℕ) (e : ℕ → Ω → ℝ) (g : ℝ → ℝ) (hg : g 0 = 0) (u : ℝ)
    (ω : Ω) :
    itoStepValue T n (fun k ω => g (e k ω)) u ω = g (itoStepValue T n e u ω) := by
  unfold itoStepValue
  by_cases h : ∃ k ∈ Finset.range (2 ^ n), (k : ℝ) * T.val / (2 : ℝ) ^ n < u ∧
      u ≤ ((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n
  · obtain ⟨k, hk, hc⟩ := h
    have key : ∀ v : ℕ → ℝ, ∑ j ∈ Finset.range (2 ^ n), (if (j : ℝ) * T.val / (2 : ℝ) ^ n < u ∧
        u ≤ ((j : ℝ) + 1) * T.val / (2 : ℝ) ^ n then v j else 0) = v k := by
      intro v
      rw [Finset.sum_eq_single_of_mem k hk
        (fun j _ hjk => if_neg (fun hcj => hjk (cell_uniq hcj hc))), if_pos hc]
    exact (key (fun j => g (e j ω))).trans (congrArg g (key (fun j => e j ω))).symm
  · have z : ∀ v : ℕ → ℝ, ∑ j ∈ Finset.range (2 ^ n), (if (j : ℝ) * T.val / (2 : ℝ) ^ n < u ∧
        u ≤ ((j : ℝ) + 1) * T.val / (2 : ℝ) ^ n then v j else 0) = 0 :=
      fun v => Finset.sum_eq_zero (fun j hj => if_neg (fun hc => h ⟨j, hj, hc⟩))
    exact (z (fun j => g (e j ω))).trans (hg.symm.trans (congrArg g (z (fun j => e j ω))).symm)

lemma stepValue_meas (T : ℝ≥0) (n : ℕ) (e : ℕ → Ω → ℝ) (ω : Ω) :
    Measurable (fun u => itoStepValue T n e u ω) := by
  have : (fun u => itoStepValue T n e u ω) = fun u => ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * T.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n)).indicator
        (fun _ => e k ω) u := funext fun u => itoStepValue_eq_sum_indicator T n e u ω
  rw [this]
  exact Finset.measurable_sum _ fun k _ => measurable_const.indicator measurableSet_Ioc

lemma err_intervalIntegrable (T : ℝ≥0) (n : ℕ) (e : ℕ → Ω → ℝ) {H : ℝ≥0 → Ω → ℝ} {D : ℝ}
    (hD : ∀ u ω, |H u ω| ≤ D) (hHm : ∀ ω, Measurable (fun u : ℝ => H u.toNNReal ω)) (ω : Ω) :
    IntervalIntegrable (fun u => (itoStepValue T n e u ω - H u.toNNReal ω) ^ 2) volume 0 T.val := by
  have h1 := itoStepValue_sq_intervalIntegrable T n e ω
  have hc : IntervalIntegrable (fun _ : ℝ => 2 * D ^ 2) volume 0 T.val := intervalIntegrable_const
  refine ((h1.const_mul 2).add hc).mono_fun
    (((stepValue_meas T n e ω).sub (hHm ω)).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD u.toNNReal ω)
  have hH2 : H u.toNNReal ω ^ 2 ≤ D ^ 2 :=
    sq_le_sq.2 (by rw [abs_of_nonneg hD0]; exact hD _ _)
  have hx := sq_nonneg (itoStepValue T n e u ω + H u.toNNReal ω)
  have hs := sq_nonneg (itoStepValue T n e u ω)
  have hid : 2 * itoStepValue T n e u ω ^ 2 + 2 * H u.toNNReal ω ^ 2 -
      (itoStepValue T n e u ω - H u.toNNReal ω) ^ 2 =
      (itoStepValue T n e u ω + H u.toNNReal ω) ^ 2 := by ring
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
  linarith

/-- Bounded nonnegative functions tending to zero in measure have integrals tending to zero. -/
lemma integral_tendsto_zero_of_bdd {F : ℕ → Ω → ℝ} {K : ℝ}
    (hFm : ∀ n, AEStronglyMeasurable (F n) P) (hF0 : ∀ n ω, 0 ≤ F n ω) (hFK : ∀ n ω, F n ω ≤ K)
    (h : TendstoInMeasure P F atTop (fun _ => 0)) :
    Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set K' := max K 1 with hK'
  have hK'pos : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hδ : 0 < ε / 2 := by linarith
  have hm := (tendstoInMeasure_iff_dist.1 h) (ε / 2) hδ
  have hev : ∀ᶠ n in atTop, P {ω | ε / 2 ≤ dist (F n ω) 0} < ENNReal.ofReal (ε / (2 * K')) :=
    (tendsto_order.1 hm).2 _ (ENNReal.ofReal_pos.2 (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  set S := {ω | ε / 2 ≤ dist (F n ω) 0} with hS
  set S' := toMeasurable P S with hS'
  have hS'm : MeasurableSet S' := measurableSet_toMeasurable P S
  have hPS' : P S' < ENNReal.ofReal (ε / (2 * K')) := by
    rw [hS', measure_toMeasurable]; exact hN n hn
  have hreal : P.real S' < ε / (2 * K') := ENNReal.toReal_lt_of_lt_ofReal hPS'
  have hint : Integrable (F n) P :=
    memLp_one_iff_integrable.1 (MemLp.of_bound (hFm n) K' (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 n ω)]
      exact (hFK n ω).trans (le_max_left _ _)))
  have hg : Integrable (fun ω => ε / 2 + K' * S'.indicator (fun _ => (1 : ℝ)) ω) P :=
    (integrable_const _).add ((integrable_const (1 : ℝ)).indicator hS'm |>.const_mul K')
  have hle : ∫ ω, F n ω ∂P ≤ ∫ ω, (ε / 2 + K' * S'.indicator (fun _ => (1 : ℝ)) ω) ∂P := by
    refine integral_mono hint hg (fun ω => ?_)
    by_cases hω : ω ∈ S'
    · rw [Set.indicator_of_mem hω, mul_one]
      have := (hFK n ω).trans (le_max_left K 1)
      linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      have hωS : ω ∉ S := fun h => hω (subset_toMeasurable P S h)
      simp only [hS, Set.mem_setOf_eq, not_le, Real.dist_eq, sub_zero] at hωS
      rw [abs_of_nonneg (hF0 n ω)] at hωS
      exact hωS.le
  have hval : ∫ ω, (ε / 2 + K' * S'.indicator (fun _ => (1 : ℝ)) ω) ∂P = ε / 2 + K' * P.real S' := by
    rw [integral_add (integrable_const _) ((integrable_const (1 : ℝ)).indicator hS'm |>.const_mul K'),
      integral_const, integral_const_mul, integral_indicator_const (1 : ℝ) hS'm]
    simp
  have hK'r : K' * P.real S' < ε / 2 := by
    have := mul_lt_mul_of_pos_left hreal hK'pos
    rw [show K' * (ε / (2 * K')) = ε / 2 by field_simp] at this
    exact this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (hF0 n))]
  linarith

/-! The clamped approximants as elementary combinations. -/

/-- Clamped coefficients. -/
noncomputable def clampSeq (D : ℝ) (a0 : ℕ → ℕ → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  max (-D) (min D (a0 n k ω))




lemma grid_le (T : ℝ≥0) (n k : ℕ) :
    (k : ℝ≥0) * T / (2 : ℝ≥0) ^ n ≤ ((k : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right le_self_add (by positivity)) (by positivity)

lemma grid_top (T : ℝ≥0) (n k : ℕ) (hk : k < 2 ^ n) :
    ((k : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n ≤ T := by
  have hk1 : (k : ℝ≥0) + 1 ≤ (2 : ℝ≥0) ^ n := by exact_mod_cast Nat.succ_le_of_lt hk
  rw [div_le_iff₀ (by positivity), mul_comm T]
  exact mul_le_mul_of_nonneg_right hk1 (by positivity)

/-- The grid elementary process `Y 1_[k T/2^n, (k+1) T/2^n)`. -/
noncomputable def gElem (T : ℝ≥0) (n : ℕ) (k : Fin (2 ^ n)) (Y : Ω → ℝ)
    (hY : Measurable[m (((k : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] Y) (C : ℝ)
    (hC : ∀ ω, |Y ω| ≤ C) : Elem m T where
  u := ((k : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ n
  v := (((k : ℕ) : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n
  huv := grid_le T n k
  hvT := grid_top T n k k.2
  Y := Y
  hY := hY
  C := C
  hC := hC

lemma sum_single_comb {ι : Type*} [Fintype ι] {T : ℝ≥0} (e : ι → Elem m T)
    (g : Elem m T → ℝ → ℝ) (hg0 : ∀ i, g i 0 = 0)
    (hgadd : ∀ i b1 b2, g i (b1 + b2) = g i b1 + g i b2) :
    (∑ k, Finsupp.single (e k) (1 : ℝ)).sum g = ∑ k, g (e k) 1 := by
  rw [← Finsupp.sum_finsetSum_index hg0 hgadd]
  exact Finset.sum_congr rfl fun k _ => Finsupp.sum_single_index (hg0 _)

/-- The left-closed grid step function agrees with `itoStepValue` off the finite grid. -/
lemma ind_grid_eq (T : ℝ≥0) (n k : ℕ) {u : ℝ}
    (hu1 : u ≠ (k : ℝ) * T.val / (2 : ℝ) ^ n) (hu2 : u ≠ ((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n)
    (y : ℝ) :
    ind ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n) (((k : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n) u * y =
      if (k : ℝ) * T.val / (2 : ℝ) ^ n < u ∧ u ≤ ((k : ℝ) + 1) * T.val / (2 : ℝ) ^ n
        then y else 0 := by
  unfold ind
  simp only [Set.indicator_apply, Set.mem_Ico, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat]
  have e1 : ((k : ℝ) * (T : ℝ) / 2 ^ n ≤ u ∧ u < ((k : ℝ) + 1) * (T : ℝ) / 2 ^ n) ↔
      ((k : ℝ) * T.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * T.val / 2 ^ n) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm hu1), h2.le⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.le, lt_of_le_of_ne h2 hu2⟩
  by_cases hc : (k : ℝ) * T.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * T.val / 2 ^ n
  · rw [if_pos (e1.2 hc), if_pos hc, one_mul]
  · rw [if_neg (fun h => hc (e1.1 h)), if_neg hc, zero_mul]


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

theorem pred_approx (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0)
    {H : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ u ω, |H u ω| ≤ D)
    (hHm : Measurable (fun z : ℝ × Ω => H z.1.toNNReal z.2))
    (a0 : ℕ → ℕ → Ω → ℝ)
    (ha0m : ∀ n k : ℕ, k < 2 ^ n → Measurable[m ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] (a0 n k))
    (ha0H : TendstoInMeasure P (fun n ω => ∫ u in (0 : ℝ)..T.val,
        (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2) atTop (fun _ => (0 : ℝ))) :
    ∃ s : ℕ → (Elem m T →₀ ℝ), Tendsto (fun n => eLpNorm (fun z =>
        (s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) 2 (μT P T)) atTop (𝓝 0) := by
  have hT0 : (0 : ℝ) ≤ T.val := T.2
  have hHm' : ∀ ω, Measurable (fun u : ℝ => H u.toNNReal ω) :=
    fun ω => hHm.comp (measurable_id.prodMk measurable_const)
  have hcm : ∀ n k : ℕ, k < 2 ^ n →
      Measurable[m ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] (clampSeq D a0 n k) :=
    fun n k hk => measurable_const.max (measurable_const.min (ha0m n k hk))
  have hcb : ∀ n k ω, |clampSeq D a0 n k ω| ≤ D := fun n k ω => clamp_abs_le hD0
  have hg0 : max (-D) (min D 0) = 0 := by
    rw [min_eq_right hD0, max_eq_right (neg_nonpos.2 hD0)]
  have hsvc : ∀ n u ω, itoStepValue T n (clampSeq D a0 n) u ω =
      max (-D) (min D (itoStepValue T n (a0 n) u ω)) :=
    fun n u ω => stepValue_comp T n (a0 n) (fun x => max (-D) (min D x)) hg0 u ω
  have herr : ∀ n u ω, (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2 ≤
      (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2 := fun n u ω => by
    rw [hsvc]; exact sq_le_sq.2 (clamp_sub_le (hD _ _))
  have hEc0 : ∀ n ω, 0 ≤ ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2 :=
    fun n ω => intervalIntegral.integral_nonneg hT0 (fun u _ => sq_nonneg _)
  have hEa0 : ∀ n ω, 0 ≤ ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2 :=
    fun n ω => intervalIntegral.integral_nonneg hT0 (fun u _ => sq_nonneg _)
  have hEcle : ∀ n ω, (∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) ≤
      ∫ u in (0 : ℝ)..T.val, (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2 :=
    fun n ω => intervalIntegral.integral_mono_on hT0
      (err_intervalIntegrable T n _ hD hHm' ω) (err_intervalIntegrable T n _ hD hHm' ω)
      (fun u _ => herr n u ω)
  have hEc : TendstoInMeasure P (fun n ω => ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) atTop
      (fun _ => (0 : ℝ)) := by
    refine tendstoInMeasure_zero_of_abs_le (K := 1) one_pos ha0H ha0H (fun n ω => ?_)
    rw [abs_of_nonneg (hEc0 n ω), abs_of_nonneg (hEa0 n ω)]
    linarith [hEcle n ω, hEa0 n ω]
  -- the elementary combinations
  let e : (n : ℕ) → Fin (2 ^ n) → Elem m T := fun n k =>
    gElem T n k (clampSeq D a0 n k) (hcm n k k.2) D (hcb n k)
  let s : ℕ → (Elem m T →₀ ℝ) := fun n => ∑ k, Finsupp.single (e n k) (1 : ℝ)
  have hsE : ∀ n (z : ℝ × Ω), (s n).sum (fun i c => c * efun i z) = ∑ k : Fin (2 ^ n),
      ind (((k : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ n) ((((k : ℕ) : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n) z.1 *
        clampSeq D a0 n k z.2 := by
    intro n z
    show (∑ k, Finsupp.single (e n k) (1 : ℝ)).sum _ = _
    rw [sum_single_comb (e n) (fun i c => c * efun i z) (fun i => zero_mul _)
      (fun i b1 b2 => add_mul _ _ _)]
    simp only [one_mul, efun, e, gElem]
  have hoff : ∀ n (u : ℝ) (ω : Ω),
      u ∉ (fun j : ℕ => (j : ℝ) * T.val / (2 : ℝ) ^ n) '' Set.Iic (2 ^ n) →
      ∑ k : Fin (2 ^ n), ind (((k : ℕ) : ℝ≥0) * T / (2 : ℝ≥0) ^ n)
        ((((k : ℕ) : ℝ≥0) + 1) * T / (2 : ℝ≥0) ^ n) u * clampSeq D a0 n k ω =
      itoStepValue T n (clampSeq D a0 n) u ω := by
    intro n u ω hu
    unfold itoStepValue
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine ind_grid_eq T n k (fun h => hu ⟨k, Set.mem_Iic.2 (le_of_lt k.2), h.symm⟩)
      (fun h => hu ⟨(k : ℕ) + 1, Set.mem_Iic.2 (Nat.succ_le_of_lt k.2), by rw [h]; norm_num⟩) _
  have hGnull : ∀ n, volume ((fun j : ℕ => (j : ℝ) * T.val / (2 : ℝ) ^ n) '' Set.Iic (2 ^ n)) = 0 :=
    fun n => ((Set.finite_Iic _).image _).countable.measure_zero volume
  -- `L²(μT)` convergence
  have hψ2 : MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 (μT P T) :=
    MemLp.of_bound hHm.aestronglyMeasurable D (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hD _ _)
  have hgL : ∀ n, MemLp (fun z => (s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) 2
      (μT P T) := fun n =>
    ((Lp.memLp (eL (P := P) hle T (s n))).ae_eq (coe_eL (P := P) hle T (s n))).sub hψ2
  have hinner : ∀ n ω, ∫ u, ((s n).sum (fun i c => c * efun i (u, ω)) - H (u, ω).1.toNNReal
      (u, ω).2) ^ 2 ∂(volume.restrict (Set.Ico (0 : ℝ) T)) = ∫ u in (0 : ℝ)..T.val,
        (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2 := by
    intro n ω
    rw [intervalIntegral.integral_of_le hT0, ← integral_Ico_eq_integral_Ioc]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (hGnull n))] with u hu
    rw [hsE]
    dsimp only
    rw [hoff n u ω hu]
  have hfub : ∀ n, ∫ z, ((s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) ^ 2 ∂(μT P T) =
      ∫ ω, (∫ u in (0 : ℝ)..T.val,
        (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) ∂P := by
    intro n
    rw [show μT P T = (volume.restrict (Set.Ico (0 : ℝ) T)).prod P from rfl,
      integral_prod_symm _ (hgL n).integrable_sq]
    exact integral_congr_ae (Eventually.of_forall fun ω => hinner n ω)
  have hEm : ∀ n, AEStronglyMeasurable (fun ω => ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) P := by
    intro n
    have hi := (hgL n).integrable_sq.integral_prod_right
    exact hi.aestronglyMeasurable.congr (Eventually.of_forall fun ω => hinner n ω)
  have hEK : ∀ n ω, (∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2) ≤ T.val * (2 * D) ^ 2 := by
    intro n ω
    calc (∫ u in (0 : ℝ)..T.val,
          (itoStepValue T n (clampSeq D a0 n) u ω - H u.toNNReal ω) ^ 2)
        ≤ ∫ u in (0 : ℝ)..T.val, (2 * D) ^ 2 := by
          refine intervalIntegral.integral_mono_on hT0 (err_intervalIntegrable T n _ hD hHm' ω)
            intervalIntegrable_const (fun u _ => ?_)
          have h1 : |itoStepValue T n (clampSeq D a0 n) u ω| ≤ D := by
            rw [hsvc]; exact clamp_abs_le hD0
          have h2 := hD u.toNNReal ω
          have h3 := abs_sub (itoStepValue T n (clampSeq D a0 n) u ω) (H u.toNNReal ω)
          exact sq_le_sq.2 (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * D)]; linarith)
      _ = T.val * (2 * D) ^ 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hI : Tendsto (fun n => ∫ z, ((s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) ^ 2
      ∂(μT P T)) atTop (𝓝 0) := by
    simp only [hfub]
    exact integral_tendsto_zero_of_bdd hEm hEc0 hEK hEc
  have hψ : Tendsto (fun n => eLpNorm (fun z => (s n).sum (fun i c => c * efun i z) -
      H z.1.toNNReal z.2) 2 (μT P T)) atTop (𝓝 0) := by
    have e : ∀ n, eLpNorm (fun z => (s n).sum (fun i c => c * efun i z) - H z.1.toNNReal z.2) 2
        (μT P T) = ENNReal.ofReal ((∫ z, ((s n).sum (fun i c => c * efun i z) -
          H z.1.toNNReal z.2) ^ 2 ∂(μT P T)) ^ (2 : ℝ)⁻¹) := by
      intro n
      rw [(hgL n).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    simp only [e]
    have h0 : ENNReal.ofReal ((0 : ℝ) ^ (2 : ℝ)⁻¹) = 0 := by
      rw [Real.zero_rpow (by norm_num)]; simp
    rw [← h0]
    exact ENNReal.tendsto_ofReal
      ((Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num))).tendsto.comp hI)
  exact ⟨s, hψ⟩

/-- `pred_approx` as closure membership in `Lp ℝ 2 μT`. -/
theorem pred_mem (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0)
    {H : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ u ω, |H u ω| ≤ D)
    (hHm : Measurable (fun z : ℝ × Ω => H z.1.toNNReal z.2))
    (hψ2 : MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 (μT P T))
    (a0 : ℕ → ℕ → Ω → ℝ)
    (ha0m : ∀ n k : ℕ, k < 2 ^ n → Measurable[m ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n)] (a0 n k))
    (ha0H : TendstoInMeasure P (fun n ω => ∫ u in (0 : ℝ)..T.val,
        (itoStepValue T n (a0 n) u ω - H u.toNNReal ω) ^ 2) atTop (fun _ => (0 : ℝ))) :
    hψ2.toLp _ ∈ closure (Set.range (eL (P := P) hle T)) := by
  obtain ⟨s, hψ⟩ := pred_approx (P := P) hle T hD0 hD hHm a0 ha0m ha0H
  have hψL : Tendsto (fun n => eL (P := P) hle T (s n)) atTop (𝓝 (hψ2.toLp _)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hψ.congr' (Eventually.of_forall fun n => ?_)
    refine eLpNorm_congr_ae ?_
    filter_upwards [coe_eL (P := P) hle T (s n), hψ2.coeFn_toLp] with z e1 e2
    simp only [Pi.sub_apply, e1, e2]
  exact mem_closure_of_tendsto hψL (Eventually.of_forall fun n => ⟨s n, rfl⟩)

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

/-- The left-point dyadic sampling of `H`. -/
noncomputable def lpt (T : ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (n k : ℕ) (ω : Ω) : ℝ :=
  H ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n) ω

lemma stepValue_lpt_tendsto (T : ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (ω : Ω) {u : ℝ}
    (hu : u ∈ Set.Ioc 0 T.val)
    (hlc : Tendsto (fun v : ℝ => H v.toNNReal ω) (𝓝[<] u) (𝓝 (H u.toNNReal ω))) :
    Tendsto (fun n => itoStepValue T n (lpt T H n) u ω) atTop (𝓝 (H u.toNNReal ω)) := by
  have hc : ∀ n : ℕ, ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * T.val / 2 ^ n < u ∧
      u ≤ ((k : ℝ) + 1) * T.val / 2 ^ n ∧ itoStepValue T n (lpt T H n) u ω = lpt T H n k ω :=
    fun n => itoStepValue_eq_cell T n (lpt T H n) hu ω
  choose k _ hlo hhi hval using hc
  let w : ℕ → ℝ := fun n => (((k n : ℝ≥0) * T / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)
  have hw : ∀ n, w n = (k n : ℝ) * T.val / 2 ^ n := fun n => by
    show (((k n : ℝ≥0) * T / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) = _
    push_cast; rw [NNReal.val_eq_coe]
  have hval' : ∀ n, itoStepValue T n (lpt T H n) u ω = H (w n).toNNReal ω := fun n => by
    rw [hval n]; simp only [lpt, w, Real.toNNReal_coe]
  have hε : Tendsto (fun n : ℕ => T.val / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hlow : ∀ n, u - T.val / (2 : ℝ) ^ n ≤ w n := fun n => by
    rw [hw]
    have e : ((k n : ℝ) + 1) * T.val / 2 ^ n = (k n : ℝ) * T.val / 2 ^ n + T.val / 2 ^ n := by
      ring
    linarith [hhi n]
  have hwt : Tendsto w atTop (𝓝 u) := by
    have h1 : Tendsto (fun n : ℕ => u - T.val / (2 : ℝ) ^ n) atTop (𝓝 u) := by
      simpa using (tendsto_const_nhds (x := u)).sub hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hlow (fun n => ?_)
    rw [hw]; exact (hlo n).le
  have hwl : Tendsto w atTop (𝓝[<] u) :=
    tendsto_nhdsWithin_iff.2 ⟨hwt, Eventually.of_forall fun n => by
      show w n < u
      rw [hw]; exact hlo n⟩
  rw [show (fun n => itoStepValue T n (lpt T H n) u ω) = fun n => H (w n).toNNReal ω from
    funext hval']
  exact hlc.comp hwl

theorem pred_left (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0)
    {H : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ u ω, |H u ω| ≤ D)
    (hHm : Measurable (fun z : ℝ × Ω => H z.1.toNNReal z.2))
    (hHa : ∀ t, Measurable[m t] (H t))
    (hlc : ∀ ω, ∀ᵐ u ∂volume, u ∈ Set.Ioc 0 T.val →
      Tendsto (fun v : ℝ => H v.toNNReal ω) (𝓝[<] u) (𝓝 (H u.toNNReal ω)))
    (hψ2 : MemLp (fun z : ℝ × Ω => H z.1.toNNReal z.2) 2 (μT P T)) :
    hψ2.toLp _ ∈ closure (Set.range (eL (P := P) hle T)) := by
  have hT0 : (0 : ℝ) ≤ T.val := T.2
  refine pred_mem (P := P) hle T hD0 hD hHm hψ2 (lpt T H) (fun n k _ => hHa _) ?_
  have hHm' : ∀ ω, Measurable (fun u : ℝ => H u.toNNReal ω) :=
    fun ω => hHm.comp (measurable_id.prodMk measurable_const)
  have hpt : ∀ ω, Tendsto (fun n => ∫ u in (0 : ℝ)..T.val,
      (itoStepValue T n (lpt T H n) u ω - H u.toNNReal ω) ^ 2) atTop (𝓝 0) := by
    intro ω
    rw [show (𝓝 (0 : ℝ)) = 𝓝 (∫ _ in (0 : ℝ)..T.val, (0 : ℝ)) by
      rw [intervalIntegral.integral_zero]]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (2 * D) ^ 2) (Eventually.of_forall fun n => ?_)
      (Eventually.of_forall fun n => ?_) intervalIntegrable_const ?_
    · exact (intervalIntegrable_iff.1
        (err_intervalIntegrable T n (lpt T H n) hD hHm' ω)).aestronglyMeasurable
    · refine Eventually.of_forall fun u hu => ?_
      rw [Set.uIoc_of_le hT0] at hu
      obtain ⟨k, -, -, -, hval⟩ := itoStepValue_eq_cell T n (lpt T H n) hu ω
      rw [hval, Real.norm_eq_abs, abs_pow]
      have h1 := hD ((k : ℝ≥0) * T / (2 : ℝ≥0) ^ n) ω
      have h2 := hD u.toNNReal ω
      have h3 := abs_sub (lpt T H n k ω) (H u.toNNReal ω)
      have h4 : |lpt T H n k ω - H u.toNNReal ω| ≤ 2 * D := by
        simp only [lpt] at h3 ⊢; linarith
      exact pow_le_pow_left₀ (abs_nonneg _) h4 2
    · filter_upwards [hlc ω] with u hu hu'
      rw [Set.uIoc_of_le hT0] at hu'
      have := ((stepValue_lpt_tendsto T H ω hu' (hu hu')).sub_const (H u.toNNReal ω)).pow 2
      simpa using this
  have hjm : ∀ n, Measurable (fun z : ℝ × Ω =>
      (itoStepValue T n (lpt T H n) z.1 z.2 - H z.1.toNNReal z.2) ^ 2) := by
    intro n
    refine ((?_ : Measurable fun z : ℝ × Ω => itoStepValue T n (lpt T H n) z.1 z.2).sub
      hHm).pow_const 2
    unfold itoStepValue
    refine Finset.measurable_sum _ (fun k _ => ?_)
    refine Measurable.ite ?_ (((hHa _).mono (hle _) le_rfl).comp measurable_snd) measurable_const
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) (Eventually.of_forall hpt)
  have hs : StronglyMeasurable (fun ω : Ω => ∫ u, (itoStepValue T n (lpt T H n) (u, ω).1 (u, ω).2 -
      H (u, ω).1.toNNReal (u, ω).2) ^ 2 ∂(volume.restrict (Set.Ioc (0 : ℝ) T.val))) :=
    (hjm n).stronglyMeasurable.integral_prod_left'
  refine hs.aestronglyMeasurable.congr (Eventually.of_forall fun ω => ?_)
  simp only [intervalIntegral.integral_of_le hT0]

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

lemma efun_meas (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (i : Elem m T) : Measurable (efun i) :=
  ((ind_meas i.u i.v).comp measurable_fst).mul ((i.hY.mono (hle i.u) le_rfl).comp measurable_snd)

lemma efun_abs_le {T : ℝ≥0} (i : Elem m T) (z : ℝ × Ω) : |efun i z| ≤ |i.C| := by
  rw [efun, abs_mul]
  calc |ind i.u i.v z.1| * |i.Y z.2| ≤ 1 * |i.Y z.2| :=
        mul_le_mul_of_nonneg_right (ind_abs_le _ _ _) (abs_nonneg _)
    _ ≤ |i.C| := by rw [one_mul]; exact (i.hC z.2).trans (le_abs_self _)

lemma abs_comb_le {T : ℝ≥0} (s : Elem m T →₀ ℝ) (z : ℝ × Ω) :
    |s.sum (fun i c => c * efun i z)| ≤ s.sum (fun i c => |c| * |i.C|) := by
  unfold Finsupp.sum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (efun_abs_le i z) (abs_nonneg _)

lemma comb_bound_nonneg {T : ℝ≥0} (s : Elem m T →₀ ℝ) :
    0 ≤ s.sum (fun i c => |c| * |i.C|) := by
  unfold Finsupp.sum
  exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

lemma efun_adapt (hmono : Monotone m) {T : ℝ≥0} (i : Elem m T) (t : ℝ≥0) :
    Measurable[m t] (fun ω => efun i ((t : ℝ), ω)) := by
  unfold efun
  by_cases hut : i.u ≤ t
  · show Measurable[m t] (fun ω => ind i.u i.v (t : ℝ) * i.Y ω)
    exact Measurable.const_mul (i.hY.mono (hmono hut) le_rfl) _
  · have h0 : ind i.u i.v (t : ℝ) = 0 := by
      simp only [ind, Set.indicator_apply, Set.mem_Ico]
      rw [if_neg]
      intro h
      exact hut (NNReal.coe_le_coe.1 h.1)
    simp only [h0, zero_mul]
    exact measurable_const

lemma ind_contAt {a b : ℝ≥0} {u : ℝ} (ha : u ≠ a) (hb : u ≠ b) : ContinuousAt (ind a b) u := by
  suffices h : ∀ᶠ r in 𝓝 u, ind a b r = ind a b u from
    continuousAt_const.congr (h.mono fun r hr => hr.symm)
  rcases lt_or_gt_of_ne ha with h | h
  · filter_upwards [Iio_mem_nhds h] with r hr
    simp only [ind, Set.indicator_apply, Set.mem_Ico]
    rw [if_neg (fun h' => absurd h'.1 (not_le.2 hr)), if_neg (fun h' => absurd h'.1 (not_le.2 h))]
  · rcases lt_or_gt_of_ne hb with h' | h'
    · filter_upwards [Ioo_mem_nhds h h'] with r hr
      simp only [ind, Set.indicator_apply, Set.mem_Ico]
      rw [if_pos ⟨hr.1.le, hr.2⟩, if_pos ⟨h.le, h'⟩]
    · filter_upwards [Ioi_mem_nhds h'] with r hr
      simp only [ind, Set.indicator_apply, Set.mem_Ico]
      rw [if_neg (fun h'' => absurd h''.2 (not_lt.2 (le_of_lt hr))),
        if_neg (fun h'' => absurd h''.2 (not_lt.2 h'.le))]

lemma comb_tendsto {T : ℝ≥0} (s : Elem m T →₀ ℝ) (ω : Ω) {u : ℝ} (hu0 : 0 < u)
    (hE : ∀ i ∈ s.support, u ≠ (i.u : ℝ) ∧ u ≠ (i.v : ℝ)) :
    Tendsto (fun v : ℝ => s.sum (fun i c => c * efun i ((v.toNNReal : ℝ), ω))) (𝓝 u)
      (𝓝 (s.sum (fun i c => c * efun i ((u.toNNReal : ℝ), ω)))) := by
  unfold Finsupp.sum
  refine tendsto_finset_sum _ fun i hi => ?_
  have hcu : ((u.toNNReal : ℝ)) = u := Real.coe_toNNReal _ hu0.le
  have h1 : ContinuousAt (ind i.u i.v) ((u.toNNReal : ℝ)) := by
    rw [hcu]; exact ind_contAt (hE i hi).1 (hE i hi).2
  have hc : ContinuousAt (fun v : ℝ => ind i.u i.v ((v.toNNReal : ℝ))) u :=
    h1.comp (f := fun v : ℝ => ((v.toNNReal : ℝ)))
      (NNReal.continuous_coe.comp continuous_real_toNNReal).continuousAt
  simp only [efun]
  exact (hc.tendsto.mul_const (i.Y ω)).const_mul (s i)

lemma ae_fst_Ico (T : ℝ≥0) : ∀ᵐ z ∂(μT P T), z.1 ∈ Set.Ico (0 : ℝ) T :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ico)

lemma inner_toLp_eE (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} {w : ℝ × Ω → ℝ}
    (hw : MemLp w 2 (μT P T)) (i : Elem m T) :
    ⟪hw.toLp w, eE (P := P) hle T i⟫_ℝ = ∫ z, w z * efun i z ∂(μT P T) := by
  unfold eE
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toLp, (memLp_efun (P := P) hle i).coeFn_toLp] with z h1 h2
  rw [h1, h2, RCLike.inner_apply', conj_trivial]

theorem O6_core (hle : ∀ t, m t ≤ mΩ) (T : ℝ≥0) {w : ℝ × Ω → ℝ} (hw : MemLp w 2 (μT P T))
    (hpred : hw.toLp w ∈ closure (Set.range (eL (P := P) hle T)))
    (hperp : ∀ i : Elem m T, ∫ z, w z * efun i z ∂(μT P T) = 0) : w =ᵐ[μT P T] 0 := by
  have h0 : ∀ s, ⟪hw.toLp w, eL (P := P) hle T s⟫_ℝ = 0 := by
    intro s
    induction s using Finsupp.induction_linear with
    | zero => rw [map_zero, inner_zero_right]
    | add s1 s2 h1 h2 => rw [map_add, inner_add_right, h1, h2, add_zero]
    | single i c =>
      simp only [eL, Finsupp.linearCombination_single]
      rw [inner_smul_right, inner_toLp_eE, hperp, mul_zero]
  have hcl : closure (Set.range (eL (P := P) hle T)) ⊆ {x | ⟪hw.toLp w, x⟫_ℝ = 0} :=
    closure_minimal (by rintro _ ⟨s, rfl⟩; exact h0 s)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  have hW0 : hw.toLp w = 0 := inner_self_eq_zero.1 (hcl hpred)
  filter_upwards [hw.coeFn_toLp, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μT P T)] with z h1 h2
  rw [← h1, hW0]
  exact h2


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

/-- An elementary combination times `φ`, as a process. -/
noncomputable def combφ {T : ℝ≥0} (s : Elem m T →₀ ℝ) (φ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  s.sum (fun i c => c * efun i ((t : ℝ), ω)) * φ t ω

theorem pred_mul (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) (T : ℝ≥0)
    {g : ℝ × Ω → ℝ} (hg : MemLp g 2 (μT P T))
    (hgP : hg.toLp g ∈ closure (Set.range (eL (P := P) hle T)))
    {φ : ℝ≥0 → Ω → ℝ} {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ u ω, |φ u ω| ≤ D)
    (hφm : Measurable (fun z : ℝ × Ω => φ z.1.toNNReal z.2))
    (hφa : ∀ t, Measurable[m t] (φ t))
    (hlc : ∀ ω, ∀ᵐ u ∂volume, u ∈ Set.Ioc 0 T.val →
      Tendsto (fun v : ℝ => φ v.toNNReal ω) (𝓝[<] u) (𝓝 (φ u.toNNReal ω)))
    (hgφ : MemLp (fun z => g z * φ z.1.toNNReal z.2) 2 (μT P T)) :
    hgφ.toLp _ ∈ closure (Set.range (eL (P := P) hle T)) := by
  classical
  obtain ⟨x, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hgP
  choose s hs using hxr
  have hcoe : Measurable fun z : ℝ × Ω => ((z.1.toNNReal : ℝ)) :=
    (measurable_real_toNNReal.comp measurable_fst).coe_nnreal_real
  -- facts about each `combφ (s n) φ`
  have hB : ∀ n t ω, |combφ (s n) φ t ω| ≤ (s n).sum (fun i c => |c| * |i.C|) * D := by
    intro n t ω
    rw [combφ, abs_mul]
    exact mul_le_mul (abs_comb_le _ _) (hD t ω) (abs_nonneg _) (comb_bound_nonneg _)
  have hB0 : ∀ n, 0 ≤ (s n).sum (fun i c => |c| * |i.C|) * D :=
    fun n => mul_nonneg (comb_bound_nonneg _) hD0
  have hM : ∀ n, Measurable (fun z : ℝ × Ω => combφ (s n) φ z.1.toNNReal z.2) := by
    intro n
    simp only [combφ]
    unfold Finsupp.sum
    refine (Finset.measurable_sum _ fun i _ => ?_).mul hφm
    exact measurable_const.mul ((efun_meas hle i).comp (hcoe.prodMk measurable_snd))
  have hA : ∀ n t, Measurable[m t] (combφ (s n) φ t) := by
    intro n t
    unfold combφ Finsupp.sum
    exact (Finset.measurable_sum _ fun i _ => measurable_const.mul (efun_adapt hmono i t)).mul
      (hφa t)
  have hL : ∀ n ω, ∀ᵐ u ∂volume, u ∈ Set.Ioc 0 T.val →
      Tendsto (fun v : ℝ => combφ (s n) φ v.toNNReal ω) (𝓝[<] u)
        (𝓝 (combφ (s n) φ u.toNNReal ω)) := by
    intro n ω
    let E : Finset ℝ := (s n).support.biUnion (fun i => {(i.u : ℝ), (i.v : ℝ)})
    filter_upwards [hlc ω, measure_eq_zero_iff_ae_notMem.1
      ((E : Set ℝ).toFinite.measure_zero volume)] with u h1 h2 hu
    have hE : ∀ i ∈ (s n).support, u ≠ (i.u : ℝ) ∧ u ≠ (i.v : ℝ) := fun i hi =>
      ⟨fun h => h2 (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, hi, by simp [h]⟩)),
        fun h => h2 (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, hi, by simp [h]⟩))⟩
    simp only [combφ]
    exact ((comb_tendsto (s n) ω hu.1 hE).mono_left nhdsWithin_le_nhds).mul (h1 hu)
  have hL2 : ∀ n, MemLp (fun z : ℝ × Ω => combφ (s n) φ z.1.toNNReal z.2) 2 (μT P T) :=
    fun n => MemLp.of_bound (hM n).aestronglyMeasurable _
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB n _ _)
  have hmem : ∀ n, (hL2 n).toLp _ ∈ closure (Set.range (eL (P := P) hle T)) :=
    fun n => pred_left (P := P) hle T (hB0 n) (hB n) (hM n) (hA n) (hL n) (hL2 n)
  -- convergence
  have hx' := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' x (hg.toLp g)).1 hx
  have hle' : ∀ n, eLpNorm ((fun z : ℝ × Ω => combφ (s n) φ z.1.toNNReal z.2) -
      fun z => g z * φ z.1.toNNReal z.2) 2 (μT P T) ≤
      ENNReal.ofReal D * eLpNorm (⇑(x n) - ⇑(hg.toLp g)) 2 (μT P T) := by
    intro n
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ 2
    filter_upwards [ae_fst_Ico (P := P) T, coe_eL (P := P) hle T (s n), hg.coeFn_toLp] with z hz h1 h2
    have hcz : ((z.1.toNNReal : ℝ)) = z.1 := Real.coe_toNNReal _ hz.1
    rw [← hs n] at *
    simp only [Pi.sub_apply, combφ, hcz, Prod.mk.eta, h1, h2, Real.norm_eq_abs]
    rw [← sub_mul, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hD _ _) (abs_nonneg _)
  have hconv : Tendsto (fun n => (hL2 n).toLp _) atTop (𝓝 (hgφ.toLp _)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hL2 _ hgφ]
    have h0 : Tendsto (fun n => ENNReal.ofReal D * eLpNorm (⇑(x n) - ⇑(hg.toLp g)) 2 (μT P T))
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hx' (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun n => by positivity) hle'
  exact isClosed_closure.mem_of_tendsto hconv (Eventually.of_forall hmem)

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

/-- Restriction of an elementary process to `[0,s)`. -/
noncomputable def resI {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) : Elem m T where
  u := i.u
  v := max i.u (min i.v s)
  huv := le_max_left _ _
  hvT := max_le (i.huv.trans i.hvT) ((min_le_left _ _).trans i.hvT)
  Y := i.Y
  hY := i.hY
  C := i.C
  hC := i.hC

lemma ind_resI {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) (r : ℝ) :
    ind (resI s i).u (resI s i).v r = ind i.u i.v r * ind 0 s r := by
  have hu : (0 : ℝ) ≤ i.u := i.u.2
  simp only [resI, ind, Set.indicator_apply, Set.mem_Ico, NNReal.coe_max, NNReal.coe_min,
    NNReal.coe_zero, lt_max_iff, lt_min_iff]
  by_cases h1 : (i.u : ℝ) ≤ r
  · have h1' : ¬ r < (i.u : ℝ) := not_lt.2 h1
    have h0 : (0 : ℝ) ≤ r := hu.trans h1
    by_cases h2 : r < (i.v : ℝ)
    · by_cases h3 : r < (s : ℝ)
      · simp [h1, h1', h2, h3, h0]
      · simp [h1, h1', h2, h3]
    · simp [h1, h1', h2]
  · simp [h1]

lemma efun_resI {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) (z : ℝ × Ω) :
    efun (resI s i) z = efun i z * ind 0 s z.1 := by
  simp only [efun, ind_resI]
  show ind i.u i.v z.1 * ind 0 s z.1 * i.Y z.2 = _
  ring

/-- Restriction of a combination. -/
noncomputable def resF {T : ℝ≥0} (s : ℝ≥0) (x : Elem m T →₀ ℝ) : Elem m T →₀ ℝ :=
  Finsupp.mapDomain (resI s) x

lemma comb_resF {T : ℝ≥0} (s : ℝ≥0) (x : Elem m T →₀ ℝ) (z : ℝ × Ω) :
    (resF s x).sum (fun i c => c * efun i z) = x.sum (fun i c => c * efun i z) * ind 0 s z.1 := by
  unfold resF
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  simp only [efun_resI, Finsupp.sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma int_ifun_res (hW : IncrHyp m W P) {T : ℝ≥0} (s : ℝ≥0) (i : Elem m T) {g : Ω → ℝ}
    (hg : Measurable[m s] g) :
    ∫ ω, g ω * (ifun W i ω - ifun W (resI s i) ω) ∂P = 0 := by
  by_cases hvs : i.v ≤ s
  · have hv : (resI s i).v = i.v := by
      show max i.u (min i.v s) = i.v
      rw [min_eq_left hvs, max_eq_right i.huv]
    have h0 : ∀ ω, g ω * (ifun W i ω - ifun W (resI s i) ω) = 0 := by
      intro ω
      simp only [ifun, hv]
      show g ω * (i.Y ω * (W i.v ω - W i.u ω) - i.Y ω * (W i.v ω - W i.u ω)) = 0
      ring
    simp_rw [h0, integral_zero]
  · push Not at hvs
    have hv : (resI s i).v = max i.u s := by
      show max i.u (min i.v s) = max i.u s
      rw [min_eq_right hvs.le]
    have key : ∀ ω, g ω * (ifun W i ω - ifun W (resI s i) ω) =
        (g ω * i.Y ω) * (W i.v ω - W (max i.u s) ω) := by
      intro ω
      simp only [ifun, hv]
      show g ω * (i.Y ω * (W i.v ω - W i.u ω) - i.Y ω * (W (max i.u s) ω - W i.u ω)) = _
      ring
    simp_rw [key]
    refine int_mul_dW hW (max_le i.huv hvs.le) ?_
    exact (hg.mono (hW.mono (le_max_right _ _)) le_rfl).mul
      (i.hY.mono (hW.mono (le_max_left _ _)) le_rfl)

lemma int_TL_res (hW : IncrHyp m W P) (T : ℝ≥0) (s : ℝ≥0) (x : Elem m T →₀ ℝ) {g : Ω → ℝ}
    (hg : Measurable[m s] g) (hg2 : MemLp g 2 P) :
    ∫ ω, g ω * (TL hW T x ω - TL hW T (resF s x) ω) ∂P = 0 := by
  have e : (fun ω => g ω * (TL hW T x ω - TL hW T (resF s x) ω)) =ᵐ[P]
      fun ω => ∑ i ∈ x.support, x i * (g ω * (ifun W i ω - ifun W (resI s i) ω)) := by
    filter_upwards [coe_TL hW T x, coe_TL hW T (resF s x)] with ω h1 h2
    rw [h1, h2]
    unfold resF
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    simp only [Finsupp.sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [integral_congr_ae e, integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, int_ifun_res hW s i hg, mul_zero]
  · intro i _
    refine Integrable.const_mul ?_ _
    exact hg2.integrable_mul ((memLp_ifun hW i).sub (memLp_ifun hW (resI s i)))

/-- The restricted integrand `a 1_{[0,s)}` as an `L²` element. -/
lemma memLp_res {T : ℝ≥0} {a : ℝ × Ω → ℝ} (ha : MemLp a 2 (μT P T)) (s : ℝ≥0) :
    MemLp (fun z => a z * ind 0 s z.1) 2 (μT P T) := by
  refine ha.of_le (ha.aestronglyMeasurable.mul
    ((ind_meas 0 s).comp measurable_fst).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (ind_abs_le _ _ _)

lemma norm_res_sub_le (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (a : Lp ℝ 2 (μT P T)) (s : ℝ≥0)
    (x : Elem m T →₀ ℝ) :
    ‖eL (P := P) hle T (resF s x) - (memLp_res (Lp.memLp a) s).toLp _‖ ≤
      ‖eL (P := P) hle T x - a‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_sub (eL (P := P) hle T (resF s x)) ((memLp_res (Lp.memLp a) s).toLp _),
    Lp.coeFn_sub (eL (P := P) hle T x) a, coe_eL (P := P) hle T (resF s x), coe_eL (P := P) hle T x,
    (memLp_res (Lp.memLp a) s).coeFn_toLp] with z h1 h2 h3 h4 h5
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, comb_resF, ← sub_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (ind_abs_le _ _ _)

/-- If `TL x_n → θ` and `a ∈ Pred` represents `θ`, then `eL x_n → a`. -/
theorem eL_tendsto (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (ha : ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪a, eL (P := P) hW.le T x⟫_ℝ)
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T)))
    {x : ℕ → (Elem m T →₀ ℝ)} (hx : Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ)) :
    Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 a) := by
  have hc : CauchySeq fun n => eL (P := P) hW.le T (x n) := by
    have hcu : CauchySeq fun n => TL hW T (x n) := hx.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcu ε hε
    refine ⟨N, fun i hi j hj => ?_⟩
    rw [dist_eq_norm, ← map_sub, ← norm_TL hW T, map_sub, ← dist_eq_norm]
    exact hN i hi j hj
  obtain ⟨ψ, hψ⟩ := cauchySeq_tendsto_of_complete hc
  have hψP : ψ ∈ closure (Set.range (eL (P := P) hW.le T)) :=
    mem_closure_of_tendsto hψ (Eventually.of_forall fun n => ⟨x n, rfl⟩)
  have horth : ∀ y, ⟪a - ψ, eL (P := P) hW.le T y⟫_ℝ = 0 := by
    intro y
    have h1 : Tendsto (fun n => ⟪TL hW T (x n), TL hW T y⟫_ℝ) atTop (𝓝 ⟪θ, TL hW T y⟫_ℝ) :=
      hx.inner tendsto_const_nhds
    have h2 : Tendsto (fun n => ⟪eL (P := P) hW.le T (x n), eL (P := P) hW.le T y⟫_ℝ) atTop
        (𝓝 ⟪ψ, eL (P := P) hW.le T y⟫_ℝ) := hψ.inner tendsto_const_nhds
    simp only [inner_TL] at h1
    rw [inner_sub_left, ← ha y, tendsto_nhds_unique h1 h2, sub_self]
  have hcl : closure (Set.range (eL (P := P) hW.le T)) ⊆ {w | ⟪a - ψ, w⟫_ℝ = 0} :=
    closure_minimal (by rintro _ ⟨y, rfl⟩; exact horth y)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  have hmem : a - ψ ∈ closure (Set.range (eL (P := P) hW.le T)) := by
    have := (Pred (P := P) hW.le T).sub_mem ((mem_Pred_iff hW.le T a).2 haP)
      ((mem_Pred_iff hW.le T ψ).2 hψP)
    exact (mem_Pred_iff hW.le T _).1 this
  have h0 : a - ψ = 0 := inner_self_eq_zero.1 (hcl hmem)
  rw [sub_eq_zero.1 h0]
  exact hψ

end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
lemma sq_norm_toLp {μ : Measure (ℝ × Ω)} {F : ℝ × Ω → ℝ} (hF : MemLp F 2 μ) :
    ‖hF.toLp F‖ ^ 2 = ∫ z, F z ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with z h
  rw [h, RCLike.inner_apply', conj_trivial, sq]

omit [IsProbabilityMeasure P] in
lemma sq_norm_toLpΩ {F : Ω → ℝ} (hF : MemLp F 2 P) :
    ‖hF.toLp F‖ ^ 2 = ∫ ω, F ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with z h
  rw [h, RCLike.inner_apply', conj_trivial, sq]

/-- **S1**: pairing of `θ = I(a)` with an `m s`-measurable `g` sees only `a 1_{[0,s)}`. -/
theorem S1 (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P}
    (hθ : θ ∈ closure (Set.range (TL hW T)))
    {a : Lp ℝ 2 (μT P T)} (ha : ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪a, eL (P := P) hW.le T x⟫_ℝ)
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T))) (s : ℝ≥0)
    {g : Ω → ℝ} (hg : Measurable[m s] g) (hg2 : MemLp g 2 P) :
    ⟪θ, hg2.toLp g⟫_ℝ ≤ ‖(memLp_res (Lp.memLp a) s).toLp _‖ * ‖hg2.toLp g‖ := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hθ
  choose y hy using hxr
  have hx' : Tendsto (fun n => TL hW T (y n)) atTop (𝓝 θ) := by
    simp_rw [hy]; exact hx
  have hEa := eL_tendsto hW T ha haP hx'
  have hres : Tendsto (fun n => eL (P := P) hW.le T (resF s (y n))) atTop
      (𝓝 ((memLp_res (Lp.memLp a) s).toLp _)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => norm_res_sub_le hW.le a s (y n)) ?_
    exact tendsto_iff_norm_sub_tendsto_zero.1 hEa
  have heq : ∀ n, ⟪TL hW T (y n), hg2.toLp g⟫_ℝ = ⟪TL hW T (resF s (y n)), hg2.toLp g⟫_ℝ := by
    intro n
    have h0 : ⟪TL hW T (y n) - TL hW T (resF s (y n)), hg2.toLp g⟫_ℝ = 0 := by
      rw [L2.inner_def]
      refine (integral_congr_ae ?_).trans (int_TL_res hW T s (y n) hg hg2)
      filter_upwards [Lp.coeFn_sub (TL hW T (y n)) (TL hW T (resF s (y n))), hg2.coeFn_toLp]
        with ω h1 h2
      rw [h1, h2, Pi.sub_apply, RCLike.inner_apply', conj_trivial, mul_comm]
    rw [inner_sub_left, sub_eq_zero] at h0
    exact h0
  have hlim1 : Tendsto (fun n => ⟪TL hW T (resF s (y n)), hg2.toLp g⟫_ℝ) atTop
      (𝓝 ⟪θ, hg2.toLp g⟫_ℝ) := by
    simp_rw [← heq]; exact hx'.inner tendsto_const_nhds
  have hlim2 : Tendsto (fun n => ‖eL (P := P) hW.le T (resF s (y n))‖ * ‖hg2.toLp g‖) atTop
      (𝓝 (‖(memLp_res (Lp.memLp a) s).toLp _‖ * ‖hg2.toLp g‖)) :=
    hres.norm.mul_const _
  refine le_of_tendsto_of_tendsto' hlim1 hlim2 fun n => ?_
  rw [← norm_TL hW T]
  exact real_inner_le_norm _ _

/-- **S1c**: `E[(E[θ | m s])²] ≤ ∫ a² 1_{[0,s)}`. -/
theorem S1c (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P}
    (hθ : θ ∈ closure (Set.range (TL hW T)))
    {a : Lp ℝ 2 (μT P T)} (ha : ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪a, eL (P := P) hW.le T x⟫_ℝ)
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T))) (s : ℝ≥0) :
    ∫ ω, (condExp (m s) P (θ : Ω → ℝ) ω) ^ 2 ∂P ≤
      ∫ z, (a z * ind 0 s z.1) ^ 2 ∂(μT P T) := by
  set φ := condExp (m s) P (θ : Ω → ℝ) with hφ
  have hφ2 : MemLp φ 2 P := (Lp.memLp θ).condExp (by norm_num)
  have hφs : StronglyMeasurable[m s] φ := stronglyMeasurable_condExp
  have h1 := S1 hW T hθ ha haP s hφs.measurable hφ2
  have hθi : Integrable (θ : Ω → ℝ) P := (Lp.memLp θ).integrable (by norm_num)
  have hpi : Integrable (fun ω => φ ω * (θ : Ω → ℝ) ω) P := hφ2.integrable_mul (Lp.memLp θ)
  have hpull : ∫ ω, φ ω * φ ω ∂P = ∫ ω, φ ω * (θ : Ω → ℝ) ω ∂P := by
    rw [← integral_condExp (hW.le s) (f := fun ω => φ ω * (θ : Ω → ℝ) ω)]
    exact (integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hφs hpi hθi)).symm
  have hin : ⟪θ, hφ2.toLp φ⟫_ℝ = ‖hφ2.toLp φ‖ ^ 2 := by
    rw [sq_norm_toLpΩ, L2.inner_def]
    calc ∫ ω, ⟪(θ : Ω → ℝ) ω, (hφ2.toLp φ : Ω → ℝ) ω⟫_ℝ ∂P = ∫ ω, φ ω * (θ : Ω → ℝ) ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hφ2.coeFn_toLp] with ω h
          rw [h, RCLike.inner_apply', conj_trivial, mul_comm]
      _ = ∫ ω, φ ω ^ 2 ∂P := by rw [← hpull]; simp_rw [sq]
  rw [hin] at h1
  have h2 : ‖hφ2.toLp φ‖ ≤ ‖(memLp_res (Lp.memLp a) s).toLp _‖ := by
    rcases (norm_nonneg (hφ2.toLp φ)).eq_or_lt with h | h
    · rw [← h]; exact norm_nonneg _
    · nlinarith
  rw [← sq_norm_toLpΩ hφ2, ← sq_norm_toLp (memLp_res (Lp.memLp a) s)]
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

lemma ind_sq (u v : ℝ≥0) (r : ℝ) : ind u v r ^ 2 = ind u v r := by
  simp only [ind, Set.indicator_apply]
  split_ifs <;> norm_num

lemma ind_sub {s s' : ℝ≥0} (hss : s ≤ s') (r : ℝ) : ind 0 s' r * ind s s' r = ind s s' r := by
  rw [ind_mul]
  simp only [NNReal.coe_zero, ind]
  rw [max_eq_right (NNReal.coe_nonneg s), min_self]

lemma ov_self {s s' : ℝ≥0} (hss : s ≤ s') : ov s s' s s' = (s' : ℝ) - s := by
  simp only [ov, min_self, max_self]
  exact max_eq_left (sub_nonneg.2 (by exact_mod_cast hss))

omit [IsProbabilityMeasure P] in
lemma memLp_mulind {T : ℝ≥0} {a : ℝ × Ω → ℝ} (ha : MemLp a 2 (μT P T)) (u v : ℝ≥0) :
    MemLp (fun z => a z * ind u v z.1) 2 (μT P T) := by
  refine ha.of_le (ha.aestronglyMeasurable.mul
    ((ind_meas u v).comp measurable_fst).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (ind_abs_le _ _ _)

lemma memLp_snd_ind {T : ℝ≥0} {w : Ω → ℝ} (hw : MemLp w 2 P) (u v : ℝ≥0) :
    MemLp (fun z : ℝ × Ω => w z.2 * ind u v z.1) 2 (μT P T) := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Ω => w z.2 * ind u v z.1) (μT P T) := by
    unfold μT
    exact hw.aestronglyMeasurable.comp_snd.mul ((ind_meas u v).comp measurable_fst).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  have hi : Integrable (fun r : ℝ => ind u v r ^ 2) (volume.restrict (Set.Ico (0 : ℝ) T)) := by
    refine (integrable_const (1 : ℝ)).mono' ((ind_meas u v).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (ind_abs_le _ _ _)
  have h2 := hi.mul_prod (hw.integrable_sq)
  unfold μT
  exact h2.congr (Eventually.of_forall fun z => by simp only; ring)

lemma int_snd_ind_sq {T : ℝ≥0} (w : Ω → ℝ) (u v : ℝ≥0) (hvT : v ≤ T) :
    ∫ z, (w z.2 * ind u v z.1) ^ 2 ∂(μT P T) = ov u v u v * ∫ ω, w ω ^ 2 ∂P := by
  have e : ∀ z : ℝ × Ω, (w z.2 * ind u v z.1) ^ 2 = (ind u v z.1 * ind u v z.1) * w z.2 ^ 2 :=
    fun z => by ring
  simp_rw [e]
  unfold μT
  rw [integral_prod_mul (fun r => ind u v r * ind u v r) (fun ω => w ω ^ 2), int_time T hvT]

omit [IsProbabilityMeasure P] in
lemma inner_toLp_toLp {μ : Measure (ℝ × Ω)} {F G : ℝ × Ω → ℝ} (hF : MemLp F 2 μ)
    (hG : MemLp G 2 μ) : ⟪hF.toLp F, hG.toLp G⟫_ℝ = ∫ z, F z * G z ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with z h1 h2
  rw [h1, h2, RCLike.inner_apply', conj_trivial]

/-- **C3**: a process `w(ω) 1_{[0,s')}(r)` with `w ⊥ L^∞(m s')` is orthogonal to `Pred`. -/
lemma perp_tail (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) {T : ℝ≥0} (s' : ℝ≥0) {w : Ω → ℝ}
    (hw : MemLp w 2 P)
    (hwY : ∀ Y : Ω → ℝ, Measurable[m s'] Y → ∀ C : ℝ, (∀ ω, |Y ω| ≤ C) → ∫ ω, w ω * Y ω ∂P = 0)
    {ψ : ℝ × Ω → ℝ} (hψ : MemLp ψ 2 (μT P T))
    (hψP : hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hle T))) :
    ∫ z, w z.2 * ind 0 s' z.1 * ψ z ∂(μT P T) = 0 := by
  have hF := memLp_snd_ind (T := T) hw 0 s'
  have h0 : ∀ i : Elem m T, ∫ z, w z.2 * ind 0 s' z.1 * efun i z ∂(μT P T) = 0 := by
    intro i
    have e : ∀ z : ℝ × Ω, w z.2 * ind 0 s' z.1 * efun i z =
        (ind 0 s' z.1 * ind i.u i.v z.1) * (w z.2 * i.Y z.2) := by
      intro z; simp only [efun]; ring
    simp_rw [e]
    unfold μT
    rw [integral_prod_mul (fun r => ind 0 s' r * ind i.u i.v r) (fun ω => w ω * i.Y ω)]
    by_cases hu : i.u < s'
    · rw [hwY i.Y (i.hY.mono (hmono hu.le) le_rfl) i.C i.hC, mul_zero]
    · have hz : (fun r => ind 0 s' r * ind i.u i.v r) = fun _ => (0 : ℝ) := by
        funext r
        rw [ind_mul, Set.indicator_apply, if_neg]
        rintro ⟨h1, h2⟩
        have hu' : (s' : ℝ) ≤ i.u := by exact_mod_cast not_lt.1 hu
        have a1 : (i.u : ℝ) ≤ r := (le_max_right _ _).trans h1
        have a2 : r < s' := (lt_min_iff.1 h2).1
        linarith
      rw [hz, integral_zero, zero_mul]
  have h1 : ∀ x, ⟪hF.toLp _, eL (P := P) hle T x⟫_ℝ = 0 := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => rw [map_zero, inner_zero_right]
    | add s1 s2 h1 h2 => rw [map_add, inner_add_right, h1, h2, add_zero]
    | single i c =>
      simp only [eL, Finsupp.linearCombination_single]
      rw [inner_smul_right, inner_toLp_eE, h0, mul_zero]
  have hcl : closure (Set.range (eL (P := P) hle T)) ⊆ {x | ⟪hF.toLp _, x⟫_ℝ = 0} :=
    closure_minimal (by rintro _ ⟨x, rfl⟩; exact h1 x)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  have := hcl hψP
  simp only [Set.mem_setOf_eq] at this
  rw [inner_toLp_toLp] at this
  exact this

/-- `c 1_{[s,s')}` stays predictable. -/
lemma pred_cell (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) {T : ℝ≥0} {c : ℝ × Ω → ℝ}
    (hc : MemLp c 2 (μT P T)) (hcP : hc.toLp c ∈ closure (Set.range (eL (P := P) hle T)))
    (s s' : ℝ≥0) :
    (memLp_mulind hc s s').toLp _ ∈ closure (Set.range (eL (P := P) hle T)) := by
  have hφm : Measurable (fun z : ℝ × Ω => (fun (t : ℝ≥0) (_ : Ω) => ind s s' (t : ℝ)) z.1.toNNReal z.2) :=
    (ind_meas s s').comp (measurable_coe_nnreal_real.comp measurable_fst.real_toNNReal)
  have hgφ : MemLp (fun z => c z * (fun (t : ℝ≥0) (_ : Ω) => ind s s' (t : ℝ)) z.1.toNNReal z.2) 2
      (μT P T) := by
    refine hc.of_le (hc.aestronglyMeasurable.mul hφm.aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (ind_abs_le _ _ _)
  have hp := pred_mul hle hmono T hc hcP (φ := fun (t : ℝ≥0) (_ : Ω) => ind s s' (t : ℝ))
    zero_le_one (fun u ω => ind_abs_le _ _ _) hφm (fun t => measurable_const) (fun ω => by
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (s : ℝ)),
        compl_mem_ae_iff.2 (measure_singleton (s' : ℝ))] with u h1 h2 hu
      have hcont : Continuous (fun v : ℝ => ((v.toNNReal : ℝ≥0) : ℝ)) :=
        NNReal.continuous_coe.comp continuous_real_toNNReal
      have hu0 : ((u.toNNReal : ℝ≥0) : ℝ) = u := Real.coe_toNNReal u hu.1.le
      have hca : ContinuousAt (ind s s') ((u.toNNReal : ℝ≥0) : ℝ) := by
        rw [hu0]
        exact ind_contAt (Set.mem_compl_singleton_iff.1 h1) (Set.mem_compl_singleton_iff.1 h2)
      exact (ContinuousAt.comp (f := fun v : ℝ => ((v.toNNReal : ℝ≥0) : ℝ)) (x := u) hca
        hcont.continuousAt).tendsto.mono_left nhdsWithin_le_nhds) hgφ
  have heq : (memLp_mulind hc s s').toLp _ = hgφ.toLp _ := by
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [ae_fst_Ico (P := P) T] with z hz
    show c z * ind s s' z.1 = c z * ind s s' ((z.1.toNNReal : ℝ≥0) : ℝ)
    rw [Real.coe_toNNReal _ hz.1]
  rw [heq]
  exact hp

/-- **S2**: `∫ c² 1_{[s,s')} ≤ (s' - s) E[(E[θ | m s'])²]` for the predictable projection `c` of `θ`. -/
theorem S2 (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {c : ℝ × Ω → ℝ}
    (hc : MemLp c 2 (μT P T)) (hcP : hc.toLp c ∈ closure (Set.range (eL (P := P) hW.le T)))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hW.le T)) →
      ∫ z, c z * ψ z ∂(μT P T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT P T))
    {s s' : ℝ≥0} (hss : s ≤ s') (hs'T : s' ≤ T) :
    ∫ z, (c z * ind s s' z.1) ^ 2 ∂(μT P T) ≤
      ((s' : ℝ) - s) * ∫ ω, (condExp (m s') P (θ : Ω → ℝ) ω) ^ 2 ∂P := by
  set φ := condExp (m s') P (θ : Ω → ℝ) with hφdef
  have hφ2 : MemLp φ 2 P := (Lp.memLp θ).condExp (by norm_num)
  have hψ := memLp_mulind hc s s'
  have hψP := pred_cell hW.le hW.mono hc hcP s s'
  have hθ2 : MemLp (θ : Ω → ℝ) 2 P := Lp.memLp θ
  -- X = ∫ θ(z.2) ψ
  have hX : ∫ z, (c z * ind s s' z.1) ^ 2 ∂(μT P T) =
      ∫ z, (θ : Ω → ℝ) z.2 * (c z * ind s s' z.1) ∂(μT P T) := by
    rw [← hproj _ hψ hψP]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [mul_pow, ind_sq]; ring
  -- replace θ by φ
  have hwY : ∀ Y : Ω → ℝ, Measurable[m s'] Y → ∀ C : ℝ, (∀ ω, |Y ω| ≤ C) →
      ∫ ω, ((θ : Ω → ℝ) ω - φ ω) * Y ω ∂P = 0 := by
    intro Y hY C hC
    have hY2 : MemLp Y 2 P := MemLp.of_bound (hY.mono (hW.le s') le_rfl).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
    have hYθ : Integrable (fun ω => Y ω * (θ : Ω → ℝ) ω) P := hY2.integrable_mul hθ2
    have hpull : ∫ ω, Y ω * φ ω ∂P = ∫ ω, Y ω * (θ : Ω → ℝ) ω ∂P := by
      rw [← integral_condExp (hW.le s') (f := fun ω => Y ω * (θ : Ω → ℝ) ω)]
      exact (integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hY.stronglyMeasurable hYθ
        (hθ2.integrable (by norm_num)))).symm
    have e : (fun ω => ((θ : Ω → ℝ) ω - φ ω) * Y ω) = fun ω => Y ω * (θ : Ω → ℝ) ω - Y ω * φ ω := by
      funext ω; ring
    have hYφ : Integrable (fun ω => Y ω * φ ω) P := hY2.integrable_mul hφ2
    rw [e, integral_sub hYθ hYφ, hpull, sub_self]
  have hperp := perp_tail hW.le hW.mono s' (hθ2.sub hφ2) hwY hψ hψP
  have hI1 : Integrable (fun z : ℝ × Ω => (θ : Ω → ℝ) z.2 * ind 0 s' z.1 * (c z * ind s s' z.1))
      (μT P T) := (memLp_snd_ind (T := T) hθ2 0 s').integrable_mul hψ
  have hI2 : Integrable (fun z : ℝ × Ω => φ z.2 * ind 0 s' z.1 * (c z * ind s s' z.1))
      (μT P T) := (memLp_snd_ind (T := T) hφ2 0 s').integrable_mul hψ
  have hrepl : ∫ z, (θ : Ω → ℝ) z.2 * (c z * ind s s' z.1) ∂(μT P T) =
      ∫ z, (φ z.2 * ind s s' z.1) * (c z * ind s s' z.1) ∂(μT P T) := by
    have e1 : ∀ (w : Ω → ℝ) (z : ℝ × Ω), w z.2 * ind 0 s' z.1 * (c z * ind s s' z.1) =
        w z.2 * (c z * ind s s' z.1) := by
      intro w z
      have := ind_sub hss z.1
      calc w z.2 * ind 0 s' z.1 * (c z * ind s s' z.1)
          = w z.2 * c z * (ind 0 s' z.1 * ind s s' z.1) := by ring
        _ = w z.2 * (c z * ind s s' z.1) := by rw [this]; ring
    have e2 : ∀ z : ℝ × Ω, (φ z.2 * ind s s' z.1) * (c z * ind s s' z.1) =
        φ z.2 * (c z * ind s s' z.1) := by
      intro z
      have := ind_sq s s' z.1
      calc (φ z.2 * ind s s' z.1) * (c z * ind s s' z.1)
          = φ z.2 * c z * ind s s' z.1 ^ 2 := by ring
        _ = φ z.2 * (c z * ind s s' z.1) := by rw [this]; ring
    have hsplit : ∫ z, ((θ : Ω → ℝ) z.2 - φ z.2) * ind 0 s' z.1 * (c z * ind s s' z.1) ∂(μT P T) =
        ∫ z, (θ : Ω → ℝ) z.2 * ind 0 s' z.1 * (c z * ind s s' z.1) ∂(μT P T) -
        ∫ z, φ z.2 * ind 0 s' z.1 * (c z * ind s s' z.1) ∂(μT P T) := by
      rw [← integral_sub hI1 hI2]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only; ring
    have hp' : ∫ z, ((θ : Ω → ℝ) z.2 - φ z.2) * ind 0 s' z.1 * (c z * ind s s' z.1) ∂(μT P T) = 0 :=
      hperp
    rw [hsplit, sub_eq_zero] at hp'
    simp_rw [e1] at hp'
    simp_rw [e2]
    exact hp'
  -- Cauchy-Schwarz
  have hΦ := memLp_snd_ind (T := T) hφ2 s s'
  have hcs : ∫ z, (φ z.2 * ind s s' z.1) * (c z * ind s s' z.1) ∂(μT P T) ≤
      ‖hΦ.toLp _‖ * ‖hψ.toLp _‖ := by
    rw [← inner_toLp_toLp hΦ hψ]
    exact real_inner_le_norm _ _
  have hXn : ∫ z, (c z * ind s s' z.1) ^ 2 ∂(μT P T) = ‖hψ.toLp _‖ ^ 2 := (sq_norm_toLp hψ).symm
  have hΦn : ‖hΦ.toLp _‖ ^ 2 = ((s' : ℝ) - s) * ∫ ω, φ ω ^ 2 ∂P := by
    rw [sq_norm_toLp hΦ, int_snd_ind_sq φ s s' hs'T, ov_self hss]
  have hle : ‖hψ.toLp _‖ ^ 2 ≤ ‖hΦ.toLp _‖ * ‖hψ.toLp _‖ := by
    rw [← hXn, hX, hrepl]; exact hcs
  have hle2 : ‖hψ.toLp _‖ ≤ ‖hΦ.toLp _‖ := by
    rcases (norm_nonneg (hψ.toLp _)).eq_or_lt with h | h
    · rw [← h]; exact norm_nonneg _
    · nlinarith
  rw [hXn, ← hΦn]
  exact pow_le_pow_left₀ (norm_nonneg _) hle2 2

end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-- One step of the energy argument: vanishing of `a` on `[0,w)` propagates to `[0,t)` when
`R² (t - w) ≤ 1/2`. -/
lemma U1_step (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P}
    (hθ : θ ∈ closure (Set.range (TL hW T)))
    {a : Lp ℝ 2 (μT P T)} (ha : ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪a, eL (P := P) hW.le T x⟫_ℝ)
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T)))
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT P T))
    (hcP : hc.toLp c ∈ closure (Set.range (eL (P := P) hW.le T)))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hW.le T)) →
      ∫ z, c z * ψ z ∂(μT P T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT P T))
    {R : ℝ} (hac : ∀ᵐ z ∂(μT P T), |a z| ≤ R * |c z|)
    {w t : ℝ≥0} (hwt : w ≤ t) (htT : t ≤ T) (hR : R ^ 2 * ((t : ℝ) - w) ≤ 1 / 2)
    (hw : ∀ᵐ z ∂(μT P T), z.1 < (w : ℝ) → a z = 0) : ∀ᵐ z ∂(μT P T), z.1 < (t : ℝ) → a z = 0 := by
  have hA := memLp_res (Lp.memLp a) t
  have hg0 : 0 ≤ ∫ z, (a z * ind 0 t z.1) ^ 2 ∂(μT P T) := integral_nonneg fun z => sq_nonneg _
  have h1 : ∫ z, (a z * ind 0 t z.1) ^ 2 ∂(μT P T) = ∫ z, (a z * ind w t z.1) ^ 2 ∂(μT P T) := by
    refine integral_congr_ae ?_
    filter_upwards [hw, ae_fst_Ico (P := P) T] with z hz hz0
    by_cases hzw : z.1 < w
    · show (a z * ind 0 t z.1) ^ 2 = (a z * ind w t z.1) ^ 2
      rw [hz hzw, zero_mul, zero_mul]
    · have hzw' : (w : ℝ) ≤ z.1 := not_lt.1 hzw
      have h0 : (0 : ℝ) ≤ z.1 := hz0.1
      have : ind 0 t z.1 = ind w t z.1 := by
        simp only [ind, Set.indicator_apply, Set.mem_Ico, NNReal.coe_zero]
        by_cases h2 : z.1 < t <;> simp [h0, hzw', h2]
      show (a z * ind 0 t z.1) ^ 2 = (a z * ind w t z.1) ^ 2
      rw [this]
  have hcI := memLp_mulind hc w t
  have h2 : ∫ z, (a z * ind w t z.1) ^ 2 ∂(μT P T) ≤
      ∫ z, R ^ 2 * (c z * ind w t z.1) ^ 2 ∂(μT P T) := by
    refine integral_mono_ae ((memLp_mulind (Lp.memLp a) w t).integrable_sq)
      (hcI.integrable_sq.const_mul _) ?_
    filter_upwards [hac] with z hz
    have hsq : a z ^ 2 ≤ R ^ 2 * c z ^ 2 := by
      have h0 : |a z| ^ 2 ≤ (R * |c z|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hz 2
      rw [sq_abs, mul_pow, sq_abs] at h0
      exact h0
    have hi : 0 ≤ ind w t z.1 ^ 2 := sq_nonneg _
    calc (a z * ind w t z.1) ^ 2 = a z ^ 2 * ind w t z.1 ^ 2 := by ring
      _ ≤ R ^ 2 * c z ^ 2 * ind w t z.1 ^ 2 := mul_le_mul_of_nonneg_right hsq hi
      _ = R ^ 2 * (c z * ind w t z.1) ^ 2 := by ring
  rw [integral_const_mul] at h2
  have h3 := S2 hW T hc hcP hproj hwt htT
  have h4 := S1c hW T hθ ha haP t
  have hR0 : 0 ≤ R ^ 2 := sq_nonneg R
  have htw : 0 ≤ (t : ℝ) - w := sub_nonneg.2 (by exact_mod_cast hwt)
  have key : ∫ z, (a z * ind 0 t z.1) ^ 2 ∂(μT P T) ≤
      1 / 2 * ∫ z, (a z * ind 0 t z.1) ^ 2 ∂(μT P T) := by
    calc ∫ z, (a z * ind 0 t z.1) ^ 2 ∂(μT P T)
        ≤ R ^ 2 * ∫ z, (c z * ind w t z.1) ^ 2 ∂(μT P T) := (le_of_eq h1).trans h2
      _ ≤ R ^ 2 * (((t : ℝ) - w) * ∫ ω, (condExp (m t) P (θ : Ω → ℝ) ω) ^ 2 ∂P) :=
          mul_le_mul_of_nonneg_left h3 hR0
      _ ≤ R ^ 2 * (((t : ℝ) - w) * ∫ z, (a z * ind 0 t z.1) ^ 2 ∂(μT P T)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 htw) hR0
      _ = (R ^ 2 * ((t : ℝ) - w)) * ∫ z, (a z * ind 0 t z.1) ^ 2 ∂(μT P T) := by ring
      _ ≤ 1 / 2 * ∫ z, (a z * ind 0 t z.1) ^ 2 ∂(μT P T) := mul_le_mul_of_nonneg_right hR hg0
  have hgz : ∫ z, (a z * ind 0 t z.1) ^ 2 ∂(μT P T) = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hA.integrable_sq).1 hgz
  filter_upwards [hae, ae_fst_Ico (P := P) T] with z hz hz0 hzt
  have hi1 : ind 0 t z.1 = 1 := by
    simp only [ind, Set.indicator_apply, Set.mem_Ico, NNReal.coe_zero]
    rw [if_pos ⟨hz0.1, hzt⟩]
  have hz' : (a z * ind 0 t z.1) ^ 2 = 0 := hz
  rw [hi1, mul_one] at hz'
  exact (pow_eq_zero_iff two_ne_zero).1 hz'

/-- **U1 (bounded coefficient)**: if `θ = I(a)`, `c` is the predictable projection of `θ`,
`|a| ≤ R |c|` and `a = 0` before `v`, then `θ = 0`.  (Energy argument in steps of length
`1/(2(R²+1))`; no Gronwall needed.) -/
theorem U1_bdd (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P}
    (hθ : θ ∈ closure (Set.range (TL hW T)))
    {a : Lp ℝ 2 (μT P T)} (ha : ∀ x, ⟪θ, TL hW T x⟫_ℝ = ⟪a, eL (P := P) hW.le T x⟫_ℝ)
    (haP : a ∈ closure (Set.range (eL (P := P) hW.le T)))
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT P T))
    (hcP : hc.toLp c ∈ closure (Set.range (eL (P := P) hW.le T)))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hW.le T)) →
      ∫ z, c z * ψ z ∂(μT P T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT P T))
    {R : ℝ} (hac : ∀ᵐ z ∂(μT P T), |a z| ≤ R * |c z|)
    {v : ℝ≥0} (hv : ∀ᵐ z ∂(μT P T), z.1 < (v : ℝ) → a z = 0) : θ = 0 := by
  have hpos : (0 : ℝ) < 1 / (2 * (R ^ 2 + 1)) := by positivity
  set δ : ℝ≥0 := ⟨1 / (2 * (R ^ 2 + 1)), hpos.le⟩ with hδ
  have hδr : (δ : ℝ) = 1 / (2 * (R ^ 2 + 1)) := rfl
  have hRδ : R ^ 2 * (δ : ℝ) ≤ 1 / 2 := by
    rw [hδr, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hstep : ∀ n : ℕ, ∀ᵐ z ∂(μT P T), z.1 < ((min T (v + (n : ℝ≥0) * δ) : ℝ≥0) : ℝ) →
      a z = 0 := by
    intro n
    induction n with
    | zero =>
      filter_upwards [hv] with z hz hzl
      refine hz (lt_of_lt_of_le hzl ?_)
      simp
    | succ n ih =>
      refine U1_step hW T hθ ha haP hc hcP hproj hac ?_ (min_le_left _ _) ?_ ih
      · refine min_le_min_left _ ?_
        gcongr
        exact_mod_cast Nat.le_succ n
      · have e1 : ((min T (v + (n : ℝ≥0) * δ) : ℝ≥0) : ℝ) = min (T : ℝ) ((v : ℝ) + n * δ) := by
          push_cast; rfl
        have e2 : ((min T (v + ((n + 1 : ℕ) : ℝ≥0) * δ) : ℝ≥0) : ℝ) =
            min (T : ℝ) ((v : ℝ) + ((n : ℝ) + 1) * δ) := by
          push_cast; rfl
        rw [e1, e2]
        have hd : min (T : ℝ) ((v : ℝ) + ((n : ℝ) + 1) * δ) - min (T : ℝ) ((v : ℝ) + n * δ) ≤ δ := by
          have a1 := min_le_left (T : ℝ) ((v : ℝ) + ((n : ℝ) + 1) * δ)
          have a2 := min_le_right (T : ℝ) ((v : ℝ) + ((n : ℝ) + 1) * δ)
          rcases min_choice (T : ℝ) ((v : ℝ) + n * δ) with h | h <;> rw [h] <;> nlinarith
        calc R ^ 2 * (min (T : ℝ) ((v : ℝ) + ((n : ℝ) + 1) * δ) - min (T : ℝ) ((v : ℝ) + n * δ))
            ≤ R ^ 2 * δ := mul_le_mul_of_nonneg_left hd (sq_nonneg R)
          _ ≤ 1 / 2 := hRδ
  obtain ⟨n, hn⟩ := exists_nat_ge ((T : ℝ) / δ)
  have hTn : T ≤ v + (n : ℝ≥0) * δ := by
    have h1 : (T : ℝ) ≤ n * δ := by
      rw [div_le_iff₀ (by rw [hδr]; exact hpos)] at hn; exact hn
    have h2 : (T : ℝ) ≤ ((v + (n : ℝ≥0) * δ : ℝ≥0) : ℝ) := by
      push_cast; linarith [v.2]
    exact_mod_cast h2
  have haT := hstep n
  rw [min_eq_left hTn] at haT
  have ha0 : (a : ℝ × Ω → ℝ) =ᵐ[μT P T] 0 := by
    filter_upwards [haT, ae_fst_Ico (P := P) T] with z h1 h2
    exact h1 h2.2
  have haz : a = 0 := (Lp.eq_zero_iff_ae_eq_zero).2 ha0
  have hperp : ∀ x, ⟪θ, TL hW T x⟫_ℝ = 0 := fun x => by rw [ha x, haz, inner_zero_left]
  have hcl : closure (Set.range (TL hW T)) ⊆ {y | ⟪θ, y⟫_ℝ = 0} :=
    closure_minimal (by rintro _ ⟨x, rfl⟩; exact hperp x)
      (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
  exact inner_self_eq_zero.1 (hcl hθ)

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

lemma rep_dist (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) (x : Elem m T →₀ ℝ) :
    ‖TL hW T x - θ‖ = ‖eL (P := P) hW.le T x - b‖ := by
  obtain ⟨hθ, hb, hi⟩ := h
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 hθ
  choose y hy using hxr
  have hx' : Tendsto (fun n => TL hW T (y n)) atTop (𝓝 θ) := by simp_rw [hy]; exact hx
  have hE := eL_tendsto hW T hi hb hx'
  have h1 : Tendsto (fun n => ‖TL hW T x - TL hW T (y n)‖) atTop (𝓝 ‖TL hW T x - θ‖) :=
    (tendsto_const_nhds.sub hx').norm
  have h2 : Tendsto (fun n => ‖eL (P := P) hW.le T x - eL (P := P) hW.le T (y n)‖) atTop
      (𝓝 ‖eL (P := P) hW.le T x - b‖) := (tendsto_const_nhds.sub hE).norm
  have he : ∀ n, ‖TL hW T x - TL hW T (y n)‖ =
      ‖eL (P := P) hW.le T x - eL (P := P) hW.le T (y n)‖ := by
    intro n; rw [← map_sub, ← map_sub, norm_TL]
  simp_rw [he] at h1
  exact tendsto_nhds_unique h1 h2
























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
-- ===== slice of RUmod (scratch/probe/slice8c/cuts/r_q1.lean.src/RUmod.lean): 11/17 top-level decls kept =====

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
open StochCalcZ2 StochCalcZ3 StochCalcO3
open StochCalcZK
open StochCalcRU
open scoped NNReal ENNReal

variable {p : Params} {Ω : Type*} [mΩ : MeasurableSpace Ω]





end StochCalcQ2U

end StochCalcP6

-- ===== slice of P8c066573M16c (scratch/probe/slice8c/cuts/r_q1.lean.src/P8c066573M16c.lean): 38/865 top-level decls kept =====

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


lemma rep_conv (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) {x : ℕ → (Elem m T →₀ ℝ)}
    (hb : Tendsto (fun n => eL (P := P) hW.le T (x n)) atTop (𝓝 b)) :
    Tendsto (fun n => TL hW T (x n)) atTop (𝓝 θ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hb ⊢
  simp_rw [rep_dist hW T h]
  exact hb


lemma rep_norm (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) : ‖θ‖ = ‖b‖ := by
  have := rep_dist hW T h 0
  simpa using this

lemma rep_add (hW : IncrHyp m W P) (T : ℝ≥0) {θ₁ θ₂ : Lp ℝ 2 P} {b₁ b₂ : Lp ℝ 2 (μT P T)}
    (h₁ : Rep hW T θ₁ b₁) (h₂ : Rep hW T θ₂ b₂) : Rep hW T (θ₁ + θ₂) (b₁ + b₂) := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h₁.2.1
  choose y hy using hxr
  obtain ⟨xs', hxr', hx''⟩ := mem_closure_iff_seq_limit.1 h₂.2.1
  choose y' hy' using hxr'
  have e1 : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b₁) := by
    simp_rw [hy]; exact hx
  have e2 : Tendsto (fun n => eL (P := P) hW.le T (y' n)) atTop (𝓝 b₂) := by
    simp_rw [hy']; exact hx''
  refine rep_lim hW T (x := fun n => y n + y' n) ?_ ?_
  · simp_rw [map_add]; exact (rep_conv hW T h₁ e1).add (rep_conv hW T h₂ e2)
  · simp_rw [map_add]; exact e1.add e2


















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

lemma rep_neg (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {b : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ b) : Rep hW T (-θ) (-b) := by
  obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h.2.1
  choose y hy using hxr
  have e1 : Tendsto (fun n => eL (P := P) hW.le T (y n)) atTop (𝓝 b) := by
    simp_rw [hy]; exact hx
  refine rep_lim hW T (x := fun n => -y n) ?_ ?_
  · simp_rw [map_neg]; exact (rep_conv hW T h e1).neg
  · simp_rw [map_neg]; exact e1.neg

lemma rep_sub (hW : IncrHyp m W P) (T : ℝ≥0) {θ₁ θ₂ : Lp ℝ 2 P} {b₁ b₂ : Lp ℝ 2 (μT P T)}
    (h₁ : Rep hW T θ₁ b₁) (h₂ : Rep hW T θ₂ b₂) : Rep hW T (θ₁ - θ₂) (b₁ - b₂) := by
  simpa [sub_eq_add_neg] using rep_add hW T h₁ (rep_neg hW T h₂)

lemma int_eq_inner (f : Lp ℝ 2 P) {g : Ω → ℝ} (hg2 : MemLp g 2 P) :
    ∫ ω, f ω * g ω ∂P = ⟪f, hg2.toLp g⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg2.coeFn_toLp] with ω h1
  rw [h1, RCLike.inner_apply', conj_trivial]















end StochCalcO3

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

lemma stop_meas (hle : ∀ t, m t ≤ mΩ) {τ : Ω → ℝ≥0} (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) :
    Measurable τ := measurable_of_Iic fun x => hle x _ (hτ x)




/-- L2 with existence: `1_{τ ≤ r} a` is an integrand, and its integral `δ` satisfies
`δ ⊥ ξ 1_{u < τ}` for bounded `m u`-measurable `ξ`. -/
theorem L2full (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ a) {τ : Ω → ℝ≥0} (hτT : ∀ ω, τ ω ≤ T)
    (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) {bc : Lp ℝ 2 (μT P T)}
    (hbc : bc =ᵐ[μT P T] fun z => (if (τ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z) :
    ∃ δ, Rep hW T δ bc ∧ ∀ (u : ℝ≥0) (ξ : Ω → ℝ), Measurable[m u] ξ → ∀ C : ℝ,
      (∀ ω, |ξ ω| ≤ C) → ∫ ω, δ ω * (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P = 0 := by
  exact (by obtain ⟨δ, h1, h2⟩ := HedgePSNV.stopped_integrand_representation hW.mono hW.le hW.adapt hW.indep hW.mem2 hW.mean hW.var T (StochCalcP6.StochCalcO3.μT P T) rfl ((StochCalcP6.StochCalcRU.rep_iff hW T θ a).1 h).1 ((StochCalcP6.StochCalcRU.rep_iff hW T θ a).1 h).2.1 ((StochCalcP6.StochCalcRU.rep_iff hW T θ a).1 h).2.2 hτT hτ hbc; exact ⟨δ, (StochCalcP6.StochCalcRU.rep_iff hW T δ bc).2 (by unfold StochCalcP6.StochCalcRU.RepU; exact h1), h2⟩)















end StochCalcO3

/-! (B1) cutting a predictable integrand at a stopping time keeps it predictable. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-- `1_{u < τ}`. -/
noncomputable def befG (τ : Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ := if u < τ ω then 1 else 0

lemma abs_befG_le (τ : Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) : |befG τ u ω| ≤ 1 := by
  unfold befG; split_ifs <;> simp

lemma befG_contAt (τ : Ω → ℝ≥0) (ω : Ω) {u : ℝ} (hu0 : 0 < u) (hu : u ≠ (τ ω : ℝ)) :
    ContinuousAt (fun v : ℝ => befG τ v.toNNReal ω) u := by
  suffices h : ∀ᶠ v in 𝓝 u, befG τ v.toNNReal ω = befG τ u.toNNReal ω from
    continuousAt_const.congr (h.mono fun v hv => hv.symm)
  rcases lt_or_gt_of_ne hu with h | h
  · filter_upwards [Ioo_mem_nhds hu0 h] with v hv
    have hv' : v.toNNReal < τ ω := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hv.1.le]; exact hv.2
    have hu' : u.toNNReal < τ ω := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0.le]; exact h
    simp only [befG, if_pos hv', if_pos hu']
  · filter_upwards [Ioi_mem_nhds h] with v hv
    have hv' : ¬ v.toNNReal < τ ω := by
      rw [← NNReal.coe_lt_coe, not_lt]; exact (le_of_lt hv).trans (Real.le_coe_toNNReal v)
    have hu' : ¬ u.toNNReal < τ ω := by
      rw [← NNReal.coe_lt_coe, not_lt]; exact h.le.trans (Real.le_coe_toNNReal u)
    simp only [befG, if_neg hv', if_neg hu']

/-- (B1) `g ∈ Pred`, `τ` a stopping time  =>  `g 1_{r < τ} ∈ Pred`. -/
theorem pred_bef (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) (T : ℝ≥0)
    {g : ℝ × Ω → ℝ} (hg : MemLp g 2 (μT P T))
    (hgP : hg.toLp g ∈ closure (Set.range (eL (P := P) hle T)))
    {τ : Ω → ℝ≥0} (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s})
    (hgφ : MemLp (fun z => g z * befG τ z.1.toNNReal z.2) 2 (μT P T)) :
    hgφ.toLp _ ∈ closure (Set.range (eL (P := P) hle T)) := by
  have ht : Measurable (fun z : ℝ × Ω => z.1.toNNReal) :=
    measurable_real_toNNReal.comp measurable_fst
  have hτm := stop_meas hle hτ
  refine pred_mul hle hmono T hg hgP zero_le_one (abs_befG_le τ) ?_ (fun t => ?_) (fun ω => ?_) hgφ
  · unfold befG
    exact Measurable.ite (measurableSet_lt ht (hτm.comp measurable_snd)) measurable_const
      measurable_const
  · have hs : MeasurableSet[m t] {ω | t < τ ω} := by
      have h := (hτ t).compl
      convert h using 1
      ext ω
      simp [not_le]
    unfold befG
    exact Measurable.ite hs measurable_const measurable_const
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton ((τ ω : ℝ)))] with u hu hu'
    have hne : u ≠ (τ ω : ℝ) := fun h => hu (by rw [h]; rfl)
    exact (befG_contAt τ ω hu'.1 hne).tendsto.mono_left nhdsWithin_le_nhds

end StochCalcO3
-- O7B2 tail (8c066573 relay 24): append after probe/8c066573_B.lean (= L0.lean + O7B_tail).

/-! (B2) the cut-off integral `δ = I(1_{τ ≤ r} a)` is orthogonal to `1_{r<τ} ψ`, and
(B3) the projections of `θ` and of `θ - δ` agree before `τ`. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

lemma befG_meas (hle : ∀ t, m t ≤ mΩ) {τ : Ω → ℝ≥0}
    (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) :
    Measurable (fun z : ℝ × Ω => befG τ z.1.toNNReal z.2) := by
  have ht : Measurable (fun z : ℝ × Ω => z.1.toNNReal) :=
    measurable_real_toNNReal.comp measurable_fst
  unfold befG
  exact Measurable.ite (measurableSet_lt ht ((stop_meas hle hτ).comp measurable_snd))
    measurable_const measurable_const

lemma memLp_mul_befG {T : ℝ≥0} (hle : ∀ t, m t ≤ mΩ) {τ : Ω → ℝ≥0}
    (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) {g : ℝ × Ω → ℝ} (hg : MemLp g 2 (μT P T)) :
    MemLp (fun z => g z * befG τ z.1.toNNReal z.2) 2 (μT P T) := by
  refine hg.of_le (hg.aestronglyMeasurable.mul (befG_meas hle hτ).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  calc |g z| * |befG τ z.1.toNNReal z.2| ≤ |g z| * 1 :=
        mul_le_mul_of_nonneg_left (abs_befG_le _ _ _) (abs_nonneg _)
    _ = |g z| := mul_one _

lemma eE_mem (hle : ∀ t, m t ≤ mΩ) {T : ℝ≥0} (i : Elem m T) :
    (memLp_efun (P := P) hle i).toLp _ ∈ closure (Set.range (eL (P := P) hle T)) :=
  subset_closure ⟨Finsupp.single i 1, by
    simp only [eL, Finsupp.linearCombination_single, one_smul]; rfl⟩

/-- (B2), elementary case. -/
lemma bef_elem (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) (T : ℝ≥0)
    {τ : Ω → ℝ≥0} (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) {δ : Lp ℝ 2 P}
    (hδ0 : ∀ (u : ℝ≥0) (ξ : Ω → ℝ), Measurable[m u] ξ → ∀ C : ℝ,
      (∀ ω, |ξ ω| ≤ C) → ∫ ω, δ ω * (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P = 0)
    (i : Elem m T) :
    ∫ z, (δ : Ω → ℝ) z.2 * (befG τ z.1.toNNReal z.2 * efun i z) ∂(μT P T) = 0 := by
  have hδi : Integrable (δ : Ω → ℝ) P := (Lp.memLp δ).integrable one_le_two
  have hg : Measurable (fun z : ℝ × Ω => befG τ z.1.toNNReal z.2 * efun i z) :=
    (befG_meas hle hτ).mul (efun_meas hle i)
  have hint : Integrable (fun z : ℝ × Ω => (δ : Ω → ℝ) z.2 * (befG τ z.1.toNNReal z.2 * efun i z))
      ((volume.restrict (Set.Ico (0 : ℝ) T)).prod P) := by
    refine ((hδi.norm.comp_snd (volume.restrict (Set.Ico (0 : ℝ) T))).const_mul |i.C|).mono'
      ((hδi.aestronglyMeasurable.comp_snd).mul hg.aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [abs_mul]
    calc |befG τ z.1.toNNReal z.2| * |efun i z| ≤ 1 * |i.C| :=
          mul_le_mul (abs_befG_le _ _ _) (efun_abs_le i z) (abs_nonneg _) zero_le_one
      _ = |i.C| := one_mul _
  unfold μT
  rw [integral_prod _ hint]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
  simp only [Pi.zero_apply]
  by_cases hr : r ∈ Set.Ico (i.u : ℝ) i.v
  · have hur : i.u ≤ r.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ((NNReal.coe_nonneg _).trans hr.1)]
      exact hr.1
    refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans
      (hδ0 r.toNNReal i.Y (i.hY.mono (hmono hur) le_rfl) i.C i.hC)
    simp only [efun, ind, Set.indicator_of_mem hr, befG]
    ring
  · simp [efun, ind, Set.indicator_of_notMem hr]

/-- (B3) cut projections agree before `τ`. -/
theorem cut_proj (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) (T : ℝ≥0)
    {τ : Ω → ℝ≥0} (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) {δ θ θτ : Lp ℝ 2 P}
    (hd : θ - θτ = δ)
    (hδ0 : ∀ (u : ℝ≥0) (ξ : Ω → ℝ), Measurable[m u] ξ → ∀ C : ℝ,
      (∀ ω, |ξ ω| ≤ C) → ∫ ω, δ ω * (ξ ω * (if u < τ ω then (1 : ℝ) else 0)) ∂P = 0)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT P T))
    (hcP : hc.toLp c ∈ closure (Set.range (eL (P := P) hle T)))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hle T)) →
      ∫ z, c z * ψ z ∂(μT P T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT P T))
    {cτ : ℝ × Ω → ℝ} (hcτ : MemLp cτ 2 (μT P T))
    (hcτP : hcτ.toLp cτ ∈ closure (Set.range (eL (P := P) hle T)))
    (hprojτ : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hle T)) →
      ∫ z, cτ z * ψ z ∂(μT P T) = ∫ z, (θτ : Ω → ℝ) z.2 * ψ z ∂(μT P T)) :
    ∀ᵐ z ∂(μT P T), befG τ z.1.toNNReal z.2 * c z = befG τ z.1.toNNReal z.2 * cτ z := by
  have hcc : MemLp (c - cτ) 2 (μT P T) := hc.sub hcτ
  have hccP : hcc.toLp _ ∈ closure (Set.range (eL (P := P) hle T)) := by
    refine (mem_Pred_iff hle T _).1 ?_
    rw [MemLp.toLp_sub hc hcτ]
    exact Submodule.sub_mem _ ((mem_Pred_iff hle T _).2 hcP) ((mem_Pred_iff hle T _).2 hcτP)
  have hw := memLp_mul_befG hle hτ hcc
  have hθ2 : ∀ φ : Lp ℝ 2 P, MemLp (fun z : ℝ × Ω => (φ : Ω → ℝ) z.2) 2 (μT P T) := fun φ => by
    unfold μT; exact (Lp.memLp φ).comp_snd _
  have hδe : ∀ᵐ z ∂(μT P T), (δ : Ω → ℝ) z.2 = (θ : Ω → ℝ) z.2 - (θτ : Ω → ℝ) z.2 := by
    have h : (δ : Ω → ℝ) =ᵐ[P] fun ω => (θ : Ω → ℝ) ω - (θτ : Ω → ℝ) ω := by
      rw [← hd]; exact Lp.coeFn_sub θ θτ
    unfold μT
    exact Measure.quasiMeasurePreserving_snd.ae h
  have hperp : ∀ i : Elem m T,
      ∫ z, (c - cτ) z * befG τ z.1.toNNReal z.2 * efun i z ∂(μT P T) = 0 := by
    intro i
    have hψ := memLp_mul_befG hle hτ (memLp_efun (P := P) hle i)
    have hψP := pred_bef hle hmono T (memLp_efun (P := P) hle i) (eE_mem hle i) hτ hψ
    have h1 := hproj _ hψ hψP
    have h2 := hprojτ _ hψ hψP
    have h3 := bef_elem hle hmono T hτ hδ0 i
    calc ∫ z, (c - cτ) z * befG τ z.1.toNNReal z.2 * efun i z ∂(μT P T)
        = ∫ z, (c z * (efun i z * befG τ z.1.toNNReal z.2) -
            cτ z * (efun i z * befG τ z.1.toNNReal z.2)) ∂(μT P T) := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          simp only [Pi.sub_apply]; ring
      _ = ∫ z, c z * (efun i z * befG τ z.1.toNNReal z.2) ∂(μT P T) -
            ∫ z, cτ z * (efun i z * befG τ z.1.toNNReal z.2) ∂(μT P T) :=
          integral_sub (hc.integrable_mul hψ) (hcτ.integrable_mul hψ)
      _ = ∫ z, (θ : Ω → ℝ) z.2 * (efun i z * befG τ z.1.toNNReal z.2) ∂(μT P T) -
            ∫ z, (θτ : Ω → ℝ) z.2 * (efun i z * befG τ z.1.toNNReal z.2) ∂(μT P T) := by
          rw [h1, h2]
      _ = ∫ z, ((θ : Ω → ℝ) z.2 * (efun i z * befG τ z.1.toNNReal z.2) -
            (θτ : Ω → ℝ) z.2 * (efun i z * befG τ z.1.toNNReal z.2)) ∂(μT P T) :=
          (integral_sub ((hθ2 θ).integrable_mul hψ) ((hθ2 θτ).integrable_mul hψ)).symm
      _ = ∫ z, (δ : Ω → ℝ) z.2 * (befG τ z.1.toNNReal z.2 * efun i z) ∂(μT P T) := by
          refine integral_congr_ae ?_
          filter_upwards [hδe] with z hz
          rw [hz]; ring
      _ = 0 := h3
  have h0 := O6_core hle T hw (pred_bef hle hmono T hcc hccP hτ hw) hperp
  filter_upwards [h0] with z hz
  simp only [Pi.sub_apply, Pi.zero_apply] at hz
  linear_combination hz

end StochCalcO3

/-! O7.1 (U1, general): energy uniqueness for `a = -η c` with `η` continuous adapted. -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m : ℝ≥0 → MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ}

/-- One localization step: `1_{r < τ_R} a = 0`. -/
lemma U1_loc (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ a) {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT P T))
    (hcP : hc.toLp c ∈ closure (Set.range (eL (P := P) hW.le T)))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hW.le T)) →
      ∫ z, c z * ψ z ∂(μT P T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT P T))
    {η : ℝ≥0 → Ω → ℝ} (hηa : ∀ u, Measurable[m u] (η u)) (hηc : ∀ ω, Continuous fun v => η v ω)
    (hac : ∀ᵐ z ∂(μT P T), a z = -(η z.1.toNNReal z.2) * c z)
    {v : ℝ≥0} (hv : ∀ᵐ z ∂(μT P T), z.1 < (v : ℝ) → a z = 0) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ z ∂(μT P T), befG (StochCalcHit.hitR η R T) z.1.toNNReal z.2 * a z = 0 := by
  set τ := StochCalcHit.hitR η R T with hτdef
  let F : Filtration ℝ≥0 mΩ := ⟨m, hW.mono, hW.le⟩
  have hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s} := fun s =>
    StochCalcHit.hitR_isStopping F (fun u => (hηa u).stronglyMeasurable) hηc R T s
  have hτT : ∀ ω, τ ω ≤ T := StochCalcHit.hitR_le η R T
  have hτm := stop_meas hW.le hτ
  have hcut : Measurable (fun z : ℝ × Ω => if (τ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le (hτm.comp measurable_snd).coe_nnreal_real measurable_fst)
      measurable_const measurable_const
  have hbm : MemLp (fun z => (if (τ z.2 : ℝ) ≤ z.1 then (1 : ℝ) else 0) * a z) 2 (μT P T) := by
    refine (Lp.memLp a).of_le (hcut.aestronglyMeasurable.mul (Lp.memLp a).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    split_ifs <;> simp
  obtain ⟨δ, hδ, hδ0⟩ := L2full hW T h hτT hτ hbm.coeFn_toLp
  have hθτ := rep_sub hW T h hδ
  have hθτ2 : MemLp (fun z : ℝ × Ω => ((θ - δ : Lp ℝ 2 P) : Ω → ℝ) z.2) 2 (μT P T) := by
    unfold μT; exact (Lp.memLp _).comp_snd _
  obtain ⟨cτ, hcτ, hcτP, hprojτ⟩ := proj_fun hW.le T hθτ2
  have hcc := cut_proj hW.le hW.mono T hτ (sub_sub_cancel θ δ) hδ0 hc hcP hproj hcτ hcτP hprojτ
  have haτ : ∀ᵐ z ∂(μT P T), ((a - hbm.toLp _ : Lp ℝ 2 (μT P T)) : ℝ × Ω → ℝ) z =
      befG τ z.1.toNNReal z.2 * a z := by
    filter_upwards [Lp.coeFn_sub a (hbm.toLp _), hbm.coeFn_toLp, ae_fst_Ico (P := P) T]
      with z h1 h2 h3
    rw [h1, Pi.sub_apply, h2]
    have h0 : (0 : ℝ) ≤ z.1 := h3.1
    unfold befG
    by_cases hz : (τ z.2 : ℝ) ≤ z.1
    · have hn : ¬ z.1.toNNReal < τ z.2 := by
        rw [not_lt, ← NNReal.coe_le_coe, Real.coe_toNNReal _ h0]; exact hz
      rw [if_pos hz, if_neg hn]; ring
    · have hn : z.1.toNNReal < τ z.2 := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ h0]; exact lt_of_not_ge hz
      rw [if_neg hz, if_pos hn]; ring
  have hθ0 : θ - δ = 0 := by
    refine U1_bdd hW T hθτ.1 hθτ.2.2 hθτ.2.1 hcτ hcτP hprojτ (R := R) ?_ (v := v) ?_
    · filter_upwards [haτ, hac, hcc] with z h1 h2 h3
      rw [h1]
      by_cases hz : z.1.toNNReal < τ z.2
      · have hb : befG τ z.1.toNNReal z.2 = 1 := if_pos hz
        have hη := StochCalcHit.abs_lt_of_lt_hitR hz
        rw [hb, one_mul, one_mul] at h3
        rw [hb, one_mul, h2, h3, abs_mul, abs_neg]
        exact mul_le_mul_of_nonneg_right hη.le (abs_nonneg _)
      · have hb : befG τ z.1.toNNReal z.2 = 0 := if_neg hz
        rw [hb, zero_mul, abs_zero]
        exact mul_nonneg hR (abs_nonneg _)
    · filter_upwards [haτ, hv] with z h1 h2 hz
      rw [h1, h2 hz, mul_zero]
  have hn := rep_norm hW T hθτ
  rw [hθ0, norm_zero] at hn
  have hz : a - hbm.toLp _ = 0 := norm_eq_zero.1 hn.symm
  rw [hz] at haτ
  filter_upwards [haτ, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μT P T)] with z h1 h2
  rw [← h1, h2, Pi.zero_apply]

/-- O7.1 (U1): `θ = I(a)`, `a = -η c` with `c` the predictable projection of `θ`, `η` continuous
adapted, `a = 0` before `v`  =>  `θ = 0`. -/
theorem U1 (hW : IncrHyp m W P) (T : ℝ≥0) {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)}
    (h : Rep hW T θ a) {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT P T))
    (hcP : hc.toLp c ∈ closure (Set.range (eL (P := P) hW.le T)))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hW.le T)) →
      ∫ z, c z * ψ z ∂(μT P T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT P T))
    {η : ℝ≥0 → Ω → ℝ} (hηa : ∀ u, Measurable[m u] (η u)) (hηc : ∀ ω, Continuous fun v => η v ω)
    (hac : ∀ᵐ z ∂(μT P T), a z = -(η z.1.toNNReal z.2) * c z)
    {v : ℝ≥0} (hv : ∀ᵐ z ∂(μT P T), z.1 < (v : ℝ) → a z = 0) : θ = 0 := by
  have hall : ∀ᵐ z ∂(μT P T), ∀ n : ℕ,
      befG (StochCalcHit.hitR η n T) z.1.toNNReal z.2 * a z = 0 :=
    ae_all_iff.2 fun n => U1_loc hW T h hc hcP hproj hηa hηc hac hv (Nat.cast_nonneg n)
  have ha0 : (a : ℝ × Ω → ℝ) =ᵐ[μT P T] 0 := by
    filter_upwards [hall, ae_fst_Ico (P := P) T] with z h1 h2
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      (hηc z.2).continuousOn
    obtain ⟨n, hn⟩ := exists_nat_gt C
    have hT : StochCalcHit.hitR η n T z.2 = T := StochCalcHit.hitR_eq_T fun w hw =>
      lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using hC w ⟨bot_le, hw⟩) hn
    have hlt : z.1.toNNReal < StochCalcHit.hitR η n T z.2 := by
      rw [hT, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ h2.1]; exact h2.2
    have h1n := h1 n
    rw [show befG (StochCalcHit.hitR η n T) z.1.toNNReal z.2 = 1 from if_pos hlt, one_mul] at h1n
    exact h1n
  have hA : a = 0 := Lp.ext (ha0.trans (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μT P T)).symm)
  have hn := rep_norm hW T h
  rw [hA, norm_zero] at hn
  exact norm_eq_zero.1 hn

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

/-- A K-elementary process viewed as an F-elementary process. -/
def Elem.lift {mK mF : ℝ≥0 → MeasurableSpace Ω} (hKF : ∀ s, mK s ≤ mF s) {T : ℝ≥0}
    (i : Elem mK T) : Elem mF T where
  u := i.u
  v := i.v
  huv := i.huv
  hvT := i.hvT
  Y := i.Y
  hY := i.hY.mono (hKF i.u) le_rfl
  C := i.C
  hC := i.hC

/-- The clamped conditional expectation `E[Y | mK u]` of an F-elementary integrand. -/
noncomputable def ceY (mK : ℝ≥0 → MeasurableSpace Ω) (P : Measure Ω) {mF : ℝ≥0 → MeasurableSpace Ω}
    {T : ℝ≥0} (i : Elem mF T) (ω : Ω) : ℝ :=
  max (-|i.C|) (min |i.C| (condExp (mK i.u) P i.Y ω))

/-- The K-elementary process `E[Y | mK u] 1_[u,v)`. -/
noncomputable def Elem.proj (mK : ℝ≥0 → MeasurableSpace Ω) (P : Measure Ω)
    {mF : ℝ≥0 → MeasurableSpace Ω} {T : ℝ≥0} (i : Elem mF T) : Elem mK T where
  u := i.u
  v := i.v
  huv := i.huv
  hvT := i.hvT
  Y := ceY mK P i
  hY := by
    have h := (stronglyMeasurable_condExp (m := mK i.u) (μ := P) (f := i.Y)).measurable
    exact measurable_const.max (measurable_const.min h)
  C := |i.C|
  hC := fun ω => by
    unfold ceY
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith [abs_nonneg i.C]) (min_le_left _ _)⟩

lemma ceY_ae {mK mF : ℝ≥0 → MeasurableSpace Ω} {T : ℝ≥0} (i : Elem mF T) :
    ceY mK P i =ᵐ[P] condExp (mK i.u) P i.Y := by
  have hb : ∀ᵐ ω ∂P, |i.Y ω| ≤ ((⟨|i.C|, abs_nonneg _⟩ : ℝ≥0) : ℝ) :=
    Eventually.of_forall fun ω => (i.hC ω).trans (le_abs_self _)
  filter_upwards [ae_bdd_condExp_of_ae_bdd (m := mK i.u) hb] with ω hω
  have hω' : -|i.C| ≤ condExp (mK i.u) P i.Y ω ∧ condExp (mK i.u) P i.Y ω ≤ |i.C| := abs_le.1 hω
  unfold ceY
  rw [min_eq_right hω'.2, max_eq_right hω'.1]

/-- Conditional expectation of an L²-element is a contraction. -/
lemma norm_ce_le {m : MeasurableSpace Ω} {ψ f : Lp ℝ 2 P} (h : (ψ : Ω → ℝ) =ᵐ[P] condExp m P f) :
    ‖ψ‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae h]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_condExp_le_eLpNorm _ one_le_two)

lemma integrable_L2 (f : Lp ℝ 2 P) : Integrable (f : Ω → ℝ) P := (Lp.memLp f).integrable one_le_two

/-- Self-adjointness of the conditional expectation against an `m`-measurable L² element. -/
lemma inner_ce {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {θ φ : Lp ℝ 2 P}
    (hφ : (φ : Ω → ℝ) =ᵐ[P] condExp m P θ) (g : Lp ℝ 2 P)
    (hg : AEStronglyMeasurable[m] (g : Ω → ℝ) P) : ⟪φ, g⟫_ℝ = ⟪θ, g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  have hint : Integrable ((θ : Ω → ℝ) * (g : Ω → ℝ)) P :=
    (Lp.memLp θ).integrable_mul (Lp.memLp g)
  have hpull := condExp_mul_of_aestronglyMeasurable_right hg hint (integrable_L2 (mΩ := mΩ) θ)
  calc ∫ ω, ⟪(φ : Ω → ℝ) ω, (g : Ω → ℝ) ω⟫_ℝ ∂P
      = ∫ ω, condExp m P ((θ : Ω → ℝ) * (g : Ω → ℝ)) ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hφ, hpull] with ω h1 h2
        rw [RCLike.inner_apply', conj_trivial, h1, h2, Pi.mul_apply, mul_comm]
    _ = ∫ ω, ((θ : Ω → ℝ) * (g : Ω → ℝ)) ω ∂P := integral_condExp hm
    _ = ∫ ω, ⟪(θ : Ω → ℝ) ω, (g : Ω → ℝ) ω⟫_ℝ ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        beta_reduce
        rw [RCLike.inner_apply', conj_trivial, Pi.mul_apply, mul_comm]

lemma ifun_meas_T {m : ℝ≥0 → MeasurableSpace Ω} (hW : IncrHyp m W P) {T : ℝ≥0} (i : Elem m T) :
    Measurable[m T] (ifun W i) :=
  (i.hY.mono (hW.mono (i.huv.trans i.hvT)) le_rfl).mul
    ((dW_meas hW i.huv).mono (hW.mono i.hvT) le_rfl)

/-- Conditional expectation of one F-elementary integral onto `mK T`. -/
lemma ce_ifun {mF mK : ℝ≥0 → MeasurableSpace Ω} (hF : IncrHyp mF W P) (hK : IncrHyp mK W P)
    {T : ℝ≥0}
    (H1 : ∀ (u : ℝ≥0) (Y : Ω → ℝ), u ≤ T → Measurable[mF u] Y → (∃ C, ∀ ω, |Y ω| ≤ C) →
      condExp (mK T) P Y =ᵐ[P] condExp (mK u) P Y)
    (i : Elem mF T) :
    condExp (mK T) P (ifun W i) =ᵐ[P] ifun W (Elem.proj mK P i) := by
  have hdW : StronglyMeasurable[mK T] (fun ω => W i.v ω - W i.u ω) :=
    ((dW_meas hK i.huv).mono (hK.mono i.hvT) le_rfl).stronglyMeasurable
  have hYi : Integrable i.Y P :=
    (memLp_top_of_bound (i.hY.mono (hF.le i.u) le_rfl).aestronglyMeasurable i.C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact i.hC ω)).integrable le_top
  have hint : Integrable (i.Y * fun ω => W i.v ω - W i.u ω) P :=
    (memLp_ifun hF i).integrable one_le_two
  have hpull := condExp_mul_of_stronglyMeasurable_right hdW hint hYi
  have hH := H1 i.u i.Y (i.huv.trans i.hvT) i.hY ⟨i.C, i.hC⟩
  have hc := ceY_ae (mK := mK) (P := P) i
  have e : ifun W i = (i.Y * fun ω => W i.v ω - W i.u ω) := rfl
  rw [e]
  filter_upwards [hpull, hH, hc] with ω h1 h2 h3
  rw [h1, Pi.mul_apply, h2, ← h3]
  rfl

lemma ce_TL {mF mK : ℝ≥0 → MeasurableSpace Ω} (hF : IncrHyp mF W P) (hK : IncrHyp mK W P)
    {T : ℝ≥0}
    (H1 : ∀ (u : ℝ≥0) (Y : Ω → ℝ), u ≤ T → Measurable[mF u] Y → (∃ C, ∀ ω, |Y ω| ≤ C) →
      condExp (mK T) P Y =ᵐ[P] condExp (mK u) P Y)
    (x : Elem mF T →₀ ℝ) :
    (TL hK T (Finsupp.mapDomain (Elem.proj mK P) x) : Ω → ℝ) =ᵐ[P]
      condExp (mK T) P (TL hF T x : Ω → ℝ) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    simp only [Finsupp.mapDomain_zero, map_zero]
    refine (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P)).trans ?_
    refine (condExp_congr_ae (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P))).trans ?_ |>.symm
    rw [condExp_zero]
  | add x y hx hy =>
    rw [Finsupp.mapDomain_add, map_add, map_add]
    filter_upwards [Lp.coeFn_add (TL hK T (Finsupp.mapDomain (Elem.proj mK P) x))
        (TL hK T (Finsupp.mapDomain (Elem.proj mK P) y)), hx, hy,
      condExp_congr_ae (m := mK T) (Lp.coeFn_add (TL hF T x) (TL hF T y)),
      condExp_add (m := mK T) (integrable_L2 (TL hF T x)) (integrable_L2 (TL hF T y))]
      with ω h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, h3, h4, h5, Pi.add_apply]
  | single i c =>
    rw [Finsupp.mapDomain_single]
    simp only [TL, Finsupp.linearCombination_single]
    filter_upwards [Lp.coeFn_smul c (eI hK T (Elem.proj mK P i)),
      (memLp_ifun hK (Elem.proj mK P i)).coeFn_toLp,
      condExp_congr_ae (m := mK T) (Lp.coeFn_smul c (eI hF T i)),
      condExp_congr_ae (m := mK T) (((memLp_ifun hF i).coeFn_toLp).const_smul c),
      condExp_smul (m := mK T) (μ := P) c (ifun W i),
      ce_ifun hF hK H1 i] with ω h1 h2 h3 h4 h5 h6
    rw [h1, Pi.smul_apply, h3]
    simp only [eI] at h2 ⊢
    rw [h4, h5, Pi.smul_apply, h6, h2]

/-- **O7.2 (K-projection)**. -/
theorem Kproj {mF mK : ℝ≥0 → MeasurableSpace Ω} (hF : IncrHyp mF W P) (hK : IncrHyp mK W P)
    (hKF : ∀ s, mK s ≤ mF s) (T : ℝ≥0)
    (H1 : ∀ (u : ℝ≥0) (Y : Ω → ℝ), u ≤ T → Measurable[mF u] Y → (∃ C, ∀ ω, |Y ω| ≤ C) →
      condExp (mK T) P Y =ᵐ[P] condExp (mK u) P Y)
    {θ : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)} (h : Rep hF T θ a)
    {φ : Lp ℝ 2 P} (hφ : (φ : Ω → ℝ) =ᵐ[P] condExp (mK T) P θ) :
    ∃ b : Lp ℝ 2 (μT P T), Rep hK T φ b ∧
      ∀ ψ ∈ closure (Set.range (eL (P := P) hK.le T)), ⟪b, ψ⟫_ℝ = ⟪a, ψ⟫_ℝ := by
  let K := Pred (P := P) hK.le T
  haveI : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let b : Lp ℝ 2 (μT P T) := K.starProjection a
  have hbK : b ∈ K := by
    simp only [b, Submodule.starProjection_apply]
    exact (K.orthogonalProjection _).2
  have hbψ : ∀ ψ ∈ closure (Set.range (eL (P := P) hK.le T)), ⟪b, ψ⟫_ℝ = ⟪a, ψ⟫_ℝ := by
    intro ψ hψ
    have hψK : ψ ∈ K := (mem_Pred_iff hK.le T ψ).2 hψ
    simp only [b]
    rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 hψK]
  refine ⟨b, ⟨?_, (mem_Pred_iff hK.le T b).1 hbK, fun x => ?_⟩, hbψ⟩
  · -- closure part
    obtain ⟨xs, hxr, hx⟩ := mem_closure_iff_seq_limit.1 h.1
    choose y hy using hxr
    have hx' : Tendsto (fun n => TL hF T (y n)) atTop (𝓝 θ) := by simp_rw [hy]; exact hx
    have hlim : Tendsto (fun n => TL hK T (Finsupp.mapDomain (Elem.proj mK P) (y n))) atTop (𝓝 φ) := by
      rw [tendsto_iff_norm_sub_tendsto_zero] at hx' ⊢
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => norm_ce_le (m := mK T) ?_) hx'
      filter_upwards [Lp.coeFn_sub (TL hK T (Finsupp.mapDomain (Elem.proj mK P) (y n))) φ,
        ce_TL hF hK H1 (y n), hφ,
        condExp_congr_ae (m := mK T) (Lp.coeFn_sub (TL hF T (y n)) θ),
        condExp_sub (m := mK T) (integrable_L2 (TL hF T (y n))) (integrable_L2 θ)]
        with ω h1 h2 h3 h4 h5
      rw [h1, Pi.sub_apply, h2, h3, h4, h5, Pi.sub_apply]
    exact mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ⟨_, rfl⟩)
  · -- inner identity
    have hx : ⟪φ, TL hK T x⟫_ℝ = ⟪a, eL (P := P) hK.le T x⟫_ℝ := by
      induction x using Finsupp.induction_linear with
      | zero => simp
      | add x y hx hy => simp only [map_add, inner_add_right, hx, hy]
      | single i c =>
        simp only [TL, eL, Finsupp.linearCombination_single, inner_smul_right]
        congr 1
        have hg : AEStronglyMeasurable[mK T] (eI hK T i : Ω → ℝ) P :=
          (ifun_meas_T hK i).stronglyMeasurable.aestronglyMeasurable.congr
            (memLp_ifun hK i).coeFn_toLp.symm
        rw [inner_ce (hK.le T) hφ _ hg]
        have h1 := h.2.2 (Finsupp.single (Elem.lift hKF i) 1)
        simp only [TL, eL, Finsupp.linearCombination_single, one_smul] at h1
        exact h1
    rw [hx, hbψ _ (subset_closure ⟨x, rfl⟩)]

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

lemma eta_meas (hle : ∀ t, m t ≤ mΩ) {η : ℝ≥0 → Ω → ℝ} (hηa : ∀ u, Measurable[m u] (η u))
    (hηc : ∀ ω, Continuous fun v => η v ω) :
    Measurable (fun z : ℝ × Ω => η z.1.toNNReal z.2) := by
  have hu : Measurable (Function.uncurry η) :=
    measurable_uncurry_of_continuous_of_measurable hηc fun u => (hηa u).mono (hle u) le_rfl
  exact hu.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

lemma etabef_abs_le {η : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0} {R : ℝ} (hR : 0 ≤ R)
    (hητ : ∀ u ω, u < τ ω → |η u ω| ≤ R) (u : ℝ≥0) (ω : Ω) : |η u ω * befG τ u ω| ≤ R := by
  unfold befG
  split_ifs with h
  · rw [mul_one]; exact hητ u ω h
  · rw [mul_zero, abs_zero]; exact hR

lemma memLp_mul_etabef {T : ℝ≥0} (hle : ∀ t, m t ≤ mΩ) {η : ℝ≥0 → Ω → ℝ}
    (hηa : ∀ u, Measurable[m u] (η u)) (hηc : ∀ ω, Continuous fun v => η v ω)
    {τ : Ω → ℝ≥0} (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) {R : ℝ} (hR : 0 ≤ R)
    (hητ : ∀ u ω, u < τ ω → |η u ω| ≤ R) {g : ℝ × Ω → ℝ} (hg : MemLp g 2 (μT P T)) :
    MemLp (fun z => g z * (η z.1.toNNReal z.2 * befG τ z.1.toNNReal z.2)) 2 (μT P T) := by
  refine (hg.const_mul R).of_le (hg.aestronglyMeasurable.mul
    ((eta_meas hle hηa hηc).mul (befG_meas hle hτ)).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul (g z), abs_mul R, abs_of_nonneg hR, mul_comm R]
  exact mul_le_mul_of_nonneg_left (etabef_abs_le hR hητ _ _) (abs_nonneg _)

/-- `g ∈ Pred` => `g η 1_{r<τ} ∈ Pred` when `|η| ≤ R` before `τ`. -/
theorem pred_etabef (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) (T : ℝ≥0)
    {g : ℝ × Ω → ℝ} (hg : MemLp g 2 (μT P T))
    (hgP : hg.toLp g ∈ closure (Set.range (eL (P := P) hle T)))
    {η : ℝ≥0 → Ω → ℝ} (hηa : ∀ u, Measurable[m u] (η u)) (hηc : ∀ ω, Continuous fun v => η v ω)
    {τ : Ω → ℝ≥0} (hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s}) {R : ℝ} (hR : 0 ≤ R)
    (hητ : ∀ u ω, u < τ ω → |η u ω| ≤ R) :
    (memLp_mul_etabef (P := P) (T := T) hle hηa hηc hτ hR hητ hg).toLp _ ∈
      closure (Set.range (eL (P := P) hle T)) := by
  refine pred_mul hle hmono T hg hgP (φ := fun u ω => η u ω * befG τ u ω) hR
    (etabef_abs_le hR hητ) ((eta_meas hle hηa hηc).mul (befG_meas hle hτ)) (fun t => ?_)
    (fun ω => ?_) _
  · have hs : MeasurableSet[m t] {ω | t < τ ω} := by
      have h := (hτ t).compl
      convert h using 1
      ext ω
      simp [not_le]
    exact (hηa t).mul (by unfold befG; exact Measurable.ite hs measurable_const measurable_const)
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton ((τ ω : ℝ)))] with u hu hu'
    have hne : u ≠ (τ ω : ℝ) := fun h => hu (by rw [h]; rfl)
    have h1 : ContinuousAt (fun v : ℝ => η v.toNNReal ω) u :=
      ((hηc ω).comp continuous_real_toNNReal).continuousAt
    exact (h1.mul (befG_contAt τ ω hu'.1 hne)).tendsto.mono_left nhdsWithin_le_nhds

/-- **O7.4a (identification)**. -/
theorem ident (hle : ∀ t, m t ≤ mΩ) (hmono : Monotone m) (T : ℝ≥0)
    {b c' : ℝ × Ω → ℝ} (hb : MemLp b 2 (μT P T))
    (hbP : hb.toLp b ∈ closure (Set.range (eL (P := P) hle T)))
    (hc' : MemLp c' 2 (μT P T)) (hc'P : hc'.toLp c' ∈ closure (Set.range (eL (P := P) hle T)))
    {η : ℝ≥0 → Ω → ℝ} (hηa : ∀ u, Measurable[m u] (η u)) (hηc : ∀ ω, Continuous fun v => η v ω)
    (H : ∀ (R : ℕ) (i : Elem m T),
      ∫ z, b z * (befG (StochCalcHit.hitR η R T) z.1.toNNReal z.2 * efun i z) ∂(μT P T) =
        -∫ z, c' z * (η z.1.toNNReal z.2 * befG (StochCalcHit.hitR η R T) z.1.toNNReal z.2 *
          efun i z) ∂(μT P T)) :
    ∀ᵐ z ∂(μT P T), b z = -(η z.1.toNNReal z.2) * c' z := by
  have hloc : ∀ R : ℕ, ∀ᵐ z ∂(μT P T),
      b z * befG (StochCalcHit.hitR η R T) z.1.toNNReal z.2 +
        c' z * (η z.1.toNNReal z.2 * befG (StochCalcHit.hitR η R T) z.1.toNNReal z.2) = 0 := by
    intro R
    set τ := StochCalcHit.hitR η R T with hτdef
    let F : Filtration ℝ≥0 mΩ := ⟨m, hmono, hle⟩
    have hτ : ∀ s, MeasurableSet[m s] {ω | τ ω ≤ s} := fun s =>
      StochCalcHit.hitR_isStopping F (fun u => (hηa u).stronglyMeasurable) hηc R T s
    have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    have hητ : ∀ u ω, u < τ ω → |η u ω| ≤ R := fun u ω h =>
      (StochCalcHit.abs_lt_of_lt_hitR h).le
    have h1 := memLp_mul_befG hle hτ hb
    have h2 := memLp_mul_etabef hle hηa hηc hτ hR hητ hc'
    have hw := h1.add h2
    have hwP : hw.toLp _ ∈ closure (Set.range (eL (P := P) hle T)) := by
      refine (mem_Pred_iff hle T _).1 ?_
      rw [MemLp.toLp_add h1 h2]
      exact Submodule.add_mem _ ((mem_Pred_iff hle T _).2 (pred_bef hle hmono T hb hbP hτ h1))
        ((mem_Pred_iff hle T _).2 (pred_etabef hle hmono T hc' hc'P hηa hηc hτ hR hητ))
    have hperp : ∀ i : Elem m T, ∫ z, ((fun z => b z * befG τ z.1.toNNReal z.2) +
        fun z => c' z * (η z.1.toNNReal z.2 * befG τ z.1.toNNReal z.2)) z * efun i z ∂(μT P T) = 0 := by
      intro i
      have hψ1 := memLp_mul_befG hle hτ (memLp_efun (P := P) hle i)
      have hψ2 := memLp_mul_etabef hle hηa hηc hτ hR hητ (memLp_efun (P := P) hle i)
      have i1 := hb.integrable_mul hψ1
      have i2 := hc'.integrable_mul hψ2
      have e1 : ∫ z, b z * (befG τ z.1.toNNReal z.2 * efun i z) ∂(μT P T) =
          ∫ z, b z * (efun i z * befG τ z.1.toNNReal z.2) ∂(μT P T) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_); simp only; ring
      have e2 : ∫ z, c' z * (η z.1.toNNReal z.2 * befG τ z.1.toNNReal z.2 * efun i z) ∂(μT P T) =
          ∫ z, c' z * (efun i z * (η z.1.toNNReal z.2 * befG τ z.1.toNNReal z.2)) ∂(μT P T) := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_); simp only; ring
      have hH := H R i
      rw [e1, e2] at hH
      calc ∫ z, ((fun z => b z * befG τ z.1.toNNReal z.2) +
            fun z => c' z * (η z.1.toNNReal z.2 * befG τ z.1.toNNReal z.2)) z * efun i z ∂(μT P T)
          = ∫ z, (b z * (efun i z * befG τ z.1.toNNReal z.2) +
              c' z * (efun i z * (η z.1.toNNReal z.2 * befG τ z.1.toNNReal z.2))) ∂(μT P T) := by
            refine integral_congr_ae (Eventually.of_forall fun z => ?_)
            simp only [Pi.add_apply]; ring
        _ = ∫ z, b z * (efun i z * befG τ z.1.toNNReal z.2) ∂(μT P T) +
              ∫ z, c' z * (efun i z * (η z.1.toNNReal z.2 * befG τ z.1.toNNReal z.2)) ∂(μT P T) :=
            integral_add i1 i2
        _ = 0 := by rw [hH, neg_add_cancel]
    have h0 := O6_core hle T hw hwP hperp
    filter_upwards [h0] with z hz
    simpa only [Pi.add_apply, Pi.zero_apply] using hz
  have hall := ae_all_iff.2 hloc
  filter_upwards [hall, ae_fst_Ico (P := P) T] with z h1 h2
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    (hηc z.2).continuousOn
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hT : StochCalcHit.hitR η n T z.2 = T := StochCalcHit.hitR_eq_T fun w hw =>
    lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using hC w ⟨bot_le, hw⟩) hn
  have hlt : z.1.toNNReal < StochCalcHit.hitR η n T z.2 := by
    rw [hT, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ h2.1]; exact h2.2
  have h1n := h1 n
  rw [show befG (StochCalcHit.hitR η n T) z.1.toNNReal z.2 = 1 from if_pos hlt, mul_one,
    mul_one] at h1n
  linear_combination h1n

end StochCalcO3

/-! O7.4b (8c066573 relay 25): `Kshift`.  If `θ = I_F(a)` with `a = -η c`, `c` the F-projection of
`θ`, and `η` continuous and K-adapted, then `φ = E[θ | mK T]` satisfies `φ = I_K(b)` with
`b = -η c_φ`, `c_φ` the K-projection of `φ` (the hypothesis shape of `U1` in the filtration K). -/

namespace StochCalcO3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace RealInnerProductSpace NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {W : ℝ≥0 → Ω → ℝ}

lemma predK_sub {mF mK : ℝ≥0 → MeasurableSpace Ω} (hF : IncrHyp mF W P) (hK : IncrHyp mK W P)
    (hKF : ∀ s, mK s ≤ mF s) (T : ℝ≥0) :
    closure (Set.range (eL (P := P) hK.le T)) ⊆ closure (Set.range (eL (P := P) hF.le T)) := by
  refine closure_mono ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨Finsupp.mapDomain (Elem.lift hKF) x, ?_⟩
  simp only [eL, Finsupp.linearCombination_mapDomain]
  rfl

lemma snd_ce {mK : ℝ≥0 → MeasurableSpace Ω} (hK : IncrHyp mK W P) (T : ℝ≥0) {θ φ : Lp ℝ 2 P}
    (hφ : (φ : Ω → ℝ) =ᵐ[P] condExp (mK T) P θ) {ψ : ℝ × Ω → ℝ} (hψ : MemLp ψ 2 (μT P T))
    (hψP : hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hK.le T))) :
    ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT P T) = ∫ z, (φ : Ω → ℝ) z.2 * ψ z ∂(μT P T) := by
  have hθ2 : ∀ g : Lp ℝ 2 P, MemLp (fun z : ℝ × Ω => (g : Ω → ℝ) z.2) 2 (μT P T) := fun g => by
    unfold μT; exact (Lp.memLp g).comp_snd _
  have hw := (hθ2 θ).sub (hθ2 φ)
  have hel : ∀ i : Elem mK T, ⟪hw.toLp _, eE (P := P) hK.le T i⟫_ℝ = 0 := by
    intro i
    rw [inner_toLp_eE]
    have hY2 : MemLp i.Y 2 P :=
      memLp_of_bounded (a := -i.C) (b := i.C)
        (Eventually.of_forall fun ω => abs_le.1 (i.hC ω))
        (i.hY.mono (hK.le i.u) le_rfl).aestronglyMeasurable 2
    have hg : AEStronglyMeasurable[mK T] (hY2.toLp i.Y : Ω → ℝ) P :=
      ((i.hY.mono (hK.mono (i.huv.trans i.hvT)) le_rfl).stronglyMeasurable.aestronglyMeasurable).congr
        hY2.coeFn_toLp.symm
    have hi := inner_ce (hK.le T) hφ _ hg
    rw [← int_eq_inner, ← int_eq_inner] at hi
    have e : ∫ z, ((fun z : ℝ × Ω => (θ : Ω → ℝ) z.2) - fun z : ℝ × Ω => (φ : Ω → ℝ) z.2) z * efun i z
        ∂(μT P T) = ∫ z, ind i.u i.v z.1 * ((θ : Ω → ℝ) z.2 * i.Y z.2 - (φ : Ω → ℝ) z.2 * i.Y z.2)
        ∂(μT P T) := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [Pi.sub_apply, efun]; ring
    rw [e, μT, integral_prod_mul (fun r => ind i.u i.v r)
      (fun ω => (θ : Ω → ℝ) ω * i.Y ω - (φ : Ω → ℝ) ω * i.Y ω),
      integral_sub (f := fun ω => (θ : Ω → ℝ) ω * i.Y ω) (g := fun ω => (φ : Ω → ℝ) ω * i.Y ω)
        ((Lp.memLp θ).integrable_mul hY2) ((Lp.memLp φ).integrable_mul hY2), hi,
      sub_self, mul_zero]
  have hcl : closure (Set.range (eL (P := P) hK.le T)) ⊆ {x | ⟪hw.toLp _, x⟫_ℝ = 0} := by
    refine closure_minimal ?_ (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
    rintro _ ⟨x, rfl⟩
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [Set.mem_setOf_eq, map_add, inner_add_right] at hx hy ⊢; rw [hx, hy, add_zero]
    | single i c =>
      simp only [Set.mem_setOf_eq, eL, Finsupp.linearCombination_single, inner_smul_right]
      rw [hel i, mul_zero]
  have h0 := hcl hψP
  simp only [Set.mem_setOf_eq] at h0
  rw [inner_toLp_toLp] at h0
  have e2 : ∫ z, ((fun z : ℝ × Ω => (θ : Ω → ℝ) z.2) - fun z : ℝ × Ω => (φ : Ω → ℝ) z.2) z * ψ z ∂(μT P T) =
      ∫ z, ((θ : Ω → ℝ) z.2 * ψ z - (φ : Ω → ℝ) z.2 * ψ z) ∂(μT P T) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]; ring
  rw [e2, integral_sub (f := fun z => (θ : Ω → ℝ) z.2 * ψ z) (g := fun z => (φ : Ω → ℝ) z.2 * ψ z)
    ((hθ2 θ).integrable_mul hψ) ((hθ2 φ).integrable_mul hψ)] at h0
  linarith


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
-- ===== slice of P8c066573M17 (scratch/probe/slice8c/cuts/r_q1.lean.src/P8c066573M17.lean): 0/73 top-level decls kept =====

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

-- ===== slice of P8c066573M18 (scratch/probe/slice8c/cuts/r_q1.lean.src/P8c066573M18.lean): 2/23 top-level decls kept =====

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

theorem KshiftG {mF mK : ℝ≥0 → MeasurableSpace Ω} (hF : IncrHyp mF W P) (hK : IncrHyp mK W P)
    (hKF : ∀ s, mK s ≤ mF s) (T : ℝ≥0)
    (H1 : ∀ (u : ℝ≥0) (Y : Ω → ℝ), u ≤ T → Measurable[mF u] Y → (∃ C, ∀ ω, |Y ω| ≤ C) →
      condExp (mK T) P Y =ᵐ[P] condExp (mK u) P Y)
    {θ θB : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)} (h : Rep hF T θB a)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT P T))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hF.le T)) →
      ∫ z, c z * ψ z ∂(μT P T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT P T))
    {η : ℝ≥0 → Ω → ℝ} (hηa : ∀ u, Measurable[mK u] (η u)) (hηc : ∀ ω, Continuous fun v => η v ω)
    (hac : ∀ᵐ z ∂(μT P T), a z = -(η z.1.toNNReal z.2) * c z)
    {φ : Lp ℝ 2 P} (hφ : (φ : Ω → ℝ) =ᵐ[P] condExp (mK T) P θ)
    (hφB : (φ : Ω → ℝ) =ᵐ[P] condExp (mK T) P θB)
    {cφ : ℝ × Ω → ℝ} (hcφ : MemLp cφ 2 (μT P T))
    (hcφP : hcφ.toLp cφ ∈ closure (Set.range (eL (P := P) hK.le T)))
    (hprojφ : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hK.le T)) →
      ∫ z, cφ z * ψ z ∂(μT P T) = ∫ z, (φ : Ω → ℝ) z.2 * ψ z ∂(μT P T)) :
    ∃ b : Lp ℝ 2 (μT P T), Rep hK T φ b ∧
      ∀ᵐ z ∂(μT P T), b z = -(η z.1.toNNReal z.2) * cφ z := by
  obtain ⟨b, hb, hbψ⟩ := Kproj hF hK hKF T H1 h hφB
  refine ⟨b, hb, ?_⟩
  have hbm : MemLp (b : ℝ × Ω → ℝ) 2 (μT P T) := Lp.memLp b
  have hbP : hbm.toLp _ ∈ closure (Set.range (eL (P := P) hK.le T)) := by
    rw [Lp.toLp_coeFn]; exact hb.2.1
  refine ident hK.le hK.mono T hbm hbP hcφ hcφP hηa hηc fun R i => ?_
  set τ := StochCalcHit.hitR η R T with hτdef
  let F : Filtration ℝ≥0 mΩ := ⟨mK, hK.mono, hK.le⟩
  have hτ : ∀ s, MeasurableSet[mK s] {ω | τ ω ≤ s} := fun s =>
    StochCalcHit.hitR_isStopping F (fun u => (hηa u).stronglyMeasurable) hηc R T s
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hητ : ∀ u ω, u < τ ω → |η u ω| ≤ R := fun u ω h => (StochCalcHit.abs_lt_of_lt_hitR h).le
  have hψ1 := memLp_mul_befG hK.le hτ (memLp_efun (P := P) hK.le i)
  have hψ1P := pred_bef hK.le hK.mono T (memLp_efun (P := P) hK.le i) (eE_mem hK.le i) hτ hψ1
  have hψ2 := memLp_mul_etabef hK.le hηa hηc hτ hR hητ (memLp_efun (P := P) hK.le i)
  have hψ2P := pred_etabef hK.le hK.mono T (memLp_efun (P := P) hK.le i) (eE_mem hK.le i)
    hηa hηc hτ hR hητ
  have s1 : ∫ z, b z * (befG τ z.1.toNNReal z.2 * efun i z) ∂(μT P T) =
      ∫ z, a z * (efun i z * befG τ z.1.toNNReal z.2) ∂(μT P T) := by
    have e := hbψ _ hψ1P
    rw [← Lp.toLp_coeFn b hbm, inner_toLp_toLp, ← Lp.toLp_coeFn a (Lp.memLp a),
      inner_toLp_toLp] at e
    rw [← e]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_); simp only; ring
  have s2 : ∫ z, a z * (efun i z * befG τ z.1.toNNReal z.2) ∂(μT P T) =
      -∫ z, c z * (efun i z * (η z.1.toNNReal z.2 * befG τ z.1.toNNReal z.2)) ∂(μT P T) := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hac] with z hz
    rw [hz]; ring
  have s3 := hproj _ hψ2 (predK_sub hF hK hKF T hψ2P)
  have s4 := snd_ce hK T hφ hψ2 hψ2P
  have s5 := hprojφ _ hψ2 hψ2P
  rw [s1, s2, s3, s4, ← s5]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun z => ?_); simp only; ring

theorem Q1coreG {mF mK : ℝ≥0 → MeasurableSpace Ω} (hF : IncrHyp mF W P) (hK : IncrHyp mK W P)
    (hKF : ∀ s, mK s ≤ mF s) (T : ℝ≥0)
    (H1 : ∀ (u : ℝ≥0) (Y : Ω → ℝ), u ≤ T → Measurable[mF u] Y → (∃ C, ∀ ω, |Y ω| ≤ C) →
      condExp (mK T) P Y =ᵐ[P] condExp (mK u) P Y)
    {θ θB : Lp ℝ 2 P} {a : Lp ℝ 2 (μT P T)} (h : Rep hF T θB a)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 (μT P T))
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 (μT P T),
      hψ.toLp ψ ∈ closure (Set.range (eL (P := P) hF.le T)) →
      ∫ z, c z * ψ z ∂(μT P T) = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂(μT P T))
    {η : ℝ≥0 → Ω → ℝ} (hηa : ∀ u, Measurable[mK u] (η u)) (hηc : ∀ ω, Continuous fun v => η v ω)
    (hac : ∀ᵐ z ∂(μT P T), a z = -(η z.1.toNNReal z.2) * c z)
    {Θ : Lp ℝ 2 P} (hΘ : (Θ : Ω → ℝ) =ᵐ[P] condExp (mK T) P θ)
    (hΘB : (Θ : Ω → ℝ) =ᵐ[P] condExp (mK T) P θB) (t : ℝ≥0)
    (hΘt : ∀ Y : Ω → ℝ, Measurable[mK t] Y → ∀ C : ℝ, (∀ ω, |Y ω| ≤ C) →
      ∫ ω, (Θ : Ω → ℝ) ω * Y ω ∂P = 0) :
    Θ = 0 := by
  have hΘ2 : MemLp (fun z : ℝ × Ω => (Θ : Ω → ℝ) z.2) 2 (μT P T) := by
    unfold μT; exact (Lp.memLp Θ).comp_snd _
  obtain ⟨cΘ, hcΘ, hcΘP, hprojΘ⟩ := proj_fun hK.le T hΘ2
  obtain ⟨b, hb, hbη⟩ := KshiftG hF hK hKF T H1 h hc hproj hηa hηc hac hΘ hΘB hcΘ hcΘP hprojΘ
  have hres := memLp_mulind hcΘ 0 t
  have hresP := pred_cell hK.le hK.mono hcΘ hcΘP 0 t
  have h0 : ∫ z, cΘ z * (cΘ z * ind 0 t z.1) ∂(μT P T) = 0 := by
    rw [hprojΘ _ hres hresP]
    have hpt := perp_tail hK.le hK.mono t (Lp.memLp Θ) hΘt hcΘ hcΘP
    rw [← hpt]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    ring
  have hnn : 0 ≤ᵐ[μT P T] fun z => cΘ z * (cΘ z * ind 0 t z.1) :=
    Eventually.of_forall fun z => by
      have : 0 ≤ ind 0 t z.1 := by
        simp only [ind, Set.indicator_apply]; split_ifs <;> norm_num
      have h2 : cΘ z * (cΘ z * ind 0 t z.1) = cΘ z ^ 2 * ind 0 t z.1 := by ring
      show 0 ≤ cΘ z * (cΘ z * ind 0 t z.1)
      rw [h2]
      exact mul_nonneg (sq_nonneg _) this
  have hint : Integrable (fun z => cΘ z * (cΘ z * ind 0 t z.1)) (μT P T) :=
    hcΘ.integrable_mul hres
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0
  have hv : ∀ᵐ z ∂(μT P T), z.1 < (t : ℝ) → b z = 0 := by
    filter_upwards [hz, hbη, ae_fst_Ico (P := P) T] with z hz1 hz2 hz3 hlt
    have hi : ind 0 t z.1 = 1 := by
      simp only [ind, Set.indicator_apply]
      rw [if_pos ⟨by exact_mod_cast hz3.1, hlt⟩]
    have hc0 : cΘ z = 0 := by
      have : cΘ z * (cΘ z * ind 0 t z.1) = 0 := hz1
      rw [hi, mul_one, mul_self_eq_zero] at this
      exact this
    rw [hz2, hc0, mul_zero]
  exact U1 hK T hb hcΘ hcΘP hprojΘ hηa hηc hbη hv

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

-- ===== slice of __current__ (scratch/probe/slice8c/cuts/r_q1.lean.src/__current__.lean): 0/98 top-level decls kept =====

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





end StochCalcK3G

end StochCalcP6


open MeasureTheory ProbabilityTheory in
open scoped NNReal in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} {mF mK : ℝ≥0 → MeasurableSpace Ω}
    (hF1 : Monotone mF) (hF2 : ∀ s, mF s ≤ mΩ) (hF3 : ∀ s, Measurable[mF s] (W s))
    (hF4 : ∀ u v, u ≤ v →
      Indep (mF u) (MeasurableSpace.comap (fun ω => W v ω - W u ω) inferInstance) P)
    (hF5 : ∀ u v, MemLp (fun ω => W v ω - W u ω) 2 P)
    (hF6 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ∂P = 0)
    (hF7 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ^ 2 ∂P = (v : ℝ) - u)
    (hK1 : Monotone mK) (hK2 : ∀ s, mK s ≤ mΩ) (hK3 : ∀ s, Measurable[mK s] (W s))
    (hK4 : ∀ u v, u ≤ v →
      Indep (mK u) (MeasurableSpace.comap (fun ω => W v ω - W u ω) inferInstance) P)
    (hK5 : ∀ u v, MemLp (fun ω => W v ω - W u ω) 2 P)
    (hK6 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ∂P = 0)
    (hK7 : ∀ u v, u ≤ v → ∫ ω, (W v ω - W u ω) ^ 2 ∂P = (v : ℝ) - u)
    (hKF : ∀ s, mK s ≤ mF s) (T : ℝ≥0)
    (μ : Measure (ℝ × Ω)) (hμ : μ = (volume.restrict (Set.Ico (0 : ℝ) T)).prod P)
    (H1 : ∀ (u : ℝ≥0) (Y : Ω → ℝ), u ≤ T → Measurable[mF u] Y → (∃ C, ∀ ω, |Y ω| ≤ C) →
      condExp (mK T) P Y =ᵐ[P] condExp (mK u) P Y)
    {θ θB : Lp ℝ 2 P} {a : Lp ℝ 2 μ}
    (hr1 : θB ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 P | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[mF u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun ω => Y ω * (W v ω - W u ω)) 2 P, g = h.toLp _} : Set (Lp ℝ 2 P)))
    (hr2 : a ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[mF u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)))
    (hr3 : ∀ u v : ℝ≥0, u ≤ v → v ≤ T → ∀ Y : Ω → ℝ, Measurable[mF u] Y →
        (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
        ∫ ω, (θB : Ω → ℝ) ω * (Y ω * (W v ω - W u ω)) ∂P =
          ∫ z, (a : ℝ × Ω → ℝ) z * ((Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) ∂μ)
    {c : ℝ × Ω → ℝ} (hc : MemLp c 2 μ)
    (hproj : ∀ ψ : ℝ × Ω → ℝ, ∀ hψ : MemLp ψ 2 μ,
      hψ.toLp ψ ∈ closure (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ u v : ℝ≥0, u ≤ v ∧ v ≤ T ∧
          ∃ Y : Ω → ℝ, Measurable[mF u] Y ∧ (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) ∧
          ∃ h : MemLp (fun z : ℝ × Ω => (Set.Ico (u : ℝ) v).indicator (fun _ => (1 : ℝ)) z.1 * Y z.2) 2 μ,
            g = h.toLp _} : Set (Lp ℝ 2 μ)) →
      ∫ z, c z * ψ z ∂μ = ∫ z, (θ : Ω → ℝ) z.2 * ψ z ∂μ)
    {η : ℝ≥0 → Ω → ℝ} (hηa : ∀ u, Measurable[mK u] (η u)) (hηc : ∀ ω, Continuous fun v => η v ω)
    (hac : ∀ᵐ z ∂μ, a z = -(η z.1.toNNReal z.2) * c z)
    {Θ : Lp ℝ 2 P} (hΘ : (Θ : Ω → ℝ) =ᵐ[P] condExp (mK T) P θ)
    (hΘB : (Θ : Ω → ℝ) =ᵐ[P] condExp (mK T) P θB) (t : ℝ≥0)
    (hΘt : ∀ Y : Ω → ℝ, Measurable[mK t] Y → ∀ C : ℝ, (∀ ω, |Y ω| ≤ C) →
      ∫ ω, (Θ : Ω → ℝ) ω * Y ω ∂P = 0) :
    Θ = 0 := by
  subst hμ
  have hF : StochCalcP6.StochCalcO3.IncrHyp mF W P := ⟨hF1, hF2, hF3, hF4, hF5, hF6, hF7⟩
  have hK : StochCalcP6.StochCalcO3.IncrHyp mK W P := ⟨hK1, hK2, hK3, hK4, hK5, hK6, hK7⟩
  exact StochCalcP6.StochCalcO3.Q1coreG hF hK hKF T H1
    ((StochCalcP6.StochCalcRU.rep_iff hF T θB a).2 (by unfold StochCalcP6.StochCalcRU.RepU; exact ⟨hr1, hr2, hr3⟩)) hc
    (fun ψ hψ hm => hproj ψ hψ (by rw [StochCalcP6.StochCalcRU.closure_eL] at hm; exact hm)) hηa hηc hac hΘ hΘB t hΘt
