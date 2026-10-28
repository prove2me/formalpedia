-- Prove2me | solution 1 for OAI.DilutedSpinGlass.ConcreteReservoir.scoreError_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T07:59:38.360118+00:00
-- url     : https://prove2.me/submissions/c236aca7-a6c7-40e4-a186-b040d5430f92

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Theorems.Thm_OAI_DilutedSpinGlass_PhysicalRoot_spin_selected_concentration

section
-- module Solutions.OAIQ041_DS.Compat
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PatternComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open scoped Topology BigOperators

namespace DilutedSpinGlass

theorem extractionProbe_pos (j : ℕ) : 0 < extractionProbe j := by
  unfold extractionProbe
  positivity

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundSuperposition
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open Set

lemma extractionProbe_le_quarter (j : ℕ) : extractionProbe j ≤ 1/4 := by
  unfold extractionProbe
  rw [div_le_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+4)]
  have := Nat.cast_nonneg (α := ℝ) j
  linarith

lemma extractionProbe_abs_le_quarter (j : ℕ) : |extractionProbe j| ≤ 1/4 := by
  rw [abs_of_pos (extractionProbe_pos j)]
  exact extractionProbe_le_quarter j

lemma probeLow_pos (j : ℕ) : 0 < probeLow j := pow_pos (extractionProbe_pos j) _
lemma probeLow_lt_high (j : ℕ) : probeLow j < probeHigh j := by
  have := probeLow_pos j
  unfold probeHigh
  linarith
lemma probeHigh_lt_quarter (j : ℕ) : probeHigh j < 1/4 := by
  have hp : probeLow j ≤ (1/4:ℝ)^4 := by
    apply (pow_le_pow_left₀ (extractionProbe_pos j).le (extractionProbe_le_quarter j) (j+4)).trans
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  unfold probeHigh
  nlinarith

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ConcentrationRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open Filter
open scoped Topology

lemma sqrt_scoreScale_div {x : ℝ} (hx : 0 < x) :
    Real.sqrt (x^((3:ℝ)/4))/(x^((3:ℝ)/4)) = x^(-(3:ℝ)/8) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hx.le,← Real.rpow_sub hx]
  congr 1
  norm_num

lemma sqrt_div_scoreMargin_scale {x : ℝ} (hx : 0 < x) :
    Real.sqrt x/(x^(-(1:ℝ)/8)*x^((3:ℝ)/4)) = x^(-(1:ℝ)/8) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_add hx,← Real.rpow_sub hx]
  congr 1
  norm_num

/-- Exact normalization of the four-term concentration envelope. -/
theorem score_envelope_normalize {x K T ell w : ℝ} (hx : 0 < x) (hK : 0 ≤ K)
    (hT : 0 ≤ T) (hell : 0 < ell) (hw : 0 < w) :
    (Real.sqrt (T*x^((3:ℝ)/4))/ell+
      4*Real.sqrt (K*x)/(x^(-(1:ℝ)/8))+
      12*(x^(-(1:ℝ)/8))*(x^((3:ℝ)/4))/ell+
      Real.sqrt (x^((3:ℝ)/4)))/(w*x^((3:ℝ)/4)) =
    ((Real.sqrt T/ell+1)/w)*x^(-(3:ℝ)/8)+
      ((4*Real.sqrt K+12/ell)/w)*x^(-(1:ℝ)/8) := by
  have hs : x^((3:ℝ)/4) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  have hr : x^(-(1:ℝ)/8) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  rw [Real.sqrt_mul hT,Real.sqrt_mul hK]
  have h1 := sqrt_scoreScale_div hx
  have h2 := sqrt_div_scoreMargin_scale hx
  field_simp at h1 h2 ⊢
  rw [h1,h2]
  ring

/-- Monotonicity version used with the physical variance envelope. -/
theorem score_envelope_bound {x K T ell w v R : ℝ} (hx : 0 < x) (hK : 0 ≤ K)
    (hT : 0 ≤ T) (hell : 0 < ell) (hw : 0 < w) (hR : R ≤ K*x)
    (hv : v ≤ Real.sqrt (T*x^((3:ℝ)/4))/ell+
      4*Real.sqrt R/(x^(-(1:ℝ)/8))+
      12*(x^(-(1:ℝ)/8))*(x^((3:ℝ)/4))/ell+Real.sqrt (x^((3:ℝ)/4))) :
    v/(w*x^((3:ℝ)/4)) ≤
      ((Real.sqrt T/ell+1)/w)*x^(-(3:ℝ)/8)+
      ((4*Real.sqrt K+12/ell)/w)*x^(-(1:ℝ)/8) := by
  rw [← score_envelope_normalize hx hK hT hell hw]
  apply div_le_div_of_nonneg_right _ (mul_nonneg hw.le (Real.rpow_nonneg hx.le _))
  exact hv.trans (by gcongr)

lemma scoreScale_le {N : ℕ} (hN : 1 ≤ N) : scoreScale N ≤ (N:ℝ) := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  simpa only [scoreScale,Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (3:ℝ)/4 ≤ 1)

/-- The variance bound required in normalization holds for any reservoir
with interaction rate at most linear in N, and for s_N=N^(3/4). -/
lemma physical_score_variance_linear {N : ℕ} (hN : 1 ≤ N) {r C H R : ℝ}
    (hr : r ≤ R*N) :
    3*C^2*r+4*scoreScale N+2*H^2*N ≤ (3*C^2*R+4+2*H^2)*N := by
  have hh := mul_le_mul_of_nonneg_left hr (by positivity : (0:ℝ) ≤ 3*C^2)
  have hs := scoreScale_le hN
  nlinarith

/-- Both prescribed normalized score rates vanish, including the thermal
term; the constants may depend on the fixed type and depth. -/
theorem tendsto_score_rate (A B : ℝ) :
    Tendsto (fun N : ℕ => A*(N:ℝ)^(-(3:ℝ)/8)+B*(N:ℝ)^(-(1:ℝ)/8))
      atTop (𝓝 0) := by
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 3/8)).comp tendsto_natCast_atTop_atTop
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop
  convert (h1.const_mul A).add (h2.const_mul B) using 1 <;> norm_num [neg_div]

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)

theorem expect_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : P.expect f ≤ P.expect g := by
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x))

variable {n : ℕ}

theorem abs_expect_le {f : Ω → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    |P.expect f| ≤ B := by
  apply abs_le.mpr
  constructor
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).1)
    simpa only [expect_const] using h
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).2)
    simpa only [expect_const] using h

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

theorem poissonWeight_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℕ) = (r : ℝ) * poissonWeight r n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Poisson add-one (the count part of pert:palm), including zero rate. -/
theorem poisson_add_one (r : ℝ≥0) (f : ℕ → ℝ)
    (hf : Integrable (fun n => f (n+1)) (poissonMeasure r)) :
    (∫ n : ℕ, (n : ℝ) * f n ∂poissonMeasure r) =
      (r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r := by
  have hs := (hasSum_integral_poissonMeasure hf).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ) * f (n+1))
      ((r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r) := by
    simp_rw [poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ) * f n) ht
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at ht'
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul, ← mul_assoc, poissonWeight] using ht'.tsum_eq

/-- Integrability of the count is proved from the same add-one recurrence. -/
theorem poisson_integrable_count (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)) r := by
    simp_rw [poissonWeight_succ_mul]
    unfold poissonWeight
    simpa only [mul_one] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ)) ht
  simp only [Nat.cast_zero, mul_zero, zero_add] at ht'
  simpa only [Real.norm_natCast, poissonWeight] using ht'.summable

@[simp] theorem poisson_mean (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  simpa using poisson_add_one r (fun _ => 1) (integrable_const 1)

theorem poisson_integrable_linear (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*n) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

theorem poisson_integrable_count_sq (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)^2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hnext : Integrable (fun n : ℕ => ((n+1 : ℕ) : ℝ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 1) (B := 1)
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    exact le_of_eq (add_comm _ _)
  have hs := (hasSum_integral_poissonMeasure hnext).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : Summable (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)^2) := by
    simp_rw [pow_two, ← mul_assoc, poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs.summable
  have ht' := Summable.comp_nat_add (f := fun n => poissonWeight r n * (n : ℝ)^2) (k := 1) ht
  simpa only [Real.norm_eq_abs, abs_sq, poissonWeight] using ht'

@[simp] theorem poisson_second_moment (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2 + r := by
  have hi : Integrable (fun n : ℕ => ((n+1 : ℕ) : ℝ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 1) (B := 1)
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    exact le_of_eq (add_comm _ _)
  have h := poisson_add_one r (fun n => (n : ℝ)) hi
  simp only [← pow_two, Nat.cast_add, Nat.cast_one] at h
  rw [integral_add (poisson_integrable_count r) (integrable_const 1), poisson_mean,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- A quadratic envelope suffices; no exponential moment is used. -/
theorem poisson_integrable_quadratic (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*(n : ℝ)^2) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count_sq r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_Perturbations
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
theorem perturb_factor_lower {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (q : Fin n) (y : FinitePath Ω L) :
    (1:ℝ)/2 ≤ 1+t*D q y+u*E q y := by
  have ht' := mul_le_mul_of_nonneg_left (hD q y) (abs_nonneg t)
  have hu' := mul_le_mul_of_nonneg_left (hE q y) (abs_nonneg u)
  rw [← abs_mul, mul_one] at ht' hu'
  linarith [(abs_le.mp (ht'.trans ht)).1, (abs_le.mp (hu'.trans hu)).1]

omit [Fintype Ω] in
theorem perturb_fraction_bound {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (q : Fin n) (y : FinitePath Ω L) :
    |E q y / (1+t*D q y+u*E q y)| ≤ 2 := by
  have hb := perturb_factor_lower D E hD hE ht hu q y
  have hp : 0 < 1+t*D q y+u*E q y := by linarith
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
  linarith [hE q y]

omit [Fintype Ω] in
theorem perturbScore_bound {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (y : FinitePath Ω L) :
    |perturbScore D E t u y| ≤ 2*n := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ q, |E q y / (1+t*D q y+u*E q y)|) ≤ ∑ _q : Fin n, (2:ℝ) :=
      Finset.sum_le_sum (fun q _ => perturb_fraction_bound D E hD hE ht hu q y)
    _ = _ := by simp [mul_comm]

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_path_expect (L : ℕ) (T : KernelTower Ω L) (m : Fin L → ℝ)
    {f g : X → FinitePath Ω L → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y))
    (hg : ∀ y, Measurable (fun x => g x y)) :
    Measurable (fun x => (law L (tilt L T m (f x))).expect (g x)) := by
  induction L with
  | zero => simpa only [law_zero_expect] using hg ()
  | succ L ih =>
    simp_rw [law_succ_expect (Ω := Ω) L]
    exact T.1.measurable_tilt_expect (m 0)
      (fun a => measurable_backwardLog L (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)))
      (fun a => ih (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)) (fun b => hg (a,b)))

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

omit [Fintype Ω] in
theorem measurable_perturbLog {L n : ℕ}
    {base : X → FinitePath Ω L → ℝ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hbase : ∀ y, Measurable (fun x => base x y))
    (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u)
    (y : FinitePath Ω L) :
    Measurable (fun x => perturbLog (base x) (D x) (E x) (t x) (u x) y) := by
  apply (hbase y).add
  apply Finset.measurable_sum
  intro q _
  exact ((measurable_const.add (ht.mul (hD q y))).add (hu.mul (hE q y))).log

omit [Fintype Ω] in
theorem measurable_perturbScore {L n : ℕ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u)
    (y : FinitePath Ω L) :
    Measurable (fun x => perturbScore (D x) (E x) (t x) (u x) y) := by
  apply Finset.measurable_sum
  intro q _
  exact (hE q y).div ((measurable_const.add (ht.mul (hD q y))).add (hu.mul (hE q y)))

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MixtureMeasures
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

variable {I : Type*} {X : I → Type*} [MeasurableSpace I]
  [∀ i, MeasurableSpace (X i)]

omit [MeasurableSpace I] in
theorem measurable_sigmaUncurry {Y : Type*} [MeasurableSpace Y] {f : (i : I) → X i → Y}
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x : Sigma X => f x.1 x.2) := by
  rw [measurable_iff_comap_le]
  apply le_iInf
  intro i
  rw [← MeasurableSpace.comap_le_iff_le_map]
  rw [MeasurableSpace.comap_comp]
  exact (hf i).comap_le

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
variable {I : Type*} {X : I → Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    [∀ i, MeasurableSpace (X i)]
    (μ : Measure I) (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]

/-- Sufficient integrability on the genuine disjoint-union root law. -/
theorem familyLaw_integrable_bound (f : (i : I) → X i → ℝ)
    (hf : ∀ i, Measurable (f i)) {B : I → ℝ} (hB : Integrable B μ)
    (hb : ∀ i x, |f i x| ≤ B i) :
    Integrable (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν) := by
  let F : Sigma X → ℝ := fun z => f z.1 z.2
  have hm : Measurable F := measurable_sigmaUncurry hf
  have hi (i : I) : Integrable (f i) (ν i) :=
    Integrable.of_bound (hf i).aestronglyMeasurable (B i) (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hb i x))
  have hi' (i : I) : Integrable F (familyKernel ν i) := by
    change Integrable F ((ν i).map (Sigma.mk i))
    exact (integrable_map_measure hm.aestronglyMeasurable (measurable_sigmaMk i).aemeasurable).mpr (hi i)
  apply (Measure.integrable_comp_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi', ?_⟩
  apply hB.mono' Measurable.of_discrete.aestronglyMeasurable
  apply ae_of_all
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  change (∫ z, ‖F z‖ ∂(ν i).map (Sigma.mk i)) ≤ B i
  rw [integral_map (measurable_sigmaMk i).aemeasurable hm.norm.aestronglyMeasurable]
  have hh := integral_mono (hi i).norm (integrable_const (B i))
    (fun x => by simpa only [Real.norm_eq_abs] using hb i x)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

omit [∀ i, IsProbabilityMeasure (ν i)] in
 
theorem integral_familyLaw (f : (i : I) → X i → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hi : Integrable (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν)) :
    (∫ z : Sigma X, f z.1 z.2 ∂familyLaw μ ν) = ∫ i, ∫ x, f i x ∂ν i ∂μ := by
  unfold familyLaw at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  change (∫ i, ∫ z : Sigma X, f z.1 z.2 ∂(ν i).map (Sigma.mk i) ∂μ) = _
  apply integral_congr_ae
  apply ae_of_all
  intro i
  exact integral_map (measurable_sigmaMk i).aemeasurable
    (measurable_sigmaUncurry hf).aestronglyMeasurable

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)

theorem familyPoisson_count_integrable :
    Integrable (fun z : Sigma X => (z.1 : ℝ)) (familyLaw (poissonMeasure r) ν) := by
  apply familyLaw_integrable_bound (poissonMeasure r) ν (fun n _ => (n : ℝ)) (fun _ => measurable_const)
    (poisson_integrable_count r)
  intro n _
  simp

theorem familyPoisson_count_mean :
    (∫ z : Sigma X, (z.1 : ℝ) ∂familyLaw (poissonMeasure r) ν) = (r : ℝ) := by
  rw [integral_familyLaw (poissonMeasure r) ν (fun n _ => (n : ℝ)) (fun _ => measurable_const)
    (familyPoisson_count_integrable ν r)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,poisson_mean]

theorem familyPoisson_memLp_linear {f : (n : ℕ) → X n → ℝ}
    (hf : ∀ n, Measurable (f n)) {A B : ℝ} (hb : ∀ n x, |f n x| ≤ A+B*n) :
    MemLp (fun z : Sigma X => f z.1 z.2) 2 (familyLaw (poissonMeasure r) ν) := by
  apply (memLp_two_iff_integrable_sq (measurable_sigmaUncurry hf).aestronglyMeasurable).mpr
  apply familyLaw_integrable_bound (poissonMeasure r) ν (fun n x => (f n x)^2) (fun n => (hf n).pow_const 2)
    (B := fun n => 2*A^2+2*B^2*(n : ℝ)^2)
  · apply poisson_integrable_quadratic r (A := 2*A^2) (B := 2*B^2)
    intro n
    rw [abs_of_nonneg (by positivity)]
  · intro n x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hsq : (f n x)^2 ≤ (A+B*n)^2 := by
      exact sq_le_sq' (abs_le.mp (hb n x)).1 (abs_le.mp (hb n x)).2
    nlinarith [sq_nonneg (A-B*n)]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set

namespace DilutedSpinGlass.KernelTower
open _root_.MeasureTheory ProbabilityTheory
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_correctedPerturbScore {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    {base : X → FinitePath Ω L → ℝ} {D E : X → Fin n → FinitePath Ω L → ℝ}
    {t u : X → ℝ} (hbase : ∀ y, Measurable (fun x => base x y))
    (hD : ∀ q y, Measurable (fun x => D x q y))
    (hE : ∀ q y, Measurable (fun x => E x q y)) (ht : Measurable t) (hu : Measurable u) :
    Measurable (fun x => correctedPerturbScore T m (base x) (D x) (E x) (t x) (u x)) := by
  apply (measurable_path_expect L T m (measurable_perturbLog hbase hD hE ht hu)
    (measurable_perturbScore hD hE ht hu)).add
  exact hu.const_mul _

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)

theorem familyPoisson_count_memLp :
    MemLp (fun z : Sigma X => (z.1 : ℝ)) 2 (familyLaw (poissonMeasure r) ν) := by
  apply familyPoisson_memLp_linear ν r (fun _ => measurable_const) (A := 0) (B := 1)
  intro n x
  simp

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_JointRootParam
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {X I Y U : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] [MeasurableSpace U] {M : ℕ}

/-- Joint measurability through both random counts, with an external parameter. -/
theorem measurable_packRoot_param
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → U → ℝ}
    (hF : ∀ k n, Measurable (fun z : ((RootPath Y M × RootPath X k) × RootPath I n) × U => F z.1.1.1 k z.1.1.2 n z.1.2 z.2)) :
    Measurable (fun z : FullRootState Y X I M × U => packRoot (fun h k x n y => F h k x n y z.2) z.1) := by
  have hn (k : ℕ) : Measurable (fun z : ((RootPath Y M × RootPath X k) × U) × Sigma (RootPath I) =>
      F z.1.1.1 k z.1.1.2 z.2.1 z.2.2 z.1.2) :=
    measurable_prodSigma (f := fun (z : (RootPath Y M × RootPath X k) × U) n y => F z.1.1 k z.1.2 n y z.2)
      (fun n => (hF k n).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  have hk : Measurable (fun z : ((RootPath Y M × Sigma (RootPath I)) × U) × Sigma (RootPath X) =>
      F z.1.1.1 z.2.1 z.2.2 z.1.1.2.1 z.1.1.2.2 z.1.2) :=
    measurable_prodSigma (f := fun (z : (RootPath Y M × Sigma (RootPath I)) × U) k x => F z.1.1 k x z.1.2.1 z.1.2.2 z.2)
      (fun k => (hn k).comp (((measurable_fst.fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd).prodMk measurable_fst.fst.snd))
  exact hk.comp (((measurable_fst.fst.prodMk measurable_fst.snd.snd).prodMk measurable_snd).prodMk measurable_fst.snd.fst)

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

omit [MeasurableSpace U] in
theorem fullRoot_count_memLp :
    MemLp (fun z : FullRootState Y X I M => (z.2.2.1 : ℝ)) 2 (fullRootLaw ξ μ ν r s) := by
  exact ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)

omit [MeasurableSpace U] in
theorem fullRoot_count_mean :
    (∫ z : FullRootState Y X I M, (z.2.2.1 : ℝ) ∂fullRootLaw ξ μ ν r s) = s := by
  change (∫ z, (fun w : Sigma (RootPath X) × Sigma (RootPath I) => (w.2.1:ℝ)) z.2
    ∂(rootLaw M ξ).prod ((compoundRootLaw μ r).prod (compoundRootLaw ν s))) = _
  rw [integral_fun_snd (fun w : Sigma (RootPath X) × Sigma (RootPath I) => (w.2.1:ℝ)),
    integral_fun_snd (fun w : Sigma (RootPath I) => (w.1:ℝ))]
  simp only [probReal_univ,one_smul]
  exact familyPoisson_count_mean (fun n => rootLaw n (fun _ => ν)) s

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountedSteps
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} {A : I → Type} {L n : ℕ}

theorem selectedCoefficient_bound (roots : Fin n → I) (sel : I → Bool)
    (D : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (q : Fin n) (y : FinitePath (Ω × Row (A := A) roots) L) :
    |selectedCoefficient roots sel D q y| ≤ 1 := by
  unfold selectedCoefficient
  split
  · exact hD _ _ _
  · norm_num

/-- Every unselected term remains in the same log weight and the same finite
mark prior. This is an identity, not a distributional truncation. -/
theorem selected_perturbLog_eq (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    KernelTower.perturbLog (otherLog base roots sel fixed)
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u =
      logWeight base roots (selectedFactor sel fixed D E t u) := by
  funext y
  unfold KernelTower.perturbLog otherLog logWeight
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  cases h : sel (roots q) <;> simp [selectedFactor,selectedCoefficient,h]

variable [Fintype Ω] [∀ i, Fintype (A i)]

theorem corrected_score_eq (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    KernelTower.correctedPerturbScore (tower roots L T Q) m (otherLog base roots sel fixed)
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u =
      selectedScore T Q m base roots sel fixed D E t u+4*n*u := by
  rw [KernelTower.correctedPerturbScore,selected_perturbLog_eq]
  rfl

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SelectedRegularity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem selectedFactor_log_bound (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) :
    |Real.log (selectedFactor sel fixed D E t u i x y)| ≤ 1 := by
  unfold selectedFactor
  split
  · have ht' := mul_le_mul_of_nonneg_left (hD i x y) (abs_nonneg t)
    have hu' := mul_le_mul_of_nonneg_left (hE i x y) (abs_nonneg u)
    rw [← abs_mul,mul_one] at ht' hu'
    have hlo : (1:ℝ)/2 ≤ 1+t*D i x y+u*E i x y := by
      linarith [(abs_le.mp (ht'.trans ht)).1,(abs_le.mp (hu'.trans hu)).1]
    have hhi : 1+t*D i x y+u*E i x y ≤ (3:ℝ)/2 := by
      linarith [(abs_le.mp (ht'.trans ht)).2,(abs_le.mp (hu'.trans hu)).2]
    have hpos : 0 < 1+t*D i x y+u*E i x y := by linarith
    have hlog := Real.log_le_sub_one_of_pos hpos
    have hinv : (1+t*D i x y+u*E i x y)⁻¹ ≤ 2 := by
      apply (inv_le_iff_one_le_mul₀ hpos).mpr
      linarith
    have hlogInv := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at hlogInv
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · exact hf i x y

/-- Joint parameter regularity of the fully tilted selected score at fixed
labels. The countable random labels are reintroduced below. -/
theorem measurable_selected_correctedScore {X : Type} [MeasurableSpace X]
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y)) (t : ℝ) :
    Measurable (fun z : X × ℝ => selectedScore T Q m (base z.1) roots sel fixed D E t z.2+4*n*z.2) := by
  have hh := KernelTower.measurable_correctedPerturbScore (tower roots L T Q) m
    (base := fun z : X × ℝ => otherLog (base z.1) roots sel fixed)
    (D := fun _ : X × ℝ => selectedCoefficient roots sel D)
    (E := fun _ : X × ℝ => selectedCoefficient roots sel E)
    (t := fun _ : X × ℝ => t) (u := fun z => z.2)
    (fun y => ((hb (physical roots L y)).comp measurable_fst).add measurable_const)
    (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const measurable_snd
  simpa only [corrected_score_eq] using hh

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedRegularity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

theorem measurable_fullSelectedScore
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedScore T Q m base sel fixed D E t z.1 z.2) := by
  apply measurable_packRoot_param (F := fun h k x n y u =>
    selectedScore T Q m (base h k x) (rootArray n y) sel fixed D E t u+4*n*u)
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × ℝ) × RootPath I n =>
      selectedScore T Q m (base z.1.1.1 k z.1.1.2) (rootArray n z.2) sel fixed D E t z.1.2+4*n*z.1.2) := by
    apply measurable_from_prod_countable_left
    intro roots
    exact measurable_selected_correctedScore T Q m
      (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n roots) sel fixed D E (hb k) t
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal

lemma clipReal_bound {C : ℝ} (hC : 0 ≤ C) (x : ℝ) : |clipReal C x| ≤ C := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedRawConcentration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedRawScore_eq
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u : ℝ) :
    fullSelectedRawScore T Q m base sel fixed D E t z u =
    fullSelectedScore T Q m base sel fixed D E t z u-(4*u)*(z.2.2.1:ℝ) := by
  unfold fullSelectedRawScore fullSelectedScore packRoot
  ring

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedError
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedDeviation_nonneg (z : FullRootState Y X I M) (u center : ℝ) :
    0 ≤ fullSelectedDeviation T Q m base sel fixed D E t z u center :=
  FiniteLaw.expect_nonneg _ (fun _ => abs_nonneg _)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedDeviation_bound
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) (center : ℝ) :
    fullSelectedDeviation T Q m base sel fixed D E t z u center ≤ 2*(z.2.2.1:ℝ)+|center| := by
  apply (FiniteLaw.expect_mono _ (fun y => (abs_sub _ _).trans
    (add_le_add (KernelTower.perturbScore_bound _ _
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht hu y) le_rfl))).trans_eq
  exact FiniteLaw.expect_const _ _

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedRawScore_bound
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (z : FullRootState Y X I M) :
    |fullSelectedRawScore T Q m base sel fixed D E t z u| ≤ 2*(z.2.2.1:ℝ) := by
  apply FiniteLaw.abs_expect_le
  exact KernelTower.perturbScore_bound _ _ (selectedCoefficient_bound _ sel D hD)
    (selectedCoefficient_bound _ sel E hE) ht hu

theorem measurable_fullSelectedRawScore
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedRawScore T Q m base sel fixed D E t z.1 z.2) := by
  simp_rw [fullSelectedRawScore_eq]
  exact (measurable_fullSelectedScore T Q m base sel fixed D E t hb).sub
    ((measurable_const.mul measurable_snd).mul ((measurable_sigmaUncurry (f := fun n (_ : RootPath I n) => (n:ℝ)) (fun _ => measurable_const)).comp measurable_fst.snd.snd))

theorem measurable_fullSelectedDeviation
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {center : ℝ → ℝ} (hc : Measurable center) :
    Measurable (fun z : FullRootState Y X I M × ℝ => fullSelectedDeviation T Q m base sel fixed D E t z.1 z.2 (center z.2)) := by
  apply measurable_packRoot_param (F := fun h k x n y u =>
    fullSelectedDeviation T Q m base sel fixed D E t (h,⟨k,x⟩,⟨n,y⟩) u (center u))
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × ℝ) × RootPath I n =>
      fullSelectedDeviation T Q m base sel fixed D E t (z.1.1.1,⟨k,z.1.1.2⟩,⟨n,z.2⟩) z.1.2 (center z.1.2)) := by
    apply measurable_from_prod_countable_left
    intro y
    dsimp only [fullSelectedDeviation]
    apply KernelTower.measurable_path_expect L (tower (rootArray n y) L T Q) m
      (f := fun z : (RootPath Y M × RootPath X k) × ℝ =>
        KernelTower.perturbLog (otherLog (base z.1.1 k z.1.2) (rootArray n y) sel fixed)
          (selectedCoefficient (rootArray n y) sel D) (selectedCoefficient (rootArray n y) sel E) t z.2)
      (g := fun z : (RootPath Y M × RootPath X k) × ℝ => fun w =>
        |KernelTower.perturbScore (selectedCoefficient (rootArray n y) sel D)
          (selectedCoefficient (rootArray n y) sel E) t z.2 w-center z.2|)
    · apply KernelTower.measurable_perturbLog
      · intro w
        exact ((hb k (physical (rootArray n y) L w)).comp measurable_fst).add measurable_const
      · exact fun _ _ => measurable_const
      · exact fun _ _ => measurable_const
      · exact measurable_const
      · exact measurable_snd
    · intro w
      exact ((KernelTower.measurable_perturbScore
        (D := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n y) sel D)
        (E := fun _ : (RootPath Y M × RootPath X k) × ℝ => selectedCoefficient (rootArray n y) sel E)
        (t := fun _ : (RootPath Y M × RootPath X k) × ℝ => t) (u := fun z => z.2)
        (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const measurable_snd w).sub
          (hc.comp measurable_snd)).abs
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GlobalSelectedError
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ)

omit [Countable I] [MeasurableSingletonClass I] [∀ index, IsProbabilityMeasure (ξ index)]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem fullSelectedError_nonneg (u : ℝ) :
    0 ≤ fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u :=
  integral_nonneg (fun z => fullSelectedDeviation_nonneg T Q m base sel fixed D E t z u _)

theorem fullSelectedError_bound
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u ≤ 4*(s:ℝ) := by
  let P := fullRootLaw ξ μ ν r s
  let center := ∫ w, fullSelectedRawScore T Q m base sel fixed D E t w u ∂P
  have hci : Integrable (fun z : FullRootState Y X I M => (z.2.2.1:ℝ)) P :=
    (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hiS : Integrable (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u) P := by
    apply (hci.const_mul 2).mono'
      ((measurable_fullSelectedRawScore T Q m base sel fixed D E t hb).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using fullSelectedRawScore_bound T Q m base sel fixed D E t hD hE ht hu z)
  have hav : |center| ≤ 2*(s:ℝ) := by
    have hh := abs_integral_le_integral_abs.trans (integral_mono hiS.abs (hci.const_mul 2)
      (fun z => fullSelectedRawScore_bound T Q m base sel fixed D E t hD hE ht hu z))
    simpa only [P,integral_const_mul,fullRoot_count_mean] using hh
  have hiD : Integrable (fun z => fullSelectedDeviation T Q m base sel fixed D E t z u center) P := by
    apply ((hci.const_mul 2).add (integrable_const |center|)).mono'
      ((measurable_fullSelectedDeviation T Q m base sel fixed D E t hb measurable_const).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.comp_apply,id_eq,Pi.add_apply,Pi.sub_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedDeviation_nonneg T Q m base sel fixed D E t z u center)]
      exact fullSelectedDeviation_bound T Q m base sel fixed D E t hD hE ht hu z center)
  have hh := integral_mono hiD ((hci.const_mul 2).add (integrable_const |center|))
    (fun z => fullSelectedDeviation_bound T Q m base sel fixed D E t hD hE ht hu z center)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hci.const_mul 2) (integrable_const |center|), integral_const_mul] at hh
  simp only [P,fullRoot_count_mean,integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
  change fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u ≤ _
  change fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u ≤ _ at hh
  linarith

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ParameterProduct
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

/-- Refreshing a single coordinate by an independent sample preserves the
entire countable parameter law. The other coordinates are not truncated. -/
theorem measurePreserving_parameter_refresh {ι : Type*} [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun z : (ι → ℝ) × ℝ => Function.update z.1 i z.2)
      ((Measure.infinitePi μ).prod (μ i)) (Measure.infinitePi μ) := by
  have hm : Measurable (fun z : (ι → ℝ) × ℝ => Function.update z.1 i z.2) := by
    apply Measurable.of_eval
    intro j
    by_cases h : j = i
    · subst j
      simpa using (measurable_snd : Measurable (fun z : (ι → ℝ) × ℝ => z.2))
    · simp only [Function.update_of_ne h]
      fun_prop
  refine ⟨hm,Measure.eq_infinitePi μ ?_⟩
  intro s t ht
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet (fun j _ => ht j))]
  have he : (fun z : (ι → ℝ) × ℝ => Function.update z.1 i z.2) ⁻¹' ((s : Set ι).pi t) =
      ((s.erase i : Set ι).pi t) ×ˢ (if i ∈ s then t i else Set.univ) := by
    ext z
    simp only [mem_preimage,mem_prod,mem_pi,Finset.mem_coe,Finset.mem_erase]
    constructor
    · intro hz
      constructor
      · intro j hj
        simpa [Function.update_of_ne hj.1] using hz j hj.2
      · split_ifs with hi
        · simpa using hz i hi
        · trivial
    · rintro ⟨hz,hi⟩ j hj
      by_cases h : j = i
      · subst j
        simpa [hj] using hi
      · simpa [Function.update_of_ne h] using hz j ⟨h,hj⟩
  rw [he,Measure.prod_prod,Measure.infinitePi_pi μ (fun j _ => ht j)]
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi]
    exact Finset.prod_erase_mul _ _ hi
  · simp [hi]

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set
open scoped ENNReal


lemma intervalParameterLaw_probability {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (intervalParameterLaw a b) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

lemma integral_intervalParameterLaw {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) :
    (∫ u, f u ∂intervalParameterLaw a b) = (∫ u in a..b, f u)/(b-a) := by
  rw [intervalParameterLaw,ProbabilityTheory.cond,integral_smul_measure,Real.volume_Icc,
    ENNReal.toReal_inv,ENNReal.toReal_ofReal (sub_pos.mpr hab).le,
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab.le]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- A complete-parameter average is the independent refresh average. -/
lemma integral_parameter_refresh {ι : Type*} [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (i : ι)
    (f : (ι → ℝ) → ℝ) (hf : Measurable f) (hi : Integrable f (Measure.infinitePi μ)) :
    (∫ z, f z ∂Measure.infinitePi μ) =
      ∫ z, ∫ u, f (Function.update z i u) ∂μ i ∂Measure.infinitePi μ := by
  let H := measurePreserving_parameter_refresh μ i
  have hcomp : Integrable (fun z : (ι → ℝ) × ℝ => f (Function.update z.1 i z.2))
      ((Measure.infinitePi μ).prod (μ i)) :=
    (H.integrable_comp hf.aestronglyMeasurable).mpr hi
  rw [← integral_prod _ hcomp]
  calc
    _ = ∫ y, f y ∂Measure.map (fun z : (ι → ℝ) × ℝ => Function.update z.1 i z.2)
        ((Measure.infinitePi μ).prod (μ i)) := by rw [H.map_eq]
    _ = _ := integral_map H.measurable.aemeasurable hf.aestronglyMeasurable

/-- Uniform interval estimates with every other coordinate fixed imply the
same estimate under the literal infinite product parameter law. -/
lemma parameter_average_le {ι : Type*} [DecidableEq ι]
    (a b : ι → ℝ) (hab : ∀ i, a i < b i) (i : ι)
    (f : (ι → ℝ) → ℝ) (hf : Measurable f)
    (hi : Integrable f (Measure.infinitePi (fun i => intervalParameterLaw (a i) (b i))))
    {B : ℝ} (hB : ∀ z, (∫ u in a i..b i, f (Function.update z i u))/(b i-a i) ≤ B) :
    (∫ z, f z ∂Measure.infinitePi (fun i => intervalParameterLaw (a i) (b i))) ≤ B := by
  let μ := fun i => intervalParameterLaw (a i) (b i)
  let (i : ι) : IsProbabilityMeasure (μ i) := intervalParameterLaw_probability (hab i)
  rw [integral_parameter_refresh μ i f hf hi]
  have hcomp := ((measurePreserving_parameter_refresh μ i).integrable_comp
    hf.aestronglyMeasurable).mpr hi
  have hm := integral_mono hcomp.integral_prod_left (integrable_const B) (fun z => by
    simpa only [μ,integral_intervalParameterLaw (hab i),Function.comp_apply] using hB z)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,Function.comp_apply] using hm

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ParameterScoreMeasurable
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y U : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U] {L M : ℕ}

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
lemma measurable_otherLog_family (base : U → FinitePath Ω L → ℝ)
    (hb : ∀ y, Measurable (fun u => base u y)) {n : ℕ} (roots : Fin n → I)
    (sel : I → Bool) (fixed : U → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hf : ∀ i x y, Measurable (fun u => fixed u i x y))
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    Measurable (fun u => otherLog (base u) roots sel (fixed u) y) := by
  apply (hb _).add
  apply Finset.measurable_sum
  intro j _
  by_cases h : sel (roots j) = true
  · simp only [h,ite_true]
    exact measurable_const
  · simp only [h]
    exact (hf _ _ _).log

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_selectedScore_family
    (base : U → FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (sel : I → Bool) (fixed : U → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (t : ℝ) (u : U → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y))
    (hf : ∀ i x y, Measurable (fun z => fixed z i x y)) (hu : Measurable u) :
    Measurable (fun z => selectedScore T Q m (base z) roots sel (fixed z) D E t (u z)) := by
  have hh := KernelTower.measurable_correctedPerturbScore (tower roots L T Q) m
    (base := fun z : U => otherLog (base z) roots sel (fixed z))
    (D := fun _ : U => selectedCoefficient roots sel D)
    (E := fun _ : U => selectedCoefficient roots sel E)
    (t := fun _ : U => t) (u := u)
    (measurable_otherLog_family base hb roots sel fixed hf)
    (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const hu
  have hh' := hh.sub ((measurable_const : Measurable (fun _ : U => (4:ℝ)*n)).mul hu)
  convert hh' using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Pi.sub_apply,Pi.mul_apply,corrected_score_eq,add_sub_cancel_right]

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma measurable_selectedDeviation_family
    (base : U → FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (sel : I → Bool) (fixed : U → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (t : ℝ) (u center : U → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y))
    (hf : ∀ i x y, Measurable (fun z => fixed z i x y)) (hu : Measurable u) (hc : Measurable center) :
    Measurable (fun z =>
      (KernelTower.law L (KernelTower.tilt L (tower roots L T Q) m
        (KernelTower.perturbLog (otherLog (base z) roots sel (fixed z))
          (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t (u z)))).expect
            (fun w => |KernelTower.perturbScore (selectedCoefficient roots sel D)
              (selectedCoefficient roots sel E) t (u z) w-center z|)) := by
  apply KernelTower.measurable_path_expect L (tower roots L T Q) m
    (f := fun z : U => KernelTower.perturbLog (otherLog (base z) roots sel (fixed z))
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t (u z))
    (g := fun z : U => fun w => |KernelTower.perturbScore (selectedCoefficient roots sel D)
      (selectedCoefficient roots sel E) t (u z) w-center z|)
  · exact KernelTower.measurable_perturbLog (measurable_otherLog_family base hb roots sel fixed hf)
      (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const hu
  · intro w
    exact ((KernelTower.measurable_perturbScore
      (D := fun _ : U => selectedCoefficient roots sel D)
      (E := fun _ : U => selectedCoefficient roots sel E)
      (t := fun _ : U => t) (u := u)
      (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const hu w).sub hc).abs

variable
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed : U → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (t : ℝ)
    (u : U → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hf : ∀ i x y, Measurable (fun z => fixed z i x y)) (hu : Measurable u)
include hb hf hu

lemma measurable_fullSelectedRawScore_family :
    Measurable (fun z : FullRootState Y X I M × U =>
      fullSelectedRawScore T Q m base sel (fixed z.2) D E t z.1 (u z.2)) := by
  unfold fullSelectedRawScore
  apply measurable_packRoot_param (F := fun h k x n y v =>
    selectedScore T Q m (base h k x) (rootArray n y) sel (fixed v) D E t (u v))
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × U) × RootPath I n =>
      selectedScore T Q m (base z.1.1.1 k z.1.1.2) (rootArray n z.2) sel (fixed z.1.2) D E t (u z.1.2)) := by
    apply measurable_from_prod_countable_left
    intro y
    exact measurable_selectedScore_family T Q m
      (fun z : (RootPath Y M × RootPath X k) × U => base z.1.1 k z.1.2)
      (rootArray n y) sel (fun z => fixed z.2) D E t (fun z => u z.2)
      (fun w => (hb k w).comp measurable_fst)
      (fun i x a => (hf i x a).comp measurable_snd) (hu.comp measurable_snd)
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

lemma measurable_fullSelectedDeviation_family (center : U → ℝ) (hc : Measurable center) :
    Measurable (fun z : FullRootState Y X I M × U =>
      fullSelectedDeviation T Q m base sel (fixed z.2) D E t z.1 (u z.2) (center z.2)) := by
  apply measurable_packRoot_param (F := fun h k x n y v =>
    fullSelectedDeviation T Q m base sel (fixed v) D E t (h,⟨k,x⟩,⟨n,y⟩) (u v) (center v))
  intro k n
  have hh : Measurable (fun z : ((RootPath Y M × RootPath X k) × U) × RootPath I n =>
      fullSelectedDeviation T Q m base sel (fixed z.1.2) D E t
        (z.1.1.1,⟨k,z.1.1.2⟩,⟨n,z.2⟩) (u z.1.2) (center z.1.2)) := by
    apply measurable_from_prod_countable_left
    intro y
    exact measurable_selectedDeviation_family T Q m
      (fun z : (RootPath Y M × RootPath X k) × U => base z.1.1 k z.1.2)
      (rootArray n y) sel (fun z => fixed z.2) D E t (fun z => u z.2) (fun z => center z.2)
      (fun w => (hb k w).comp measurable_fst)
      (fun i x a => (hf i x a).comp measurable_snd) (hu.comp measurable_snd) (hc.comp measurable_snd)
  exact hh.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

lemma measurable_fullSelectedError_family
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0) :
    Measurable (fun z : U => fullSelectedError ξ μ ν r s T Q m base sel (fixed z) D E t (u z)) := by
  exact (measurable_fullSelectedDeviation_family T Q m base sel fixed D E t u hb hf hu _
    (measurable_fullSelectedRawScore_family T Q m base sel fixed D E t u hb hf hu).stronglyMeasurable.integral_prod_left'.measurable).stronglyMeasurable.integral_prod_left'.measurable

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PairSquare
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set


lemma boundParameter_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    boundParameter a b x ∈ Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

lemma boundParameter_eq {a b x : ℝ} (hx : x ∈ Icc a b) : boundParameter a b x = x := by
  simp [boundParameter,min_eq_right hx.2,max_eq_right hx.1]

lemma measurable_boundParameter (a b : ℝ) : Measurable (boundParameter a b) :=
  measurable_const.max (measurable_const.min measurable_id)

namespace HeterogeneousMarks
open scoped BigOperators NNReal ENNReal
variable {Ω I X Y U : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
theorem otherLog_congr (base : FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (sel : I → Bool) (f g : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (h : ∀ i, sel i = false → f i = g i) : otherLog base roots sel f = otherLog base roots sel g := by
  unfold otherLog
  congr 1
  funext i x y
  cases hi : sel i
  · simp only [Bool.false_eq_true,ite_false]
    rw [h i hi]
  · rfl

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedRawScore_congr
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (f g D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (h : ∀ i, sel i = false → f i = g i) (t u : ℝ) (z : FullRootState Y X I M) :
    fullSelectedRawScore T Q m base sel f D E t z u = fullSelectedRawScore T Q m base sel g D E t z u := by
  dsimp only [fullSelectedRawScore,packRoot,selectedScore]
  simp_rw [← selected_perturbLog_eq,otherLog_congr _ _ sel f g h]

omit [Countable I] [MeasurableSingletonClass I] in
theorem fullSelectedError_congr
    (ξ : Fin M → Measure Y) (μ : Measure X) (ν : Measure I) (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (f g D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (h : ∀ i, sel i = false → f i = g i) (t u : ℝ) :
    fullSelectedError ξ μ ν r s T Q m base sel f D E t u =
      fullSelectedError ξ μ ν r s T Q m base sel g D E t u := by
  unfold fullSelectedError
  simp_rw [fullSelectedRawScore_congr T Q m base sel f g D E h t u]
  apply integral_congr_ae
  filter_upwards [] with z
  dsimp only [fullSelectedDeviation]
  rw [otherLog_congr _ _ sel f g h]

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
lemma measurable_parameterFactor {J : Type} (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) :
    Measurable (fun u => parameterFactor key a b t D E u i x y) :=
  measurable_const.add (((measurable_boundParameter _ _).comp
    (measurable_pi_apply (key i))).mul_const _)

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
lemma parameterFactor_refresh {J : Type} [DecidableEq J] (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (j : J) (u : J → ℝ) (v : ℝ) (i : I) (hi : decide (key i = j) = false) :
    parameterFactor key a b t D E (Function.update u j v) i = parameterFactor key a b t D E u i := by
  have h : key i ≠ j := of_decide_eq_false hi
  funext x y
  simp only [parameterFactor,Function.update_of_ne h]

end HeterogeneousMarks
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SingletonRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I J X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [DecidableEq J]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

omit [Fintype Ω] [∀ index, Fintype (A index)] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] [DecidableEq J] in
lemma parameterFactor_log_bound (key : I → J) (a b t : J → ℝ)
    (hab : ∀ j, a j ≤ b j) (hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4))
    (ht : ∀ j, |t j| ≤ 1/4)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (u : J → ℝ) (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) :
    |Real.log (parameterFactor key a b t D E u i x y)| ≤ 1 := by
  have hu : |boundParameter (a (key i)) (b (key i)) (u (key i))| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [(hI (key i) (boundParameter_mem (hab (key i)) (u (key i)))).1],
      (hI (key i) (boundParameter_mem (hab (key i)) (u (key i)))).2⟩
  exact selectedFactor_log_bound (fun _ => true) (fun _ _ _ => 1) D E
    (fun _ _ _ => by simp) hD hE (ht (key i)) hu i x y

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (key : I → J) (a b t : J → ℝ)
    (D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)

omit [Countable I] [MeasurableSingletonClass I] [∀ index, IsProbabilityMeasure (ξ index)]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
lemma parameterError_nonneg (j : J) (u : J → ℝ) :
    0 ≤ parameterError ξ μ ν r s T Q m base key a b t D E j u :=
  fullSelectedError_nonneg ξ μ ν r s T Q m base _ _ D E (t j) _

lemma measurable_parameterError
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) (j : J) :
    Measurable (parameterError ξ μ ν r s T Q m base key a b t D E j) :=
  measurable_fullSelectedError_family T Q m base _ (parameterFactor key a b t D E) D E (t j)
    (fun u => boundParameter (a j) (b j) (u j)) hb
    (measurable_parameterFactor key a b t D E)
    ((measurable_boundParameter _ _).comp (measurable_pi_apply j)) ξ μ ν r s

omit [Countable I] [MeasurableSingletonClass I] [∀ index, IsProbabilityMeasure (ξ index)]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
lemma parameterError_refresh (j : J) (u : J → ℝ) {v : ℝ} (hv : v ∈ Icc (a j) (b j)) :
    parameterError ξ μ ν r s T Q m base key a b t D E j (Function.update u j v) =
      fullSelectedError ξ μ ν r s T Q m base (fun i => decide (key i = j))
        (parameterFactor key a b t D E u) D E (t j) v := by
  unfold parameterError
  rw [Function.update_self,boundParameter_eq hv]
  exact fullSelectedError_congr ξ μ ν r s T Q m base _ _ _ D E
    (fun i hi => parameterFactor_refresh key a b t D E j u v i hi) (t j) v

lemma integrable_parameterError (π : Measure (J → ℝ)) [IsProbabilityMeasure π]
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hab : ∀ j, a j ≤ b j) (hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4))
    (ht : ∀ j, |t j| ≤ 1/4)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1) (j : J) :
    Integrable (parameterError ξ μ ν r s T Q m base key a b t D E j) π := by
  apply (integrable_const (4*(s:ℝ)) : Integrable (fun _ : J → ℝ => 4*(s:ℝ)) π).mono'
    (measurable_parameterError ξ μ ν r s T Q m base key a b t D E hb j).aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_eq_abs,abs_of_nonneg (parameterError_nonneg ξ μ ν r s T Q m base key a b t D E j u)]
  exact fullSelectedError_bound ξ μ ν r s T Q m base _ _ D E (t j) hb hD hE
    (ht j) (abs_le.mpr ⟨by linarith [(hI j (boundParameter_mem (hab j) (u j))).1],
      (hI j (boundParameter_mem (hab j) (u j))).2⟩)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ParameterConcentration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks Set
open scoped NNReal ENNReal BigOperators
variable {X Y I J : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [DecidableEq J]
  {A : I → Type} [∀ i, Fintype (A i)] {N L : ℕ}

/-- Concentration averaged over the literal infinite dictionary parameter law.
All other coordinates remain fixed during the one-coordinate estimate. -/
theorem spin_parameter_concentration
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (hVm : ∀ σ, Measurable (fun x => V x σ)) (hhm : Measurable field)
    {C H c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hV : ∀ x σ, |V x σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ l, c ≤ m l)
    (key : I → J) (a b t : J → ℝ) (hab : ∀ j, a j < b j)
    (hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4)) (ht : ∀ j, |t j| ≤ 1/4)
    (D E : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (j : J) {ρ : ℝ} (hρ : 0 < ρ)
    (hJ : Icc (a j-ρ) (b j+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    let T := KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L
    let base := fun h k (x : RootPath X k) z => energy V field h k x (KernelTower.terminalState L z)
    (∫ u, parameterError (fun _ : Fin N => ξ) μ ν r s T Q m base key a b t D E j u
      ∂Measure.infinitePi (fun j => intervalParameterLaw (a j) (b j))) ≤
      Real.sqrt ((b j-a j)*(4+4*(b j-a j))/c*(s:ℝ))/(b j-a j)+
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+2*H^2*N)/ρ+
      12*ρ*(s:ℝ)/(b j-a j)+Real.sqrt s := by
  dsimp only
  let T := KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L
  let base := fun h k (x : RootPath X k) z => energy V field h k x (KernelTower.terminalState L z)
  let π := Measure.infinitePi (fun j => intervalParameterLaw (a j) (b j))
  let (j : J) : IsProbabilityMeasure (intervalParameterLaw (a j) (b j)) :=
    intervalParameterLaw_probability (hab j)
  have hb := fun k z => measurable_energy V field hVm hhm k (KernelTower.terminalState L z)
  apply parameter_average_le a b hab j
    (parameterError (fun _ : Fin N => ξ) μ ν r s T Q m base key a b t D E j)
    (measurable_parameterError _ μ ν r s T Q m base key a b t D E hb j)
    (integrable_parameterError _ μ ν r s T Q m base key a b t D E π hb
      (fun j => (hab j).le) hI ht hD hE j)
  intro u
  have heq := intervalIntegral.integral_congr (μ := volume) (a := a j) (b := b j)
    (f := fun v => parameterError (fun _ : Fin N => ξ) μ ν r s T Q m base key a b t D E j (Function.update u j v))
    (g := fun v => fullSelectedError (fun _ : Fin N => ξ) μ ν r s T Q m base
      (fun i => decide (key i = j)) (parameterFactor key a b t D E u) D E (t j) v)
    (fun v hv => parameterError_refresh _ μ ν r s T Q m base key a b t D E j u
      (by simpa only [uIcc_of_le (hab j).le] using hv))
  rw [heq]
  exact spin_selected_concentration μ ν ξ r s V field hVm hhm hC hc hV hh Q m hm
    (fun i => decide (key i = j)) (parameterFactor key a b t D E u) D E
    (parameterFactor_log_bound key a b t (fun j => (hab j).le) hI ht D E hD hE u)
    hD hE (ht j) (hab j) hρ hJ

end DilutedSpinGlass.PhysicalRoot
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ParameterRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology

lemma tendsto_scoreMargin : Tendsto scoreMargin atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (N:ℝ)^(-(1:ℝ)/8)) atTop (𝓝 0)
  simpa only [neg_div,Function.comp_def] using
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/8)).comp tendsto_natCast_atTop_atTop

lemma eventually_scoreMargin_interval {a b : ℝ} (ha : -(1:ℝ)/4 < a) (hb : b < 1/4) :
    ∀ᶠ N in atTop, Icc (a-scoreMargin N) (b+scoreMargin N) ⊆ Ioo (-(1:ℝ)/4) (1/4) := by
  have h1 := tendsto_scoreMargin.eventually (gt_mem_nhds (show (0:ℝ) < a+1/4 by linarith))
  have h2 := tendsto_scoreMargin.eventually (gt_mem_nhds (show (0:ℝ) < 1/4-b by linarith))
  filter_upwards [h1,h2] with N h1 h2 u hu
  exact ⟨by linarith [hu.1],by linarith [hu.2]⟩

end DilutedSpinGlass

namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks Set Filter
open scoped NNReal ENNReal BigOperators Topology
variable {X I : ℕ → Type} {Y J : Type}
  [∀ N, MeasurableSpace (X N)] [MeasurableSpace Y]
  [∀ N, Countable (I N)] [∀ N, MeasurableSpace (I N)] [∀ N, MeasurableSingletonClass (I N)]
  [DecidableEq J] {A : (N : ℕ) → I N → Type} [∀ N i, Fintype (A N i)] {L : ℕ}

variable (μ : (N : ℕ) → Measure (X N)) [∀ N, IsProbabilityMeasure (μ N)]
    (ν : (N : ℕ) → Measure (I N)) [∀ N, IsProbabilityMeasure (ν N)]
    (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (r : ℕ → ℝ≥0) (V : (N : ℕ) → X N → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (Q : (N : ℕ) → (i : I N) → Fin (L+1) → FiniteLaw (A N i)) (m : Fin (L+1) → ℝ)
    (key : (N : ℕ) → I N → J) (a b t w : J → ℝ)
    (D E : (N : ℕ) → (i : I N) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A N i) (L+1) → ℝ)

omit [∀ size, Countable (I size)] [∀ size, MeasurableSingletonClass (I size)]
  [∀ size, IsProbabilityMeasure (μ size)] [∀ size, IsProbabilityMeasure (ν size)]
  [IsProbabilityMeasure ξ] in
lemma normalizedParameterError_nonneg (hw : ∀ j, 0 < w j) (j : J) (N : ℕ) (u : J → ℝ) :
    0 ≤ normalizedParameterError μ ν ξ r V field Q m key a b t w D E j N u :=
  div_nonneg (parameterError_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    (mul_nonneg (hw j).le (Real.rpow_nonneg (Nat.cast_nonneg N) _))

 
theorem normalizedParameterError_tendsto
    (hVm : ∀ N σ, Measurable (fun x => V N x σ)) (hhm : Measurable field)
    {C H c R : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hR : 0 ≤ R)
    (hr : ∀ N, (r N:ℝ) ≤ R*N)
    (hV : ∀ N x σ, |V N x σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hm : ∀ l, c ≤ m l)
    (hab : ∀ j, a j < b j) (ha : ∀ j, -(1:ℝ)/4 < a j) (hb : ∀ j, b j < 1/4)
    (ht : ∀ j, |t j| ≤ 1/4) (hw : ∀ j, 0 < w j)
    (hD : ∀ N i x y, |D N i x y| ≤ 1) (hE : ∀ N i x y, |E N i x y| ≤ 1) (j : J) :
    Tendsto (fun N => ∫ u, normalizedParameterError μ ν ξ r V field Q m key a b t w D E j N u
      ∂Measure.infinitePi (fun j => intervalParameterLaw (a j) (b j))) atTop (𝓝 0) := by
  let (j : J) : IsProbabilityMeasure (intervalParameterLaw (a j) (b j)) := intervalParameterLaw_probability (hab j)
  let K := 3*C^2*R+4+2*H^2
  let ell := b j-a j
  let T := ell*(4+4*ell)/c
  have he : 0 < ell := sub_pos.mpr (hab j)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4) :=
    fun j u hu => ⟨(ha j).le.trans hu.1,hu.2.trans (hb j).le⟩
  apply squeeze_zero' (Eventually.of_forall (fun N => integral_nonneg
    (normalizedParameterError_nonneg μ ν ξ r V field Q m key a b t w D E hw j N)))
  · filter_upwards [eventually_ge_atTop 1,eventually_scoreMargin_interval (ha j) (hb j)] with N hN hJ
    have hn : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hbnd := spin_parameter_concentration (μ N) (ν N) ξ (r N)
      ⟨scoreScale N,Real.rpow_nonneg (Nat.cast_nonneg N) _⟩ (V N) field
      (hVm N) hhm hC hc (hV N) hh (Q N) m hm (key N) a b t hab hI ht
      (D N) (E N) (hD N) (hE N) j (Real.rpow_pos_of_pos hn _) hJ
    have hnrm := score_envelope_bound hn hK hT he (hw j)
      (physical_score_variance_linear hN (hr N)) hbnd
    simpa only [normalizedParameterError,integral_div,scoreScale,scoreMargin,K,T,ell] using hnrm
  · exact tendsto_score_rate ((Real.sqrt T/ell+1)/w j) ((4*Real.sqrt K+12/ell)/w j)

end DilutedSpinGlass.PhysicalRoot
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ConcreteReservoir
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot
open scoped NNReal BigOperators Topology

lemma boundedPotential_bound {p N : ℕ} {C : ℝ} (hC : 0 ≤ C) (z : Bond p N) (σ) :
    |boundedPotential C z σ| ≤ C := clipReal_bound hC _

variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

/-- Concentration for these concrete model laws (not an assumed concentration
interface) under the manuscript's bounded-stage hypotheses. -/
theorem scoreError_tendsto_oai (M : Model p) {C H c : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H) (hc : 0 < c)
    (hm : ∀ l, c ≤ m l) (hw : ∀ j, 0 < ν.real {j})
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1) (j : K×ℕ) :
    Filter.Tendsto (fun N => ∫ u, scoreError ν Q m D E M C H j N u
      ∂Measure.infinitePi (fun i : K×ℕ => intervalParameterLaw (probeLow i.2) (probeHigh i.2)))
      Filter.atTop (𝓝 0) := by
  apply normalizedParameterError_tendsto _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun N σ => measurable_boundedPotential C σ) (measurable_clipReal H)
    hC hc (NNReal.coe_nonneg M.alpha)
    (fun N => by simp only [NNReal.coe_mul,NNReal.coe_natCast]; rfl)
    (fun N => boundedPotential_bound hC) (clipReal_bound hH) hm
    (fun i => probeLow_lt_high i.2) (fun i => by have := probeLow_pos i.2; linarith)
    (fun i => probeHigh_lt_quarter i.2) (fun i => extractionProbe_abs_le_quarter i.2) hw
    (fun N i x y => hD _ _ _) (fun N i x y => hE _ _ _) j

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.ConcreteReservoir.scoreError_tendsto_oai := @OAI.DilutedSpinGlass.ConcreteReservoir.scoreError_tendsto_oai
