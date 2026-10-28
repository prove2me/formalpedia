-- Prove2me | solution 1 for OAI.DilutedSpinGlass.HeterogeneousMarks.full_selected_root_concentration_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:30:38.876447+00:00
-- url     : https://prove2.me/submissions/3364ff55-a08e-4f71-9b86-d81bb6fdbdac

import Mathlib
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A000
import Theorems.Thm_OAI_DilutedSpinGlass_HeterogeneousMarks_variance_actual_root_sat

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

theorem covariance_centered (f g : Ω → ℝ) :
    P.covariance f g = P.expect (fun x => (f x - P.expect f) * (g x - P.expect g)) := by
  rw [covariance]
  calc
    _ = P.expect (fun x => f x * g x - f x * P.expect g -
        P.expect f * g x + P.expect f * P.expect g) := by simp
    _ = _ := P.expect_congr (fun x => by ring)

variable {n : ℕ}

theorem logMean_mono {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    P.logMean m f ≤ P.logMean m g := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (P.expMoment_pos _ _)
  exact P.expect_mono (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (h x) hm.le))

/-- Root-measurable uniform bounds pass unchanged through each power mean. -/
theorem logMean_stability {m c : ℝ} (hm : 0 < m) {f g : Ω → ℝ}
    (h : ∀ x, |f x - g x| ≤ c) : |P.logMean m f - P.logMean m g| ≤ c := by
  have hfg : P.logMean m f ≤ P.logMean m g + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).2; linarith)
  have hgf : P.logMean m g ≤ P.logMean m f + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Differentiation commutes with a finite path kernel. -/
theorem hasDerivAt_expect {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} {u : ℝ}
    (h : ∀ x, HasDerivAt (fun t => f t x) (f' x) u) :
    HasDerivAt (fun t => P.expect (f t)) (P.expect f') u := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun x _ => (h x).const_mul (P.weight x))
  have heq : (∑ x, fun t => P.weight x * f t x) = (fun t => P.expect (f t)) := by
    funext t
    simp only [Finset.sum_apply, expect]
  rw [heq] at hd
  exact hd

/-- First variation of a power-mean step: the derivative is the tilted score. -/
theorem hasDerivAt_logMean {m : ℝ} (hm : m ≠ 0)
    {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} {u : ℝ}
    (h : ∀ x, HasDerivAt (fun t => f t x) (f' x) u) :
    HasDerivAt (fun t => P.logMean m (f t)) ((P.tilt m (f u)).expect f') u := by
  have he := P.hasDerivAt_expect (fun x => ((h x).const_mul m).exp)
  have hl := (he.log (ne_of_gt (P.expMoment_pos m (f u)))).div_const m
  change HasDerivAt (fun t => P.logMean m (f t)) _ u at hl
  suffices heqv : (P.tilt m (f u)).expect f' =
      (P.expect (fun x => Real.exp (m * f u x) * (m * f' x)) / P.expMoment m (f u)) / m by
    rw [heqv]
    exact hl
  rw [tilt_expect]
  have heq : P.expect (fun x => Real.exp (m * f u x) * (m * f' x)) =
      m * P.expect (fun x => Real.exp (m * f u x) * f' x) := by
    rw [← expect_mul_left]
    exact P.expect_congr (fun x => by ring)
  rw [heq]
  field_simp


/-- Differentiating an observable under a finite exponentially tilted kernel. -/
theorem hasDerivAt_tilt_expect {m : ℝ}
    {f g : ℝ → Ω → ℝ} {f' g' : Ω → ℝ} {u : ℝ}
    (hf : ∀ x, HasDerivAt (fun t => f t x) (f' x) u)
    (hg : ∀ x, HasDerivAt (fun t => g t x) (g' x) u) :
    HasDerivAt (fun t => (P.tilt m (f t)).expect (g t))
      ((P.tilt m (f u)).expect g' +
        m * (P.tilt m (f u)).covariance (g u) f') u := by
  have hnum := P.hasDerivAt_expect
    (fun x => (((hf x).const_mul m).exp).mul (hg x))
  have hden := P.hasDerivAt_expect (fun x => ((hf x).const_mul m).exp)
  have hd := hnum.div hden (ne_of_gt (P.expMoment_pos m (f u)))
  simp only [tilt_expect]
  apply hd.congr_deriv
  have hnum' : P.expect (fun x =>
      Real.exp (m * f u x) * (m * f' x) * g u x + Real.exp (m * f u x) * g' x) =
      m * P.expect (fun x => Real.exp (m * f u x) * (g u x * f' x)) +
        P.expect (fun x => Real.exp (m * f u x) * g' x) := by
    rw [expect_add, ← expect_mul_left]
    congr 1
    exact P.expect_congr (fun x => by ring)
  have hden' : P.expect (fun x => Real.exp (m * f u x) * (m * f' x)) =
      m * P.expect (fun x => Real.exp (m * f u x) * f' x) := by
    rw [← expect_mul_left]
    exact P.expect_congr (fun x => by ring)
  rw [hnum', hden', covariance, tilt_expect, tilt_expect, tilt_expect]
  simp only [expMoment, Pi.mul_apply]
  have hne : P.expect (fun x => Real.exp (m * f u x)) ≠ 0 :=
    ne_of_gt (P.expMoment_pos m (f u))
  field_simp [hne]
  ring

/-- Total variance at one edge of a finite probability tree. -/
theorem variance_bind {Λ : Type*} [Fintype Λ] (Q : Ω → FiniteLaw Λ)
    (f : Ω × Λ → ℝ) :
    (P.bind Q).covariance f f =
      P.expect (fun x => (Q x).covariance (fun y => f (x,y)) (fun y => f (x,y))) +
        P.covariance (fun x => (Q x).expect (fun y => f (x,y)))
          (fun x => (Q x).expect (fun y => f (x,y))) := by
  simp only [covariance, expect_bind, expect_sub]
  ring

theorem covariance_self_nonneg (f : Ω → ℝ) : 0 ≤ P.covariance f f := by
  rw [covariance_centered]
  exact P.expect_nonneg (fun x => mul_self_nonneg _)

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_KernelTower
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

namespace KernelTower

variable {Ω : Type} [Fintype Ω]

/-- First variation through the entire finite hierarchy, with all exponents
and all original path-dependent priors retained. -/
theorem hasDerivAt_backwardLog (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (hm : ∀ i, m i ≠ 0)
    {f : ℝ → FinitePath Ω n → ℝ} {f' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ x, HasDerivAt (fun t => f t x) (f' x) u) :
    HasDerivAt (fun t => backwardLog n T m (f t))
      ((law n (tilt n T m (f u))).expect f') u := by
  induction n with
  | zero =>
    rw [law_zero_expect (Ω := Ω)]
    exact hf ()
  | succ n ih =>
    have hs := fun x => ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
      (fun y => hf (x,y))
    rw [law_succ_expect (Ω := Ω) n]
    simpa only [backwardLog, tilt] using
      T.1.hasDerivAt_logMean (hm 0) hs


/-- The lower energy estimate in pert:second-derivative; the smallest exponent
controls the full terminal path variance, not merely the root variance. -/
theorem varianceEnergy_lower (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) {c : ℝ} (hm : ∀ i, c ≤ m i) (f : FinitePath Ω n → ℝ) :
    c * (law n T).covariance f f ≤ varianceEnergy n T m f := by
  induction n with
  | zero => simp [FiniteLaw.covariance, law_zero_expect, varianceEnergy]
  | succ n ih =>
    let g := fun x => (law n (T.2 x)).expect (fun y => f (x,y))
    have hfirst : c * T.1.covariance g g ≤ m 0 * T.1.covariance g g :=
      mul_le_mul_of_nonneg_right (hm 0) (T.1.covariance_self_nonneg g)
    have hrest := T.1.expect_mono (fun x => ih (T.2 x) (fun j => m j.succ)
      (fun j => hm j.succ) (fun y => f (x,y)))
    have hv := T.1.variance_bind (fun x => law n (T.2 x)) f
    change (law (n+1) T).covariance f f = _ at hv
    rw [hv]
    simp only [varianceEnergy]
    dsimp only [g] at hfirst
    rw [FiniteLaw.expect_mul_left] at hrest
    nlinarith

/-- Second variation through a tower. Terminal derivatives plus the positive
weighted martingale energy from every depth. No concentration is assumed. -/
theorem hasDerivAt_path_score (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (hm : ∀ i, m i ≠ 0)
    {f f' : ℝ → FinitePath Ω n → ℝ} {f'' : FinitePath Ω n → ℝ} {u : ℝ}
    (hf : ∀ x, HasDerivAt (fun t => f t x) (f' u x) u)
    (hf' : ∀ x, HasDerivAt (fun t => f' t x) (f'' x) u) :
    HasDerivAt (fun t => (law n (tilt n T m (f t))).expect (f' t))
      ((law n (tilt n T m (f u))).expect f'' +
        varianceEnergy n (tilt n T m (f u)) m (f' u)) u := by
  induction n with
  | zero =>
    simp_rw [law_zero_expect (Ω := Ω)]
    simpa only [varianceEnergy, add_zero] using hf' ()
  | succ n ih =>
    have hfirst := fun x => hasDerivAt_backwardLog n (T.2 x)
      (fun j => m j.succ) (fun j => hm j.succ) (fun y => hf (x,y))
    have hsecond := fun x => ih (T.2 x) (fun j => m j.succ)
      (fun j => hm j.succ) (fun y => hf (x,y)) (fun y => hf' (x,y))
    have hd := T.1.hasDerivAt_tilt_expect hfirst hsecond (m := m 0)
    simp_rw [law_succ_expect (Ω := Ω) n]
    simpa only [tilt, backwardLog, varianceEnergy, FiniteLaw.expect_add, add_assoc, add_comm, add_left_comm] using hd

theorem backwardLog_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, m i ≠ 0) (c : ℝ) : backwardLog n T m (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog]
    have heq : (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun _ => c)) =
        (fun _ => c) := by
      funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
    rw [heq, FiniteLaw.logMean_const _ (hm 0)]

/-- The uniform insertion bound, with full arbitrary depth-dependent priors. -/
theorem backwardLog_stability (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f g : FinitePath Ω n → ℝ} {c : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ c) :
    |backwardLog n T m f - backwardLog n T m g| ≤ c := by
  induction n with
  | zero => exact hfg ()
  | succ n ih =>
    apply T.1.logMean_stability (hm 0)
    intro x
    exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ) (fun y => hfg (x,y))

end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

theorem poisson_variance (r : ℝ≥0) :
    (∫ n : ℕ, ((n : ℝ) - r)^2 ∂poissonMeasure r) = r := by
  have heq : (fun n : ℕ => ((n : ℝ)-r)^2) =
      (fun n : ℕ => (n : ℝ)^2 - 2*(r : ℝ)*(n : ℝ) + (r : ℝ)^2) := by
    funext n
    ring
  rw [heq]
  have hi : Integrable (fun n : ℕ => (n : ℝ)^2 - 2*(r : ℝ)*n) (poissonMeasure r) :=
    (poisson_integrable_count_sq r).sub ((poisson_integrable_count r).const_mul (2*(r : ℝ)))
  rw [integral_add hi (integrable_const ((r : ℝ)^2)),
    integral_sub (poisson_integrable_count_sq r) ((poisson_integrable_count r).const_mul (2*r)),
    integral_const_mul, poisson_second_moment, poisson_mean, integral_const,
    probReal_univ, smul_eq_mul, one_mul]
  ring

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ProductTowers
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

/-- A mark block not present in a log weight integrates out, before or after
any one power-mean tilt. -/
theorem logMean_bind_fst (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω → ℝ) :
    (P.bind (fun _ => Q)).logMean m (fun z => f z.1) = P.logMean m f := by
  simp [logMean, expMoment]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem backwardLog_prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) :
    backwardLog n (prod n T U) m (fun y => f (pathFst n y)) = backwardLog n T m f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog, prod, pathFst]
    have hh : (fun z : Ω × Λ => backwardLog n
        (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
        (fun y => f (z.1, pathFst n y))) =
        (fun z : Ω × Λ => backwardLog n (T.2 z.1) (fun j => m j.succ)
          (fun y => f (z.1,y))) := by
      funext z
      exact ih (T.2 z.1) (U.2 z.2) (fun j => m j.succ) (fun y => f (z.1,y))
    rw [hh]
    exact FiniteLaw.logMean_bind_fst T.1 U.1 (m 0)
      (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_Perturbations
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
theorem hasDerivAt_perturbLog {L n : ℕ} (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) (y : FinitePath Ω L)
    (hp : ∀ q, 0 < 1+t*D q y+u*E q y) :
    HasDerivAt (fun v => perturbLog base D E t v y) (perturbScore D E t u y) u := by
  have hh (q : Fin n) := (((hasDerivAt_id u).mul_const (E q y)).const_add
    (1+t*D q y)).log (ne_of_gt (hp q))
  simpa only [perturbLog, perturbScore, id_eq, one_mul] using
    (HasDerivAt.fun_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin n))) => hh q)).const_add (base y)

omit [Fintype Ω] in
theorem hasDerivAt_perturbScore {L n : ℕ}
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ) (y : FinitePath Ω L)
    (hp : ∀ q, 0 < 1+t*D q y+u*E q y) :
    HasDerivAt (fun v => perturbScore D E t v y) (perturbCurvature D E t u y) u := by
  have hh (q : Fin n) := (hasDerivAt_const u (E q y)).div
    (((hasDerivAt_id u).mul_const (E q y)).const_add (1+t*D q y)) (ne_of_gt (hp q))
  have hsum := HasDerivAt.fun_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin n))) => hh q)
  change HasDerivAt (fun v => perturbScore D E t v y) _ u at hsum
  apply hsum.congr_deriv
  simp only [id_eq, one_mul, perturbCurvature, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q _
  simp only [div_pow]
  ring

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

omit [Fintype Ω] in
theorem perturbCurvature_bounds {L n : ℕ} (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (y : FinitePath Ω L) :
    -4*n ≤ perturbCurvature D E t u y ∧ perturbCurvature D E t u y ≤ 0 := by
  have hsq (q : Fin n) : (E q y / (1+t*D q y+u*E q y))^2 ≤ 4 := by
    have hh := abs_le.mp (perturb_fraction_bound D E hD hE ht hu q y)
    nlinarith
  have hh := Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin n))) => hsq q)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  constructor
  · dsimp [perturbCurvature]
    linarith
  · exact neg_nonpos.mpr (Finset.sum_nonneg (fun _ _ => sq_nonneg _))


end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]

theorem hasDerivAt_correctedPerturbLog {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (hm : ∀ i, m i ≠ 0) (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ)
    (hp : ∀ q y, 0 < 1+t*D q y+u*E q y) :
    HasDerivAt (correctedPerturbLog T m base D E t)
      (correctedPerturbScore T m base D E t u) u := by
  have h1 := hasDerivAt_backwardLog L T m hm
    (fun y => hasDerivAt_perturbLog base D E t u y (fun q => hp q y))
  have h2 : HasDerivAt (fun v : ℝ => 2*(n:ℝ)*v^2) (4*n*u) u := by
    exact (((hasDerivAt_id u).pow 2).const_mul (2*(n:ℝ))).congr_deriv (by
      norm_num
      ring)
  have h3 := h1.add h2
  change HasDerivAt (fun v => backwardLog L T m (perturbLog base D E t v) + 2*n*v^2)
    ((law L (tilt L T m (perturbLog base D E t u))).expect (perturbScore D E t u) + 4*n*u) u
  exact h3

theorem hasDerivAt_correctedPerturbScore {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (hm : ∀ i, m i ≠ 0) (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ) (t u : ℝ)
    (hp : ∀ q y, 0 < 1+t*D q y+u*E q y) :
    HasDerivAt (correctedPerturbScore T m base D E t)
      ((law L (tilt L T m (perturbLog base D E t u))).expect (perturbCurvature D E t u) +
        varianceEnergy L (tilt L T m (perturbLog base D E t u)) m (perturbScore D E t u) + 4*n) u := by
  have h1 := hasDerivAt_path_score L T m hm
    (fun y => hasDerivAt_perturbLog base D E t u y (fun q => hp q y))
    (fun y => hasDerivAt_perturbScore D E t u y (fun q => hp q y))
  have h2 : HasDerivAt (fun v : ℝ => 4*(n:ℝ)*v) (4*n) u := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul (4*(n:ℝ))
  change HasDerivAt (fun v =>
    (law L (tilt L T m (perturbLog base D E t v))).expect (perturbScore D E t v) + 4*n*v) _ u
  exact h1.add h2

 
theorem correctedPerturbLog_convex {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (hm : ∀ i, 0 < m i) (base : FinitePath Ω L → ℝ)
    (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t : ℝ} (ht : |t| ≤ 1/4) :
    ConvexOn ℝ (Set.Icc (-(1:ℝ)/4) (1/4)) (correctedPerturbLog T m base D E t) := by
  let J := Set.Icc (-(1:ℝ)/4) (1/4)
  have hu (u : ℝ) (h : u ∈ J) : |u| ≤ 1/4 := abs_le.mpr ⟨by linarith [h.1], h.2⟩
  have hp (u : ℝ) (h : u ∈ J) (q : Fin n) (y : FinitePath Ω L) :
      0 < 1+t*D q y+u*E q y := by
    linarith [perturb_factor_lower D E hD hE ht (hu u h) q y]
  have h1 (u : ℝ) (h : u ∈ J) := hasDerivAt_correctedPerturbLog T m
    (fun i => ne_of_gt (hm i)) base D E t u (hp u h)
  have h2 (u : ℝ) (h : u ∈ J) := hasDerivAt_correctedPerturbScore T m
    (fun i => ne_of_gt (hm i)) base D E t u (hp u h)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun u h => (h1 u h).continuousAt.continuousWithinAt)
    (fun u h => (h1 u (interior_subset h)).hasDerivWithinAt)
    (fun u h => (h2 u (interior_subset h)).hasDerivWithinAt)
  intro u h
  have hb := (law L (tilt L T m (perturbLog base D E t u))).expect_mono
    (fun y => (perturbCurvature_bounds D E hD hE ht (hu u (interior_subset h)) y).1)
  rw [FiniteLaw.expect_const] at hb
  have hv := varianceEnergy_lower L (tilt L T m (perturbLog base D E t u)) m
    (c := 0) (fun i => (hm i).le) (perturbScore D E t u)
  simp only [zero_mul] at hv
  linarith

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_MixtureMeasures
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ConvexBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
namespace DilutedSpinGlass

/-- The deterministic three-point estimate used in pert:convex-bound. It
requires convexity only on the original open parameter domain, not globally. -/
theorem convex_derivative_fluctuation {S : Set ℝ} {f g f' g' : ℝ → ℝ}
    (hf : ConvexOn ℝ S f) (hg : ConvexOn ℝ S g)
    {u ρ : ℝ} (hρ : 0 < ρ) (hm : u-ρ ∈ S) (hu : u ∈ S) (hp : u+ρ ∈ S)
    (hfu : HasDerivAt f (f' u) u)
    (hgm : HasDerivAt g (g' (u-ρ)) (u-ρ))
    (hgu : HasDerivAt g (g' u) u)
    (hgp : HasDerivAt g (g' (u+ρ)) (u+ρ)) :
    |f' u - g' u| ≤
      (|f (u-ρ) - g (u-ρ)| + 2*|f u-g u| + |f (u+ρ)-g (u+ρ)|) / ρ +
        g' (u+ρ) - g' (u-ρ) := by
  have hum : u-ρ < u := by linarith
  have hup : u < u+ρ := by linarith
  have hfm := hf.slope_le_of_hasDerivAt hm hu hum hfu
  have hfp := hf.le_slope_of_hasDerivAt hu hp hup hfu
  have hgml := hg.le_slope_of_hasDerivAt hm hu hum hgm
  have hgmr := hg.slope_le_of_hasDerivAt hm hu hum hgu
  have hgpl := hg.le_slope_of_hasDerivAt hu hp hup hgu
  have hgpr := hg.slope_le_of_hasDerivAt hu hp hup hgp
  have hd1 : u - (u-ρ) = ρ := by ring
  have hd2 : u+ρ - u = ρ := by ring
  simp only [slope_def_field, hd1, hd2] at hfm hfp hgml hgmr hgpl hgpr
  have hfm' := (div_le_iff₀ hρ).mp hfm
  have hfp' := (le_div_iff₀ hρ).mp hfp
  have hgml' := (le_div_iff₀ hρ).mp hgml
  have hgmr' := (div_le_iff₀ hρ).mp hgmr
  have hgpl' := (le_div_iff₀ hρ).mp hgpl
  have hgpr' := (div_le_iff₀ hρ).mp hgpr
  let A := |f (u-ρ)-g (u-ρ)| + 2*|f u-g u| + |f (u+ρ)-g (u+ρ)|
  have ha : (A / ρ) * ρ = A := div_mul_cancel₀ _ (ne_of_gt hρ)
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_left₀ hρ).mp
    dsimp only [A] at ha
    nlinarith [le_abs_self (f (u-ρ)-g (u-ρ)), neg_le_abs (f u-g u),
      abs_nonneg (f u-g u), abs_nonneg (f (u+ρ)-g (u+ρ))]
  · apply (mul_le_mul_iff_left₀ hρ).mp
    dsimp only [A] at ha
    nlinarith [le_abs_self (f (u+ρ)-g (u+ρ)), neg_le_abs (f u-g u),
      abs_nonneg (f u-g u), abs_nonneg (f (u-ρ)-g (u-ρ))]

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

 
theorem integral_abs_le_sqrt_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) := by
  have hn := variance_nonneg (fun x => ‖f x‖) μ
  rw [variance_eq_sub hf.norm] at hn
  simp only [Real.norm_eq_abs, Pi.pow_apply, sq_abs] at hn
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))).mpr (by linarith)

theorem integral_deviation_le_sqrt_variance {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x-∫ y, f y ∂μ| ∂μ) ≤ Real.sqrt (variance f μ) := by
  have hh := integral_abs_le_sqrt_sq μ (hf.sub (memLp_const (∫ y, f y ∂μ)))
  change (∫ x, |f x-∫ y, f y ∂μ| ∂μ) ≤ Real.sqrt (∫ x, (f x-∫ y, f y ∂μ)^2 ∂μ) at hh
  rw [← variance_eq_integral hf.aemeasurable] at hh
  exact hh

omit [IsProbabilityMeasure μ] in
/-- Taking a root expectation preserves convexity on the original parameter
domain. This does not extend the perturbation outside its factor-positive
interval. -/
theorem convexOn_integral {S : Set ℝ} {F : Ω → ℝ → ℝ}
    (hS : Convex ℝ S) (hF : ∀ x, ConvexOn ℝ S (F x))
    (hi : ∀ u ∈ S, Integrable (fun x => F x u) μ) :
    ConvexOn ℝ S (fun u => ∫ x, F x u ∂μ) := by
  refine ⟨hS, ?_⟩
  intro a ha b hb w v hw hv hwv
  have huv : w*a+v*b ∈ S := hS ha hb hw hv hwv
  have hh := integral_mono (hi _ huv)
    (((hi a ha).const_mul w).add ((hi b hb).const_mul v))
    (fun x => (hF x).2 ha hb hw hv hwv)
  change (∫ x, F x (w*a+v*b) ∂μ) ≤ ∫ x, (w*F x a+v*F x b) ∂μ at hh
  rw [integral_add ((hi a ha).const_mul w) ((hi b hb).const_mul v), integral_const_mul,integral_const_mul] at hh
  simpa only [smul_eq_mul] using hh

/-- The probabilistic three-point convexity estimate, with its genuine
standard-deviation (rather than variance) scale. -/
theorem convex_derivative_mean_bound {S : Set ℝ} {F F' : Ω → ℝ → ℝ}
    {g g' : ℝ → ℝ} (hf : ∀ x, ConvexOn ℝ S (F x)) (hg : ConvexOn ℝ S g)
    {u ρ V : ℝ} (hρ : 0 < ρ)
    (hm : u-ρ ∈ S) (hu : u ∈ S) (hp : u+ρ ∈ S)
    (hfu : ∀ x, HasDerivAt (F x) (F' x u) u)
    (hgm : HasDerivAt g (g' (u-ρ)) (u-ρ))
    (hgu : HasDerivAt g (g' u) u) (hgp : HasDerivAt g (g' (u+ρ)) (u+ρ))
    (hD : Integrable (fun x => F' x u) μ)
    (hi : ∀ w ∈ S, MemLp (fun x => F x w) 2 μ)
    (he : ∀ w ∈ S, g w = ∫ x, F x w ∂μ)
    (hv : ∀ w ∈ S, variance (fun x => F x w) μ ≤ V) :
    (∫ x, |F' x u-g' u| ∂μ) ≤ 4*Real.sqrt V/ρ+g' (u+ρ)-g' (u-ρ) := by
  have hb (w : ℝ) (hw : w ∈ S) :
      (∫ x, |F x w-g w| ∂μ) ≤ Real.sqrt V := by
    rw [he w hw]
    exact (integral_deviation_le_sqrt_variance μ (hi w hw)).trans
      (Real.sqrt_le_sqrt (hv w hw))
  have hj (w : ℝ) (hw : w ∈ S) : Integrable (fun x => |F x w-g w|) μ :=
    (((hi w hw).integrable (by norm_num)).sub (integrable_const _)).abs
  have hbound := integral_mono ((hD.sub (integrable_const _)).abs)
    (((((hj (u-ρ) hm).add ((hj u hu).const_mul 2)).add (hj (u+ρ) hp)).div_const ρ).add
      (integrable_const (g' (u+ρ)-g' (u-ρ))))
    (fun x => by
      have hh := convex_derivative_fluctuation (hf x) hg hρ hm hu hp (hfu x) hgm hgu hgp
      change |F' x u-g' u| ≤ (|F x (u-ρ)-g (u-ρ)|+2*|F x u-g u|+|F x (u+ρ)-g (u+ρ)|)/ρ+(g' (u+ρ)-g' (u-ρ))
      linarith)
  have hv1 := hb (u-ρ) hm
  have hv2 := hb u hu
  have hv3 := hb (u+ρ) hp
  change (∫ x, |F' x u-g' u| ∂μ) ≤
    ∫ x, ((|F x (u-ρ)-g (u-ρ)|+2*|F x u-g u|+|F x (u+ρ)-g (u+ρ)|)/ρ+
      (g' (u+ρ)-g' (u-ρ))) ∂μ at hbound
  erw [integral_add
    ((((hj (u-ρ) hm).add ((hj u hu).const_mul 2)).add (hj (u+ρ) hp)).div_const ρ)
    (integrable_const _), integral_div,
    integral_add ((hj (u-ρ) hm).add ((hj u hu).const_mul 2)) (hj (u+ρ) hp),
    integral_add (hj (u-ρ) hm) ((hj u hu).const_mul 2), integral_const_mul,
    integral_const,probReal_univ,smul_eq_mul,one_mul] at hbound
  have hsum : ((∫ x, |F x (u-ρ)-g (u-ρ)| ∂μ)+2*(∫ x, |F x u-g u| ∂μ)+
      (∫ x, |F x (u+ρ)-g (u+ρ)| ∂μ))/ρ ≤ 4*Real.sqrt V/ρ :=
    div_le_div_of_nonneg_right (by linarith) (le_of_lt hρ)
  linarith

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory Set intervalIntegral

/-- The boundary-layer estimate used in pert:convex-bound. It holds on the
specified finite domain only, including when the two boundary layers overlap. -/
theorem integral_monotone_shift {k : ℝ → ℝ} {a b ρ : ℝ}
    (hab : a ≤ b) (hρ : 0 ≤ ρ) (hk : MonotoneOn k (Icc (a-ρ) (b+ρ))) :
    (∫ u in a..b, k (u+ρ)-k (u-ρ)) ≤ 2*ρ*(k (b+ρ)-k (a-ρ)) := by
  have hlo : a-ρ ≤ b+ρ := by linarith
  have hint {x y : ℝ} (hx : x ∈ Icc (a-ρ) (b+ρ)) (hy : y ∈ Icc (a-ρ) (b+ρ)) :
      IntervalIntegrable k volume x y := by
    apply MonotoneOn.intervalIntegrable
    intro z hz w hw hzw
    apply hk _ _ hzw
    · change min x y ≤ z ∧ z ≤ max x y at hz
      exact ⟨le_trans (le_min hx.1 hy.1) hz.1, le_trans hz.2 (max_le hx.2 hy.2)⟩
    · change min x y ≤ w ∧ w ≤ max x y at hw
      exact ⟨le_trans (le_min hx.1 hy.1) hw.1, le_trans hw.2 (max_le hx.2 hy.2)⟩
  have ham : a-ρ ∈ Icc (a-ρ) (b+ρ) := ⟨le_rfl,hlo⟩
  have hap : a+ρ ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith,by linarith⟩
  have hbm : b-ρ ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith,by linarith⟩
  have hbp : b+ρ ∈ Icc (a-ρ) (b+ρ) := ⟨hlo,le_rfl⟩
  have hplus : IntervalIntegrable (fun u => k (u+ρ)) volume a b := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx y hy hxy
    exact hk ⟨by linarith [hx.1],by linarith [hx.2]⟩
      ⟨by linarith [hy.1],by linarith [hy.2]⟩ (by linarith)
  have hminus : IntervalIntegrable (fun u => k (u-ρ)) volume a b := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx y hy hxy
    exact hk ⟨by linarith [hx.1],by linarith [hx.2]⟩
      ⟨by linarith [hy.1],by linarith [hy.2]⟩ (by linarith)
  rw [integral_sub hplus hminus,integral_comp_add_right,integral_comp_sub_right]
  have he1 := integral_add_adjacent_intervals (hint ham hap) (hint hap hbp)
  have he2 := integral_add_adjacent_intervals (hint ham hbm) (hint hbm hbp)
  have hbnd := integral_mono_on (by linarith : b-ρ ≤ b+ρ) (hint hbm hbp)
    (intervalIntegrable_const (c := k (b+ρ))) (fun x hx =>
      hk ⟨by linarith [hx.1],hx.2⟩ hbp hx.2)
  have hand := integral_mono_on (by linarith : a-ρ ≤ a+ρ)
    (intervalIntegrable_const (c := k (a-ρ))) (hint ham hap) (fun x hx =>
      hk ham ⟨hx.1,by linarith [hx.2]⟩ hx.1)
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hbnd hand
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory Set intervalIntegral

 
theorem integral_convex_derivative_bound {D k : ℝ → ℝ} {a b ρ V B : ℝ}
    (hab : a < b) (hρ : 0 < ρ)
    (hD : IntervalIntegrable D volume a b)
    (hk : MonotoneOn k (Icc (a-ρ) (b+ρ)))
    (hpoint : ∀ u ∈ Icc a b, D u ≤ 4*Real.sqrt V/ρ+k (u+ρ)-k (u-ρ))
    (hB : k (b+ρ)-k (a-ρ) ≤ B) :
    (∫ u in a..b, D u)/(b-a) ≤ 4*Real.sqrt V/ρ+(2*ρ*B)/(b-a) := by
  have hi {c : ℝ} (hc : -ρ ≤ c ∧ c ≤ ρ) :
      IntervalIntegrable (fun u => k (u+c)) volume a b := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (le_of_lt hab)]
    intro x hx y hy hxy
    exact hk ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)
  have hp := hi (c := ρ) ⟨by linarith,le_rfl⟩
  have hm : IntervalIntegrable (fun u => k (u-ρ)) volume a b := by
    simpa only [sub_eq_add_neg] using (hi (c := -ρ) ⟨le_rfl,by linarith⟩)
  have hs := integral_monotone_shift (le_of_lt hab) (le_of_lt hρ) hk
  have hbnd := integral_mono_on (le_of_lt hab) hD
    ((intervalIntegrable_const (c := 4*Real.sqrt V/ρ)).add (hp.sub hm))
    (fun u hu => by simpa only [add_sub_assoc] using hpoint u hu)
  change (∫ u in a..b, D u) ≤ ∫ u in a..b, (4*Real.sqrt V/ρ+(k (u+ρ)-k (u-ρ))) at hbnd
  rw [integral_add intervalIntegrable_const (hp.sub hm),intervalIntegral.integral_const,
    smul_eq_mul] at hbnd
  have hB' := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2*ρ)
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  have hne : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  rw [add_mul,div_mul_cancel₀ _ hne]
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem hasDerivAt_rootMean {F G : X → ℝ → ℝ} {S : Set ℝ}
    (hS : IsOpen S) (hFm : ∀ u, Measurable (fun x => F x u))
    (hGm : ∀ u, Measurable (fun x => G x u))
    (hi : ∀ u ∈ S, Integrable (fun x => F x u) μ)
    {B : X → ℝ} (hB : Integrable B μ) (hb : ∀ x u, u ∈ S → |G x u| ≤ B x)
    (hd : ∀ x u, u ∈ S → HasDerivAt (F x) (G x u) u) {u : ℝ} (hu : u ∈ S) :
    HasDerivAt (fun v => ∫ x, F x v ∂μ) (∫ x, G x u ∂μ) u := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (hS.mem_nhds hu)
    (Eventually.of_forall (fun v => (hFm v).aestronglyMeasurable)) (hi u hu)
    (hGm u).aestronglyMeasurable
    (ae_of_all _ (fun x v hv => by simpa only [Real.norm_eq_abs] using hb x v hv))
    hB (ae_of_all _ hd)).2

omit [IsProbabilityMeasure μ] in
theorem rootMean_abs_le {G : X → ℝ → ℝ} (hGm : ∀ u, Measurable (fun x => G x u))
    {B : X → ℝ} (hB : Integrable B μ) {u : ℝ} (hb : ∀ x, |G x u| ≤ B x) :
    |∫ x, G x u ∂μ| ≤ ∫ x, B x ∂μ := by
  exact (abs_integral_le_integral_abs).trans
    (integral_mono (hB.mono' (hGm u).aestronglyMeasurable (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hb x))).abs hB hb)

/-- Root fluctuation estimate after averaging the actual convex score;
all differentiations of expectations are justified by the integrable
random count bound. -/
theorem root_derivative_integral_bound {F G : X → ℝ → ℝ} {S : Set ℝ}
    (hS : IsOpen S) (hSc : Convex ℝ S)
    (hFm : ∀ u, Measurable (fun x => F x u))
    (hGm : Measurable (fun z : X × ℝ => G z.1 z.2))
    (hfc : ∀ x, ConvexOn ℝ S (F x))
    (hLp : ∀ u ∈ S, MemLp (fun x => F x u) 2 μ)
    {B : X → ℝ} (hB : Integrable B μ) (hb : ∀ x u, u ∈ S → |G x u| ≤ B x)
    (hd : ∀ x u, u ∈ S → HasDerivAt (F x) (G x u) u)
    {a b ρ V : ℝ} (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ S)
    (hv : ∀ u ∈ Icc (a-ρ) (b+ρ), variance (fun x => F x u) μ ≤ V) :
    (∫ u in a..b, (∫ x, |G x u-∫ y, G y u ∂μ| ∂μ))/(b-a) ≤
      4*Real.sqrt V/ρ+4*ρ*(∫ x, B x ∂μ)/(b-a) := by
  let g (u : ℝ) := ∫ x, F x u ∂μ
  let k (u : ℝ) := ∫ x, G x u ∂μ
  let D (u : ℝ) := ∫ x, |G x u-k u| ∂μ
  have hG (u : ℝ) : Measurable (fun x => G x u) :=
    hGm.comp (measurable_id.prodMk measurable_const)
  have hi (u : ℝ) (hu : u ∈ S) : Integrable (fun x => F x u) μ :=
    (hLp u hu).integrable (by norm_num)
  have hg : ConvexOn ℝ S g := convexOn_integral μ hSc hfc hi
  have hdg (u : ℝ) (hu : u ∈ S) : HasDerivAt g (k u) u :=
    hasDerivAt_rootMean μ hS hFm hG hi hB hb hd hu
  have hk : MonotoneOn k (Icc (a-ρ) (b+ρ)) := by
    intro x hx y hy hxy
    have hh := hg.monotoneOn_deriv (fun u hu => (hdg u hu).differentiableAt) (hJ hx) (hJ hy) hxy
    rwa [(hdg x (hJ hx)).deriv,(hdg y (hJ hy)).deriv] at hh
  have hki (u : ℝ) (hu : u ∈ S) : Integrable (fun x => G x u) μ :=
    hB.mono' (hG u).aestronglyMeasurable (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hb x u hu))
  have hkab (u : ℝ) (hu : u ∈ S) : |k u| ≤ ∫ x, B x ∂μ :=
    rootMean_abs_le μ hG hB (fun x => hb x u hu)
  have hDm : Measurable D := by
    have hkm : Measurable k := (hGm.stronglyMeasurable.integral_prod_left').measurable
    exact (((hGm.sub (hkm.comp measurable_snd)).abs).stronglyMeasurable.integral_prod_left').measurable
  have hDb (u : ℝ) (hu : u ∈ Icc a b) : |D u| ≤ 2*(∫ x, B x ∂μ) := by
    have huS : u ∈ S := hJ ⟨by linarith [hu.1],by linarith [hu.2]⟩
    rw [abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
    have hh := integral_mono ((hki u huS).sub (integrable_const (k u))).abs
      (hB.add (integrable_const |k u|))
      (fun x => (abs_sub _ _).trans (add_le_add (hb x u huS) le_rfl))
    simp only [Pi.add_apply, Pi.sub_apply] at hh
    rw [integral_add hB (integrable_const _),integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
    dsimp only [D]
    linarith [hkab u huS]
  have hDi : IntervalIntegrable D volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    exact Measure.integrableOn_of_bounded (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      hDm.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioc
        (fun u hu => by simpa only [Real.norm_eq_abs] using hDb u ⟨hu.1.le,hu.2⟩))
  have hpoint (u : ℝ) (hu : u ∈ Icc a b) :
      D u ≤ 4*Real.sqrt V/ρ+k (u+ρ)-k (u-ρ) := by
    have hm : u-ρ ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have h0 : u ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    have hp : u+ρ ∈ Icc (a-ρ) (b+ρ) := ⟨by linarith [hu.1],by linarith [hu.2]⟩
    apply convex_derivative_mean_bound μ
      (fun x => (hfc x).subset hJ (convex_Icc _ _)) (hg.subset hJ (convex_Icc _ _)) hρ hm h0 hp
      (fun x => hd x u (hJ h0)) (hdg _ (hJ hm)) (hdg _ (hJ h0)) (hdg _ (hJ hp))
      (hki u (hJ h0)) (fun w hw => hLp w (hJ hw)) (fun _ _ => rfl) hv
  have hB' : k (b+ρ)-k (a-ρ) ≤ 2*(∫ x, B x ∂μ) := by
    have hlo : a-ρ ≤ b+ρ := by linarith
    have h1 := hkab (b+ρ) (hJ ⟨hlo,le_rfl⟩)
    have h2 := hkab (a-ρ) (hJ ⟨le_rfl,hlo⟩)
    linarith [le_abs_self (k (b+ρ)), neg_abs_le (k (a-ρ))]
  have hh := integral_convex_derivative_bound hab hρ hDi hk hpoint hB'
  convert hh using 1 <;> first | rfl | ring

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ReservoirVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

omit [MeasurableSpace X] in
theorem correctedPerturbScore_bound {L n : ℕ} (T : KernelTower Ω L) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (D E : Fin n → FinitePath Ω L → ℝ)
    (hD : ∀ q y, |D q y| ≤ 1) (hE : ∀ q y, |E q y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    |correctedPerturbScore T m base D E t u| ≤ 3*n := by
  unfold correctedPerturbScore
  have h1 := (law L (tilt L T m (perturbLog base D E t u))).abs_expect_le
    (perturbScore_bound D E hD hE ht hu)
  have h3 : |4*(n:ℝ)*u| ≤ (n : ℝ) := by
    rw [abs_mul,abs_of_nonneg (by positivity)]
    nlinarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  have h4 := abs_add_le
    ((law L (tilt L T m (perturbLog base D E t u))).expect (perturbScore D E t u)) (4*n*u)
  linarith

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

theorem familyPoisson_count_variance :
    variance (fun z : Sigma X => (z.1 : ℝ)) (familyLaw (poissonMeasure r) ν) = r := by
  rw [variance_eq_integral (familyPoisson_count_memLp ν r).aemeasurable,
    familyPoisson_count_mean]
  rw [integral_familyLaw (poissonMeasure r) ν (fun n _ => ((n : ℝ)-r)^2)
    (fun _ => measurable_const) ((familyPoisson_count_memLp ν r).sub (memLp_const (r : ℝ))).integrable_sq]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,poisson_variance]

theorem familyPoisson_count_deviation :
    (∫ z : Sigma X, |(z.1 : ℝ)-r| ∂familyLaw (poissonMeasure r) ν) ≤ Real.sqrt r := by
  have h := integral_deviation_le_sqrt_variance (familyLaw (poissonMeasure r) ν)
    (familyPoisson_count_memLp ν r)
  rwa [familyPoisson_count_mean,familyPoisson_count_variance] at h

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem rootDeviation_nonneg (f : X → ℝ) : 0 ≤ rootDeviation μ f :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem rootDeviation_add_le {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    rootDeviation μ (f+g) ≤ rootDeviation μ f+rootDeviation μ g := by
  unfold rootDeviation
  simp only [Pi.add_apply]
  rw [integral_add hf hg]
  have hi := integral_mono ((hf.add hg).sub (integrable_const _)).abs
    (((hf.sub (integrable_const _)).abs).add ((hg.sub (integrable_const _)).abs))
    (fun x => (show |f x+g x-((∫ y, f y ∂μ)+(∫ y, g y ∂μ))| ≤
      |f x-(∫ y, f y ∂μ)|+|g x-(∫ y, g y ∂μ)| by
        have heq : f x+g x-((∫ y, f y ∂μ)+(∫ y, g y ∂μ)) =
            (f x-(∫ y, f y ∂μ))+(g x-(∫ y, g y ∂μ)) := by ring
        rw [heq]
        exact abs_add_le _ _))
  have hr := integral_add (hf.sub (integrable_const (∫ y, f y ∂μ))).abs
    (hg.sub (integrable_const (∫ y, g y ∂μ))).abs
  dsimp only [Pi.add_apply,Pi.sub_apply] at hr hi
  rw [hr] at hi
  exact hi

omit [IsProbabilityMeasure μ] in
theorem rootDeviation_smul (c : ℝ) (f : X → ℝ) :
    rootDeviation μ (fun x => c*f x) = |c| * rootDeviation μ f := by
  simp only [rootDeviation,integral_const_mul,← mul_sub,abs_mul]

theorem rootDeviation_sub_le {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    rootDeviation μ (f-g) ≤ rootDeviation μ f+rootDeviation μ g := by
  have h := rootDeviation_add_le μ hf (hg.const_mul (-1))
  rw [rootDeviation_smul] at h
  have heq : f-g = f+(fun x => (-1:ℝ)*g x) := by
    ext x
    simp [sub_eq_add_neg]
  rw [heq]
  simpa only [abs_neg,abs_one,one_mul] using h

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem measurable_rootDeviation {G : X → ℝ → ℝ}
    (hG : Measurable (fun z : X × ℝ => G z.1 z.2)) :
    Measurable (fun u => rootDeviation μ (fun x => G x u)) := by
  have hk : Measurable (fun u => ∫ x, G x u ∂μ) :=
    (hG.stronglyMeasurable.integral_prod_left').measurable
  exact ((hG.sub (hk.comp measurable_snd)).abs.stronglyMeasurable.integral_prod_left').measurable

theorem rootDeviation_bound {f B : X → ℝ} (hf : Measurable f)
    (hB : Integrable B μ) (hb : ∀ x, |f x| ≤ B x) :
    rootDeviation μ f ≤ 2*(∫ x, B x ∂μ) := by
  have hi : Integrable f μ := hB.mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  have hh := integral_mono ((hi.sub (integrable_const _)).abs)
    (hB.add (integrable_const |∫ x, f x ∂μ|))
      (fun x => (abs_sub _ _).trans (add_le_add (hb x) le_rfl))
  simp only [Pi.add_apply,integral_add hB (integrable_const _),integral_const,
    probReal_univ,smul_eq_mul,one_mul] at hh
  have hav : |∫ x, f x ∂μ| ≤ ∫ x, B x ∂μ :=
    (abs_integral_le_integral_abs).trans (integral_mono hi.abs hB hb)
  simp only [Pi.sub_apply] at hh
  dsimp only [rootDeviation]
  linarith

theorem intervalIntegrable_rootDeviation {G : X → ℝ → ℝ}
    (hG : Measurable (fun z : X × ℝ => G z.1 z.2)) {B : X → ℝ}
    (hB : Integrable B μ) {a b : ℝ} (hab : a ≤ b)
    (hb : ∀ x u, u ∈ Icc a b → |G x u| ≤ B x) :
    IntervalIntegrable (fun u => rootDeviation μ (fun x => G x u)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply Measure.integrableOn_of_bounded
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measurable_rootDeviation μ hG).aestronglyMeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro u hu
  rw [Real.norm_eq_abs,abs_of_nonneg (rootDeviation_nonneg μ _)]
  exact rootDeviation_bound μ (hG.comp (measurable_id.prodMk measurable_const)) hB
    (fun x => hb x u ⟨hu.1.le,hu.2⟩)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_HeterogeneousMarks
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

variable {k L : ℕ}

/-- Typewise log-factor errors sum on the actual root list. -/
theorem root_factor_stability (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor factor' : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (C : I → ℝ) (hC : ∀ i x y, |Real.log (factor i x y) - Real.log (factor' i x y)| ≤ C i) :
    |root T Q m base roots factor - root T Q m base roots factor'| ≤ ∑ q, C (roots q) := by
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simp only [logWeight, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun q _ => hC _ _ _))

end DilutedSpinGlass.HeterogeneousMarks

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
variable {k L : ℕ}

/-- The complete independent row can be integrated as a single finite mark.
Its dimension depends on the realized labels, never on a deterministic cutoff. -/
theorem tower_eq_prod (roots : Fin k → I) (L : ℕ) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    tower roots L T Q = KernelTower.prod L T
      (markPrior L (fun d => FiniteLaw.pi (fun j => Q (roots j) d))) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · rfl
    · funext y
      exact ih (T.2 y.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_eq_fst (roots : Fin k → I)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    physical roots L y = KernelTower.pathFst L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical roots L y.2) = (y.1.1, KernelTower.pathFst L y.2)
    rw [ih]

/-- All unused finite priors integrate out, exactly, even if their dimension
varies over the full countable type list. -/
theorem root_one (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin k → I) :
    root T Q m base roots (fun _ _ _ => 1) = KernelTower.backwardLog L T m base := by
  unfold root
  have heq : logWeight (A := A) base roots (fun _ _ _ => 1) =
      base ∘ KernelTower.pathFst L := by
    funext y
    simp only [logWeight, Real.log_one, Finset.sum_const_zero, add_zero,
      physical_eq_fst, Function.comp_apply]
  rw [heq, tower_eq_prod]
  exact KernelTower.backwardLog_prod_fst L T _ m base

/-- The pathwise perturbation cost is additive over all realized labels. -/
theorem root_base_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (C : I → ℝ) (hC : ∀ i x y, |Real.log (factor i x y)| ≤ C i) :
    |root T Q m base roots factor - KernelTower.backwardLog L T m base| ≤
      ∑ q, C (roots q) := by
  rw [← root_one T Q m base roots]
  exact root_factor_stability T Q m hm base roots factor (fun _ _ _ => 1) C
    (fun i x y => by simpa only [Real.log_one, sub_zero] using hC i x y)

/-- No lower bound on a type's intensity occurs in this global domination. -/
theorem abs_root_le (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hC : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base roots factor| ≤ |KernelTower.backwardLog L T m base| + C*k := by
  have h := root_base_bound T Q m hm base roots factor (fun _ => C) hC
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have ht := abs_add_le (root T Q m base roots factor - KernelTower.backwardLog L T m base)
    (KernelTower.backwardLog L T m base)
  rw [sub_add_cancel] at ht
  linarith

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_AnchorExtension
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
@[simp] theorem tilt_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ j, m j ≠ 0) (c : ℝ) : tilt n T m (fun _ => c) = T := by
  induction n with
  | zero =>
    change () = T
    cases T
    rfl
  | succ n ih =>
    simp only [tilt, backwardLog_const n _ _ (fun j => hm j.succ),
      FiniteLaw.tilt_const, ih _ _ (fun j => hm j.succ)]
    cases T
    rfl
end DilutedSpinGlass.KernelTower

open Filter Set
open scoped Topology BigOperators

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UniformIndexCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {Ω I X : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace X] {L : ℕ}

theorem root_uniform_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j) (base : FinitePath Ω L → ℝ)
    {n : ℕ} (roots : Fin n → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {B C : ℝ}
    (hb : ∀ y, |base y| ≤ B) (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base roots factor| ≤ B+C*n := by
  have hh := KernelTower.backwardLog_stability L T m hm
    (f := base) (g := fun _ => 0) (by simpa only [sub_zero] using hb)
  rw [KernelTower.backwardLog_const L T m (fun j => ne_of_gt (hm j)) 0, sub_zero] at hh
  exact (abs_root_le T Q m hm base roots factor hf).trans (add_le_add hh le_rfl)

theorem measurable_root (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (factor : X → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y))
    (hf : ∀ i y z, Measurable (fun x => factor x i y z)) :
    Measurable (fun x => root T Q m (base x) roots (factor x)) := by
  apply KernelTower.measurable_backwardLog
  intro y
  exact (hb _).add (Finset.measurable_sum _ (fun j _ => (hf _ _ _).log))

theorem measurable_root_base [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y))
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (n : ℕ) :
    Measurable (fun z : X × RootPath I n => root T Q m (base z.1) (rootArray n z.2) factor) := by
  apply measurable_from_prod_countable_left
  intro roots
  exact measurable_root T Q m base (rootArray n roots) (fun _ => factor) hb
    (fun _ _ _ => measurable_const)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_JointRootLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}

theorem measurable_packRoot
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2)) :
    Measurable (packRoot F) := by
  have hn (k : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × Sigma (RootPath I) =>
      F z.1.1 k z.1.2 z.2.1 z.2.2) := measurable_prodSigma (f := fun (z : RootPath Y M × RootPath X k) n y => F z.1 k z.2 n y) (hF k)
  have hk : Measurable (fun z : (RootPath Y M × Sigma (RootPath I)) × Sigma (RootPath X) =>
      F z.1.1 z.2.1 z.2.2 z.1.2.1 z.1.2.2) :=
    measurable_prodSigma (f := fun (z : RootPath Y M × Sigma (RootPath I)) k x => F z.1 k x z.2.1 z.2.2) (fun k => (hn k).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  exact hk.comp ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

theorem fullRoot_memLp_linear
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*k+D*n) :
    MemLp (packRoot F) 2 (fullRootLaw ξ μ ν r s) := by
  have hk := ((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).comp_fst
    (compoundRootLaw ν s)).comp_snd (rootLaw M ξ)
  have hn := ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)
  have he : MemLp (fun z : FullRootState Y X I M => B+C*z.2.1.1+D*z.2.2.1) 2
      (fullRootLaw ξ μ ν r s) := (memLp_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' (measurable_packRoot hF).aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs,packRoot] using hb z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2))

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CountedSteps
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

theorem corrected_log_eq (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    KernelTower.correctedPerturbLog (tower roots L T Q) m (otherLog base roots sel fixed)
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u =
      root T Q m base roots (selectedFactor sel fixed D E t u)+2*n*u^2 := by
  rw [KernelTower.correctedPerturbLog,selected_perturbLog_eq]
  rfl

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_JointRootParam
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullCountCorrection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}
variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

theorem fullRoot_count_deviation :
    rootDeviation (fullRootLaw ξ μ ν r s) (fun z : FullRootState Y X I M => (z.2.2.1:ℝ)) ≤ Real.sqrt s := by
  rw [rootDeviation,fullRoot_count_mean]
  change (∫ z, (fun w : Sigma (RootPath X) × Sigma (RootPath I) => |(w.2.1:ℝ)-s|) z.2
    ∂(rootLaw M ξ).prod ((compoundRootLaw μ r).prod (compoundRootLaw ν s))) ≤ _
  rw [integral_fun_snd (fun w : Sigma (RootPath X) × Sigma (RootPath I) => |(w.2.1:ℝ)-s|),
    integral_fun_snd (fun w : Sigma (RootPath I) => |(w.1:ℝ)-s|)]
  simp only [probReal_univ,one_smul]
  exact familyPoisson_count_deviation (fun n => rootLaw n (fun _ => ν)) s

theorem fullRoot_deviation_sub_count {f : FullRootState Y X I M → ℝ}
    (hf : Integrable f (fullRootLaw ξ μ ν r s)) (c : ℝ) :
    rootDeviation (fullRootLaw ξ μ ν r s) (fun z => f z-c*(z.2.2.1:ℝ)) ≤
      rootDeviation (fullRootLaw ξ μ ν r s) f+|c| *Real.sqrt s := by
  have h := rootDeviation_sub_le (fullRootLaw ξ μ ν r s) hf
    (((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul c)
  rw [rootDeviation_smul] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (fullRoot_count_deviation ξ μ ν r s) (abs_nonneg c)))

theorem fullRoot_deviation_sub_count_integral
    {G : FullRootState Y X I M → ℝ → ℝ}
    (hG : Measurable (fun z : FullRootState Y X I M × ℝ => G z.1 z.2))
    {B : FullRootState Y X I M → ℝ} (hB : Integrable B (fullRootLaw ξ μ ν r s))
    {a b : ℝ} (hab : a ≤ b)
    (hb : ∀ z u, u ∈ Icc a b → |G z u| ≤ B z)
    {c : ℝ → ℝ} (hc : Measurable c) (hcb : ∀ u ∈ Icc a b, |c u| ≤ 1) :
    (∫ u in a..b, rootDeviation (fullRootLaw ξ μ ν r s)
      (fun z => G z u-c u*(z.2.2.1:ℝ))) ≤
    (∫ u in a..b, rootDeviation (fullRootLaw ξ μ ν r s) (fun z => G z u)) +
      (b-a)*Real.sqrt s := by
  let P := fullRootLaw ξ μ ν r s
  have hcount : Measurable (fun z : FullRootState Y X I M × ℝ => (z.1.2.2.1:ℝ)) :=
    (measurable_sigmaUncurry (f := fun n (_ : RootPath I n) => (n:ℝ))
      (fun _ => measurable_const)).comp measurable_fst.snd.snd
  have hci := (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hF : Measurable (fun z : FullRootState Y X I M × ℝ => G z.1 z.2-c z.2*(z.1.2.2.1:ℝ)) :=
    hG.sub ((hc.comp measurable_snd).mul hcount)
  have hFi : IntervalIntegrable (fun u => rootDeviation P
      (fun z => G z u-c u*(z.2.2.1:ℝ))) volume a b := by
    apply intervalIntegrable_rootDeviation P hF (hB.add hci) hab
    intro z u hu
    have hn : 0 ≤ (z.2.2.1:ℝ) := Nat.cast_nonneg _
    simpa only [Pi.add_apply] using
      (abs_sub (G z u) (c u*(z.2.2.1:ℝ))).trans
        (add_le_add (hb z u hu) (by rw [abs_mul,abs_of_nonneg hn]; nlinarith [hcb u hu]))
  have hGi := intervalIntegrable_rootDeviation P hG hB hab hb
  have hh := intervalIntegral.integral_mono_on hab hFi (hGi.add intervalIntegrable_const)
    (fun u hu => (fullRoot_deviation_sub_count ξ μ ν r s
      (hB.mono' (hG.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (ae_of_all _ (fun z => by change |G z u| ≤ B z; exact hb z u hu))) (c u)).trans
          (add_le_add le_rfl (show |c u| *Real.sqrt s ≤ Real.sqrt s by
            nlinarith [hcb u hu,Real.sqrt_nonneg (s:ℝ)])))
  simpa only [intervalIntegral.integral_add hGi intervalIntegrable_const,
    intervalIntegral.integral_const,smul_eq_mul] using hh

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SelectedRegularity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullSelectedRegularity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedLog_eq (z : FullRootState Y X I M) (u : ℝ) :
    fullSelectedLog T Q m base sel fixed D E t z u =
      KernelTower.correctedPerturbLog (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
        (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E) t u := by
  rw [corrected_log_eq]
  unfold fullSelectedLog packRoot
  ring

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedScore_eq (z : FullRootState Y X I M) (u : ℝ) :
    fullSelectedScore T Q m base sel fixed D E t z u =
      KernelTower.correctedPerturbScore (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
        (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E) t u := by
  rw [corrected_score_eq]
  rfl

theorem measurable_fullSelectedLog
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) (u : ℝ) :
    Measurable (fun z => fullSelectedLog T Q m base sel fixed D E t z u) := by
  apply measurable_packRoot
  intro k n
  exact (measurable_root_base T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2)
    (hb k) (selectedFactor sel fixed D E t u) n).add measurable_const

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

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullSelectedConcentration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

/-- Concentration of the actual selected corrected score under the full common
reservoir law. The variance estimate is produced from replacement controls,
not a premise. All unselected types keep their original factors and priors. -/
theorem full_selected_corrected_concentration
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (fieldBound : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ fieldBound j)
    {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    let G := fullSelectedScore T Q m base sel fixed D E t
    (∫ u in a..b, (∫ z, |G z u-∫ w, G w u ∂fullRootLaw ξ μ ν r s| ∂fullRootLaw ξ μ ν r s))/(b-a) ≤
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2)/ρ+12*ρ*(s:ℝ)/(b-a) := by
  let F := fullSelectedLog T Q m base sel fixed D E t
  let G := fullSelectedScore T Q m base sel fixed D E t
  have hFeq (z : FullRootState Y X I M) : F z =
      KernelTower.correctedPerturbLog (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m
        (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
        (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E) t :=
    funext (fun u => fullSelectedLog_eq T Q m base sel fixed D E t z u)
  have hu (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) : |u| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [h.1],h.2.le⟩
  have hbsel (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :=
    selectedFactor_log_bound sel fixed D E hf hD hE ht (hu u h)
  have hFm (u : ℝ) : Measurable (fun z => F z u) :=
    measurable_fullSelectedLog T Q m base sel fixed D E t hbmeas u
  have hGm : Measurable (fun z : FullRootState Y X I M × ℝ => G z.1 z.2) :=
    measurable_fullSelectedScore T Q m base sel fixed D E t hbmeas
  have hfc (z : FullRootState Y X I M) : ConvexOn ℝ (Ioo (-(1:ℝ)/4) (1/4)) (F z) := by
    have hh := (KernelTower.correctedPerturbLog_convex
      (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m hm
      (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed)
      (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D)
      (selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E)
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht).subset
      Ioo_subset_Icc_self (convex_Ioo _ _)
    rw [hFeq]
    exact hh
  have hLp (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :
      MemLp (fun z => F z u) 2 (fullRootLaw ξ μ ν r s) := by
    refine fullRoot_memLp_linear ξ μ ν r s
      (F := fun h k x n y => root T Q m (base h k x) (rootArray n y)
        (selectedFactor sel fixed D E t u)+(2*u^2)*n)
      (B := B) (C := C) (D := 1+|2*u^2|) ?_ ?_
    · intro k n
      exact (measurable_root_base T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2)
        (hbmeas k) (selectedFactor sel fixed D E t u) n).add measurable_const
    · intro h' k x n y
      have hh := root_uniform_bound T Q m hm (base h' k x) (rootArray n y)
        (selectedFactor sel fixed D E t u) (hb h' k x) (hbsel u h)
      calc
        _ ≤ |root T Q m (base h' k x) (rootArray n y) (selectedFactor sel fixed D E t u)|+|(2*u^2)*(n:ℝ)| := abs_add_le _ _
        _ ≤ B+C*k+1*n+|2*u^2| *n := by
          rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
          exact add_le_add hh le_rfl
        _ = _ := by ring
  have hbound (z : FullRootState Y X I M) (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :
      |G z u| ≤ 3*(z.2.2.1:ℝ) := by
    rw [show G z u = _ from fullSelectedScore_eq T Q m base sel fixed D E t z u]
    exact KernelTower.correctedPerturbScore_bound _ _ _ _ _
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht (hu u h)
  have hd (z : FullRootState Y X I M) (u : ℝ) (h : u ∈ Ioo (-(1:ℝ)/4) (1/4)) :
      HasDerivAt (F z) (G z u) u := by
    have hp (q : Fin z.2.2.1) (y : FinitePath (Ω × Row (A := A) (rootArray z.2.2.1 z.2.2.2)) L) :
        0 < 1+t*selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel D q y+
          u*selectedCoefficient (rootArray z.2.2.1 z.2.2.2) sel E q y := by
      have hh := KernelTower.perturb_factor_lower _ _
        (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht (hu u h) q y
      linarith
    rw [hFeq,show G z u = _ from fullSelectedScore_eq T Q m base sel fixed D E t z u]
    exact KernelTower.hasDerivAt_correctedPerturbLog (tower (rootArray z.2.2.1 z.2.2.2) L T Q) m (fun j => ne_of_gt (hm j))
        (otherLog (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) sel fixed) _ _ t u hp
  have hv (u : ℝ) (h : u ∈ Icc (a-ρ) (b+ρ)) :
      variance (fun z => F z u) (fullRootLaw ξ μ ν r s) ≤
        3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2 := by
    have hh := variance_actual_root_sat μ ν ξ r s T Q m hm base hbmeas
      (selectedFactor sel fixed D E t u) hC (by norm_num : (0:ℝ) ≤ 1) hb (hbsel u (hJ h))
      hrep hadd fieldBound hfield (2*u^2)
    have hsq := mul_self_le_mul_self (abs_nonneg u) (hu u (hJ h))
    simp only [← pow_two,sq_abs] at hsq
    have hc : |2*u^2| ≤ 1/8 := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith
    have hcc := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ 1+|2*u^2|)
      (show 1+|2*u^2| ≤ 9/8 by linarith)
    have hcoef : 3*(1+|2*u^2|)^2 ≤ 4 := by nlinarith
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hcoef s.coe_nonneg])
  have hh := root_derivative_integral_bound (fullRootLaw ξ μ ν r s)
    isOpen_Ioo (convex_Ioo _ _) hFm hGm hfc hLp
    (((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul 3) hbound hd hab hρ hJ hv
  rw [integral_const_mul,fullRoot_count_mean] at hh
  convert hh using 1 <;> first | rfl | ring

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullSelectedRawConcentration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

/-- The actual selected score, with the auxiliary convex correction removed. -/
theorem full_selected_root_concentration_sat_oai
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (fieldBound : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ fieldBound j)
    {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    let G := fullSelectedRawScore T Q m base sel fixed D E t
    (∫ u in a..b, (∫ z, |G z u-∫ w, G w u ∂fullRootLaw ξ μ ν r s| ∂fullRootLaw ξ μ ν r s))/(b-a) ≤
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2)/ρ+12*ρ*(s:ℝ)/(b-a)+Real.sqrt s := by
  let G := fullSelectedScore T Q m base sel fixed D E t
  let P := fullRootLaw ξ μ ν r s
  have hI : Icc a b ⊆ Ioo (-(1:ℝ)/4) (1/4) := by
    intro u hu
    exact hJ ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hu (u : ℝ) (h : u ∈ Icc a b) : |u| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [(hI h).1],(hI h).2.le⟩
  have hbG (z : FullRootState Y X I M) (u : ℝ) (h : u ∈ Icc a b) :
      |G z u| ≤ 3*(z.2.2.1:ℝ) := by
    rw [show G z u = _ from fullSelectedScore_eq T Q m base sel fixed D E t z u]
    exact KernelTower.correctedPerturbScore_bound _ _ _ _ _
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht (hu u h)
  have hcor := fullRoot_deviation_sub_count_integral ξ μ ν r s
    (measurable_fullSelectedScore T Q m base sel fixed D E t hbmeas)
    (((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul 3)
    hab.le hbG (show Measurable (fun u : ℝ => 4*u) from measurable_const.mul measurable_id)
    (fun u h => by rw [abs_mul]; norm_num; linarith [hu u h])
  have hmain := full_selected_corrected_concentration μ ν ξ r s T Q m hm base hbmeas
    sel fixed D E hC hb hf hD hE hrep hadd fieldBound hfield ht hab hρ hJ
  dsimp only at hmain ⊢
  change (∫ u in a..b, rootDeviation P (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u))/(b-a) ≤ _
  simp_rw [fullSelectedRawScore_eq]
  have hh := div_le_div_of_nonneg_right hcor (sub_pos.mpr hab).le
  rw [add_div,mul_div_cancel_left₀ _ (ne_of_gt (sub_pos.mpr hab))] at hh
  exact hh.trans (add_le_add hmain le_rfl)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.HeterogeneousMarks.full_selected_root_concentration_sat_oai := @OAI.DilutedSpinGlass.HeterogeneousMarks.full_selected_root_concentration_sat_oai
