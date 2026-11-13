-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_fixed_order_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:40:49.817862+00:00
-- url     : https://prove2.me/submissions/d4d950cc-ee52-4998-8e7b-cfa7cb88c51b

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_anchored_actual_step

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CorrectionScaleAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scale arithmetic in the normalized metric-error estimate. -/
noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

lemma scale_quotient_product {t : ℝ} (ht : 0 < t) (a b c : ℝ) :
    (t ^ a * t ^ b) / t ^ c = t ^ (a + b - c) := by
  rw [← Real.rpow_add ht, Real.rpow_sub ht]

lemma scale_ratio_power {t : ℝ} (ht : 0 < t) (a b c d e : ℝ) :
    (t ^ a * (t ^ b / t ^ c) ^ d) / (t ^ e) ^ (2 : ℕ) =
      t ^ (a + (b - c) * d - 2 * e) := by
  rw [← Real.rpow_sub ht, ← Real.rpow_mul ht.le]
  rw [← Real.rpow_natCast (t ^ e) 2, ← Real.rpow_mul ht.le]
  rw [scale_quotient_product ht]
  congr 1
  ring

lemma scale_ratio_power_linear {t : ℝ} (ht : 0 < t) (a b d e : ℝ) :
    (t ^ a * (t ^ b / t) ^ d) / (t ^ e) ^ (2 : ℕ) =
      t ^ (a + (b - 1) * d - 2 * e) := by
  simpa only [Real.rpow_one] using scale_ratio_power ht a b 1 d e

lemma scale_cubic_quotient {t : ℝ} (ht : 0 < t) (a b c : ℝ) :
    ((t ^ a) ^ (3 : ℕ) / t ^ b) / (t ^ c) ^ (2 : ℕ) =
      t ^ (3 * a - b - 2 * c) := by
  rw [← Real.rpow_natCast (t ^ a) 3, ← Real.rpow_mul ht.le]
  rw [← Real.rpow_natCast (t ^ c) 2, ← Real.rpow_mul ht.le]
  rw [← Real.rpow_sub ht, ← Real.rpow_sub ht]
  congr 1
  ring

/-- The six exponents remain above the common exponent used in the
all-order recurrence, including the smaller next-block amplitude. -/
theorem error_exponents_ge_common {k : ℝ} (hk : 10 ≤ k) :
    (1 / 5 : ℝ) ≤ (13 * k + 8) / 5 ∧
    (1 / 5 : ℝ) ≤ (3 * k - 18) / 5 ∧
    (1 / 5 : ℝ) ≤ (18 * k + 8) / 5 ∧
    (1 / 5 : ℝ) ≤ (38 * k + 28) / 5 ∧
    (1 / 5 : ℝ) ≤ (13 * k + 8) / 5 ∧
    (1 / 5 : ℝ) ≤ (33 * k + 28) / 5 := by
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> [linarith; skip]
  constructor <;> linarith

/-- Exact normalization of the small-mode error term. -/
theorem normalized_mode_scale {t : ℝ} (ht : 0 < t) (k : ℝ) :
    (t ^ k * (t ^ (6 / 5 : ℝ) / t ^ (11 / 10 : ℝ)) ^ (40 * (k + 1))) /
      (t ^ ((6 / 5 : ℝ) * (k + 1))) ^ (2 : ℕ) = t ^ ((13 * k + 8) / 5) := by
  rw [scale_ratio_power ht]
  congr 1
  ring

/-- Exact normalization of the cubic error term. -/
theorem normalized_cubic_scale {t : ℝ} (ht : 0 < t) (k : ℝ) :
    ((t ^ k) ^ (3 : ℕ) / t ^ (6 / 5 : ℝ)) /
      (t ^ ((6 / 5 : ℝ) * (k + 1))) ^ (2 : ℕ) = t ^ ((3 * k - 18) / 5) := by
  rw [scale_cubic_quotient ht]
  congr 1
  ring

/-- The two powers in the smoothing defect, before their coefficients. -/
theorem normalized_defect_tail_scales {t : ℝ} (ht : 0 < t) (k : ℝ) :
    ((t ^ k) ^ (2 : ℕ) * (t ^ (11 / 10 : ℝ) / t) ^ (40 * (k + 1))) /
        (t ^ ((6 / 5 : ℝ) * (k + 1))) ^ (2 : ℕ) = t ^ ((18 * k + 8) / 5) ∧
    ((t ^ k) ^ (2 : ℕ) * (t ^ (6 / 5 : ℝ) / t) ^ (40 * (k + 1))) /
        (t ^ ((6 / 5 : ℝ) * (k + 1))) ^ (2 : ℕ) = t ^ ((38 * k + 28) / 5) := by
  rw [← Real.rpow_natCast (t ^ k) 2, ← Real.rpow_mul ht.le]
  constructor
  · rw [scale_ratio_power_linear ht]
    congr 1
    ring
  · rw [scale_ratio_power_linear ht]
    congr 1
    ring

/-- The two powers in the bilinear cross term, before their coefficients. -/
theorem normalized_cross_tail_scales {t : ℝ} (ht : 0 < t) (k : ℝ) :
    (t ^ k * (t ^ (11 / 10 : ℝ) / t) ^ (40 * (k + 1))) /
        (t ^ ((6 / 5 : ℝ) * (k + 1))) ^ (2 : ℕ) = t ^ ((13 * k + 8) / 5) ∧
    (t ^ k * (t ^ (6 / 5 : ℝ) / t) ^ (40 * (k + 1))) /
        (t ^ ((6 / 5 : ℝ) * (k + 1))) ^ (2 : ℕ) = t ^ ((33 * k + 28) / 5) := by
  constructor
  · rw [scale_ratio_power_linear ht]
    congr 1
    ring
  · rw [scale_ratio_power_linear ht]
    congr 1
    ring

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CorrectionErrorEnvelope
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The six normalized errors satisfy the common all-order recurrence bound. -/
noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

/-- A common envelope for the six powers in the exact-correction error table.
The coefficients of both high-derivative terms remain linear. -/
theorem normalized_error_envelope {t k B C P Q R : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : 10 ≤ k)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) :
    P * (B * t ^ ((18 * k + 8) / 5) + C * t ^ ((38 * k + 28) / 5)) +
      Q * (t ^ ((13 * k + 8) / 5) + t ^ ((3 * k - 18) / 5)) +
      R * (B * t ^ ((13 * k + 8) / 5) + C * t ^ ((33 * k + 28) / 5)) ≤
      (P + 2 * Q + R) * (1 + B + C) * t ^ (1 / 5 : ℝ) := by
  obtain ⟨h1, h2, h3, h4, _, h6⟩ := error_exponents_ge_common hk
  have b1 := Real.rpow_le_rpow_of_exponent_ge ht ht1 h1
  have b2 := Real.rpow_le_rpow_of_exponent_ge ht ht1 h2
  have b3 := Real.rpow_le_rpow_of_exponent_ge ht ht1 h3
  have b4 := Real.rpow_le_rpow_of_exponent_ge ht ht1 h4
  have b6 := Real.rpow_le_rpow_of_exponent_ge ht ht1 h6
  calc
    _ ≤ P * (B * t ^ (1 / 5 : ℝ) + C * t ^ (1 / 5 : ℝ)) +
        Q * (t ^ (1 / 5 : ℝ) + t ^ (1 / 5 : ℝ)) +
        R * (B * t ^ (1 / 5 : ℝ) + C * t ^ (1 / 5 : ℝ)) := by gcongr
    _ = (P * (B + C) + 2 * Q + R * (B + C)) * t ^ (1 / 5 : ℝ) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
      nlinarith [mul_nonneg hQ hB, mul_nonneg hQ hC]

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingFirstMoment
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-moment control of the error of the actual convolution operator. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

lemma firstMoment_nonneg (K : Base → ℝ) : 0 ≤ firstMoment K :=
  integral_nonneg fun _x => mul_nonneg (norm_nonneg _) (norm_nonneg _)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteSmootherApproximation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-order smoother approximates using only the displayed finite
number of input derivatives. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma approximationConstant_nonneg (r j : ℕ) : 0 ≤ approximationConstant r j :=
  mul_nonneg
    (pow_nonneg (add_nonneg zero_le_one (integral_nonneg fun _ => norm_nonneg _)) _)
    (pow_nonneg (firstMoment_nonneg _) _)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PositivePolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit normal-frame budgets have fixed polynomial growth. This
keeps their exponents independent of multiplicative input constants. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma polynomialBound_const {c : ℝ} (hc : 0 ≤ c) : HasPolynomialBound (fun _ => c) := by
  exact ⟨0,max 1 c,le_max_left _ _,fun x _ => ⟨hc,by
    simp only [pow_zero,mul_one]
    exact le_max_right (1 : ℝ) c⟩⟩

lemma polynomialBound_id : HasPolynomialBound (fun x => x) := by
  exact ⟨1,1,le_rfl,fun x hx => ⟨zero_le_one.trans hx,by simp⟩⟩

lemma HasPolynomialBound.add {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x+g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C+D,by linarith,?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨add_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x+g x ≤ C*x^d+D*x^e := add_le_add hf'.2 hg'.2
    _ ≤ C*x^(d+e)+D*x^(d+e) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_right d e)) (zero_le_one.trans hC))
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_left e d)) (zero_le_one.trans hD))
    _ = (C+D)*x^(d+e) := by ring

lemma HasPolynomialBound.mul {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x*g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C*D,by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)],?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨mul_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x*g x ≤ (C*x^d)*(D*x^e) := mul_le_mul hf'.2 hg'.2 hg'.1
      (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hx) _))
    _ = (C*D)*x^(d+e) := by rw [pow_add]; ring

lemma HasPolynomialBound.pow {f : ℝ → ℝ} (hf : HasPolynomialBound f) (n : ℕ) :
    HasPolynomialBound (fun x => (f x)^n) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  refine ⟨d*n,C^n,one_le_pow₀ hC,?_⟩
  intro x hx
  have hh := hf x hx
  refine ⟨pow_nonneg hh.1 _,?_⟩
  calc
    (f x)^n ≤ (C*x^d)^n := pow_le_pow_left₀ hh.1 hh.2 _
    _ = C^n*x^(d*n) := by rw [mul_pow,pow_mul]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialBudgetAlgebra
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite composition and inverse-scale evaluation of the polynomial
budgets in the correction construction. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.of_le {f g : ℝ → ℝ} (hg : HasPolynomialBound g)
    (h0 : ∀ x, 1 ≤ x → 0 ≤ f x) (hle : ∀ x, 1 ≤ x → f x ≤ g x) :
    HasPolynomialBound f := by
  obtain ⟨d,C,hC,hg⟩ := hg
  exact ⟨d,C,hC,fun x hx => ⟨h0 x hx,(hle x hx).trans (hg x hx).2⟩⟩

lemma HasPolynomialBound.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, HasPolynomialBound (f i)) :
    HasPolynomialBound (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polynomialBound_const (show (0:ℝ) ≤ 0 by rfl)
  | @insert i s hi ih =>
    have h := (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanIteration
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth of the actual finite mean iteration and of the
finite value budget appearing in its explicit smallness threshold. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.nonneg {f : ℝ → ℝ} (hf : HasPolynomialBound f)
    {x : ℝ} (hx : 1 ≤ x) : 0 ≤ f x := by
  obtain ⟨_,_,_,h⟩ := hf
  exact (h x hx).1

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExplicitPowerThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit integer-power thresholds for the finitely many real powers
used by the first correction block. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

theorem powerThreshold_spec {n : ℕ} (hn : 0 < n) {c b p : ℝ}
    (hc : 0 ≤ c) (hb : 0 < b) (hp : (n : ℝ)⁻¹ ≤ p) :
    0 < powerThreshold n c b ∧ powerThreshold n c b ≤ 1 ∧
    ∀ t : ℝ, 0 < t → t < powerThreshold n c b → c*t^p < b := by
  let q := min 1 (b/(c+1))
  have hq : 0 < q := lt_min zero_lt_one (div_pos hb (by linarith))
  have hq1 : q ≤ 1 := min_le_left _ _
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ⟨pow_pos hq n, pow_le_one₀ hq.le hq1,?_⟩
  intro t ht hsmall
  have ht1 : t ≤ 1 := hsmall.le.trans (pow_le_one₀ hq.le hq1)
  have hroot : t^((n : ℝ)⁻¹) < q := by
    have h := Real.rpow_lt_rpow ht.le hsmall (inv_pos.mpr hn')
    change t^((n : ℝ)⁻¹) < (q^n)^((n : ℝ)⁻¹) at h
    rwa [← Real.rpow_natCast, Real.rpow_rpow_inv hq.le hn'.ne'] at h
  have htp : t^p < q :=
    (Real.rpow_le_rpow_of_exponent_ge ht ht1 hp).trans_lt hroot
  have hqb : (c+1)*q ≤ b := by
    have h := (le_div_iff₀ (show 0 < c+1 by linarith)).mp
      (show q ≤ b/(c+1) from min_le_right _ _)
    nlinarith
  calc
    c*t^p ≤ (c+1)*t^p := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg ht.le _)
    _ < (c+1)*q := mul_lt_mul_of_pos_left htp (by linarith)
    _ ≤ b := hqb

/-- An upper bound on the reciprocal threshold follows from upper bounds
on the coefficient and reciprocal margin. -/
lemma powerThreshold_inverse_le {n : ℕ} {c b C B : ℝ}
    (hc : 0 ≤ c) (hb : 0 < b) (hC : c ≤ C) (hB : b⁻¹ ≤ B) :
    (powerThreshold n c b)⁻¹ ≤ (1+(C+1)*B)^n := by
  have hC0 : 0 ≤ C := hc.trans hC
  have hB0 : 0 ≤ B := (inv_pos.mpr hb).le.trans hB
  have hq : 0 < min 1 (b/(c+1)) := lt_min zero_lt_one (div_pos hb (by linarith))
  have hi : (min 1 (b/(c+1)))⁻¹ ≤ 1+(C+1)*B := by
    have hh : (c+1)/b ≤ (C+1)*B := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (by linarith) hB (inv_nonneg.mpr hb.le) (by linarith)
    by_cases hle : b/(c+1) ≤ 1
    · rw [min_eq_right hle, inv_div]
      linarith
    · rw [min_eq_left (le_of_not_ge hle), inv_one]
      nlinarith
  rw [powerThreshold, ← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr hq.le) hi n

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPowerThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial reciprocal control for explicit positive-power thresholds.
No compactness choice enters the numerical threshold. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection
open RealModes

theorem powerThreshold_inverse_polynomial (n : ℕ) (c b C B : ℝ → ℝ)
    (hC : HasPolynomialBound C) (hB : HasPolynomialBound B)
    (hc : ∀ x, 1 ≤ x → 0 ≤ c x) (hb : ∀ x, 1 ≤ x → 0 < b x)
    (hcC : ∀ x, 1 ≤ x → c x ≤ C x)
    (hbB : ∀ x, 1 ≤ x → (b x)⁻¹ ≤ B x) :
    HasPolynomialBound (fun x => (powerThreshold n (c x) (b x))⁻¹) := by
  apply HasPolynomialBound.of_le
    (((polynomialBound_const zero_le_one).add
      ((hC.add (polynomialBound_const zero_le_one)).mul hB)).pow n)
  · intro x hx
    apply inv_nonneg.mpr
    unfold powerThreshold
    exact pow_nonneg (le_min zero_le_one (div_nonneg (hb x hx).le (by linarith [hc x hx]))) _
  · intro x hx
    exact powerThreshold_inverse_le (hc x hx) (hb x hx) (hcC x hx) (hbB x hx)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExplicitFixedOrderThreshold
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-order scale conditions with one explicitly specified
threshold. Its reciprocal is polynomial in the finite numerical budgets. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.ExactCorrection

theorem fixedOrderThreshold_spec (k : ℕ) (hk : 10 ≤ k)
    (ρ a η D B K : ℝ) (hρ : 0 < ρ) (ha : 0 < a) (hη : 0 < η)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hK : 0 ≤ K) (C : ℕ → ℝ) :
    0 < fixedOrderThreshold k ρ a η D B K C ∧
    fixedOrderThreshold k ρ a η D B K C ≤ 1 ∧
    ∀ t : ℝ, 0 < t → t < fixedOrderThreshold k ρ a η D B K C →
    ∀ j : ℕ, k ≤ j → j ≤ k+1 →
      t^(6/5 : ℝ)/t^(11/10 : ℝ) ≤ η ∧
      D*B*(t^(11/10 : ℝ)/t)^(40*(k+1)) ≤ min (ρ/4) (a/8) ∧
      (t^((6/5 : ℝ)*(j : ℝ))/t^(k : ℝ))^(2 : ℕ)*K ≤ a/8 ∧
      (∀ m ≤ k/2, C m*(t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^m ≤ ρ*t) ∧
      t^((6/5 : ℝ)*(j : ℝ)) ≤ t^(k : ℝ) ∧
      t^((6/5 : ℝ)*((k : ℝ)+1)) ≤ t^((6/5 : ℝ)*(j : ℝ)) := by
  let M := 1+∑ m ∈ Finset.range (k/2+1), |C m|
  let S := fixedOrderNumericalBudget k D B K C
  let b := min η (min (ρ/4) (a/8))
  have hsum : 0 ≤ ∑ m ∈ Finset.range (k/2+1), |C m| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hDB := mul_nonneg hD hB
  have hS : 0 ≤ S := by dsimp [S, fixedOrderNumericalBudget] <;> linarith
  have hS1 : 1 ≤ S := by dsimp [S, fixedOrderNumericalBudget] <;> linarith
  have hSDB : D*B ≤ S := by dsimp [S, fixedOrderNumericalBudget] <;> linarith
  have hSK : K ≤ S := by dsimp [S, fixedOrderNumericalBudget] <;> linarith
  have hSM : M ≤ S := by dsimp [S, fixedOrderNumericalBudget, M] <;> linarith
  have hb : 0 < b := lt_min hη (lt_min (by positivity) (by positivity))
  have hε := powerThreshold_spec (n := 10) (by decide) hS hb
    (show ((10 : ℕ) : ℝ)⁻¹ ≤ (1/10 : ℝ) by norm_num)
  refine ⟨hε.1,hε.2.1,?_⟩
  intro t ht htε j hkj hjk
  have ht1 : t ≤ 1 := htε.le.trans hε.2.1
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hkj' : (k : ℝ) ≤ j := by exact_mod_cast hkj
  have hjk' : (j : ℝ) ≤ (k : ℝ)+1 := by exact_mod_cast hjk
  have hbound (c p : ℝ) (hc : c ≤ S) (hp : (1/10 : ℝ) ≤ p) : c*t^p ≤ b := by
    have hh := (powerThreshold_spec (n := 10) (by decide) hS hb
      (show ((10 : ℕ) : ℝ)⁻¹ ≤ p by norm_num; exact hp)).2.2 t ht htε
    exact (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg ht.le _)).trans hh.le
  have hr : t^(6/5 : ℝ)/t^(11/10 : ℝ) = t^(1/10 : ℝ) := by
    rw [← Real.rpow_sub ht]
    norm_num
  have hs : t^(11/10 : ℝ)/t = t^(1/10 : ℝ) := by
    conv_lhs => rhs; rw [← Real.rpow_one t]
    rw [← Real.rpow_sub ht]
    norm_num
  have hpow : (t^(11/10 : ℝ)/t)^(40*(k+1)) = t^(4*((k : ℝ)+1)) := by
    rw [hs,← Real.rpow_natCast,← Real.rpow_mul ht.le]
    congr 1
    push_cast
    ring
  have hδ : (t^((6/5 : ℝ)*(j : ℝ))/t^(k : ℝ))^(2 : ℕ) =
      t^((12/5 : ℝ)*(j : ℝ)-2*(k : ℝ)) := by
    rw [← Real.rpow_sub ht,← Real.rpow_natCast,← Real.rpow_mul ht.le]
    congr 1
    ring
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hr]
    have hh := hbound 1 (1/10) hS1 le_rfl
    simpa only [one_mul] using hh.trans (min_le_left _ _)
  · rw [hpow]
    exact (hbound (D*B) _ hSDB (by linarith)).trans (min_le_right _ _)
  · rw [hδ,mul_comm]
    exact (hbound K _ hSK (by linarith)).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  · intro m hm
    have hCM : C m ≤ M := by
      have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (k/2+1)) => abs_nonneg (C j))
        (Finset.mem_range.mpr (by omega : m < k/2+1))
      have hc := le_abs_self (C m)
      dsimp [M]
      linarith
    let e : ℝ := (k : ℝ)+(1/5 : ℝ)-(6/5 : ℝ)*(m : ℝ)
    have hmk : 2*m ≤ k := by omega
    have hmk' : (2 : ℝ)*(m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have he : (1/10 : ℝ) ≤ e := by dsimp [e] <;> linarith
    have heρ : C m*t^e ≤ ρ := (hbound (C m) e (hCM.trans hSM) he).trans (by
      have hbρ : b ≤ ρ/4 := (min_le_right _ _).trans (min_le_left _ _)
      linarith)
    have hratio : (t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^m = t^e*t := by
      rw [← Real.rpow_natCast,← Real.rpow_mul ht.le,scale_quotient_product ht]
      conv_rhs => rhs; rw [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      dsimp [e]
      ring
    calc
      _ = C m*((t^(k : ℝ)*t^(6/5 : ℝ))/(t^(6/5 : ℝ))^m) := by ring
      _ = (C m*t^e)*t := by rw [hratio]; ring
      _ ≤ ρ*t := mul_le_mul_of_nonneg_right heρ ht.le
  · exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFixedOrderThreshold
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At each fixed order, the reciprocal of the scale threshold is
polynomial in the numerical data and reciprocal geometric margins. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.ExactCorrection
open RealModes

theorem fixedOrderNumericalBudget_polynomial (k : ℕ) (D B K : ℝ → ℝ) (C : ℕ → ℝ → ℝ)
    (hD : HasPolynomialBound D) (hB : HasPolynomialBound B) (hK : HasPolynomialBound K)
    (hC : ∀ m, HasPolynomialBound (C m)) :
    HasPolynomialBound (fun x => fixedOrderNumericalBudget k (D x) (B x) (K x) (fun m => C m x)) := by
  have hp := (((polynomialBound_const (show (0 : ℝ) ≤ 2 by norm_num)).add (hD.mul hB)).add hK).add
    (HasPolynomialBound.sum (Finset.range (k/2+1)) C (fun m _ => hC m))
  apply HasPolynomialBound.of_le hp
  · intro x hx
    have hd := hD.nonneg hx
    have hb := hB.nonneg hx
    have hk := hK.nonneg hx
    unfold fixedOrderNumericalBudget
    positivity
  · intro x hx
    have habs : ∀ m, |C m x| = C m x := fun m => abs_of_nonneg ((hC m).nonneg hx)
    simp only [fixedOrderNumericalBudget, habs]
    exact le_rfl

lemma min_inverse_le_add {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (min x y)⁻¹ ≤ x⁻¹+y⁻¹ := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    linarith [inv_nonneg.mpr hy.le]
  · rw [min_eq_right h]
    linarith [inv_nonneg.mpr hx.le]

theorem fixedOrderThreshold_inverse_polynomial (k : ℕ)
    (ρ a η D B K : ℝ → ℝ) (C : ℕ → ℝ → ℝ) (R A H : ℝ → ℝ)
    (hD : HasPolynomialBound D) (hB : HasPolynomialBound B) (hK : HasPolynomialBound K)
    (hC : ∀ m, HasPolynomialBound (C m))
    (hR : HasPolynomialBound R) (hA : HasPolynomialBound A) (hH : HasPolynomialBound H)
    (hρ : ∀ x, 1 ≤ x → 0 < ρ x) (ha : ∀ x, 1 ≤ x → 0 < a x)
    (hη : ∀ x, 1 ≤ x → 0 < η x)
    (hρR : ∀ x, 1 ≤ x → (ρ x)⁻¹ ≤ R x)
    (haA : ∀ x, 1 ≤ x → (a x)⁻¹ ≤ A x)
    (hηH : ∀ x, 1 ≤ x → (η x)⁻¹ ≤ H x) :
    HasPolynomialBound (fun x => (fixedOrderThreshold k (ρ x) (a x) (η x)
      (D x) (B x) (K x) (fun m => C m x))⁻¹) := by
  let S := fun x => fixedOrderNumericalBudget k (D x) (B x) (K x) (fun m => C m x)
  have hS : HasPolynomialBound S := fixedOrderNumericalBudget_polynomial k D B K C hD hB hK hC
  let b := fun x => min (η x) (min (ρ x/4) (a x/8))
  let P := fun x => H x+4*R x+8*A x
  have hP : HasPolynomialBound P := (hH.add
    ((polynomialBound_const (show (0 : ℝ) ≤ 4 by norm_num)).mul hR)).add
      ((polynomialBound_const (show (0 : ℝ) ≤ 8 by norm_num)).mul hA)
  apply powerThreshold_inverse_polynomial 10 S b S P hS hP
    (fun x hx => hS.nonneg hx) (fun x hx => lt_min (hη x hx)
      (lt_min (div_pos (hρ x hx) (by norm_num)) (div_pos (ha x hx) (by norm_num))))
    (fun _ _ => le_rfl)
  intro x hx
  have hρp : 0 < ρ x/4 := div_pos (hρ x hx) (by norm_num)
  have hap : 0 < a x/8 := div_pos (ha x hx) (by norm_num)
  have hρi : (ρ x/4)⁻¹ ≤ 4*R x := by
    rw [inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hρR x hx) (by norm_num)
  have hai : (a x/8)⁻¹ ≤ 8*A x := by
    rw [inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (haA x hx) (by norm_num)
  have hi := min_inverse_le_add (hη x hx) (lt_min hρp hap)
  have hj := min_inverse_le_add hρp hap
  change (min (η x) (min (ρ x/4) (a x/8)))⁻¹ ≤ H x+4*R x+8*A x
  linarith [hηH x hx]

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTailBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-input smoothing-tail estimate at every output order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory WeightedEstimates
open JetPolynomial (Base)

lemma approximationConstant_le_tail {r j : ℕ} (hj : j ≤ r) :
    approximationConstant r j ≤ tailConstant r := by
  have h : approximationConstant r j ≤
      ∑ i ∈ Finset.range (r + 1), approximationConstant r i :=
    Finset.single_le_sum (fun i _ => approximationConstant_nonneg r i)
      (Finset.mem_range.mpr (by omega))
  exact h.trans (le_add_of_nonneg_right (pow_nonneg
    (add_nonneg zero_le_one (integral_nonneg fun _ => norm_nonneg _)) r))

lemma tailConstant_nonneg (r : ℕ) : 0 ≤ tailConstant r :=
  (approximationConstant_nonneg r 0).trans (approximationConstant_le_tail (Nat.zero_le r))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GeometricScaleThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The grid scale-ratio threshold has a polynomial reciprocal. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection
open RealModes

lemma geometricScaleThreshold_pos {a E : ℝ} (ha : 0 < a) (hE : 0 < E)
    (e : ℕ) {x : ℝ} (hx : 1 ≤ x) : 0 < geometricScaleThreshold a E e x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  unfold geometricScaleThreshold
  exact lt_min zero_lt_one (div_pos (by linarith) (by positivity))

theorem geometricScaleThreshold_inverse_polynomial {a E : ℝ} (ha : 0 < a) (hE : 0 < E) (e : ℕ) :
    HasPolynomialBound (fun x => (geometricScaleThreshold a E e x)⁻¹) := by
  have hp : HasPolynomialBound (fun x : ℝ => 1+(4*E/a)*x^e) :=
    (polynomialBound_const zero_le_one).add
      ((polynomialBound_const (by positivity : 0 ≤ 4*E/a)).mul (polynomialBound_id.pow e))
  apply HasPolynomialBound.of_le hp
  · intro x hx
    exact inv_nonneg.mpr (geometricScaleThreshold_pos ha hE e hx).le
  · intro x hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hv : 0 < (a-a/2)/(2*(E*x^e)) := div_pos (by linarith) (by positivity)
    calc
      (geometricScaleThreshold a E e x)⁻¹ ≤ 1+((a-a/2)/(2*(E*x^e)))⁻¹ := by
        simpa only [inv_one,geometricScaleThreshold] using min_inverse_le_add zero_lt_one hv
      _ = 1+(4*E/a)*x^e := by
        rw [inv_div]
        have hhalf : a-a/2 = a/2 := by ring
        rw [hhalf]
        field_simp
        ring

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExactScaleOrdering
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and ordering of the actual scales in each correction step. -/
noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

theorem exact_scale_positive {t : ℝ} (ht : 0 < t) (k : ℕ) :
    0 < t^((6/5 : ℝ)*((k : ℝ)+1)) ∧ 0 < t^(k : ℝ) ∧
      0 < t^(6/5 : ℝ) ∧ 0 < t^(11/10 : ℝ) :=
  ⟨Real.rpow_pos_of_pos ht _,Real.rpow_pos_of_pos ht _,
    Real.rpow_pos_of_pos ht _,Real.rpow_pos_of_pos ht _⟩

theorem exact_scale_order {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) {k : ℕ} (hk : 10 ≤ k) :
    t^((6/5 : ℝ)*((k : ℝ)+1)) ≤ t^(k : ℝ) ∧
      t^(k : ℝ) ≤ t^(6/5 : ℝ) ∧ t^(6/5 : ℝ) ≤ t^(11/10 : ℝ) ∧
      t^(11/10 : ℝ) ≤ t := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith),
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith),
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num),?_⟩
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (show (1 : ℝ) ≤ 11/10 by norm_num)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalizedStepEnvelope
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized one-step error has the six powers in the
correction table, with linear dependence on both input bounds. -/
noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

theorem normalized_step_envelope {t k B C D E U T : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : 10 ≤ k)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hU : 0 ≤ U) (hT : 0 ≤ T) :
    ((t ^ ((6/5 : ℝ)*(k+1))) ^ (2 : ℕ))⁻¹ *
      (((t^k)^(2 : ℕ) + E*U*t^k) * D *
        (B*(t^(11/10 : ℝ)/t)^(40*(k+1)) + C*(t^(6/5 : ℝ)/t)^(40*(k+1))) +
        T*(t^k*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1)) + (t^k)^(3 : ℕ)/t^(6/5 : ℝ))) ≤
      (D+E*U*D+2*T)*(1+B+C)*t^(1/5 : ℝ) := by
  have he : ((t ^ ((6/5 : ℝ)*(k+1))) ^ (2 : ℕ))⁻¹ *
      (((t^k)^(2 : ℕ) + E*U*t^k) * D *
        (B*(t^(11/10 : ℝ)/t)^(40*(k+1)) + C*(t^(6/5 : ℝ)/t)^(40*(k+1))) +
        T*(t^k*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1)) + (t^k)^(3 : ℕ)/t^(6/5 : ℝ))) =
      D * (B * (((t^k)^(2 : ℕ)*(t^(11/10 : ℝ)/t)^(40*(k+1))) /
          (t^((6/5 : ℝ)*(k+1)))^(2 : ℕ)) +
        C * (((t^k)^(2 : ℕ)*(t^(6/5 : ℝ)/t)^(40*(k+1))) /
          (t^((6/5 : ℝ)*(k+1)))^(2 : ℕ))) +
      T * ((t^k*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1))) /
          (t^((6/5 : ℝ)*(k+1)))^(2 : ℕ) +
        ((t^k)^(3 : ℕ)/t^(6/5 : ℝ)) /(t^((6/5 : ℝ)*(k+1)))^(2 : ℕ)) +
      (E*U*D) * (B * ((t^k*(t^(11/10 : ℝ)/t)^(40*(k+1))) /
          (t^((6/5 : ℝ)*(k+1)))^(2 : ℕ)) +
        C * ((t^k*(t^(6/5 : ℝ)/t)^(40*(k+1))) /
          (t^((6/5 : ℝ)*(k+1)))^(2 : ℕ))) := by ring
  rw [he,(normalized_defect_tail_scales ht k).1,(normalized_defect_tail_scales ht k).2,
    normalized_mode_scale ht k,normalized_cubic_scale ht k,
    (normalized_cross_tail_scales ht k).1,(normalized_cross_tail_scales ht k).2]
  calc
    _ ≤ (D+2*T+E*U*D)*(1+B+C)*t^(1/5 : ℝ) :=
      normalized_error_envelope ht ht1 hk hB hC hD hT (mul_nonneg (mul_nonneg hE hU) hD)
    _ = _ := by ring

/-- The same estimate with the integer smoothing order used by the
scheduled correction sequence. -/
theorem normalized_step_envelope_nat {t B C D E U T : ℝ} {k : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : 10 ≤ k)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hU : 0 ≤ U) (hT : 0 ≤ T) :
    ((t ^ ((6/5 : ℝ)*((k : ℝ)+1))) ^ (2 : ℕ))⁻¹ *
      (((t^(k : ℝ))^(2 : ℕ) + E*U*t^(k : ℝ)) * D *
        (B*(t^(11/10 : ℝ)/t)^(40*(k+1)) + C*(t^(6/5 : ℝ)/t)^(40*(k+1))) +
        T*(t^(k : ℝ)*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1)) +
          (t^(k : ℝ))^(3 : ℕ)/t^(6/5 : ℝ))) ≤
      (D+E*U*D+2*T)*(1+B+C)*t^(1/5 : ℝ) := by
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have h := normalized_step_envelope ht ht1 hk' hB hC hD hE hU hT
  simpa only [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using h

/-- The actual finite-mode residual has one extra power of the frequency
ratio, which only improves the same normalized envelope. -/
theorem normalized_step_envelope_nat_succ {t B C D E U T : ℝ} {k : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : 10 ≤ k)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hU : 0 ≤ U) (hT : 0 ≤ T) :
    ((t ^ ((6/5 : ℝ)*((k : ℝ)+1))) ^ (2 : ℕ))⁻¹ *
      (((t^(k : ℝ))^(2 : ℕ) + E*U*t^(k : ℝ)) * D *
        (B*(t^(11/10 : ℝ)/t)^(40*(k+1)) + C*(t^(6/5 : ℝ)/t)^(40*(k+1))) +
        T*(t^(k : ℝ)*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1)+1) +
          (t^(k : ℝ))^(3 : ℕ)/t^(6/5 : ℝ))) ≤
      (D+E*U*D+2*T)*(1+B+C)*t^(1/5 : ℝ) := by
  have hs : 0 < t^(11/10 : ℝ) := Real.rpow_pos_of_pos ht _
  have hratio : 0 ≤ t^(6/5 : ℝ)/t^(11/10 : ℝ) :=
    div_nonneg (Real.rpow_nonneg ht.le _) hs.le
  have hratio1 : t^(6/5 : ℝ)/t^(11/10 : ℝ) ≤ 1 := by
    apply (div_le_one hs).mpr
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  have hp := pow_le_pow_of_le_one hratio hratio1 (Nat.le_succ (40*(k+1)))
  calc
    _ ≤ ((t ^ ((6/5 : ℝ)*((k : ℝ)+1))) ^ (2 : ℕ))⁻¹ *
        (((t^(k : ℝ))^(2 : ℕ) + E*U*t^(k : ℝ)) * D *
          (B*(t^(11/10 : ℝ)/t)^(40*(k+1)) + C*(t^(6/5 : ℝ)/t)^(40*(k+1))) +
          T*(t^(k : ℝ)*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1)) +
            (t^(k : ℝ))^(3 : ℕ)/t^(6/5 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sq_nonneg _))
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hT
      exact add_le_add (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg ht.le _)) le_rfl
    _ ≤ _ := normalized_step_envelope_nat ht ht1 hk hB hC hD hE hU hT

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AnchoredFixedOrderStep
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial fixed-order thresholds for the actual anchored correction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry MetricGoodPhaseData
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredFixedFiberNormed
local instance anchoredFixedFiberSpace_r564a9b_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance anchoredFixedDualAdd_r564a9b_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance anchoredFixedDualSmul_r564a9b_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance anchoredFixedSectionNormed_r564a9b_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance anchoredFixedSectionSpace_r564a9b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem anchored_fixed_order_step_oai (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ z₀ a D : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧
    ∀ k : ℕ, 10 ≤ k → ∀ Budget : ℝ → ℝ, HasPolynomialBound Budget →
    ∃ ε : ℝ → ℝ, ∃ P L : ℕ → ℝ → ℝ,
      HasPolynomialBound (fun x => (ε x)⁻¹) ∧
      (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (L m)) ∧
      (∀ x, 1 ≤ x → 0 < ε x ∧ ε x ≤ 1) ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
    ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
    ∀ t : ℝ, 0 < t → t < ε z⁻¹ → ∀ j : ℕ, k ≤ j → j ≤ k+1 →
      A.InputBound t (40*(k+1)) (Budget z⁻¹) G (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
      A.WeightedBound 1 2 ((z^4/D)/4) (G-F) →
      (∀ x, ‖A.tensorEncode (normalizedTensorDefect g.inner (t^(k : ℝ)) G) x-A.tensorEncode g.inner x‖ ≤ a/8) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound (t^(6/5 : ℝ)) m (P m z⁻¹*(t^(k : ℝ)*t^(6/5 : ℝ))) U) ∧
        (∀ m ≤ k/2, A.WeightedBound 1 m ((z^4/D)*t) U) ∧
        ∀ m C, 0 ≤ C → A.InputBound t m C G (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
          A.TensorWeightedBound (t^(6/5 : ℝ)) m (L m z⁻¹*(1+Budget z⁻¹+C)*t^(1/5 : ℝ))
            (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U)-g.inner) := by
  classical
  obtain ⟨z₀,a,D,K,hz₀,hz₀1,ha,hD,hK,hall⟩ := A.anchored_actual_step g houter R c B b hc hB hb
  refine ⟨z₀,a,D,hz₀,hz₀1,ha,hD,?_⟩
  intro k hk Budget hBudget
  let r := 40*(k+1)
  obtain ⟨T,hT,hr⟩ := hall r
  obtain ⟨e,E,P,Q,Dm,Em,hE,hP,hQ,hDm,hEm,hbuild⟩ := hr r Budget hBudget
  let ρ := fun x : ℝ => 1/(D*x^4)
  let η := ExactCorrection.geometricScaleThreshold a E e
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hρ (x : ℝ) (hx : 1 ≤ x) : 0 < ρ x := by
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    dsimp [ρ] <;> positivity
  have hη (x : ℝ) (hx : 1 ≤ x) : 0 < η x := ExactCorrection.geometricScaleThreshold_pos ha hE0 e hx
  let ε := fun x => ExactCorrection.fixedOrderThreshold k (ρ x) a (η x) T (Budget x) K (fun m => P m x)
  have hε (x : ℝ) (hx : 1 ≤ x) := ExactCorrection.fixedOrderThreshold_spec k hk
    (ρ x) a (η x) T (Budget x) K (hρ x hx) ha (hη x hx) hT (hBudget.nonneg hx) hK (fun m => P m x)
  have hρinv : HasPolynomialBound (fun x => (ρ x)⁻¹) := by
    have hp := (polynomialBound_const hD0.le).mul (polynomialBound_id.pow 4)
    simpa only [ρ,one_div,inv_inv] using hp
  have hηinv : HasPolynomialBound (fun x => (η x)⁻¹) :=
    ExactCorrection.geometricScaleThreshold_inverse_polynomial ha hE0 e
  have hεpoly : HasPolynomialBound (fun x => (ε x)⁻¹) :=
    ExactCorrection.fixedOrderThreshold_inverse_polynomial k ρ (fun _ => a) η
      (fun _ => T) Budget (fun _ => K) P (fun x => (ρ x)⁻¹) (fun _ => a⁻¹) (fun x => (η x)⁻¹)
      (polynomialBound_const hT) hBudget (polynomialBound_const hK) hP hρinv
      (polynomialBound_const (inv_nonneg.mpr ha.le)) hηinv hρ (fun _ _ => ha) hη
      (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  let L := fun m x => Dm m*tailConstant r+Em m*P (m+1) x*(Dm m*tailConstant r)+2*Q m x
  have hL (m : ℕ) : HasPolynomialBound (L m) := by
    exact ((polynomialBound_const (mul_nonneg (hDm m) (tailConstant_nonneg r))).add
      (((polynomialBound_const (hEm m)).mul (hP (m+1))).mul
        (polynomialBound_const (mul_nonneg (hDm m) (tailConstant_nonneg r))))).add
      ((polynomialBound_const (by norm_num : (0:ℝ) ≤ 2)).mul (hQ m))
  refine ⟨ε,P,L,hεpoly,hP,hL,fun x hx => ⟨(hε x hx).1,(hε x hx).2.1⟩,?_⟩
  intro z hz hzsmall F hF hFb hFm G hG t ht htε j hkj hjk hinput hnear hmetric
  have hx : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr (hzsmall.trans hz₀1)
  have hρform : ρ z⁻¹ = z^4/D := by
    dsimp [ρ]
    rw [inv_pow]
    field_simp
  have ht1 : t ≤ 1 := htε.le.trans (hε z⁻¹ hx).2.1
  obtain ⟨hτη,htail,hratio,hlow,hδ'δ,hmin⟩ := (hε z⁻¹ hx).2.2 t ht htε j hkj hjk
  rw [hρform] at htail hlow
  obtain ⟨hminpos,hδ,hτ,hs⟩ := ExactCorrection.exact_scale_positive ht k
  have hδ' : 0 < t^((6/5 : ℝ)*(j : ℝ)) := Real.rpow_pos_of_pos ht _
  obtain ⟨_,hδτ,hτs,hst⟩ := ExactCorrection.exact_scale_order ht ht1 hk
  obtain ⟨U,hU,hUB,herror⟩ := hbuild z hz hzsmall F hF hFb hFm G hG (t^(k : ℝ))
    (t^((6/5 : ℝ)*(j : ℝ))) t (t^(11/10 : ℝ)) (t^(6/5 : ℝ))
    hδ hδ' hδ'δ ht ht1 hs hst hτ hτs hδτ hτη hinput hnear hmetric htail hratio
  refine ⟨U,hU,hUB,?_,?_⟩
  · intro m hm i j hj x hx'
    have hb' := (hUB j i).deriv_le hτ (le_refl j) hx'
    have hh := hb'.trans (hlow j (hj.trans hm))
    simpa only [one_pow,one_mul] using hh
  · intro m C hC hCm i
    apply (herror m C hC hCm i).mono_const
    have he : normalizedStepBound r r (Budget z⁻¹) (Dm m) (Em m) ((P (m+1) z⁻¹)) ((Q m z⁻¹)) C
        (t^(k : ℝ)) (t^((6/5 : ℝ)*(j : ℝ)))
        (t^(6/5 : ℝ)) (t^(11/10 : ℝ)) t =
      ((t^((6/5 : ℝ)*(j : ℝ)))^2)⁻¹ *
        (((t^(k : ℝ))^2 + Em m*(P (m+1) z⁻¹)*t^(k : ℝ)) * (Dm m*tailConstant r) *
          ((Budget z⁻¹)*(t^(11/10 : ℝ)/t)^r+C*(t^(6/5 : ℝ)/t)^r) +
          (Q m z⁻¹)*(t^(k : ℝ)*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(r+1)+
            (t^(k : ℝ))^3/t^(6/5 : ℝ))) := by
      unfold normalizedStepBound
      field_simp [hτ.ne']
    rw [he]
    have hden : ((t^((6/5 : ℝ)*(j : ℝ)))^2)⁻¹ ≤
        ((t^((6/5 : ℝ)*((k : ℝ)+1)))^2)⁻¹ := by
      apply (inv_le_inv₀ (sq_pos_of_pos hδ') (sq_pos_of_pos hminpos)).mpr
      nlinarith
    have hdm := hDm m
    have hem := hEm m
    have hbm := ((hP (m+1)).nonneg hx)
    have htm := ((hQ m).nonneg hx)
    have htc := tailConstant_nonneg r
    have hB₀ := hBudget.nonneg hx
    have hnum : 0 ≤
        (((t^(k : ℝ))^2 + Em m*(P (m+1) z⁻¹)*t^(k : ℝ)) * (Dm m*tailConstant r) *
          ((Budget z⁻¹)*(t^(11/10 : ℝ)/t)^r+C*(t^(6/5 : ℝ)/t)^r) +
          (Q m z⁻¹)*(t^(k : ℝ)*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(r+1)+
            (t^(k : ℝ))^3/t^(6/5 : ℝ))) := by positivity
    exact (mul_le_mul_of_nonneg_right hden hnum).trans
      (ExactCorrection.normalized_step_envelope_nat_succ ht ht1 hk (hBudget.nonneg hx) hC
        (mul_nonneg (hDm m) (tailConstant_nonneg r)) (hEm m) (((hP (m+1)).nonneg hx)) (((hQ m).nonneg hx)))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_fixed_order_step_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_fixed_order_step_oai.{u_1}
