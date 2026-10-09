-- Prove2me | solution 1 for OAI.SevenEighths.ProbeHighRowFamily.continuedCompensatedLocal_unramified_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:15:41.320142+00:00
-- url     : https://prove2.me/submissions/462e5a33-03fc-4f73-9aed-a8a5c9e04a5c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B023
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_rowClosedMarked_unramified

section
-- module Solutions.OAIHecke.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open Polynomial

/-- Backport (Mathlib d13f23b), with Mathlib's own proof. -/
theorem multiplicity_eq_zero_of_not_dvd {α : Type*} [Monoid α] {a b : α} (h : ¬ a ∣ b) :
    multiplicity a b = 0 :=
  multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_zero.mpr h)
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Euler
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramified_marked_error (R V qInv K W D : ℂ)
    (hR : 1 - R ≠ 0) (hV : 1 - V ≠ 0) :
    markedFactor R V qInv K (-D + W * R) 1 + D =
      (R * ((1 - qInv) + (1 - V) * (W - D)) - K * V) /
        ((1 - R) * (1 - V)) := by
  unfold markedFactor
  field_simp
  ring

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Local
namespace OAI

namespace SevenEighths.ProbeLocal
noncomputable section

theorem continuedCorrection_defect (V W D Pstar : ℂ) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold continuedCorrection
  field_simp
  ring

theorem continued_normalized_cancellation (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        continuedCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement continuedCorrection
  field_simp
  linear_combination -(1 - V) * (1 - W) * hBD + (1 - V) * hvW

end
end SevenEighths.ProbeLocal

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CorrectionBounds
namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal

lemma one_sub_ne_zero_of_norm_le_half (a : ℂ) (ha : ‖a‖ ≤ 1/2) : 1 - a ≠ 0 := by
  intro h
  have : a = 1 := by linear_combination -h
  rw [this, norm_one] at ha
  norm_num at ha

lemma inv_one_sub_norm_le_two (a : ℂ) (ha : ‖a‖ ≤ 1/2) : ‖(1-a)⁻¹‖ ≤ 2 := by
  have hl := norm_sub_norm_le (1 : ℂ) a
  simp only [norm_one] at hl
  have hd : 0 < ‖1-a‖ := by linarith
  rw [norm_inv, ← one_div, div_le_iff₀ hd]
  linarith

theorem unramified_marked_error_bound (R V qInv K W D : ℂ)
    (hR : ‖R‖ ≤ 1/2) (hV : ‖V‖ ≤ 1/2) (hq : ‖qInv‖ ≤ 1) (hD : ‖D‖ ≤ 1/2) :
    ‖ProbeEuler.markedFactor R V qInv K (-D + W*R) 1 + D‖ ≤
      12 * ‖R‖ * (1 + ‖W‖) + 4 * ‖K‖ * ‖V‖ := by
  rw [ProbeEuler.unramified_marked_error R V qInv K W D
    (one_sub_ne_zero_of_norm_le_half R hR) (one_sub_ne_zero_of_norm_le_half V hV),
    div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
  have hnum : ‖R*((1-qInv)+(1-V)*(W-D))-K*V‖ ≤
      ‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖ := by
    calc
      _ ≤ ‖R*((1-qInv)+(1-V)*(W-D))‖ + ‖K*V‖ := norm_sub_le _ _
      _ = ‖R‖ * ‖(1-qInv)+(1-V)*(W-D)‖ + ‖K‖*‖V‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖R‖ * (‖1-qInv‖ + ‖1-V‖*‖W-D‖) + ‖K‖*‖V‖ := by
        gcongr
        simpa only [norm_mul] using norm_add_le (1-qInv) ((1-V)*(W-D))
      _ ≤ ‖R‖ * (2 + (1+‖V‖)*(‖W‖+‖D‖)) + ‖K‖*‖V‖ := by
        gcongr
        · calc ‖1-qInv‖ ≤ ‖(1:ℂ)‖+‖qInv‖ := norm_sub_le _ _
               _ ≤ 2 := by simp only [norm_one]; linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) V
        · exact norm_sub_le W D
  have hv := inv_one_sub_norm_le_two V hV
  have hr := inv_one_sub_norm_le_two R hR
  calc
    _ ≤ (‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖) * (2*2) := by
      gcongr
    _ ≤ 12 * ‖R‖ * (1+‖W‖) + 4*‖K‖*‖V‖ := by
      have he : 2 + (1+‖V‖)*(‖W‖+‖D‖) ≤ 3*(1+‖W‖) := by
        have : (1+‖V‖)*(‖W‖+‖D‖) ≤ (3/2:ℝ)*(‖W‖+1/2) := by gcongr ; linarith
        nlinarith [norm_nonneg W]
      nlinarith [mul_le_mul_of_nonneg_left he (norm_nonneg R)]

theorem continuedCorrection_defect_bound (V W D Pstar : ℂ)
    (hV : ‖V‖ ≤ 1/2) (hD : ‖D‖ ≤ 1/2) :
    ‖continuedCorrection V W D Pstar - 1‖ ≤
      2 * (‖D‖ * (‖V‖+‖W‖+‖V‖*‖W‖) + ‖V‖*‖W‖ +
        2*(1+‖W‖)*‖Pstar+D‖) := by
  rw [continuedCorrection_defect _ _ _ _ (one_sub_ne_zero_of_norm_le_half D hD),
    div_eq_mul_inv, norm_mul]
  have hA : ‖V+W-V*W‖ ≤ ‖V‖+‖W‖+‖V‖*‖W‖ := by
    calc
      _ ≤ ‖V+W‖+‖V*W‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul]; gcongr; exact norm_add_le V W
  have hnum : ‖D*(V+W-V*W)-V*W+(1-V)*(1-W)*(Pstar+D)‖ ≤
      ‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖ := by
    calc
      _ ≤ ‖D*(V+W-V*W)-V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := norm_add_le _ _
      _ ≤ ‖D*(V+W-V*W)‖+‖V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖D‖*‖V+W-V*W‖+‖V‖*‖W‖+‖1-V‖*‖1-W‖*‖Pstar+D‖ := by simp only [norm_mul]
      _ ≤ _ := by
        gcongr
        · calc ‖1-V‖ ≤ 1+‖V‖ := by simpa only [norm_one] using norm_sub_le (1:ℂ) V
               _ ≤ 2 := by linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) W
  calc
    _ ≤ (‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖)*2 := by
      gcongr
      exact inv_one_sub_norm_le_two D hD
    _ = _ := by ring

end SevenEighths.ProbeLocal
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical

namespace FiniteGaussPhase

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_angularFactor (a : O) (ha : a ≠ 0) : ‖angularFactor a‖ = 1 := by
  rw [angularFactor, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

end FiniteGaussPhase

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma angularFactor_norm_le_one (a : ActualEisensteinCubic.O) : ‖FiniteGaussPhase.angularFactor a‖≤1 := by
  by_cases ha : a=0
  · subst a; simp [FiniteGaussPhase.angularFactor]
  · exact (FiniteGaussPhase.norm_angularFactor a ha).le

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

end CompletedGauss

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Row
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve InitialMeanSquare ProbeCompleted

local notation "O" => ActualEisensteinCubic.O

theorem targetMonoid_norm_le_one (η : HeckeFamily.Character) (a : O) :
    ‖targetMonoid η a‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue (Ideal.Quotient.mk η.modulus a)

end SevenEighths.ProbeRow
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.EulerCoordinates
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma actualAPhase_norm_le_one (eta : HeckeFamily.Character) (p : O) :
    ‖actualAPhase eta p‖ ≤ 1 := by
  simp only [actualAPhase, norm_mul, norm_pow, norm_star]
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) (CompletedGauss.angularFactor_norm_le_one p))).trans
    (pow_le_one₀ (norm_nonneg _) (ProbeRow.targetMonoid_norm_le_one eta p))

lemma coordV_norm (Q : ℝ) (hQ : 0 < Q) (z : ℂ) :
    ‖coordV Q z‖ = Q ^ (-6*z.re) := by
  rw [coordV, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp

lemma coordR_norm_le (Q : ℝ) (hQ : 0 < Q) (A x z : ℂ) (hA : ‖A‖ ≤ 1) :
    ‖coordR Q A x z‖ ≤ Q ^ (4-6*x.re-6*z.re) := by
  rw [coordR, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hA

lemma coordW_norm_le (Q : ℝ) (hQ : 0 < Q) (v w : ℂ) (hv : ‖v‖ ≤ 1) :
    ‖coordW Q v w‖ ≤ Q ^ (-w.re) := by
  rw [coordW, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) hv

lemma coordD_norm_le (Q : ℝ) (hQ : 0 < Q) (eta v x : ℂ)
    (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖coordD Q eta v x‖ ≤ Q ^ (-x.re) := by
  rw [coordD, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  apply mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _)
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) he).trans hv

lemma coordK_norm_le (Q : ℝ) (hQ : 1 ≤ Q) (eta x w : ℂ) (he : ‖eta‖ ≤ 1) :
    ‖coordK Q eta x w‖ ≤ Q ^ (1-x.re-w.re) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hsub : ‖(Q:ℂ)-1‖ = Q-1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hQ)]
  rw [coordK, norm_mul, norm_mul, hsub, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
  have heq : (1-x.re-w.re) = 1 + (-x.re-w.re) := by ring
  rw [heq, Real.rpow_add hQ0, Real.rpow_one]
  simp only [Complex.sub_re, Complex.neg_re]
  gcongr
  calc ‖eta‖*(Q-1) ≤ 1*(Q-1) := mul_le_mul_of_nonneg_right he (sub_nonneg.mpr hQ)
       _ ≤ Q := by linarith

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.EulerRegion
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma rpow_le_half (Q a : ℝ) (hQ : 4 ≤ Q) (ha : a ≤ -(1/2)) : Q^a ≤ 1/2 := by
  have hQ0 : 0 < Q := by linarith
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ0
  have hs2 := Real.sq_sqrt hQ0.le
  calc
    Q^a ≤ Q^(-(1/2:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha
    _ = (Real.sqrt Q)⁻¹ := by rw [Real.rpow_neg hQ0.le, ← Real.sqrt_eq_rpow]
    _ ≤ 1/2 := by rw [← one_div, div_le_iff₀ hs]; nlinarith [Real.sqrt_nonneg Q]

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Canonical
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

end SevenEighths.CenteredMomentCanonical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Sextic
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem actualSextic_pow_eq_one_iff (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) (n : ℕ) :
    actualSextic P hg ^ n = 1 ↔ 6 ∣ n := by
  rw [← orderOf_dvd_iff_pow_eq_one, CenteredMomentCanonical.actualSextic_order_six P hg hc]

end SevenEighths.ProbePrimePower
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrimeConstants
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma actualSextic_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) : actualSextic P hg ^ 6 = 1 :=
  (actualSextic_pow_eq_one_iff P hg hc 6).mpr (by decide)

end SevenEighths.ProbePrimePower
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrincipalEulerIdentity
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma evenRatio_eq_coordR (Q : ℝ) (hQ : 0<Q) (a x z : ℂ) :
    evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z) = coordR Q (a^2) x z := by
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold evenRatio coordR coordV
  calc
    _ = a^2 * ((Q:ℂ)^4 * ((Q:ℂ)^(-x))^6 * (Q:ℂ)^(-6*z)) := by ring
    _ = a^2 * ((Q:ℂ)^(4:ℂ) * (Q:ℂ)^((6:ℂ)*(-x)) * (Q:ℂ)^(-6*z)) := by
      rw [Complex.cpow_ofNat]
      have h6 : (Q:ℂ)^((6:ℂ)*(-x)) = ((Q:ℂ)^(-x))^6 := by
        simpa using Complex.cpow_nat_mul (Q:ℂ) 6 (-x)
      rw [h6]
    _ = a^2 * (Q:ℂ)^((4:ℂ)+6*(-x)+(-6*z)) := by
      rw [← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
    _ = _ := by congr 2; ring

lemma coordK_eq_geometric (Q : ℝ) (hQ : 0<Q) (eta x w : ℂ) :
    coordK Q eta x w = eta*((Q:ℂ)-1)*((Q:ℂ)^(-x))*((Q:ℂ)^(-w)) := by
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold coordK
  rw [show -x-w = -x+(-w) by ring, Complex.cpow_add _ _ hn]
  ring

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

include hc

omit hc

lemma actualACube_sq (eta : HeckeFamily.Character) (p : O) :
    actualACube eta p ^ 2 = actualAPhase eta p := by
  unfold actualACube actualAPhase
  ring

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighEulerRational
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma targetMonoid_primaryGenerator (η : HeckeFamily.Character) (I : Ideal O) (hs : Supported I) :
    targetMonoid η (primaryGenerator I)=HeckeFamily.idealCoeff η I := by
  calc
    _ = HeckeFamily.idealCoeff η (Ideal.span {primaryGenerator I}) :=
      (HeckeFamily.idealCoeff_span η (supported_primaryGenerator_ne_zero I hs)).symm
    _ = _ := by rw [span_primaryGenerator_of_supported I hs]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsActual
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem actualSextic_unit_six (p b : O) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hb : IsCoprime b p) :
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^6=1 := by
  have h := congrArg (fun χ : MulChar (O ⧸ Ideal.span {p}) ℂ =>
    χ (Ideal.Quotient.mk _ b)) (actualSextic_six _ hg hc)
  simpa only [MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),
    MulChar.one_apply ((isUnit_quotient_span_iff p b).mpr hb.symm)] using h

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsFirstRamified
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma first_region_V_half (Q : ℝ) (hQ : 4≤Q) (z : ℂ) (hz : (17/50:ℝ)≤z.re) :
    ‖coordV Q z‖≤1/2 := by
  rw [coordV_norm Q (by linarith)]
  exact rpow_le_half Q _ hQ (by linarith)

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsFirstRegion
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramifiedClosed_first_region_bound (Q : ℝ) (A eta v x w z : ℂ) (eps : ℝ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (heps : 0<eps) (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedClosed Q A eta v x w z-1‖≤240*Q^(-1-min eps (1/50:ℝ)) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let L := Q^(1/100:ℝ)
  let E := Q^(-(109/100:ℝ))
  let T := Q^(-1-min eps (1/50:ℝ))
  have hL1 : 1≤L := Real.one_le_rpow hQ1 (by norm_num)
  have hT : 0≤T := Real.rpow_nonneg hQ0.le _
  have hV : ‖V‖≤Q^(-(51/25:ℝ)) := by
    rw [show V=coordV Q z from rfl,coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖≤Q^(-(11/10:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖≤L :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖≤Q^(-(51/100:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖≤Q^(-eps) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖≤1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb c : ℝ) (ha : 0≤a) (hb : 0≤b)
      (haa : a≤Q^aa) (hbb : b≤Q^bb) (hc : aa+bb≤ c) : a*b≤Q^c := by
    calc
      a*b≤Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤Q^c := Real.rpow_le_rpow_of_exponent_le hQ1 hc
  have hRL : ‖R‖*L≤E := hprod _ _ _ _ _ (norm_nonneg _) (by positivity) hR le_rfl (by norm_num)
  have hKV : ‖K‖*‖V‖≤E := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by linarith)
  have hRW : ‖R‖*(1+‖W‖)≤2*E := by
    calc
      _≤‖R‖*(2*L) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _≤2*E := by nlinarith
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hPE : ‖P+D‖≤28*E := by
    have hh := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    dsimp only [P]
    nlinarith
  have hEL : E*L≤T := hprod _ _ _ _ _ (by positivity) (by positivity) le_rfl le_rfl
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hWE : (1+‖W‖)*‖P+D‖≤56*T := by
    calc
      _≤(2*L)*(28*E) := mul_le_mul (by linarith) hPE (norm_nonneg _) (by positivity)
      _≤56*T := by nlinarith
  have hDV : ‖D‖*‖V‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hVW : ‖V‖*‖W‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hDW : ‖D‖*‖W‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (coordD_norm_le Q hQ0 eta v x heta hv) (coordW_norm_le Q hQ0 v w hv)
    (by have := min_le_left eps (1/50:ℝ);linarith)
  have hDVW : ‖D‖*‖V‖*‖W‖≤T := by
    calc
      _ = (‖D‖*‖W‖)*‖V‖ := by ring
      _ ≤ ‖D‖*‖W‖ := mul_le_of_le_one_right (by positivity) (by linarith)
      _ ≤ T := hDW
  have hh := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖≤240*T
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalSlotEstimate
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex

namespace SevenEighths.PrincipalSlotEstimate
open ProbeEuler ProbeLocal

theorem unit_phase_inverse (η : ℂ) (hη : ‖η‖ = 1) : star η * η = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hη]
  norm_num

end SevenEighths.PrincipalSlotEstimate

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedCancellation
namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal
theorem compensated_phase_error_bound (V W D P B q vInv : ℂ) (T : ℝ)
    (_hT : 0 ≤ T) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1)
    (hD : ‖D‖ ≤ 1 / 2) (hq : ‖q‖ ≤ 1)
    (hVT : ‖V‖ ≤ T) (hDT : ‖D‖ ≤ T)
    (hE : ‖P + D‖ ≤ 28 * T) (hBE : ‖B‖ * ‖P + D‖ ≤ 28 * T)
    (hv : ‖vInv‖≤1) (hBD : B * D = vInv) (hWq : vInv*W = q) :
    ‖compensatedReplacement V W D P B q + continuedCorrection V W D P*vInv‖ ≤ 720 * T := by
  have h1V : ‖1 - V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have h1W : ‖1 - W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have h1q : ‖vInv - q‖ ≤ 2 := by
    have := norm_sub_le vInv q
    linarith
  have hiV := inv_one_sub_norm_le_two V hV
  have hiD := inv_one_sub_norm_le_two D hD
  have hfac : ‖(1 - V) * (1 - W) / (1 - D)‖ ≤ 8 := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      ‖1 - V‖ * ‖1 - W‖ * ‖(1 - D)⁻¹‖ ≤ (2 : ℝ) * 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hleft : ‖(vInv - q) * (V / (1 - V) - D)‖ ≤ 6 * T := by
    calc
      _ = ‖vInv - q‖ * ‖V / (1 - V) - D‖ := norm_mul _ _
      _ ≤ 2 * (‖V‖ * 2 + ‖D‖) := by
        gcongr
        calc
          _ ≤ ‖V / (1 - V)‖ + ‖D‖ := norm_sub_le _ _
          _ ≤ _ := by rw [div_eq_mul_inv, norm_mul]; gcongr
      _ ≤ 6 * T := by linarith
  have hright : ‖(B + vInv - q) * (P + D)‖ ≤ 84 * T := by
    have hc : ‖B + vInv - q‖ ≤ ‖B‖ + 2 := by
      calc
        _ = ‖B + (vInv - q)‖ := by congr 1; ring
        _ ≤ ‖B‖ + ‖vInv - q‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc
      _ = ‖B + vInv - q‖ * ‖P + D‖ := norm_mul _ _
      _ ≤ (‖B‖ + 2) * ‖P + D‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ 84 * T := by nlinarith
  have hid := continued_normalized_cancellation V W D P B q vInv
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD)
    hBD hWq
  rw [hid, norm_mul]
  calc
    _ ≤ 8 * (‖(vInv - q) * (V / (1 - V) - D)‖ + ‖(B + vInv - q) * (P + D)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 720 * T := by linarith

end SevenEighths.ProbeLocal
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedError
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

lemma unramifiedMarked_selected_error (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedMarked Q A eta v x w z+coordD Q eta v x‖≤28 ∧
    ‖star eta*(Q:ℂ)^x‖*‖unramifiedMarked Q A eta v x w z+coordD Q eta v x‖≤28 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta*(Q:ℂ)^x
  have hR : ‖R‖≤Q^(4-6*x.re-6*z.re) := coordR_norm_le Q hQ0 A x z hA
  have hV : ‖V‖=Q^(-6*z.re) := coordV_norm Q hQ0 z
  have hD : ‖D‖≤Q^(-x.re) := coordD_norm_le Q hQ0 eta v x heta hv
  have hW : ‖W‖≤1 := (coordW_norm_le Q hQ0 v w hv).trans
    (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hK : ‖K‖≤Q^(1-x.re-w.re) := coordK_norm_le Q hQ1 eta x w heta
  have hB : ‖B‖≤Q^x.re := by
    dsimp only [B]
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by linarith))
  have hVh : ‖V‖≤1/2 := by rw [hV];exact rpow_le_half Q _ hQ (by linarith)
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by linarith))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb : ℝ) (ha : 0≤a) (hb : 0≤b)
      (haa : a≤Q^aa) (hbb : b≤Q^bb) (he : aa+bb≤0) : a*b≤1 := by
    calc
      a*b≤Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤1 := Real.rpow_le_one_of_one_le_of_nonpos hQ1 he
  have hKV : ‖K‖*‖V‖≤1 := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV.le (by linarith)
  have hBR : ‖B‖*‖R‖≤1 := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hB hR (by linarith)
  have hKV' : ‖K‖*‖V‖≤Q^(1-x.re-w.re-6*z.re) := by
    calc
      _≤Q^(1-x.re-w.re)*Q^(-6*z.re) := mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
      _=_ := by rw [←Real.rpow_add hQ0];congr 1;ring
  have hBKV : ‖B‖*(‖K‖*‖V‖)≤1 := hprod _ _ _ _ (norm_nonneg _) (by positivity) hB hKV' (by linarith)
  have hE := unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
  change ‖unramifiedMarked Q A eta v x w z+D‖≤_ at hE
  have hE' : ‖unramifiedMarked Q A eta v x w z+D‖≤24*‖R‖+4*(‖K‖*‖V‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg R)]
  constructor
  · change ‖unramifiedMarked Q A eta v x w z+D‖≤28
    linarith
  · have hh := mul_le_mul_of_nonneg_left hE' (norm_nonneg B)
    change ‖B‖*‖unramifiedMarked Q A eta v x w z+D‖≤28
    nlinarith

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedUnramified
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ProbeLocal

lemma selected_phase_identities (Q : ℝ) (eta v x w : ℂ)
    (hQ : 0<Q) (heta : ‖eta‖=1) (hv : ‖v‖=1) :
    (star eta*(Q:ℂ)^x)*coordD Q eta v x=star v ∧
      star v*coordW Q v w=(Q:ℂ)^(-w) := by
  have hQ0 : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  constructor
  · unfold coordD
    calc
      _=(star eta*eta)*((Q:ℂ)^x*(Q:ℂ)^(-x))*star v := by ring
      _=star v := by rw [PrincipalSlotEstimate.unit_phase_inverse eta heta,←Complex.cpow_add _ _ hQ0];simp
  · unfold coordW
    rw [←mul_assoc,PrincipalSlotEstimate.unit_phase_inverse v hv,one_mul]

lemma unramifiedSelected_error_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v‖≤720 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by linarith)
  have hD : ‖coordD Q eta v x‖≤1/2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans (rpow_le_half Q _ hQ (by linarith))
  have hW : ‖coordW Q v w‖≤1 :=
    (coordW_norm_le Q hQ0 v w hv.le).trans (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  have he := unramifiedMarked_selected_error Q A eta v x w z hQ hA heta.le hv.le hx hw hz
  have hi := selected_phase_identities Q eta v x w hQ0 heta hv
  have hh := compensated_phase_error_bound (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w)) (star v) 1
    (by norm_num) hV hW hD hq (by linarith) (by linarith)
    (by simpa using he.1) (by simpa using he.2) (by rw [norm_star,hv]) hi.1 hi.2
  simpa only [mul_one,unramifiedSelected,unramifiedClosed,unramifiedMarked] using hh

lemma unramifiedSelected_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedSelected Q A eta v x w z‖≤961 := by
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (1/4) hQ hA heta.le hv.le
    (by norm_num) (by linarith) hz (by linarith) (by linarith)
  have hpow : Q^(-1-min (1/4:ℝ) (1/50))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hH : ‖unramifiedClosed Q A eta v x w z‖≤241 := by
    have hh := norm_add_le (unramifiedClosed Q A eta v x w z-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at hh
    nlinarith
  have he := unramifiedSelected_error_bound Q A eta v x w z hQ hA heta hv hx hw hz
  have hh := norm_sub_le
    (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)
    (unramifiedClosed Q A eta v x w z*star v)
  rw [add_sub_cancel_right,norm_mul,norm_star,hv,mul_one] at hh
  linarith

lemma unramifiedSelected_zero (Q : ℝ) (v x w z : ℂ) :
    unramifiedSelected Q 0 0 v x w z= -(Q:ℂ)^(-w)*(1-coordV Q z*coordW Q v w) := by
  simp only [unramifiedSelected,unramifiedMarked,coordR,coordD,coordK,zero_mul,
    neg_zero,add_zero,markedFactor,zero_sub,sub_zero,div_one,mul_zero,
    star_zero,compensatedReplacement]
  ring

lemma unramifiedSelected_zero_bound (Q : ℝ) (v x w z : ℂ)
    (hQ : 4≤Q) (hv : ‖v‖≤1) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖unramifiedSelected Q 0 0 v x w z‖≤2 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hV : ‖coordV Q z‖≤1 := by
    rw [coordV_norm Q hQ0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  have hW : ‖coordW Q v w‖≤1 :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  rw [unramifiedSelected_zero,norm_mul,norm_neg]
  have ht := norm_sub_le (1:ℂ) (coordV Q z*coordW Q v w)
  rw [norm_one,norm_mul] at ht
  have hp : ‖coordV Q z‖*‖coordW Q v w‖≤1 := by nlinarith [norm_nonneg (coordV Q z)]
  nlinarith [norm_nonneg (1-coordV Q z*coordW Q v w)]

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedActual
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma elementCoeff_zero_or_norm_one (eta : HeckeFamily.Character) (p : O) :
    HeckeFamily.elementCoeff eta p=0 ∨ ‖HeckeFamily.elementCoeff eta p‖=1 := by
  by_cases h : HeckeFamily.elementCoeff eta p=0
  · exact Or.inl h
  · right
    let : Finite (O ⧸ eta.modulus) := Ring.HasFiniteQuotients.finiteQuotient eta.modulus_ne_bot
    let : Fintype (O ⧸ eta.modulus) := Fintype.ofFinite _
    have hu : IsUnit (Ideal.Quotient.mk eta.modulus p) := eta.residue.apply_ne_zero_iff.mp h
    obtain ⟨u,hu⟩ := hu
    change ‖eta.residue (Ideal.Quotient.mk eta.modulus p)‖=1
    rw [←hu]
    exact FiniteRayExpansion.norm_char_unit eta.residue u

theorem actualUnramifiedSelected_bound (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hu : IsCoprime u p)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (x w z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖actualUnramifiedSelected eta p u hg x w z‖≤961 := by
  have hv := Complex.norm_eq_one_of_pow_eq_one (ProbePhysical.actualSextic_unit_six p u hg hc hu) (by decide : (6:ℕ)≠0)
  unfold actualUnramifiedSelected
  rcases elementCoeff_zero_or_norm_one eta p with heta|heta
  · have hA : actualAPhase eta p=0 := by simp [actualAPhase,heta]
    rw [heta,hA]
    exact (unramifiedSelected_zero_bound _ _ x w z hQ hv.le hw hz).trans (by norm_num)
  · exact unramifiedSelected_bound _ _ _ _ x w z hQ (actualAPhase_norm_le_one eta p) heta hv hx hw hz

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.Valuation
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification UniqueFactorizationMonoid

attribute [local instance] OAI.SevenEighths.ProbeHighRowFamily.instIsPrincipalIdealRingO_solutions
theorem unitPart_spec (u : FreeRow) (p : O) (hp : Prime p) :
    u.val=p^(multiplicity p u.val)*unitPart u p hp ∧ ¬p∣unitPart u p hp :=
  Classical.choose_spec ((FiniteMultiplicity.of_prime_left hp u.property.1).exists_eq_pow_mul_and_not_dvd)

theorem unitPart_coprime (u : FreeRow) (p : O) (hp : Prime p) : IsCoprime (unitPart u p hp) p :=
  (hp.irreducible.coprime_iff_not_dvd.mpr (unitPart_spec u p hp).2).symm

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.SelectedUnramified
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem continuedMarkedLocal_unramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1) :
    continuedMarkedLocal η u P hs x w z=
      unramifiedMarked P.val.absNorm (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) (idealRowHom u.val P.val) x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hnot : ¬p∣u.val := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hj := multiplicity_eq_zero_of_not_dvd hnot
  have hb : unitPart u p hp=u.val := by
    have he := (unitPart_spec u p hp).1
    rw [hj,pow_zero,one_mul] at he
    exact he.symm
  have hu : IsCoprime u.val p := by rw [←hb]; exact unitPart_coprime u p hp
  have hρ := actualSextic_unit_six p u.val hg.1 hg.2 hu
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) :=
    HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (actualACube η p) x z
  simp only [Complex.ofReal_natCast] at hr
  have hR' : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hr,actualACube_sq,hspan]
    exact hR
  have hv' : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by rw [hspan];exact hV
  have hh := rowClosedMarked_unramified p hp hg.1 hg.2 (targetMonoid η p) (actualACube η p)
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
    (coordV (Ideal.absNorm (Ideal.span {p})) z) _ hρ hv' hR'
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (targetMonoid η p) x w
  simp only [Complex.ofReal_natCast] at hk
  have hi : (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val))⁻¹=
      star (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val)) :=
    Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hρ (by decide))
  have heta : idealCoeff η P.val=targetMonoid η p :=
    (targetMonoid_primaryGenerator η P.val hs).symm
  have hphase : idealRowHom u.val P.val=
      actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    conv_lhs => rw [←hspan]
    exact idealRowHom_prime u.val (Ideal.span {p}) hg.1
  simp only [hspan] at hh hr hk
  unfold continuedMarkedLocal
  change rowClosedMarked p hp hg.1 (targetMonoid η p) (actualACube η p)
    ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
    (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) (multiplicity p u.val)=_
  rw [hj,hb,hh,hr,←hk,actualACube_sq,heta,hphase]
  simp only [unramifiedMarked,coordD,coordW,div_eq_mul_inv,hi,Complex.ofReal_natCast]
  congr 1; ring

theorem continuedCompensatedLocal_unramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1) :
    continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))=
      unramifiedSelected P.val.absNorm (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) (idealRowHom u.val P.val) x w z := by
  rw [continuedCompensatedLocal,continuedMarkedLocal_unramified η u P hs hn x w z hV hR]
  rfl

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.SelectedBounds
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma continuedCompensatedLocal_unramified_bound_oai (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : ¬P.val∣Ideal.span {u.val}) (hQ : (4:ℝ)≤P.val.absNorm)
    (x w z : ℂ) (hx : (7/8:ℝ)≤x.re) (hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤961 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hnot : ¬p∣u.val := by
    intro hd
    apply hP
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hu : IsCoprime u.val p := (hp.irreducible.coprime_iff_not_dvd.mpr hnot).symm
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hV : ‖coordV P.val.absNorm z‖<1 := by
    exact (first_region_V_half _ hQ z hz).trans_lt (by norm_num)
  have hR : ‖coordR P.val.absNorm (actualAPhase η p) x z‖<1 := by
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact (rpow_le_half _ _ hQ (by linarith)).trans_lt (by norm_num)
  rw [continuedCompensatedLocal_unramified η u P hs hP x w z hV hR]
  have hb := actualUnramifiedSelected_bound η p u.val hg.1 hg.2 hu (hspan.symm ▸ hQ) x w z hx hw hz
  have he : idealCoeff η P.val=elementCoeff η p := by rw [←hspan,idealCoeff_span η hp.ne_zero]
  have hv : idealRowHom u.val P.val=actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    rw [←hspan,idealRowHom_prime u.val (Ideal.span {p}) hg.1]
  simpa only [actualUnramifiedSelected,hspan,he,hv] using hb

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeHighRowFamily.continuedCompensatedLocal_unramified_bound_oai := @OAI.SevenEighths.ProbeHighRowFamily.continuedCompensatedLocal_unramified_bound_oai
