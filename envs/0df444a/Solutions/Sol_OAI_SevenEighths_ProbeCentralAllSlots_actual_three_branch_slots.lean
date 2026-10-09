-- Prove2me | solution 1 for OAI.SevenEighths.ProbeCentralAllSlots.actual_three_branch_slots
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T05:19:06.899348+00:00
-- url     : https://prove2.me/submissions/9da58239-1193-4519-bad6-0b991a329dba

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Theorems.Thm_OAI_SevenEighths_ProbeCentralRepeatedSubset_actual_repeated_subset
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_rowClosedMarked_unramified
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_unramifiedSelected_central_quotient
import Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_actual_central_ramified_normalized

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsCentralQuotient
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma unramifiedClosed_central_lower (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤Q) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖unramifiedClosed Q A eta v x w z‖ := by
  have hQ0 : 0<Q := by linarith
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (10*e)
    (by linarith) hA heta hv (by positivity) (by rw [hx];linarith)
    (by rw [hz]) (by rw [hw];linarith) (by rw [hx,hw];linarith)
  have hp : Q^(-1-min (10*e) (1/50:ℝ))≤Q^(-1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by
      have hm : 0≤ min (10*e) (1/50:ℝ) := by positivity
      linarith)
  have hi : Q^(-1:ℝ)≤1/480 := by
    rw [Real.rpow_neg_one,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) hQ
  have ht := norm_sub_le (1:ℂ) (unramifiedClosed Q A eta v x w z)
  have ht' := norm_add_le (1-unramifiedClosed Q A eta v x w z)
    (unramifiedClosed Q A eta v x w z)
  rw [sub_add_cancel,norm_one,norm_sub_rev] at ht'
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrincipalSignalComparison
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
namespace SevenEighths.PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal

variable {κ ι : Type*}

theorem idealCoeff_norm_one_of_coprime (χ : Character) (J : Ideal HeckeFamily.O)
    (hJ : J ≠ ⊥) (hc : IsCoprime J χ.modulus) : ‖idealCoeff χ J‖ = 1 := by
  let := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ χ.modulus) := Fintype.ofFinite _
  have hu : IsUnit (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator J)) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime χ.modulus _).mpr (by
      simpa only [Ideal.span_singleton_generator] using hc)
  obtain ⟨u, hu⟩ := hu
  change ‖IdealCharacter.value χ.modulus χ.residue J‖ = 1
  rw [IdealCharacter.value, if_neg hJ, ← hu]
  exact FiniteRayExpansion.norm_char_unit χ.residue u

open ProbePhysical ActualEisensteinCubic CompletedGauss

open PrincipalMellinResidues

end SevenEighths.PrincipalSignalComparison
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.SelectedPrimeSums
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

lemma finite_ideal_count (S : Finset (Ideal O)) (H : ℝ) (hH : 0≤H)
    (hS : ∀I∈S,I≠0) (hN : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (S.card:ℝ)≤128*H := by
  by_cases hh : 1≤H
  · exact DescentFiberCost.finite_ideal_count_real S H hh hS hN
  · have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hI
      have hp : (1:ℝ)≤Ideal.absNorm I := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
      have := hN I hI
      linarith
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

lemma ramified_card_bound (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ, 0<C ∧ ∀ (U : Ideal O), U≠0 → ∀S : Finset (Ideal O),
      ((S.filter (fun P=>P∣U)).card:ℝ)≤C*(Ideal.absNorm U:ℝ)^eps := by
  obtain ⟨C,hC,hb⟩ := IdealDivisorBound.ideal_divisor_small_power eps heps
  refine ⟨C,hC,?_⟩
  intro U hU S
  apply (show ((S.filter (fun P=>P∣U)).card:ℝ)≤(IdealMobiusDivisorSum.idealDivisors U).card from ?_).trans (hb U hU)
  exact_mod_cast Finset.card_le_card (show S.filter (fun P=>P∣U)⊆IdealMobiusDivisorSum.idealDivisors U from by
    intro P hP
    exact (IdealMobiusDivisorSum.mem_idealDivisors hU).mpr (Finset.mem_filter.mp hP).2)

lemma annularPower_nonneg (a b r : ℝ) (ha : 0<a) : 0≤annularPower a b r :=
  (Real.rpow_nonneg ha.le _).trans (le_max_left _ _)

lemma annular_rpow (a b P q r : ℝ) (ha : 0<a) (hb : 0<b) (hP : 0<P)
    (hqa : a*P≤q) (hqb : q≤b*P) : q^r≤annularPower a b r*P^r := by
  have hq : 0<q := (mul_pos ha hP).trans_le hqa
  by_cases hr : 0≤ r
  · calc
      q^r≤(b*P)^r := Real.rpow_le_rpow hq.le hqb hr
      _=b^r*P^r := Real.mul_rpow hb.le hP.le
      _≤annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hP.le _)
  · calc
      q^r≤(a*P)^r := Real.rpow_le_rpow_of_nonpos (mul_pos ha hP) hqa (by linarith)
      _=a^r*P^r := Real.mul_rpow ha.le hP.le
      _≤annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hP.le _)

theorem annular_slot_majorant (eps a b r d : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) :
    ∃C : ℝ, 0<C ∧ ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀S : Finset (Ideal O), (∀I∈S,I≠0) →
      (∀I∈S,a*P≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤b*P) →
      (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1))
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨D,hD,hdiv⟩ := ramified_card_bound eps heps
  let A := annularPower a b (r-1)
  let B := annularPower a b (r-1+d)
  have hA : 0≤A := annularPower_nonneg a b _ ha
  have hB : 0≤B := annularPower_nonneg a b _ ha
  refine ⟨1+128*b*A+D*B,by positivity,?_⟩
  intro U hU P hP S hS hSP
  have hP0 : 0<P := by linarith
  have hU1 : (1:ℝ)≤Ideal.absNorm U := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU)
  have hUpow : 1≤(Ideal.absNorm U:ℝ)^eps := Real.one_le_rpow hU1 heps.le
  have hq (I : Ideal O) (hI : I∈S) : 0<(Ideal.absNorm I:ℝ) :=
    (mul_pos ha hP0).trans_le (hSP I hI).1
  have hc := finite_ideal_count S (b*P) (by positivity) hS (fun I hI=>(hSP I hI).2)
  have heP : P*P^(r-1)=P^r := by
    calc
      _=P^(1:ℝ)*P^(r-1) := by rw [Real.rpow_one]
      _=P^r := by rw [←Real.rpow_add hP0];congr 1;ring
  have hfirst : (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1))≤128*b*A*P^r := by
    calc
      _≤∑_I∈S,A*P^(r-1) := Finset.sum_le_sum (fun I hI=>annular_rpow a b P _ _ ha hb hP0 (hSP I hI).1 (hSP I hI).2)
      _=(S.card:ℝ)*(A*P^(r-1)) := by simp
      _≤(128*(b*P))*(A*P^(r-1)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=128*b*A*(P*P^(r-1)) := by ring
      _=128*b*A*P^r := by rw [heP]
  have hsecond : (∑I∈S.filter (fun I=>I∣U),(Ideal.absNorm I:ℝ)^(r-1+d))≤
      D*B*(Ideal.absNorm U:ℝ)^eps*P^r := by
    have hpP : P^(r-1+d)≤P^r := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
    calc
      _≤∑_I∈S.filter (fun I=>I∣U),B*P^(r-1+d) := by
        apply Finset.sum_le_sum
        intro I hI
        exact annular_rpow a b P _ _ ha hb hP0 (hSP I (Finset.mem_filter.mp hI).1).1 (hSP I (Finset.mem_filter.mp hI).1).2
      _=((S.filter (fun I=>I∣U)).card:ℝ)*(B*P^(r-1+d)) := by simp
      _≤(D*(Ideal.absNorm U:ℝ)^eps)*(B*P^r) := by
        gcongr
        exact hdiv U hU S
      _=D*B*(Ideal.absNorm U:ℝ)^eps*P^r := by ring
  have hsum : (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1))≤
      (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1))+
        ∑I∈S.filter (fun I=>I∣U),(Ideal.absNorm I:ℝ)^(r-1+d) := by
    rw [Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro I hI
    split_ifs
    · rw [←Real.rpow_add (hq I hI)]
      exact le_add_of_nonneg_left (by positivity)
    · simp only [mul_one,add_zero,le_refl]
  apply hsum.trans
  have hup : 128*b*A*P^r≤128*b*A*(Ideal.absNorm U:ℝ)^eps*P^r := by
    nlinarith [mul_nonneg (show 0≤128*b*A*P^r by positivity) (show 0≤(Ideal.absNorm U:ℝ)^eps-1 by linarith)]
  nlinarith [mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤Ideal.absNorm U) eps) (Real.rpow_nonneg hP0.le r)]

theorem weighted_slot_bound (eps a b r d B K : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) (hB : 0≤B) (hK : 0≤K) :
    ∃C : ℝ, 0<C ∧ ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀(S : Finset (Ideal O)), (∀I∈S,I≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤B) →
    ∀(G : Ideal O→ℂ), (∀I∈S,‖G I‖≤K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑I∈S,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖)
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmajor⟩ := annular_slot_majorant eps a b r d heps ha hb hd
  refine ⟨(B*K+1)*C,by positivity,?_⟩
  intro U hU P hP S hS W hWS hWB G hG z hz
  have hP0 : 0<P := by linarith
  let T := S.filter (fun I=>W ((Ideal.absNorm I:ℝ)/P)≠0)
  have hTS : T⊆S := Finset.filter_subset _ _
  have hbounds (I : Ideal O) (hI : I∈T) : a*P≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤b*P := by
    have ht := hWS (show (Ideal.absNorm I:ℝ)/P∈Function.support W from (Finset.mem_filter.mp hI).2)
    exact ⟨(le_div_iff₀ hP0).mp ht.1,(div_le_iff₀ hP0).mp ht.2⟩
  have he : (∑I∈S,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖)=
      ∑I∈T,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖ := by
    symm
    apply Finset.sum_subset hTS
    intro I hI hn
    have hw : W ((Ideal.absNorm I:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
    simp only [hw,zero_mul,norm_zero]
  rw [he]
  have hpoint (I : Ideal O) (hI : I∈T) :
      ‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖≤
        (B*K)*((Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) := by
    have hN : (0:ℝ)<Ideal.absNorm I := (mul_pos ha hP0).trans_le (hbounds I hI).1
    have hc : ‖(Ideal.absNorm I:ℂ)^(z-1)‖=(Ideal.absNorm I:ℝ)^(r-1) := by
      simpa only [Complex.ofReal_natCast,Complex.sub_re,Complex.one_re,hz] using
        Complex.norm_cpow_eq_rpow_re_of_pos hN (z-1)
    simp only [norm_mul,hc]
    calc
      _≤B*(Ideal.absNorm I:ℝ)^(r-1)*(K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) := by
        gcongr
        · exact hWB _
        · exact hG I (hTS hI)
      _=_ := by ring
  have hmain := hmajor U hU P hP T (fun I hI=>hS I (hTS hI)) hbounds
  calc
    _≤∑I∈T,(B*K)*((Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) :=
      Finset.sum_le_sum hpoint
    _=(B*K)*∑I∈T,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) :=
      (Finset.mul_sum _ _ _).symm
    _≤(B*K)*(C*(Ideal.absNorm U:ℝ)^eps*P^r) := mul_le_mul_of_nonneg_left hmain (mul_nonneg hB hK)
    _≤((B*K+1)*C)*(Ideal.absNorm U:ℝ)^eps*P^r := by
      nlinarith [mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by positivity : (0:ℝ)≤Ideal.absNorm U) eps))
        (Real.rpow_nonneg hP0.le r)]

end SevenEighths.ProbeSelectedPrimeSums
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.Selected
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem row_phase_ramified (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val∣Ideal.span {u.val}) :
    idealRowHom u.val P.val=0 := by
  have hu : u.val∈P.val := (Ideal.dvd_iff_le.mp hP) (Ideal.subset_span (by simp))
  exact idealRowHom_zero_of_dvd u.val P.property (dvd_refl _) hu

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

theorem continuedMarkedLocal_unramified (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
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

theorem continuedCompensatedLocal_unramified (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CentralSlots
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma row_phase_norm_one_of_not_dvd (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) :
    ‖idealRowHom u.val P.val‖=1 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg := supported_prime_data p hp (hspan.symm ▸ hs)
  have hnot : ¬p∣u.val := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hu : IsCoprime u.val p := (hp.irreducible.coprime_iff_not_dvd.mpr hnot).symm
  have he : idealRowHom u.val P.val=actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    rw [←hspan,idealRowHom_prime u.val (Ideal.span {p}) hg.1]
  rw [he]
  exact Complex.norm_eq_one_of_pow_eq_one (actualSextic_unit_six p u.val hg.1 hg.2 hu) (by decide)

end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CentralNormalized
namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge

theorem actual_central_unramified_normalized (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (480:ℝ)≤P.val.absNorm)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖idealUnramifiedCorrection η u P x w z‖ ∧
    ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
      idealUnramifiedCorrection η u P x w z+star (idealRowHom u.val P.val)‖≤
        1440*(P.val.absNorm:ℝ)^(-(51/100:ℝ)) := by
  have heta := PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero hη
  have hv := row_phase_norm_one_of_not_dvd u P hs hn
  have hA := actualAPhase_norm_le_one η (primaryGenerator P.val)
  constructor
  · exact unramifiedClosed_central_lower _ a e _ _ _ x w z hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  · have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
    have hV : ‖coordV P.val.absNorm z‖<1 := by
      rw [coordV_norm _ hQ0]
      exact (rpow_le_half _ _ (by linarith) (by rw [hz];norm_num)).trans_lt (by norm_num)
    have hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 :=
      (coordR_norm_le _ hQ0 _ x z hA).trans_lt
        ((rpow_le_half _ _ (by linarith) (by rw [hx,hz];linarith)).trans_lt (by norm_num))
    rw [continuedCompensatedLocal_unramified η u P hs hn x w z hV hR]
    exact unramifiedSelected_central_quotient _ a e _ _ _ x w z hQ ha ha1 he he1 hA heta hv hx hw hz
end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CentralSplit
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

theorem centralNormalizedSlot_split (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    centralNormalizedSlot η u P hs x w z=
      -star (idealRowHom u.val P.val)+centralRegularError η u P hs x w z+
        centralRepeatedTerm η u P hs x w z := by
  by_cases hp : repeatedRowPrime u P
  · simp only [centralRegularError,centralRepeatedTerm,if_pos hp,row_phase_ramified u P hp.1,
      star_zero,neg_zero,zero_add]
  · simp only [centralRegularError,centralRepeatedTerm,if_neg hp]
    ring

theorem central_actual_local_bounds (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (480:ℝ)≤P.val.absNorm)
    (hsmall : 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖supportedCorrection η u P x w z‖ ∧
    ‖centralRegularError η u P hs x w z‖≤
      1440*(if P.val∣Ideal.span {u.val} then (P.val.absNorm:ℝ)^(1/2:ℝ)
        else (P.val.absNorm:ℝ)^(-(51/100:ℝ))) ∧
    ‖centralRepeatedTerm η u P hs x w z‖≤
      if repeatedRowPrime u P then 812*(P.val.absNorm:ℝ)^(1-w.re) else 0 := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQ1 : (1:ℝ)≤P.val.absNorm := by linarith
  by_cases hd : P.val∣Ideal.span {u.val}
  · have hb := actual_central_ramified_normalized η u P hs hd (by linarith)
      a e x w z hsmall ha ha1 he he1 hx hw hz
    have hcorr : supportedCorrection η u P x w z=ramifiedCorrection η u P hs x w z := by
      simp [supportedCorrection,hs,hd]
    refine ⟨hcorr.symm ▸ hb.1,?_,?_⟩
    · by_cases hj : 2≤ multiplicity (primaryGenerator P.val) u.val
      · simp [centralRegularError,repeatedRowPrime,hd,hj]
        positivity
      · have hp : ¬repeatedRowPrime u P := fun h=>hj h.2
        rw [centralRegularError,if_neg hp,row_phase_ramified u P hd,star_zero,add_zero,if_pos hd]
        have h := hb.2
        simp only [if_neg hj,add_zero] at h
        have hn : ‖centralNormalizedSlot η u P hs x w z‖≤800*(P.val.absNorm:ℝ)^(1/2:ℝ) := by
          dsimp only [centralNormalizedSlot]
          rw [hcorr]
          have hm := mul_le_mul_of_nonneg_left h hQ0.le
          have hpow : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-1:ℝ)=1 := by
            rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hQ0.ne'
          have hp2 : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-(1/2:ℝ))=
              (P.val.absNorm:ℝ)^(1/2:ℝ) := by
            conv_lhs => lhs;rw [←Real.rpow_one (P.val.absNorm:ℝ)]
            rw [←Real.rpow_add hQ0];norm_num
          rw [←mul_assoc,hpow,one_mul] at hm
          rw [mul_left_comm (P.val.absNorm:ℝ) 800,hp2] at hm
          exact hm
        exact hn.trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hQ0.le _))
    · by_cases hj : 2≤ multiplicity (primaryGenerator P.val) u.val
      · have hp : repeatedRowPrime u P := ⟨hd,hj⟩
        rw [centralRepeatedTerm,if_pos hp,if_pos hp]
        have h := hb.2
        rw [if_pos hj] at h
        have hpow : (P.val.absNorm:ℝ)^(-(1/2:ℝ))≤(P.val.absNorm:ℝ)^(-w.re) := by
          apply Real.rpow_le_rpow_of_exponent_le hQ1
          rw [hw];linarith
        have hn : (P.val.absNorm:ℝ)^(-1:ℝ)*‖centralNormalizedSlot η u P hs x w z‖≤
            812*(P.val.absNorm:ℝ)^(-w.re) := by
          dsimp only [centralNormalizedSlot];rw [hcorr]
          nlinarith
        have hm := mul_le_mul_of_nonneg_left hn hQ0.le
        have hi : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-1:ℝ)=1 := by
          rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hQ0.ne'
        have heq : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-w.re)=
            (P.val.absNorm:ℝ)^(1-w.re) := by
          conv_lhs => lhs;rw [←Real.rpow_one (P.val.absNorm:ℝ)]
          rw [←Real.rpow_add hQ0]; congr 1
        rw [←mul_assoc,hi,one_mul] at hm
        rw [mul_left_comm (P.val.absNorm:ℝ) 812,heq] at hm
        exact hm
      · have hp : ¬repeatedRowPrime u P := fun h=>hj h.2
        simp only [centralRepeatedTerm,if_neg hp,norm_zero,le_refl]
  · have hb := actual_central_unramified_normalized η u P hs hd hη a e x w z hQ
      ha ha1 he he1 hx hw hz
    have hc : supportedCorrection η u P x w z=idealUnramifiedCorrection η u P x w z := by
      simp [supportedCorrection,hs,hd]
    have hp : ¬repeatedRowPrime u P := fun h=>hd h.1
    refine ⟨hc.symm ▸ hb.1,?_,?_⟩
    · simpa only [centralRegularError,if_neg hp,centralNormalizedSlot,hc,if_neg hd] using hb.2
    · simp only [centralRepeatedTerm,if_neg hp,norm_zero,le_refl]
end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CentralBranchProduct
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralBranchProduct

theorem coupled_product_bound {ι : Type*} [Fintype ι]
    (L R : ℝ) (f g y : ι→ℝ) (hf : ∀i,0≤f i)
    (hsub : ∀J : Finset ι,L*(∏j ∈ J,g j)≤R*(∏j ∈ J,y j)) :
    L*(∏j : ι, (f j+g j))≤R*(∏j : ι, (f j+y j)) := by
  rw [Finset.prod_add,Finset.prod_add,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro J hJ
  calc
    _ = (∏j ∈ J,f j)*(L*∏j ∈ Finset.univ\J,g j) := by ring
    _ ≤ (∏j ∈ J,f j)*(R*∏j ∈ Finset.univ\J,y j) :=
      mul_le_mul_of_nonneg_left (hsub _) (Finset.prod_nonneg (fun j _=>hf j))
    _ = _ := by ring

theorem three_branch_bound {N : ℕ} (L R E : ℝ)
    (A B T : Fin N→ℂ) (y p : Fin N→ℝ)
    (hL : 0≤L) (hR : 0≤R) (hE : 0≤E) (hy : ∀j,0≤y j) (hp : ∀j,1≤p j)
    (hA : ∀j,‖A j‖≤y j*p j) (hB : ∀j,‖B j‖≤y j*E)
    (hT : ∀J : Finset (Fin N),L*(∏j ∈ J,‖T j‖)≤R*(∏j ∈ J,y j)) :
    L*‖∏j : Fin N, (A j+B j+T j)‖≤R*(E+2)^N*(∏j : Fin N, y j)*(∏j : Fin N,p j) := by
  have hnorm : ‖∏j : Fin N, (A j+B j+T j)‖≤∏j : Fin N,((‖A j‖+‖B j‖)+‖T j‖) := by
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _=>norm_nonneg _)
    intro j _
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hc := coupled_product_bound L R (fun j=>‖A j‖+‖B j‖) (fun j=>‖T j‖) y
    (fun j=>add_nonneg (norm_nonneg _) (norm_nonneg _)) hT
  have hpoint (j : Fin N) : (‖A j‖+‖B j‖)+y j≤y j*((E+2)*p j) := by
    have h := hp j
    have hp0 : 0≤p j := zero_le_one.trans h
    have he := mul_nonneg (show 0≤E+1 by linarith) (show 0≤p j-1 by linarith)
    have hm := mul_nonneg (hy j) he
    nlinarith [hA j,hB j]
  calc
    _ ≤ L*(∏j : Fin N,((‖A j‖+‖B j‖)+‖T j‖)) := mul_le_mul_of_nonneg_left hnorm hL
    _ ≤ R*(∏j : Fin N,((‖A j‖+‖B j‖)+y j)) := hc
    _ ≤ R*(∏j : Fin N, y j*((E+2)*p j)) := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.prod_le_prod (fun j _=>add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (hy j)) (fun j _=>hpoint j)
    _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin];ring
end SevenEighths.ProbeCentralBranchProduct

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CentralRepeatedProduct
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedProduct
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CompletedGauss
open HeckeDeletionBounds HeckeReciprocalGrowth
local notation "O" => HeckeFamily.O

lemma rowCost_nonneg (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (a e eps T : ℝ) : 0≤ rowCost S hS u a e eps T := by
  unfold rowCost presentationComplexity HeckeLogarithmic.complexity
  positivity

end SevenEighths.ProbeCentralRepeatedProduct

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.SelectedPrimeIndexed
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeSelectedPrimeSums
local notation "O" => ActualEisensteinCubic.O

lemma weighted_slot_bound_indexed (eps a b r d B K : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hd : d≤1) (hB : 0≤B) (hK : 0≤K) :
    ∃C : ℝ, 0<C ∧ ∀{ι : Type*} (f : ι→Ideal O), Function.Injective f →
    ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤P →
    ∀(S : Finset ι), (∀i∈S,f i≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤B) →
    ∀(G : ι→ℂ), (∀i∈S,‖G i‖≤K*(if f i∣U then (Ideal.absNorm (f i):ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑i∈S,‖W ((Ideal.absNorm (f i):ℝ)/P)*(Ideal.absNorm (f i):ℂ)^(z-1)*G i‖)
        ≤C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmain⟩ := weighted_slot_bound eps a b r d B K heps ha hb hd hB hK
  refine ⟨C,hC,?_⟩
  intro ι f hf U hU P hP S hS W hWS hWB G hG z hz
  let G' : Ideal O→ℂ := Function.extend f G (fun _=>0)
  have he (i : ι) : G' (f i)=G i := hf.extend_apply G (fun _=>0) i
  have hI (I : Ideal O) (hI : I∈S.image f) : I≠0 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact hS i hi
  have hg (I : Ideal O) (hI : I∈S.image f) :
      ‖G' I‖≤K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    rw [he]
    exact hG i hi
  have hh := hmain U hU P hP (S.image f) hI W hWS hWB G' hg z hz
  rw [Finset.sum_image hf.injOn] at hh
  simpa only [he] using hh

end SevenEighths.ProbeSelectedPrimeSums
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CentralSlotSum
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem central_regular_slot_sum (eps c d B : ℝ) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
      (hT : ∀P∈T,Supported P.val ∧ (480:ℝ)≤P.val.absNorm ∧ IsCoprime P.val η.modulus)
      (Y : ℝ),1≤Y → ∀(W : ℝ→ℂ),Function.support W⊆Set.Icc c d →
      (∀y,‖W y‖≤B) → ∀(a e : ℝ) (x w z : ℂ),
      (51/100:ℝ)≤a → a≤1 → 0<e → e≤1/1000 →
      x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 →
      (∀P∈T,198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
      (∑P:T,‖W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralRegularError η u P.val (hT P.val P.property).1 x w z‖)≤
      C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*Y^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed
    eps c d (-(4/25:ℝ)) 1 B 1440 heps hc hd (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro η u T hT Y hY W hWS hWB a e x w z ha ha1 he he1 hx hw hz hsmall
  let f : T→Ideal O := fun P=>P.val.val
  have hf : Function.Injective f := fun P Q h=>Subtype.ext (Subtype.ext h)
  let E : T→ℂ := fun P=>centralRegularError η u P.val (hT P.val P.property).1 x w z
  let G : T→ℂ := fun P=>((f P).absNorm:ℂ)^(1/2:ℂ)*E P
  have hnorm (P : T) : ‖G P‖≤1440*(if f P∣Ideal.span {u.val} then ((f P).absNorm:ℝ)^(1:ℝ) else 1) := by
    have hQ : (480:ℝ)≤(f P).absNorm := (hT P.val P.property).2.1
    have hQ0 : (0:ℝ)<(f P).absNorm := by linarith
    have hQ1 : (1:ℝ)≤(f P).absNorm := by linarith
    have hb := (central_actual_local_bounds η u P.val (hT P.val P.property).1
      (hT P.val P.property).2.2 a e x w z hQ (hsmall P.val P.property) ha ha1 he he1 hx hw hz).2.1
    have hn : ‖((f P).absNorm:ℂ)^(1/2:ℂ)‖=((f P).absNorm:ℝ)^(1/2:ℝ) := by
      rw [show ((f P).absNorm:ℂ)=(((f P).absNorm:ℝ):ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hQ0];norm_num
    dsimp only [G]
    rw [norm_mul,hn]
    calc
      _ ≤ ((f P).absNorm:ℝ)^(1/2:ℝ)*(1440*(if f P∣Ideal.span {u.val} then
          ((f P).absNorm:ℝ)^(1/2:ℝ) else ((f P).absNorm:ℝ)^(-(51/100:ℝ)))) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hQ0.le _)
      _ ≤ _ := by
        by_cases hp : f P∣Ideal.span {u.val}
        · simp only [if_pos hp]
          rw [mul_left_comm,←Real.rpow_add hQ0]
          norm_num
        · simp only [if_neg hp,mul_one]
          rw [mul_left_comm,←Real.rpow_add hQ0]
          have hh : ((f P).absNorm:ℝ)^((1/2:ℝ)-(51/100:ℝ))≤1 := by
            exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : (1/2:ℝ)-51/100≤0)).trans_eq (Real.rpow_zero _)
          norm_num only [show (1/2:ℝ)+-(51/100:ℝ)=(1/2:ℝ)-(51/100:ℝ) by ring]
          nlinarith
  have hb := hbound f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _=>P.val.property.ne_zero) W hWS hWB G (fun P _=>hnorm P)
    (z-1/2) (by simp only [Complex.sub_re];rw [hz];norm_num)
  have heq (P : T) :
      W (((f P).absNorm:ℝ)/Y)*((f P).absNorm:ℂ)^((z-1/2)-1)*G P=
      W (((f P).absNorm:ℝ)/Y)*((f P).absNorm:ℂ)^(z-1)*E P := by
    have hn : ((f P).absNorm:ℂ)≠0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero
    dsimp only [G]
    rw [←mul_assoc,mul_assoc (W _) ,←Complex.cpow_add _ _ hn]
    rw [show (z - 1 / 2) - 1 + 1 / 2 = z - 1 by ring]
  simpa only [heq] using hb
end SevenEighths.ProbeHighRowFamily
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CentralAllSlots
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralAllSlots
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ProbeCentralRepeatedProduct
open ProbeCentralRepeatedSubset ProbeCentralBranchProduct
local notation "O" => HeckeFamily.O

theorem actual_three_branch_slots_oai (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hs : ∀j P,P∈T j→Supported P.val),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀p : Fin N→ℝ,(∀j,1≤p j) → (∀j,‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j) →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ‖∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u P.val (hs j P.val P.property) x w z‖ ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by
  obtain ⟨Cr,hCr,hregular⟩ := central_regular_slot_sum eps c d B heps hc hd hB
  obtain ⟨Ct,hCt,hrepeated⟩ := actual_repeated_subset N e eps c d B he he1 heps hc hd hB
  refine ⟨Ct*(Cr+2)^N,by positivity,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi p hp hphase
  let L := ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖
  let U : ℝ := (Ideal.span {u.val}:Ideal O).absNorm
  let R := Ct*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*U^eps
  let A : Fin N→ℂ := fun j=>phaseSlot u (T j) (W j) (Y j) z
  let E : Fin N→ℂ := fun j=>∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
    centralRegularError η u P.val (hs j P.val P.property) x w z
  let F : Fin N→ℂ := fun j=>∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
    centralRepeatedTerm η u P.val (hs j P.val P.property) x w z
  let yy : Fin N→ℝ := fun j=>(Y j)^(-(4/25:ℝ))
  have hU : 1≤U := by dsimp [U];exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hUp : 1≤U^eps := Real.one_le_rpow hU heps.le
  have hR : 0≤R := by dsimp [R];exact mul_nonneg (mul_nonneg hCt.le (rowCost_nonneg _ _ _ _ _ _ _)) (Real.rpow_nonneg (zero_le_one.trans hU) _)
  have hyy (j : Fin N) : 0≤yy j := Real.rpow_nonneg (zero_le_one.trans (hY j)) _
  have hE (j : Fin N) : ‖E j‖≤yy j*(Cr*U^eps) := by
    have hb := hregular η u (T j) (fun P hP=>⟨hs j P hP,hQ j P hP,hη j P hP⟩)
      (Y j) (hY j) (W j) (hWS j) (hW j) a e x w z ha ha1 he he1.le hx hw hz (hsmall j)
    exact (norm_sum_le _ _).trans (hb.trans_eq (by dsimp [yy,U];ring))
  have hF (J : Finset (Fin N)) : L*(∏j∈J,‖F j‖)≤R*(∏j∈J,yy j) := by
    have hb := hrepeated S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall
      W Y hY hWS hW x w z hx hw hz hwi J
    have hp' : (∏j:J,‖F j.val‖)≤∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*
        (P.val.val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖ := by
      apply Finset.prod_le_prod (fun _ _=>norm_nonneg _)
      intro j _
      exact norm_sum_le _ _
    have hh := (mul_le_mul_of_nonneg_left hp' (show 0≤L from norm_nonneg _)).trans hb
    rw [Finset.prod_coe_sort J (fun j=>‖F j‖),
      Finset.prod_coe_sort J (fun j=>(Y j)^(-(4/25:ℝ)))] at hh
    exact hh
  have hb := three_branch_bound L R (Cr*U^eps) A E F yy p (norm_nonneg _) hR (by positivity) hyy hp hphase hE hF
  have heq : (∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralNormalizedSlot η u P.val (hs j P.val P.property) x w z)=∏j,(A j+E j+F j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [A,E,F,phaseSlot,centralNormalizedSlot_split,mul_add,Finset.sum_add_distrib]
  rw [heq]
  apply hb.trans
  have hcoef : (Cr*U^eps+2)^N≤(Cr+2)^N*U^(eps*N) := by
    have hh : Cr*U^eps+2≤(Cr+2)*U^eps := by nlinarith
    have hp' := pow_le_pow_left₀ (show 0≤Cr*U^eps+2 by positivity) hh N
    rw [mul_pow] at hp'
    have heq : (U^eps)^N=U^(eps*N) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hU)]
    rwa [heq] at hp'
  have hyprod : 0≤∏j,yy j := Finset.prod_nonneg (fun j _=>hyy j)
  have hpprod : 0≤∏j,p j := Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))
  calc
    _ ≤ R*((Cr+2)^N*U^(eps*N))*(∏j,yy j)*(∏j,p j) := by gcongr
    _ = _ := by
      dsimp [R,yy]
      have hh : U^eps*U^(eps*N)=U^(eps*(N+1)) := by rw [←Real.rpow_add (zero_lt_one.trans_le hU)];congr 1;ring
      calc
        _ = Ct*(Cr+2)^N*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*(U^eps*U^(eps*N))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by ring
        _ = _ := by rw [hh]
end SevenEighths.ProbeCentralAllSlots

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.ProbeCentralAllSlots.actual_three_branch_slots_oai.{u_1} := @OAI.SevenEighths.ProbeCentralAllSlots.actual_three_branch_slots_oai.{u_1}
