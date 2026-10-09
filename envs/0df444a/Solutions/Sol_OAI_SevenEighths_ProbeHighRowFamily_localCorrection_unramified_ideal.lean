-- Prove2me | solution 1 for OAI.SevenEighths.ProbeHighRowFamily.localCorrection_unramified_ideal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:25:28.514239+00:00
-- url     : https://prove2.me/submissions/cc2c7b45-6a8a-4080-bcd0-882f595b26a0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_rowClosedMarked_unramified
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_rowInner_zero_squarefree_summable
import Theorems.Thm_OAI_SevenEighths_ProbeEuler_rowMarkedSeries_eq_closed
import Theorems.Thm_OAI_SevenEighths_ProbePhysical_bareIdealHighSummand_row_at_prime
import Theorems.Thm_OAI_SevenEighths_ProbePrimePower_actualSextic_neg_one_sq
import Theorems.Thm_OAI_SmoothMobiusCorrection_prime_norm_two_le

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrimePhase
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge QuadraticGaussRay FiniteGaussPhase CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem normalizedTraceGauss_eq_normalizedGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) :
    letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
    letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
    ConcreteBreveE.normalizedTraceGauss p hp χ =
      ProbeGauss.normalizedGauss χ (quotientTrace p hp) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn : Real.sqrt (Nat.card (O ⧸ Ideal.span {p}) : ℝ) = ‖eisEmbedding p‖ := by
    change Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) = _
    rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]
  simp only [ConcreteBreveE.normalizedTraceGauss, ProbeGauss.normalizedGauss,
    quotientTrace, ← Nat.card_eq_fintype_card, hn]

end SevenEighths.ProbePhase
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.ScalarTable
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem zero_index_scalar (p : O) (_hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (k j : ℕ) (_hk : k ≠ 0) :
    (χ^k) (Ideal.Quotient.mk _ (p^j)) = if j=0 then 1 else 0 := by
  by_cases hj : j=0
  · simp [hj]
  · rw [if_neg hj]
    have hz : Ideal.Quotient.mk (Ideal.span {p}) (p^j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_pow_self p hj))
    rw [hz, MulChar.map_zero]

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

lemma one_sub_ne_zero_of_norm_lt_one (a : ℂ) (ha : ‖a‖<1) : 1-a ≠ 0 := by
  intro h
  have he : a=1 := by linear_combination -h
  rw [he, norm_one] at ha
  exact lt_irrefl _ ha

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.SpectralWeights
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma signed_diagonal_phase (omega : ℂ) (ho : omega^2=1) (e l k : ℕ) :
    omega^(((e+3*l)*k:ℕ):ℤ) * omega^(-((e*l+l.choose 2:ℕ):ℤ)) =
      omega^((e+3*l)*k+e*l+l.choose 2) := by
  have hn : omega≠0 := by intro h; simp [h] at ho
  have hi : omega⁻¹=omega := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using ho
  rw [zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, hi, ← pow_add]
  congr 1
  omega

lemma source_signed_phase (C omega : ℂ) (ho : omega^2=1) (e l k : ℕ) :
    C ^l * omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ)) =
      localCubePhase C omega e l k := by
  have hn : omega≠0 := by intro h; simp [h] at ho
  rw [sub_eq_add_neg, zpow_add₀ hn, signed_diagonal_phase omega ho]
  rfl

lemma spectral_power_split (Q : ℝ) (hQ : 0<Q) (x w z : ℂ) (e l k m : ℕ) :
    (Q:ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
      ((Q:ℂ)^(-x)/(Q:ℂ)^(1/2:ℂ))^e *
      (((Q:ℂ)^(-x))^3/(Q:ℂ))^l * ((Q:ℂ)^(-w))^k * ((Q:ℂ)^(-6*z))^m := by
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  have h1 : (Q:ℂ)^(-x)/(Q:ℂ)^(1/2:ℂ) = (Q:ℂ)^(-x-(1/2:ℂ)) :=
    (Complex.cpow_sub _ _ hn).symm
  have h3 : ((Q:ℂ)^(-x))^3/(Q:ℂ) = (Q:ℂ)^(-1-3*x) := by
    rw [← Complex.cpow_nat_mul (Q:ℂ) 3 (-x)]
    calc
      _ = (Q:ℂ)^(3*(-x)) / (Q:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]; norm_num
      _ = (Q:ℂ)^(3*(-x)-1) := (Complex.cpow_sub _ _ hn).symm
      _ = _ := by congr 1; ring
  rw [h1, h3, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
  congr 1
  ring

lemma cpow_half_eq_sqrt (Q : ℝ) (hQ : 0≤Q) :
    (Q:ℂ)^(1/2:ℂ) = (Real.sqrt Q:ℂ) := by
  rw [Real.sqrt_eq_rpow]
  simpa using (Complex.ofReal_cpow hQ (1/2:ℝ)).symm

theorem sourceWeightedScalar_eq (Q : ℝ) (hQ : 0<Q)
    (eta a gamma1 G1 C omega x w z scalar : ℂ) (hG : G1=gamma1*(Real.sqrt Q:ℂ))
    (ho : omega^2=1) (e l k m : ℕ) :
    sourceWeightedScalar Q eta a gamma1 C omega x w z scalar e l k m =
      weightedScalar Q eta a G1 C omega ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w))
        ((Q:ℂ)^(-6*z)) scalar e l k m := by
  unfold sourceWeightedScalar weightedScalar
  rw [spectral_power_split Q hQ, cpow_half_eq_sqrt Q hQ.le]
  rw [zpow_neg, zpow_natCast]
  have hphase := source_signed_phase 1 omega ho e l k
  simp only [localCubePhase, one_pow, one_mul] at hphase
  unfold localCubePhase
  rw [hphase, mul_pow a C, hG]
  simp only [mul_pow, div_pow]

  ring

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma firstGauss_eq_gamma_sqrt (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda ∉ Ideal.span {p}) :
    primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 =
      localGamma p hp.ne_zero hg 1 *
        (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hs : (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hQ).ne'
  unfold localGamma
  rw [pow_one, ProbePhase.normalizedTraceGauss_eq_normalizedGauss]
  simp only [ProbeGauss.normalizedGauss, ← Nat.card_eq_fintype_card]
  change _ = (gaussSum _ _ / (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ)) * _
  rw [div_mul_cancel₀ _ hs]
  simp only [primeGauss, map_one, one_mul, tsum_fintype, gaussSum]

theorem sourceWeightedScalar_actual (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda ∉ Ideal.span {p})
    (eta a x w z scalar : ℂ) (e l k m : ℕ) :
    sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
      (actualSextic (Ideal.span {p}) hg (-1)) x w z scalar e l k m =
    weightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-6*z)) scalar e l k m := by
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  simpa only [Complex.ofReal_natCast] using
    sourceWeightedScalar_eq _ hQ eta a (localGamma p hp.ne_zero hg 1) _
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1))
      x w z scalar (firstGauss_eq_gamma_sqrt p hp hg)
      (actualSextic_neg_one_sq _ hg) e l k m

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.ZeroIndex
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]

omit [(Ideal.span {p}).IsMaximal] in
lemma zeroIndex_inner_zero (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (hV : ‖V‖<1) :
    HasSum (fun m => zeroIndexTerm p χ W V 0 m) (1/(1-V)) := by
  simpa [zeroIndexTerm, one_div] using hasSum_geometric_of_norm_lt_one hV

include hp in
lemma zeroIndex_inner_pos (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (k : ℕ) (hk : k≠0) :
    HasSum (fun m => zeroIndexTerm p χ W V k m) (W^k) := by
  apply (hasSum_ite_eq 0 (W^k)).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hm
  dsimp only
  unfold zeroIndexTerm
  rw [if_neg hk, zero_index_scalar p hp χ k (6*m) hk]
  by_cases h : m=0
  · subst m; simp
  · have h6 : 6*m≠0 := by omega
    simp [h, h6]

include hp in
lemma zeroIndexSeries_eq (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (hW : ‖W‖<1) (hV : ‖V‖<1) :
    zeroIndexSeries p χ W V = 1/(1-V)+W/(1-W) := by
  have htail : HasSum (fun k => ∑' m, zeroIndexTerm p χ W V (k+1) m) (W/(1-W)) := by
    have he : (fun k => ∑' m, zeroIndexTerm p χ W V (k+1) m) =
        (fun k => W * W^k) := by
      funext k
      rw [(zeroIndex_inner_pos p hp χ W V (k+1) (by omega)).tsum_eq, pow_succ]
      ring
    rw [he]
    simpa [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hW).mul_left W
  have hall := HasSum.sum_range_add (f := fun k => ∑' m, zeroIndexTerm p χ W V k m) (k := 1) htail
  simpa only [zeroIndexSeries, Finset.sum_range_one,
    (zeroIndex_inner_zero p χ W V hV).tsum_eq] using hall.tsum_eq

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsPrime
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

theorem sourceRowTerm_pos (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (eta a rho x w z : ℂ) (j e l k m : ℕ)
    (ht : e+3*l≠0) :
    sourceRowTerm p hp hg eta a rho x w z j e l k m=
      rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        rho j e l k m := by
  unfold sourceRowTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [rowMarkedTerm,rowWeightedScalar,sourceScalar,if_neg ht,coordV,Complex.ofReal_natCast]

end SevenEighths.ProbeEuler
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem idealRowHighLocalFactor_eq_source (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p) (j : ℕ) (x w z : ℂ) :
    idealRowHighLocalFactor η (b*p^j) (Ideal.span {p}) x w z=
      ∑ e : Fin 2,∑' l,∑' k,∑' m,sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e.val l k m := by
  unfold idealRowHighLocalFactor
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact bareIdealHighSummand_row_at_prime η p hp hg hchar hprimary hs b hb j e.val l k m (by omega) x w z

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsZero
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})

theorem sourceRowTerm_zero (eta a rho x w z : ℂ) (j k m : ℕ) :
    sourceRowTerm p hp hg eta a rho x w z j 0 0 k m=
      rowZeroIndexTerm p (actualSextic (Ideal.span {p}) hg)
        (rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) j k m := by
  unfold sourceRowTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [rowZeroIndexTerm,sourceScalar,weightedScalar,localCubePhase,
    coordV,Complex.ofReal_natCast,mul_zero,add_zero,pow_zero,one_mul,mul_one,
    zero_mul,Nat.choose_zero_succ,ite_true,div_one,mul_pow]
  ring

omit [(Ideal.span {p}).IsMaximal] in
lemma rowZeroIndex_zero (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j : ℕ) (hV : ‖V‖<1) :
    HasSum (fun m=>rowZeroIndexTerm p χ W V j 0 m) (1/(1-V)) := by
  simpa only [rowZeroIndexTerm,ite_true,pow_zero,one_mul,one_div] using
    hasSum_geometric_of_norm_lt_one hV

include hp in
theorem rowZeroIndex_pos_ramified (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j k m : ℕ) (hj : j≠0) (hk : k≠0) : rowZeroIndexTerm p χ W V j k m=0 := by
  rw [rowZeroIndexTerm,if_neg hk,zero_index_scalar p hp χ k (j+6*m) hk,
    if_neg (by omega),zero_mul,zero_mul]

include hp in
theorem rowZeroIndexSeries_eq (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j : ℕ) (hW : ‖W‖<1) (hV : ‖V‖<1) :
    (∑' k,∑' m,rowZeroIndexTerm p χ W V j k m)=
      1/(1-V)+(if j=0 then W/(1-W) else 0) := by
  by_cases hj : j=0
  · subst j
    simp only [rowZeroIndexTerm,zero_add,ite_true]
    exact zeroIndexSeries_eq p hp χ W V hW hV
  · rw [if_neg hj,add_zero]
    rw [tsum_eq_single 0]
    · exact (rowZeroIndex_zero p χ W V j hV).tsum_eq
    · intro k hk
      simp only [rowZeroIndex_pos_ramified p hp χ W V j k _ hj hk,tsum_zero]

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsClosed
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in

theorem sourceRowSeries_eq_closed (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1) (j : ℕ) (hj : j<6) :
    sourceRowSeries p hp hg eta a rho x w z j=
      1/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)+
      (if j=0 then (rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))/
        (1-rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))) else 0)+
      rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j := by
  let X : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)
  let W : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)
  let V : ℂ := coordV (Ideal.absNorm (Ideal.span {p})) z
  let Z0 := 1/(1-V)+(if j=0 then rho*W/(1-rho*W) else 0)
  have he0 (l : ℕ) : (∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j 0 l k m)=
      rowInner p hp hg eta a X W V rho j 0 l+(if l=0 then Z0 else 0) := by
    by_cases hl : l=0
    · subst l
      simp only [sourceRowTerm_zero,rowInner_zero,ite_true,zero_add]
      exact rowZeroIndexSeries_eq p hp (actualSextic (Ideal.span {p}) hg) (rho*W) V j hW hV
    · rw [if_neg hl,add_zero]
      apply tsum_congr
      intro k
      apply tsum_congr
      intro m
      exact sourceRowTerm_pos p hp hg eta a rho x w z j 0 l k m (by omega)
  have he1 (l : ℕ) : (∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j 1 l k m)=
      rowInner p hp hg eta a X W V rho j 1 l := by
    apply tsum_congr
    intro k
    apply tsum_congr
    intro m
    exact sourceRowTerm_pos p hp hg eta a rho x w z j 1 l k m (by omega)
  have hs := rowInner_zero_squarefree_summable p hp hg hc eta a X W V rho hρ hV hR j hj
  have hc' := rowMarkedSeries_eq_closed p hp hg hc eta a X W V rho hρ hV hR j hj
  unfold rowMarkedSeries at hc'
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one] at hc'
  unfold sourceRowSeries
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one,he0,he1]
  rw [hs.tsum_add (hasSum_ite_eq 0 Z0).summable,tsum_ite_eq]
  change _=Z0+rowClosedMarked p hp hg eta a X W V rho j
  rw [←hc']
  ring

end SevenEighths.ProbeEuler
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsUnramified
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in

theorem sourceRowSeries_unramified_euler (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) rho w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta rho x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourceRowSeries p hp hg eta a rho x w z 0=
      (1-coordD Q eta rho x)/((1-coordV Q z)*(1-coordW Q rho w))*
        unramifiedClosed Q (a^2) eta rho x w z := by
  dsimp only
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a x z
  simp only [Complex.ofReal_natCast] at hr
  have hr' : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hr]; exact hR
  rw [sourceRowSeries_eq_closed p hp hg hc eta a rho x w z hρ hV hr' hW 0 (by decide)]
  rw [rowClosedMarked_unramified p hp hg hc _ _ _ _ _ _ hρ hV hr',hr]
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ eta x w
  simp only [Complex.ofReal_natCast] at hk
  rw [←hk]
  have hinv : rho⁻¹=star rho := Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hρ (by decide))
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  simp only [ite_true,div_eq_mul_inv,hinv]
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  simp only [coordW,coordD,Complex.ofReal_natCast] at hD hw ⊢
  field_simp [hD,hv,hw]
  ; ring

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsRegion
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma row_initial_geometric (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (b : O) (hb : IsCoprime b p)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)
    ‖coordV Q z‖<1 ∧ ‖coordR Q ((actualACube η p)^2) x z‖<1 ∧
      ‖coordW Q rho w‖<1 ∧ ‖coordD Q (targetMonoid η p) rho x‖<1 := by
  dsimp only
  have hP : Prime (Ideal.span {p}:Ideal O) := (Ideal.prime_span_singleton_iff).mpr hp
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hn : ‖actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)‖≤1 :=
    (Complex.norm_eq_one_of_pow_eq_one (actualSextic_unit_six p b hg hc hb) (by decide)).le
  refine ⟨?_,?_,?_,?_⟩
  · rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · apply (coordW_norm_le _ hQ0 _ w hn).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · apply (coordD_norm_le _ hQ0 _ _ x (targetMonoid_norm_le_one η p) hn).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)

theorem idealRowHighLocalFactor_unramified (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)
    idealRowHighLocalFactor η b (Ideal.span {p}) x w z=
      (1-coordD Q (targetMonoid η p) rho x)/((1-coordV Q z)*(1-coordW Q rho w))*
        unramifiedClosed Q (actualAPhase η p) (targetMonoid η p) rho x w z := by
  have hd := row_initial_geometric η p hp hg hc b hb x w z hx hw hz
  dsimp only at hd ⊢
  have he := idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs b hb 0 x w z
  simp only [pow_zero,mul_one] at he
  rw [he]
  simpa only [actualACube_sq,_root_.OAI.SevenEighths.ProbeEuler.sourceRowSeries] using
    sourceRowSeries_unramified_euler p hp hg hc (targetMonoid η p) (actualACube η p)
      _ x w z (actualSextic_unit_six p b hg hc hb) hd.1 hd.2.1 hd.2.2.1
      (one_sub_ne_zero_of_norm_lt_one _ hd.2.2.2)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.Unramified
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem localCorrection_coordinates (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (x w z : ℂ) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u.val)
    localCorrection η u ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ x w z=
      idealRowHighLocalFactor η u.val (Ideal.span {p}) x w z *
        (1-coordV Q z)*(1-coordW Q rho w)/(1-coordD Q (targetMonoid η p) rho x) := by
  dsimp only
  have hP0 : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero
  unfold localCorrection coordV coordW coordD
  simp only [CubicEisenstein.fullIdealWeight,hP0,ite_false,Complex.ofReal_natCast]
  rw [idealCoeff_span η hp.ne_zero,idealRowHom_prime u.val (Ideal.span {p}) hg]
  rw [show -(6*z)=(-6 : ℂ)*z by ring]
  rfl

theorem localCorrection_unramified (η : Character) (u : FreeRow) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : CanonicalQuadraticSieve.Supported (Ideal.span {p})) (hu : IsCoprime u.val p)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ x w z=
      actualUnramifiedClosed η p u.val hg x w z := by
  rw [localCorrection_coordinates η u p hp hg]
  rw [idealRowHighLocalFactor_unramified η p hp hg hc hprimary hs u.val hu x w z hx hw hz]
  have hgeom := row_initial_geometric η p hp hg hc u.val hu x w z hx hw hz
  dsimp only at hgeom
  have hV := one_sub_ne_zero_of_norm_lt_one _ hgeom.1
  have hW := one_sub_ne_zero_of_norm_lt_one _ hgeom.2.2.1
  have hD := one_sub_ne_zero_of_norm_lt_one _ hgeom.2.2.2
  unfold actualUnramifiedClosed
  change _=unramifiedClosed _ _ (targetMonoid η p) _ x w z
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.Ideal
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem localCorrection_unramified_ideal_oai (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hcop : IsCoprime P.val (Ideal.span {u.val}))
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    localCorrection η u P x w z=idealUnramifiedCorrection η u P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  have hu : IsCoprime u.val p := ((Ideal.isCoprime_span_singleton_iff p u.val).mp
    (by rw [hspan]; exact hcop)).symm
  have he := localCorrection_unramified η u p hp hg.1 hg.2 hprimary hsp hu x w z hx hw hz
  have hP : (⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩ : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)=P := Subtype.ext hspan
  rw [hP] at he
  unfold actualUnramifiedClosed at he
  rw [←idealCoeff_span η hp.ne_zero,←idealRowHom_prime u.val (Ideal.span {p}) hg.1,hspan] at he
  exact he

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeHighRowFamily.localCorrection_unramified_ideal_oai := @OAI.SevenEighths.ProbeHighRowFamily.localCorrection_unramified_ideal_oai
