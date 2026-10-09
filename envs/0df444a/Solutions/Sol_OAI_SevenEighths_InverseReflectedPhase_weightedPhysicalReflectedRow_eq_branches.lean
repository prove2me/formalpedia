-- Prove2me | solution 1 for OAI.SevenEighths.InverseReflectedPhase.weightedPhysicalReflectedRow_eq_branches
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:43:38.524804+00:00
-- url     : https://prove2.me/submissions/295170ed-735d-4d3e-8109-f522c603a778

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B028

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
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

namespace ActualEisensteinCubic

theorem canonicalSextic_sq_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 := by
  have hP2 : (canonicalSextic P hPgood (Ideal.Quotient.mk P q)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar P hPgood (Ideal.Quotient.mk P q)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  have hQ2 : (canonicalSextic Q hQgood (Ideal.Quotient.mk Q p)) ^ 2 =
      ConcreteTraceCRT.eisEmbedding (cubicChar Q hQgood (Ideal.Quotient.mk Q p)) := by
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), canonicalSextic_pow_two]
    rfl
  rw [hP2, hQ2, cubic_reciprocity_primary P Q hPgood hQgood p q hP hQ hpprimary hqprimary]

end ActualEisensteinCubic

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.LocalBrackets
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets

section

variable {F : Type*} [Field F] [Fintype F]

theorem rootCard_pos : 0 < rootCard F := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩

theorem rootCard_sq : rootCard F ^ 2 = (Fintype.card F : ℝ) := Real.sq_sqrt (by positivity)

theorem bracket_four_split (χ : MulChar F ℂ) (x : F) :
    bracket χ 4 x = -(rootCard F : ℂ)⁻¹ + (rootCard F : ℂ) * if x = 0 then 1 else 0 := by
  have hr : (rootCard F : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos)
  have hsq : (rootCard F : ℂ) ^ 2 = (Fintype.card F : ℂ) := by exact_mod_cast (rootCard_sq (F := F))
  simp only [bracket, ↓reduceIte]
  rw [← hsq]
  field_simp

theorem bracket_four_cube_split (χ : MulChar F ℂ) (n b : F) :
    bracket χ 4 (n * b ^ 3) = -(rootCard F : ℂ)⁻¹ +
      (rootCard F : ℂ) * (if n = 0 then 1 else 0) +
      (rootCard F : ℂ) * (if n ≠ 0 ∧ b = 0 then 1 else 0) := by
  rw [bracket_four_split]
  by_cases hn : n = 0 <;> by_cases hb : b = 0 <;> simp [hn, hb]

end

open ActualEisensteinCubic

end LocalReflectionBrackets

open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets

variable {F : Type*} [Field F] [Fintype F]

open ActualEisensteinCubic

attribute [local instance] OAI.LocalReflectionBrackets.quotientFieldNormalized
attribute [local instance] OAI.LocalReflectionBrackets.quotientFintypeNormalized
theorem canonical_bracket_four_cube_split (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (n b : O) :
    bracket (canonicalSextic P hgood) 4 (Ideal.Quotient.mk P (n * b ^ 3)) =
      -(rootCard (O ⧸ P) : ℂ)⁻¹ + (rootCard (O ⧸ P) : ℂ) * (if n ∈ P then 1 else 0) +
      (rootCard (O ⧸ P) : ℂ) * (if n ∉ P ∧ b ∈ P then 1 else 0) := by
  rw [map_mul, map_pow, bracket_four_cube_split]
  simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem]

end LocalReflectionBrackets

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

theorem idealSupport_singleton_univ (D : Ideal O) :
    idealSupport {D} D = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro P
  apply (mem_idealSupport_iff {D} D P).mpr
  obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp P.property
  have hID : I = D := Finset.mem_singleton.mp hI
  simpa only [hID] using hP

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RowCaps
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

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets

theorem bracket_four_eq_sum_exceptionalPiece (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (n b : O) :
    bracket (actualSextic P hg) 4 (Ideal.Quotient.mk P (n*b^3)) =
      ∑e : Fin 3, exceptionalPiece P e n b := by
  rw [canonical_bracket_four_cube_split]
  simp [Fin.sum_univ_succ,exceptionalPiece]
  ring

theorem rootCard_eq_sqrt_absNorm (P : Ideal O) [P.IsMaximal] :
    rootCard (O ⧸ P)=Real.sqrt (Ideal.absNorm P:ℝ) := by
  rw [rootCard,←Nat.card_eq_fintype_card]
  rfl

end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.NormalizedMass
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

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic LocalReflectionBrackets

theorem bracket_one_eq_quadratic (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (z : O) :
    bracket (actualSextic P hg) 1 (Ideal.Quotient.mk P z)=
      (actualSextic P hg (Ideal.Quotient.mk P z))^3 := by
  simp only [bracket,show (1:ℕ)≠4 by decide,show (1:ℕ)≠0 by decide,↓reduceIte]
  rw [show (1:ℕ)+2=3 by rfl,MulChar.inv_apply_eq_inv',MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]
  by_cases hz : z∈P
  · have he : Ideal.Quotient.mk P z=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
    simp [he]
  · have h6 := canonicalSextic_sixth_power_mask P hg z
    change actualSextic P hg (Ideal.Quotient.mk P (z^6))=_ at h6
    simp only [map_pow,if_neg hz] at h6
    apply inv_eq_of_mul_eq_one_right
    calc
      _ = (actualSextic P hg (Ideal.Quotient.mk P z))^6 := by ring
      _ = 1 := h6

theorem quadratic_value_cube (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (b : O) :
    (actualSextic P hg (Ideal.Quotient.mk P (b^3)))^3=
      (actualSextic P hg (Ideal.Quotient.mk P b))^3 := by
  simp only [map_pow]
  by_cases hb : b∈P
  · have he : Ideal.Quotient.mk P b=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    simp [he]
  · have h6 := canonicalSextic_sixth_power_mask P hg b
    change actualSextic P hg (Ideal.Quotient.mk P (b^6))=_ at h6
    simp only [map_pow,if_neg hb] at h6
    calc
      _ = (actualSextic P hg (Ideal.Quotient.mk P b))^3 *
          (actualSextic P hg (Ideal.Quotient.mk P b))^6 := by ring
      _ = _ := by rw [h6,mul_one]

theorem residual_bracket_cube (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (z n b : O) :
    bracket (actualSextic P hg) 1 (Ideal.Quotient.mk P (z*n*b^3))=
      (actualSextic P hg (Ideal.Quotient.mk P z))^3 *
      (actualSextic P hg (Ideal.Quotient.mk P (n*b)))^3 := by
  rw [bracket_one_eq_quadratic]
  simp only [map_mul,mul_pow]
  rw [quadratic_value_cube]
  ring

end

open ActualEisensteinCubic UniqueFactorizationMonoid

open ActualEisensteinCubic UniqueFactorizationMonoid

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ReflectedBranches
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

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic LocalReflectionBrackets

theorem bracket_eq_sum_reflectedLocalPiece (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (j : ℕ) (n b : O) :
    bracket (actualSextic P hg) j (Ideal.Quotient.mk P (n*b^3))=
      ∑e : Fin 3, reflectedLocalPiece P hg j e n b := by
  by_cases hj : j=4
  · subst j
    simpa only [reflectedLocalPiece,ite_true] using bracket_four_eq_sum_exceptionalPiece P hg n b
  · simp [reflectedLocalPiece,hj]

theorem prod_bracket_eq_full_branches {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (n b : O) :
    (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (n*b^3)))=
      ∑e : ι→Fin 3,reflectedBranch P hg j e n b := by
  simp_rw [bracket_eq_sum_reflectedLocalPiece]
  simpa only [Fintype.piFinset_univ,reflectedBranch] using
    Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset (Fin 3)))
      (fun i e => reflectedLocalPiece (P i) (hg i) (j i) e n b)

theorem reflectionExtractedDivisor_ne_zero {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hP : ∀i,P i≠0) (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) :
    reflectionExtractedDivisor P j e v≠0 := by
  unfold reflectionExtractedDivisor
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  unfold reflectionExtractedPrime
  split_ifs
  · exact hP i
  · exact one_ne_zero

end

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open MeasureTheory Filter

end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.BranchScaling
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical
namespace LocalReflectionBrackets
variable {F : Type*} [Field F] [Fintype F]

theorem bracket_mul_unit (χ : MulChar F ℂ) (j : ℕ) (z x : F) (hz : z≠0) :
    bracket χ j (z*x)=unitArgumentFactor χ j z*bracket χ j x := by
  by_cases hj4 : j=4
  · simp [unitArgumentFactor,bracket,hj4,hz]
  · by_cases hj0 : j=0
    · subst j
      simp only [unitArgumentFactor,bracket,show (0:ℕ)≠4 by decide,ite_false,ite_true,
        zero_add,map_mul]
      ring
    · simp only [unitArgumentFactor,bracket,if_neg hj4,if_neg hj0,map_mul]

end LocalReflectionBrackets
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets

theorem unit_ramified_quotient_ne_zero (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (u : Oˣ) (m : ℕ) :
    Ideal.Quotient.mk P ((u:O)*lambda^m)≠0 := by
  rw [map_mul,map_pow]
  apply mul_ne_zero
  · exact (u.isUnit.map (Ideal.Quotient.mk P)).ne_zero
  · exact pow_ne_zero _ (fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h))

theorem ramified_bracket_full_expansion {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (u : Oˣ) (m : ℕ) (n b : O) :
    (∏i,bracket (actualSextic (P i) (hg i)) (j i)
      (Ideal.Quotient.mk (P i) ((u:O)*lambda^m*(n*b^3))))=
      ramifiedBranchPhase P hg j u m*∑e : ι→Fin 3,reflectedBranch P hg j e n b := by
  have hl (i : ι) : bracket (actualSextic (P i) (hg i)) (j i)
      (Ideal.Quotient.mk (P i) ((u:O)*lambda^m*(n*b^3)))=
      unitArgumentFactor (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) ((u:O)*lambda^m))*
      bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (n*b^3)) := by
    rw [map_mul]
    exact bracket_mul_unit _ _ _ _ (unit_ramified_quotient_ne_zero (P i) (hg i) u m)
  simp_rw [hl]
  rw [Finset.prod_mul_distrib,prod_bracket_eq_full_branches P hg j n b]
  rfl

end CompletedGauss

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.CompletedEnergy
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical
namespace CompletedGauss

open ActualEisensteinCubic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)

lemma paperLambda_eq : paperLambda=paperLambdaUnit.val*lambda := by
  change 1+2*omega=(-omega)*lambda
  change (1+2*omega:ActualEisensteinCubic.O)=(-omega)*(omega-1)
  have hw:=omega_primitive.geom_sum_eq_zero (by decide : 1<(3:ℕ))
  norm_num [Finset.sum_range_succ] at hw
  linear_combination hw

end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.RamifiedValuation
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma onceCuspScale_not_three_dvd (t:Eisˣ) : ¬(3:Eis)∣onceCuspScale t := by
  rintro ⟨z,hz⟩
  have hq:Ideal.absNorm (Ideal.span {onceCuspScale t})=3:=by
    simpa only [Fin.val_zero,pow_zero,mul_one] using onceCusp_q_absNorm t 0
  have he:=congrArg (fun x:Eis=>Ideal.absNorm (Ideal.span {x})) hz
  rw [hq,←Ideal.span_singleton_mul_span_singleton,map_mul,three_absNorm] at he
  omega

lemma onceCuspScale_lambda_dvd (t:Eisˣ) : lambda∣onceCuspScale t := by
  refine ⟨(t:Eis)*(traceRamifiedUnit:Eis),?_⟩
  rw [onceCuspScale,trace_eq_ramifiedUnit]
  ring

theorem ramifiedBesselValue_exact_lambda_valuation (side:Bool) (h:Eis)
    (hb:ramifiedBesselValue side h≠0) : lambda∣h ∧ ¬lambda^2∣h := by
  have hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side):=by
    by_contra hnot
    exact hb (by simp only [ramifiedBesselValue,dif_neg hnot])
  have hl3:lambda∣(3:Eis):=
    (dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three
  constructor
  · have hd:=hl3.trans hf
    simpa only [sub_add_cancel] using dvd_add hd
      (onceCuspScale_lambda_dvd (ramifiedCuspScaleUnit side))
  · intro h2
    have h3:(3:Eis)∣h:=three_dvd_lambda_sq.trans h2
    have hq:(3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit side):=by
      convert (preTransparency := .instances) dvd_sub h3 hf using 1 ; ring
    exact onceCuspScale_not_three_dvd _ hq

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.ResiduePhases
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

open scoped BigOperators Classical

open scoped Classical BigOperators

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4BadPhase_as_fixed_residue (c0:Eis) (hc0:c0≠0) (d U:Eis) :
    A4BadPhase c0 hc0 d U=
      A4PhaseFromResidue c0 hc0 (Ideal.Quotient.mk _ (-d*U)) := by
  funext x
  simp only [A4BadPhase,A4PhaseFromResidue,map_mul]

end ShortDraftCusp

open scoped Classical BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ChineseRemainder.FrequencyLifts
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

open scoped Classical BigOperators

open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedTraceLambda_dvd_of_lambda_dvd (h:Eis) (hh:lambda∣h) :
    ramifiedTraceLambda∣h := by
  obtain ⟨q,hq⟩:=hh
  refine ⟨(paperLambdaUnit⁻¹:Eisˣ)*q,?_⟩
  change h=paperLambda*((paperLambdaUnit⁻¹:Eisˣ)*q)
  rw [paperLambda_eq,hq]
  have hu : (paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)=1 := by
    simpa only [Units.val_mul,Units.val_one] using
      congrArg (fun v:Eisˣ=>(v:Eis)) (mul_inv_cancel paperLambdaUnit)
  calc
    _=(paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)*(lambda*q) := by rw [hu,one_mul]
    _=_ := by ring

lemma paperLambdaQuotient_mul (h:Eis) (hh:ramifiedTraceLambda∣h) :
    ramifiedTraceLambda*paperLambdaQuotient h=h := by
  simp only [paperLambdaQuotient,dif_pos hh]
  exact hh.choose_spec.symm

lemma sourceCuspCoefficients_ramified_divisibility (j:Fin 3) (hj:j≠0) (h:Eis)
    (hh:(sourceCuspCoefficients j).value h≠0) : ramifiedTraceLambda∣h := by
  apply ramifiedTraceLambda_dvd_of_lambda_dvd
  fin_cases j
  · exact (hj rfl).elim
  · exact (ramifiedBesselValue_exact_lambda_valuation false h hh).1
  · exact (ramifiedBesselValue_exact_lambda_valuation true h hh).1

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Algebra
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

theorem square_eq_star_of_fourth_eq (z : ℂ) (hz : z ^ 4 = z) : z ^ 2 = star z := by
  by_cases h0 : z = 0
  · simp [h0]
  have h3 : z ^ 3 = 1 := by
    apply mul_right_cancel₀ h0
    simpa only [← pow_succ, one_mul] using hz
  have hn := Complex.norm_eq_one_of_pow_eq_one h3 (by decide : (3 : ℕ) ≠ 0)
  change z ^ 2 = (starRingEnd ℂ) z
  rw [← Complex.inv_eq_conj hn]
  apply mul_right_cancel₀ h0
  rw [inv_mul_cancel₀ h0]
  simpa only [← pow_succ] using h3

variable {R : Type*} [CommRing R] [Finite Rˣ]

omit [Finite Rˣ] in
theorem cubic_fourth_eq (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 4 = χ x := by
  have h : χ ^ 4 = χ := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, hχ, one_mul, pow_one]
  rw [← MulChar.pow_apply' χ (by decide : (4 : ℕ) ≠ 0), h]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.StaticReflectionPhases
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

section
open scoped BigOperators Classical MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss ShortDraftCusp ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

lemma fixedCuspArrayWithPhase_reflectionStaticPhase (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) :
    fixedCuspArrayWithPhase s.index u (s.reflectionStaticPhase c0 hc0 v dualNumerator u) m I J=
      s.amplitude u m I J*A4PhaseFromResidue c0 hc0 v (dualNumerator m I J) := by
  unfold fixedCuspArrayWithPhase reflectionStaticPhase amplitude
  ring

end FixedCuspShape
end CubicEisenstein
end

open scoped Classical BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical MatrixGroups Matrix

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedThetaTwists
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
open scoped BigOperators Classical

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

theorem quadraticRow_eq_primeIndex (K:Ideal Eis) (hK:Admissible K) (x:Eis) :
    quadraticRow K x=finiteSexticRow (fun P:PrimeIndex K=>P.val)
      (admissiblePrimeGood K hK) (fun _=>3) x := by
  have hs:∀I∈({K}:Finset (Ideal Eis)),Admissible I:=by
    intro I hI
    simpa only [Finset.mem_singleton.mp hI] using hK
  have heq:primePool ({K}:Finset (Ideal Eis))=primeSupport K:=by
    simp [primePool,primeSupport]
  let e:primePool ({K}:Finset (Ideal Eis))≃PrimeIndex K:={
    toFun:=fun P=>⟨P.val,heq ▸ P.property⟩
    invFun:=fun P=>⟨P.val,heq.symm ▸ P.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  rw [quadraticRow_eq_pool {K} hs K (Finset.mem_singleton_self K) x,
    idealSupport_singleton_univ]
  simp only [QuadraticInitialBound.quadraticRow,finiteSquarefreeRow,Finset.prod_pow,
    finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]
  congr 1
  exact Fintype.prod_equiv e _ _ (fun P=>rfl)

end

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

open scoped Classical BigOperators ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.FixedRayFibers
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

open scoped Classical BigOperators ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic CompletedGauss CubicKubota CubicJacobiGlobal ConcreteTraceCRT
open LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedConjugateCuspArray_nonzero (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedConjugateCuspArray j u m I J≠0) :
    fixedCuspArrayEligible I J ∧
      (sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0 := by
  have helig:fixedCuspArrayEligible I J:=by
    by_contra he
    apply h
    simp only [fixedConjugateCuspArray,fixedCuspArray,if_neg he,star_zero]
  refine ⟨helig,?_⟩
  intro hz
  apply h
  simp only [fixedConjugateCuspArray,fixedCuspArray,if_pos helig,hz,zero_div,star_zero]

lemma fixedCusp_ramified_index_pos (j:Fin 3) (hj:j≠0) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J)
    (h:(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0) : 0< m := by
  apply Nat.pos_of_ne_zero
  intro hm
  have hp:lambda∣ramifiedTraceLambda:=by
    change lambda∣paperLambda
    rw [paperLambda_eq]
    exact dvd_mul_left lambda _
  have hd:=hp.trans (sourceCuspCoefficients_ramified_divisibility j hj _ h)
  simp only [fixedCuspArrayIndex,hm,pow_zero,mul_one] at hd
  have hu:IsCoprime lambda (u:Eis):=⟨0,(↑u⁻¹:Eis),by simp⟩
  have hni:IsCoprime lambda (primaryGenerator I):=coprime_of_dvd_sub_one lambda _
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec I helig.2.1).2)
  have hnj:IsCoprime lambda (primaryGenerator J):=coprime_of_dvd_sub_one lambda _
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec J helig.2.2).2)
  exact residue_lambda_prime.not_isUnit (((hu.mul_right hni).mul_right hnj.pow_right).isUnit_of_dvd hd)

lemma paperLambdaQuotient_succ (u:Eisˣ) (m:ℕ) (n b:Eis) :
    paperLambdaQuotient ((u.val*lambda^(m+1))*n*b^3)=
      (paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3 := by
  have hp:ramifiedTraceLambda*((paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3)=
      (u.val*lambda^(m+1))*n*b^3 := by
    change paperLambda*((paperLambdaUnit⁻¹:Eisˣ).val*u.val*lambda^m*n*b^3)=_
    rw [paperLambda_eq,pow_succ]
    have hi:(paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)=1:=by simp
    calc
      _=((paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ))*(u.val*lambda^m*lambda*n*b^3):=by ring
      _=_:=by rw [hi,one_mul];ring
  have hd:ramifiedTraceLambda∣(u.val*lambda^(m+1))*n*b^3:=⟨_,hp.symm⟩
  have hn:ramifiedTraceLambda≠0:=by
    intro hz
    have he:=ramifiedEmbedding_traceLambda
    rw [hz,map_zero] at he
    exact eisLam_ne_zero he.symm
  apply mul_left_cancel₀ hn
  rw [paperLambdaQuotient_mul _ hd,hp]

theorem sourceCuspPhaseNumerator_columns (j:Fin 3) (w u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J)
    (h:(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)≠0) :
    sourceCuspPhaseNumerator j w.val (fixedCuspArrayIndex u m I J)=
      ((sourcePhaseUnit j w u).val*lambda^(sourcePhaseExponent j m))*
        (primaryGenerator I*(primaryGenerator J)^3) := by
  by_cases hj:j=0
  · subst j
    simp only [sourceCuspPhaseNumerator,sourcePhaseUnit,sourcePhaseExponent,ite_true,
      fixedCuspArrayIndex,Units.val_mul,Units.val_pow_eq_pow_val]
    change paperLambda*w.val^2*((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)=_
    rw [paperLambda_eq,pow_succ]
    ring
  · have hm:=fixedCusp_ramified_index_pos j hj u m I J helig h
    cases m with
    | zero => omega
    | succ m =>
      simp only [sourceCuspPhaseNumerator,sourcePhaseUnit,sourcePhaseExponent,if_neg hj,
        fixedCuspArrayIndex,Nat.succ_sub_succ_eq_sub,Nat.sub_zero,Units.val_neg,Units.val_mul,
        Units.val_pow_eq_pow_val]
      rw [paperLambdaQuotient_succ]
      ring

theorem fixedCuspArray_phase_brackets {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i) (exponent:ι→ℕ)
    (j:Fin 3) (w u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    fixedConjugateCuspArray j u m I J*
      (∏i,bracket (actualSextic (P i) (hg i)) (exponent i)
        (Ideal.Quotient.mk (P i) (sourceCuspPhaseNumerator j w.val (fixedCuspArrayIndex u m I J))))=
    fixedConjugateCuspArray j u m I J*
      ramifiedBranchPhase P hg exponent (sourcePhaseUnit j w u) (sourcePhaseExponent j m)*
      ∑e:ι→Fin 3,reflectedBranch P hg exponent e (primaryGenerator I) (primaryGenerator J) := by
  by_cases hz:fixedConjugateCuspArray j u m I J=0
  · rw [hz,zero_mul,zero_mul,zero_mul]
  · obtain ⟨he,hh⟩:=fixedConjugateCuspArray_nonzero j u m I J hz
    rw [sourceCuspPhaseNumerator_columns j w u m I J he hh,
      ramified_bracket_full_expansion]
    ring

end

open ActualEisensteinCubic CompletedGauss CompletedDyadic CubicKubota CubicJacobiGlobal ConcreteTraceCRT
open LocalReflectionBrackets ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

lemma phaseUpperUnit_val : (s.phaseUpperUnit:Eis)=s.upper 0 0 := s.upper_unit.unit_spec

theorem model_array_brackets {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (c0:Eis) (hc0:c0≠0) (d U:Eis) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    (s.amplitude u m I J*A4BadPhase c0 hc0 d U (s.modelDualNumerator u m I J))*
      (∏i,bracket (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))=
    ramifiedBranchPhase P hg j (sourcePhaseUnit s.index s.phaseUpperUnit u)
      (sourcePhaseExponent s.index m)*
      ∑e:ι→Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-d*U)) (s.modelDualNumerator u) u) m I J*
        reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J) := by
  let φ:=s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-d*U)) (s.modelDualNumerator u) u
  have hA:φ m I J*fixedConjugateCuspArray s.index u m I J=
      s.amplitude u m I J*A4BadPhase c0 hc0 d U (s.modelDualNumerator u m I J) := by
    rw [A4BadPhase_as_fixed_residue]
    exact s.fixedCuspArrayWithPhase_reflectionStaticPhase c0 hc0 _ _ u m I J
  have hbr:=fixedCuspArray_phase_brackets P hg j s.index s.phaseUpperUnit u m I J
  rw [s.phaseUpperUnit_val] at hbr
  change fixedConjugateCuspArray s.index u m I J*
    (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))=_ at hbr
  rw [←hA]
  calc
    _=φ m I J*(fixedConjugateCuspArray s.index u m I J*
      (∏i,bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (s.modelDualNumerator u m I J)))) := by ring
    _=φ m I J*(fixedConjugateCuspArray s.index u m I J*
      ramifiedBranchPhase P hg j (sourcePhaseUnit s.index s.phaseUpperUnit u)
        (sourcePhaseExponent s.index m)*
        ∑e:ι→Fin 3,reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J)) := by rw [hbr]
    _=_ := by
      simp only [fixedCuspArrayWithPhase]
      rw [←Finset.mul_sum]
      dsimp only [φ]
      ring

end FixedCuspShape

namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

attribute [local instance] OAI.CubicEisenstein.ControlledStratumArithmetic.coefficientField
attribute [local instance] OAI.CubicEisenstein.ControlledStratumArithmetic.coefficientFintype
lemma bracketProduct_eq (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (x:Eis) :
    D.bracketProduct hp hg j x=D.activePhase hp hg j*
      ∏i,bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x) := by
  exact Finset.prod_mul_distrib

theorem model_coefficient (D:ControlledStratumArithmetic p N a0 c0 mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    s.amplitude u m I J*
      (star D.fixedFactor*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U (s.modelDualNumerator u m I J))*
      D.bracketProduct hp hg j (s.modelDualNumerator u m I J)=
    D.modelRowPhase s hp hg j u m*
      ∑e:ι→Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0 (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U))
            (s.modelDualNumerator u) u) m I J*
        reflectedBranch (fun i=>Ideal.span {p i}) hg j e (primaryGenerator I) (primaryGenerator J) := by
  rw [D.bracketProduct_eq]
  have he:=s.model_array_brackets (fun i=>Ideal.span {p i}) hg j c0 hc0
    (D.matrix (fun _=>1) 1 1) D.U u m I J
  calc
    _=(star D.fixedFactor*D.activePhase hp hg j)*
      ((s.amplitude u m I J*A4BadPhase c0 hc0 (D.matrix (fun _=>1) 1 1) D.U (s.modelDualNumerator u m I J))*
        (∏i,bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk _ (s.modelDualNumerator u m I J)))) := by ring
    _=_ := by rw [he];dsimp only [modelRowPhase];ring

end ControlledStratumArithmetic

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Ideal
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem idealSymbol_fourth (I : Ideal Eis) (x : Eis) :
    (eisEmbedding (CubicJacobiGlobal.idealSymbol I x)) ^ 4 =
      eisEmbedding (CubicJacobiGlobal.idealSymbol I x) := by
  have hlocal (P : Ideal Eis) :
      (eisEmbedding (CubicJacobiGlobal.primeValue P x)) ^ 4 =
        eisEmbedding (CubicJacobiGlobal.primeValue P x) := by
    unfold CubicJacobiGlobal.primeValue
    split_ifs with h
    · let : P.IsMaximal := h.1
      let χ := actualSextic P h.2 ^ 2
      have hχ : χ ^ 3 = 1 := by
        dsimp [χ]
        rw [canonicalSextic_pow_two, MulChar.ringHomComp_pow, cubicChar_pow_three, MulChar.ringHomComp_one]
      simpa only [χ, canonicalSextic_pow_two, MulChar.ringHomComp_apply] using
        cubic_fourth_eq χ hχ (Ideal.Quotient.mk P x)
    · simp
  have hprod (S : Multiset (Ideal Eis)) :
      (eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod)) ^ 4 =
        eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod) := by
    induction S using Multiset.induction_on with
    | empty => simp
    | @cons P S ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, mul_pow, hlocal, ih]
  by_cases hI : I = 0
  · simp [hI]
  · simpa only [CubicJacobiGlobal.idealSymbol, if_neg hI] using
      hprod (UniqueFactorizationMonoid.normalizedFactors I)

theorem idealKernel_square_eq_star (I J : Ideal Eis) :
    idealKernel I J ^ 2 = star (idealKernel I J) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I (primaryGenerator J))

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Overlap
namespace OAI

namespace SevenEighths.InverseMoment

open UniqueFactorizationMonoid

theorem inverse_eq_square_of_fourth_eq {z : ℂ} (hz : z ^ 4 = z) :
    z⁻¹ = z ^ 2 := by
  by_cases hzero : z = 0
  · simp [hzero]
  have hcube : z ^ 3 = 1 := by
    apply mul_left_cancel₀ hzero
    calc
      z * z ^ 3 = z ^ 4 := by ring
      _ = z := hz
      _ = z * 1 := by ring
  calc
    z⁻¹ = z⁻¹ * z ^ 3 := by rw [hcube, mul_one]
    _ = z ^ 2 := by field_simp

theorem inverse_cube_square_eq_sixth {z : ℂ} (h : z ^ 6 = 0 ∨ z ^ 6 = 1) :
    ((z ^ 3)⁻¹) ^ 2 = z ^ 6 := by
  rw [← inv_pow, ← pow_mul]
  norm_num
  rcases h with h | h <;> rw [h] <;> norm_num

theorem inverse_square_cube_mask {M : Type*} [Monoid M]
    (ψ : M →* ℂ) (n b : M) (h : ψ b ^ 6 = 0 ∨ ψ b ^ 6 = 1) :
    (ψ (n * b ^ 3))⁻¹ ^ 2 = (ψ n)⁻¹ ^ 2 * ψ b ^ 6 := by
  rw [map_mul, map_pow, mul_inv_rev, mul_pow, inverse_cube_square_eq_sixth h]
  ring

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Hybrid
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid IdealMobiusDivisorSum

local notation "Eis" => ActualEisensteinCubic.O

theorem inverseCubicKernel_eq_inverse_square (P n : Ideal Eis) :
    inverseCubicKernel P n =
      (CanonicalRowCompletion.idealRowHom (CompletedGauss.primaryGenerator n) P)⁻¹ ^ 2 := by
  rw [inv_pow, CanonicalRowCompletion.idealRowHom_square,
    inverse_eq_square_of_fourth_eq (CubicSieve.idealSymbol_fourth P _)]
  exact (CubicSieve.idealKernel_square_eq_star P n).symm

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Poisson
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open FirstPassCubeLabels
open SecondPassArithmetic

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hcop

attribute [local instance] OAI.SevenEighths.InverseMoment.markedQuotientField
attribute [local instance] OAI.SevenEighths.InverseMoment.markedQuotientFintype
omit [DecidableEq ι] in
theorem row_slot_cross_phase
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k) :
    MixedCrossSeparation.crossSymbol p hg i k ^ 4 *
      MixedCrossSeparation.crossSymbol p hg k i ^ 2 = 1 := by
  have hs : MixedCrossSeparation.crossSymbol p hg i k ^ 2 =
      MixedCrossSeparation.crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  have h6 : MixedCrossSeparation.crossSymbol p hg i k ^ 6 = 1 := by
    simpa only [MixedCrossSeparation.crossSymbol, map_pow, if_neg hnot] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)
  calc
    _ = MixedCrossSeparation.crossSymbol p hg i k ^ 6 := by rw [← hs]; ring
    _ = 1 := h6

omit [DecidableEq ι] in
theorem row_slot_product_phase
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1) (R P : Finset ι) (hRP : Disjoint R P) :
    (∏ i ∈ R, ∏ k ∈ P,
      MixedCrossSeparation.crossSymbol p hg i k ^ 4 *
        MixedCrossSeparation.crossSymbol p hg k i ^ 2) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  apply Finset.prod_eq_one
  intro k hk
  exact row_slot_cross_phase p hcop hg hpr i k (fun h =>
    (Finset.disjoint_left.mp hRP) hi (h.symm ▸ hk))

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.MarkedPhase
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseMoment.markedPhaseFintype
theorem mixedActiveBracket_eq_signed [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode)
    (i : ι) (x : Eis) :
    mixedActiveBracket hp hg j S D i x = (if i ∈ S then (-1 : ℂ) else 1) *
      ((((actualSextic (Ideal.span {p i}) (hg i))⁻¹) ^ 2) (D.sigma i) *
        phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i))
          (markedActiveExponent S j i) (D.epsilon i) *
        bracket (actualSextic (Ideal.span {p i}) (hg i)) (markedActiveExponent S j i)
          (Ideal.Quotient.mk _ x)) := by
  by_cases hi : i ∈ S
  · simp only [mixedActiveBracket, markedActiveExponent, hi,
      phase, bracket, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, inv_pow, map_mul]
    ring
  · simp only [mixedActiveBracket, markedActiveExponent, hi, ite_false, one_mul]

theorem mixedActiveBracket_product [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode) (x : Eis) :
    (∏ i, mixedActiveBracket hp hg j S D i x) =
      (-1 : ℂ) ^ S.card * D.bracketProduct hp hg (markedActiveExponent S j) x := by
  simp_rw [mixedActiveBracket_eq_signed]
  rw [Finset.prod_mul_distrib]
  have hsign : (∏ i : ι, if i ∈ S then (-1 : ℂ) else 1) = (-1 : ℂ) ^ S.card := by
    rw [Finset.prod_ite]
    simp
  rw [hsign]
  rfl

theorem mixed_model_coefficient [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) :
    s.amplitude u m I J *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c0 hc0
        (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m I J)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m I J)) =
    ((-1 : ℂ) ^ S.card * D.modelRowPhase s hp hg (markedActiveExponent S j) u m) *
      ∑ e : ι → Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0
            (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1) * D.U))
            (s.modelDualNumerator u) u) m I J *
        reflectedBranch (fun i => Ideal.span {p i}) hg (markedActiveExponent S j) e
          (primaryGenerator I) (primaryGenerator J) := by
  rw [mixedActiveBracket_product]
  calc
    _ = (-1 : ℂ) ^ S.card * (s.amplitude u m I J *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c0 hc0
        (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m I J)) *
      D.bracketProduct hp hg (markedActiveExponent S j) (s.modelDualNumerator u m I J)) := by ring
    _ = _ :=
      (congrArg ((-1 : ℂ) ^ S.card * ·)
        (D.model_coefficient s hp hc0 hg (markedActiveExponent S j) u m I J)).trans
          (mul_assoc _ _ _).symm

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Local
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
open LocalReflectionBrackets
noncomputable section

lemma scalar_inverse_pair (a b c d : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : c*a*b=d) : a⁻¹*b⁻¹ = d⁻¹*c := by
  field_simp
  linear_combination -h

theorem marked_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (B z : F)
    (he : B*z*(σ : F)*(ε : F) = -1) :
    ((χ⁻¹)^2) σ * phase χ ψ 0 ε =
      (-tau χ ψ 2)*(χ (-1))⁻¹^2*(χ B)^2*(χ z)^2 := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  simp only [phase, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte,
    MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv']
  calc
    _ = (-tau χ ψ 2)*((χ σ)⁻¹*(χ ε)⁻¹)^2 := by ring
    _ = _ := by rw [hi]; ring

theorem residual_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A B z : F)
    (hsigma : (σ : F) = A*z) (he : B*z*(σ : F)*(ε : F) = -1) :
    ((χ⁻¹)^2) σ * phase χ ψ 1 ε =
      (tau χ (ψ.mulShift (-1)) 1*tau χ ψ 3)*
        (χ (-1))⁻¹^3*(χ A)*(χ B)^3*(χ z)^4 := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  have hsig : χ (σ : F) = χ A*χ z := by rw [hsigma,map_mul]
  simp only [phase, show (1 : ℕ) ≠ 4 by decide, show (1 : ℕ) ≠ 0 by decide,
    ↓reduceIte, show (1 : ℕ)+2 = 3 by decide,
    MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv']
  have hid : (χ σ)⁻¹^2*(χ ε)⁻¹^3 = (χ σ)*((χ σ)⁻¹*(χ ε)⁻¹)^3 := by
    field_simp
  calc
    _ = (tau χ (ψ.mulShift (-1)) 1*tau χ ψ 3)*((χ σ)⁻¹^2*(χ ε)⁻¹^3) := by ring
    _ = _ := by rw [hid,hi,hsig]; ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Cofactor
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss ConcreteTraceCRT
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.phaseField
attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.phaseFinite
theorem controlled_marked_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 0 (D.epsilon i) =
        markedPrimeScalar (p i) c0 (hp i) (hg i)*
          ∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 2 := by
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  rw [marked_local_phase _ _ _ _ _ _ he]
  change _ = _
  simp only [markedPrimeScalar, cofactor, map_prod, Finset.prod_pow,
    MixedCrossSeparation.crossSymbol]

theorem controlled_residual_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 1 (D.epsilon i) =
        residualPrimeScalar (p i) c0 (hp i) (hg i)*
          ∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 4 := by
  have hs : (D.sigma i : Eis ⧸ Ideal.span {p i}) =
      Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c0)*Ideal.Quotient.mk _ (cofactor p i) := by
    simpa only [map_mul] using D.sigma_value i
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  rw [residual_local_phase _ _ _ _ _ _ _ hs he]
  simp only [residualPrimeScalar, cofactor, map_prod, Finset.prod_pow,
    MixedCrossSeparation.crossSymbol]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Frozen
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma scalar_phase_power (a b : ℂ) (ha : a ≠ 0) (j : ℕ) :
    a⁻¹^2*b⁻¹^(j+2) = a^j*(a⁻¹*b⁻¹)^(j+2) := by
  symm
  calc
    _ = (a^j*(a⁻¹)^j)*(a⁻¹)^2*(b⁻¹)^(j+2) := by rw [mul_pow,pow_add]; ring
    _ = _ := by rw [← mul_pow,mul_inv_cancel₀ ha,one_pow,one_mul]

theorem general_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A B z : F)
    (hsigma : (σ : F) = A*z) (he : B*z*(σ : F)*(ε : F) = -1)
    (j : ℕ) (hj0 : j ≠ 0) (hj4 : j ≠ 4) :
    ((χ⁻¹)^2) σ * phase χ ψ j ε =
      (tau χ (ψ.mulShift (-1)) j*tau χ ψ (j+2)) *
        (χ (-1))⁻¹^(j+2)*(χ A)^j*(χ B)^(j+2)*(χ z)^(2*j+2) := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  have hsig : χ (σ : F) = χ A*χ z := by rw [hsigma,map_mul]
  simp only [phase,hj4,hj0,↓reduceIte,MulChar.pow_apply_coe,MulChar.inv_apply_eq_inv']
  calc
    _ = (tau χ (ψ.mulShift (-1)) j*tau χ ψ (j+2))*((χ σ)⁻¹^2*(χ ε)⁻¹^(j+2)) := by ring
    _ = _ := by
      rw [scalar_phase_power _ _ hs j,hi,hsig]
      simp only [mul_pow,pow_add,show 2*j=j+j by omega]
      ring

theorem exceptional_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A z : F)
    (hsigma : (σ : F) = A*z) :
    ((χ⁻¹)^2) σ * phase χ ψ 4 ε =
      (tau χ (ψ.mulShift (-1)) 4*(χ A)⁻¹^2)*(χ z)⁻¹^2 := by
  simp only [phase,↓reduceIte,hsigma,map_mul,
    ]
  simp only [MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv']
  ring

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.frozenField
attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.frozenFinite
theorem controlled_frozen_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) (j : ℕ) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) j (D.epsilon i) =
    frozenPrimeScalar (p i) c (hp i) (hg i) j *
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (cofactor p i) := by
  have hs : (D.sigma i : Eis ⧸ Ideal.span {p i}) =
      Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)*Ideal.Quotient.mk _ (cofactor p i) := by
    simpa only [map_mul] using D.sigma_value i
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  by_cases hj4 : j=4
  · subst j
    rw [exceptional_local_phase _ _ _ _ _ _ hs]
    simp only [frozenPrimeScalar,frozenCofactorCharacter,↓reduceIte,MonoidHom.comp_apply,
      RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv']
    rfl
  · by_cases hj0 : j=0
    · subst j
      rw [marked_local_phase _ _ _ _ _ _ he]
      simp [frozenPrimeScalar,frozenCofactorCharacter,markedPrimeScalar,
        MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0)]
    · rw [general_local_phase _ _ _ _ _ _ _ hs he j hj0 hj4]
      simp only [frozenPrimeScalar,frozenCofactorCharacter,hj4,hj0,↓reduceIte,
        MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,
        MulChar.coe_toMonoidHom,MulChar.pow_apply' _ (by omega : 2*j+2 ≠ 0)]
      rfl

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Cross
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
noncomputable section

theorem ordered_cross_partition_on {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (A B U : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = U) :
    (∏ i ∈ U, ((∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ a * x k i ^ b) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ A.erase i, x i k ^ a) * (∏ k ∈ B, x i k ^ a) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : U.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, if_pos hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ B.erase i, x i k ^ b) * (∏ k ∈ A, x i k ^ b) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : U.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, if_neg hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ U.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ a) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ U.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ b) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ U.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ U.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB]
      rw [Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

theorem ordered_cross_frozen_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F)
    (hu : (R ∪ P) ∪ F = Finset.univ) :
    (∏ i ∈ R ∪ P, (∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ R then a else b))*l i) =
      (∏ i ∈ R, (∏ k ∈ R.erase i, x i k^a)*(l i*∏ k ∈ F, x i k^a)) *
      (∏ i ∈ P, (∏ k ∈ P.erase i, x i k^b)*(l i*∏ k ∈ F, x i k^b)) *
      (∏ i ∈ R, ∏ k ∈ P, x i k^a*x k i^b) := by
  let ll := fun i => l i*∏ k ∈ F, x i k ^ (if i ∈ R then a else b)
  have hx : (∏ i ∈ R ∪ P, (∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ R then a else b))*l i) =
      ∏ i ∈ R ∪ P, (∏ k ∈ (R ∪ P).erase i,
        x i k ^ (if i ∈ R then a else b))*ll i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ F := fun hf => Finset.disjoint_left.mp hF hi hf
    have he : Finset.univ.erase i = (R ∪ P).erase i ∪ F := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk,or_assoc]
    rw [he,Finset.prod_union (hF.mono_left (Finset.erase_subset _ _))]
    dsimp [ll]
    ring
  rw [hx,ordered_cross_partition_on x ll a b R P (R ∪ P) hRP rfl]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    simp [ll,hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ R := fun hr => Finset.disjoint_left.mp hRP hr hi
    simp [ll,hn]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.ThreeBlocks
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.threeBlockFinite
theorem activePhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0) :
    D.activePhase hp hg j = residualWithFrozen hp hg c R F *
      markedWithFrozen hp hg c P F * frozenPhase D hp hg j F := by
  let l : ι → ℂ := fun i => if i ∈ R then residualPrimeScalar (p i) c (hp i) (hg i)
    else markedPrimeScalar (p i) c (hp i) (hg i)
  let v : ι → ℂ := fun i => (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)
  have hm : (∏ i ∈ R ∪ P, v i) = ∏ i ∈ R ∪ P,
      (∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^
        (if i ∈ R then 4 else 2))*l i := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hr : i ∈ R
    · simp only [v,hRj i hr,l,hr,ite_true]
      rw [controlled_residual_phase]
      ring
    · have hp' : i ∈ P := (Finset.mem_union.mp hi).resolve_left hr
      simp only [v,hPj i hp',l,hr,ite_false]
      rw [controlled_marked_phase]
      ring
  have hfull : D.activePhase hp hg j = (∏ i ∈ R ∪ P, v i)*frozenPhase D hp hg j F := by
    change (∏ i, v i) = (∏ i ∈ R ∪ P, v i)*(∏ i ∈ F, v i)
    rw [← Finset.prod_union hF,hu]
  rw [hfull,hm,ordered_cross_frozen_partition _ l 4 2 R P F hRP hF hu,
    InverseMoment.row_slot_product_phase p hcop hg hprimary R P hRP,mul_one]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    simp [l,hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ R := fun hr => Finset.disjoint_left.mp hRP hr hi
    simp [l,hn]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.FrozenSplit
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.frozenSplitFinite
theorem frozen_cofactor_split (hp : ∀ i, p i ≠ 0) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (i : ι) (hi : i ∈ F) :
    cofactor p i = (∏ k ∈ F.erase i, p k)*(∏ k ∈ R, p k)*(∏ k ∈ S, p k) := by
  apply mul_left_cancel₀ (hp i)
  rw [prime_mul_cofactor,← hu,Finset.prod_union hF,Finset.prod_union hRS,
    ← Finset.mul_prod_erase F p hi]
  ring

theorem frozenPhase_split [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (R S F : Finset ι) (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F)
    (hu : (R ∪ S) ∪ F = Finset.univ) :
    frozenPhase D hp hg j F = frozenCore hp hg c j F *
      frozenArgument hg j F (∏ i ∈ R, p i) * frozenArgument hg j F (∏ i ∈ S, p i) := by
  unfold frozenPhase
  simp_rw [controlled_frozen_phase]
  have he (i : ι) (hi : i ∈ F) :
      frozenPrimeScalar (p i) c (hp i) (hg i) (j i)*
        frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (cofactor p i) =
      (frozenPrimeScalar (p i) c (hp i) (hg i) (j i)*
        frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ F.erase i, p k))*
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ R, p k)*
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ S, p k) := by
    rw [frozen_cofactor_split hp R S F hRS hF hu i hi,map_mul,map_mul]
    ring
  rw [Finset.prod_congr rfl he]
  simp only [Finset.prod_mul_distrib,frozenCore,frozenArgument,MonoidHom.finsetProd_apply]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Brackets
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss
open LocalReflectionBrackets CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.bracketField
attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.bracketFinite
theorem marked_bracket_cube (P : Ideal Eis) [P.IsMaximal]
    (hg : λ₀ ∉ P) (n b : Eis) :
    bracket (actualSextic P hg) 0 (Ideal.Quotient.mk P (n*b^3)) =
      (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)⁻¹ *
      (idealRowHom n P)⁻¹^2 * (if IsCoprime P (Ideal.span {b}) then 1 else 0) := by
  have h6 : (actualSextic P hg (Ideal.Quotient.mk P b))^6 =
      if b ∈ P then 0 else 1 := by
    simpa only [map_pow] using canonicalSextic_sixth_power_mask P hg b
  have h6' : (actualSextic P hg (Ideal.Quotient.mk P b))^6 = 0 ∨
      (actualSextic P hg (Ideal.Quotient.mk P b))^6 = 1 := by
    rw [h6]; split_ifs <;> simp
  let ψ : Eis →* ℂ := (actualSextic P hg).toMonoidHom.comp (Ideal.Quotient.mk P).toMonoidHom
  have he := InverseMoment.inverse_square_cube_mask ψ n b h6'
  change ((actualSextic P hg) (Ideal.Quotient.mk P (n*b^3)))⁻¹^2 =
    ((actualSextic P hg) (Ideal.Quotient.mk P n))⁻¹^2 *
      ((actualSextic P hg) (Ideal.Quotient.mk P b))^6 at he
  simp only [bracket,show (0:ℕ) ≠ 4 by decide,↓reduceIte,
    MulChar.inv_apply_eq_inv',MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),inv_pow]
  simp only [inv_pow] at he
  rw [he,rootCard_eq_sqrt_absNorm,idealRowHom_prime n P hg,h6,
    SixthPowerAverage.prime_coprime_span_iff]
  by_cases hb : b ∈ P <;> simp [hb]

theorem marked_bracket_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (n b : Eis) :
    (∏ i, bracket (actualSextic (P i) (hg i)) 0 (Ideal.Quotient.mk (P i) (n*b^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      (idealRowHom n (∏ i, P i))⁻¹^2 *
      (if IsCoprime (∏ i, P i) (Ideal.span {b}) then 1 else 0) := by
  simp_rw [marked_bracket_cube]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  have hn : (∏ i, (Real.sqrt (Ideal.absNorm (P i) : ℝ) : ℂ)⁻¹) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ := by
    rw [map_prod,Nat.cast_prod,Real.sqrt_prod,Complex.ofReal_prod,Finset.prod_inv_distrib]
    intro i hi
    positivity
  have hc : (∏ i, (idealRowHom n (P i))⁻¹^2) = (idealRowHom n (∏ i, P i))⁻¹^2 := by
    rw [map_prod,Finset.prod_pow,Finset.prod_inv_distrib]
  have hm : (∏ i, if IsCoprime (P i) (Ideal.span {b}) then (1:ℂ) else 0) =
      if IsCoprime (∏ i, P i) (Ideal.span {b}) then 1 else 0 := by
    classical
    by_cases h : ∀ i, IsCoprime (P i) (Ideal.span {b})
    · simp [h,IsCoprime.prod_left (fun i _ => h i)]
    · obtain ⟨i,hi⟩ := not_forall.mp h
      have hp : ¬ IsCoprime (∏ i, P i) (Ideal.span {b}) := by
        intro hp
        exact hi (hp.of_isCoprime_of_dvd_left (Finset.dvd_prod_of_mem P (Finset.mem_univ i)))
      rw [if_neg hp]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [hn,hc,hm]

theorem marked_bracket_hybrid {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (∏ i, bracket (actualSextic (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) := by
  rw [marked_bracket_product,InverseMoment.inverseCubicKernel_eq_inverse_square,
    (primaryGenerator_spec b hb).1]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.IdealBridge
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
open CanonicalQuadraticSieve CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.idealBridgeFinite
theorem idealRowHom_cube_eq_quadratic (K : Ideal Eis) (hK : Admissible K) (z : Eis) :
    idealRowHom z K ^ 3 = quadraticRow K z := by
  conv_lhs => rw [← admissible_primeIndex_product K hK,map_prod,← Finset.prod_pow]
  rw [quadraticRow_eq_primeIndex K hK]
  simp only [finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ) ≠ 0)]
  apply Finset.prod_congr rfl
  intro P hP
  rw [idealRowHom_prime z P.val (admissiblePrimeGood K hK P)]

theorem residual_bracket_finset {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (R : Finset ι) (hR : Admissible (∏ i ∈ R, P i))
    (n b : Ideal Eis) :
    (∏ i ∈ R, bracket (actualSextic (P i) (hg i)) 1
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) =
      quadraticRow (∏ i ∈ R, P i) (primaryGenerator (n*b)) := by
  have hl (i : ι) : bracket (actualSextic (P i) (hg i)) 1
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3)) =
      idealRowHom (primaryGenerator (n*b)) (P i)^3 := by
    have he := residual_bracket_cube (P i) (hg i) 1 (primaryGenerator n) (primaryGenerator b)
    simpa only [one_mul,map_one,one_pow,primaryGenerator_mul,idealRowHom_prime _ (P i) (hg i)] using he
  simp_rw [hl]
  rw [Finset.prod_pow,← map_prod,idealRowHom_cube_eq_quadratic _ hR]

theorem marked_bracket_finset {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (S : Finset ι) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (∏ i ∈ S, bracket (actualSextic (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
  have he := marked_bracket_hybrid (fun i : S => P i.val) (fun i => hg i.val) n b hb
  have hl : (∏ i : S, bracket (actualSextic (P i.val) (hg i.val)) 0
      (Ideal.Quotient.mk (P i.val) (primaryGenerator n*(primaryGenerator b)^3))) =
      ∏ i ∈ S, bracket (actualSextic (P i) (hg i)) 0
        (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3)) := by
    exact Finset.prod_coe_sort S (fun i => bracket (actualSextic (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3)))
  rw [hl] at he
  simpa only [Finset.prod_coe_sort] using he

theorem full_branch_sum_hybrid {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hSj : ∀ i ∈ S, j i = 0)
    (hR : Admissible (∏ i ∈ R, P i)) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (∑ e : ι → Fin 3, reflectedBranch P hg j e (primaryGenerator n) (primaryGenerator b)) =
      (∏ i ∈ F, bracket (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      quadraticRow (∏ i ∈ R, P i) (primaryGenerator (n*b)) *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
  trans ∏ i, bracket (actualSextic (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))
  · exact (prod_bracket_eq_full_branches P hg j (primaryGenerator n) (primaryGenerator b)).symm
  let v := fun i => bracket (actualSextic (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))
  have hr : (∏ i ∈ R, v i) = quadraticRow (∏ i ∈ R, P i) (primaryGenerator (n*b)) := by
    rw [← residual_bracket_finset P hg R hR n b]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [v,hRj i hi]
  have hs : (∏ i ∈ S, v i) =
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
    rw [← marked_bracket_finset P hg S n b hb]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [v,hSj i hi]
  have hv : (∏ i, v i) = (∏ i ∈ R, v i)*(∏ i ∈ S, v i)*(∏ i ∈ F, v i) := by
    rw [← Finset.prod_union hRS,← Finset.prod_union hF,hu]
  change (∏ i, v i) = _
  rw [hv,hr,hs]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Ramified
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

theorem ramifiedPhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0)
    (u : Eisˣ) (m : ℕ) :
    ramifiedBranchPhase (fun i => Ideal.span {p i}) hg j u m =
      ramifiedBlock hg (fun _ => 1) R u m * ramifiedBlock hg (fun _ => 0) P u m *
      ramifiedBlock hg j F u m := by
  have hh : ramifiedBranchPhase (fun i => Ideal.span {p i}) hg j u m =
      ramifiedBlock hg j R u m * ramifiedBlock hg j P u m * ramifiedBlock hg j F u m := by
    unfold ramifiedBranchPhase ramifiedBlock
    rw [← Finset.prod_union hRP,← Finset.prod_union hF,hu]
    rfl
  rw [hh]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hRj i hi]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hPj i hi]

theorem modelRowPhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0)
    (u : Eisˣ) (m : ℕ) :
    D.modelRowPhase s hp hg j u m =
      (residualWithFrozen hp hg c R F * ramifiedBlock hg (fun _ => 1) R
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) *
      (markedWithFrozen hp hg c P F * ramifiedBlock hg (fun _ => 0) P
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) *
      (star D.fixedFactor * frozenPhase D hp hg j F * ramifiedBlock hg j F
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) := by
  dsimp only [ControlledStratumArithmetic.modelRowPhase]
  rw [activePhase_three_blocks D hp hg hcop hprimary R P F hRP hF hu j hRj hPj,
    ramifiedPhase_three_blocks hg R P F hRP hF hu j hRj hPj]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Coefficient
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
open InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.coefficientFinite
theorem mixed_coefficient_hybrid [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hc : c ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1)
    (hR : CanonicalQuadraticSieve.Admissible (∏ i ∈ R, Ideal.span {p i}))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    s.amplitude u m n b *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
        (s.modelDualNumerator u m n b)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m n b)) =
    ((-1:ℂ)^S.card * sourceRowPhase s hp hg (markedActiveExponent S j) R F u m * sourceSlotPhase s hp hg (markedActiveExponent S j) S F u m *
      sourceFrozenPhase D s hp hg (markedActiveExponent S j) F u m) *
      sourceColumn D s hc hg (markedActiveExponent S j) F u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) : ℂ)⁻¹ *
      CanonicalQuadraticSieve.quadraticRow (∏ i ∈ R, Ideal.span {p i}) (primaryGenerator (n*b)) *
      inverseCubicKernel (∏ i ∈ S, Ideal.span {p i}) n *
      (if IsCoprime (∏ i ∈ S, Ideal.span {p i}) b then 1 else 0) *
      (if IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) then 1 else 0) := by
  have hrj : ∀ i ∈ R, markedActiveExponent S j i = 1 := by
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hRS hi hs
    simp only [markedActiveExponent,hn,ite_false,hRj i hi]
  have hsj : ∀ i ∈ S, markedActiveExponent S j i = 0 := by
    intro i hi
    simp only [markedActiveExponent,hi,ite_true]
  have hmask : IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) := by
    apply IsCoprime.prod_left
    intro i hi
    apply IsCoprime.prod_right
    intro k hk
    exact hcop (fun h => Finset.disjoint_left.mp hRS hi (h ▸ hk))
  rw [mixed_model_coefficient,modelRowPhase_three_blocks D s hp hg hcop hprimary R S F hRS hF hu
      (markedActiveExponent S j) hrj hsj,
    frozenPhase_split D hp hg (markedActiveExponent S j) R S F hRS hF hu,← Finset.mul_sum,
    full_branch_sum_hybrid (fun i => Ideal.span {p i}) hg R S F hRS hF hu
      (markedActiveExponent S j) hrj hsj hR n b hb,if_pos hmask,mul_one]
  unfold sourceRowPhase sourceSlotPhase sourceFrozenPhase sourceColumn
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Independent
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
open InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.independentFinite
omit [Fintype ι] in
theorem frozenArgument_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j j' : ι → ℕ) (F : Finset ι)
    (hj : ∀ i ∈ F, j i = j' i) : frozenArgument hg j F = frozenArgument hg j' F := by
  unfold frozenArgument
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj i hi]

omit [Fintype ι] in
theorem frozenCore_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (j j' : ι → ℕ) (F : Finset ι) (hj : ∀ i ∈ F, j i = j' i) :
    frozenCore hp hg c j F = frozenCore hp hg c j' F := by
  unfold frozenCore
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj i hi]

omit [Fintype ι] in
theorem ramifiedBlock_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j j' : ι → ℕ) (F : Finset ι)
    (hj : ∀ i ∈ F, j i = j' i) (u : Eisˣ) (m : ℕ) :
    ramifiedBlock hg j F u m = ramifiedBlock hg j' F u m := by
  unfold ramifiedBlock
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj i hi]

theorem marked_phases_eq [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (R S F : Finset ι) (hd : Disjoint S F) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s hp hg (markedActiveExponent S j) R F u m = sourceRowPhase s hp hg j R F u m ∧
    sourceSlotPhase s hp hg (markedActiveExponent S j) S F u m = sourceSlotPhase s hp hg j S F u m ∧
    sourceFrozenPhase D s hp hg (markedActiveExponent S j) F u m = sourceFrozenPhase D s hp hg j F u m := by
  have hj : ∀ i ∈ F, markedActiveExponent S j i = j i := by
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hd hs hi
    simp only [markedActiveExponent,hn,ite_false]
  simp only [sourceRowPhase,sourceSlotPhase,sourceFrozenPhase,
    frozenArgument_congr hg _ _ F hj,frozenCore_congr hp hg c _ _ F hj,
    ramifiedBlock_congr hg _ _ F hj]
  simp

theorem marked_sourceColumn_eq [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S F : Finset ι) (hd : Disjoint S F)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    sourceColumn D s hc hg (markedActiveExponent S j) F u m n b =
      sourceColumn D s hc hg j F u m n b := by
  unfold sourceColumn
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hd hs hi
  simp only [markedActiveExponent,hn,ite_false]

theorem mixed_coefficient_hybrid_original_exponents [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hc : c ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1)
    (hR : CanonicalQuadraticSieve.Admissible (∏ i ∈ R, Ideal.span {p i}))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    s.amplitude u m n b *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
        (s.modelDualNumerator u m n b)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m n b)) =
    ((-1:ℂ)^S.card * sourceRowPhase s hp hg j R F u m * sourceSlotPhase s hp hg j S F u m *
      sourceFrozenPhase D s hp hg j F u m) *
      sourceColumn D s hc hg j F u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) : ℂ)⁻¹ *
      CanonicalQuadraticSieve.quadraticRow (∏ i ∈ R, Ideal.span {p i}) (primaryGenerator (n*b)) *
      inverseCubicKernel (∏ i ∈ S, Ideal.span {p i}) n *
      (if IsCoprime (∏ i ∈ S, Ideal.span {p i}) b then 1 else 0) *
      (if IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) then 1 else 0) := by
  have hd : Disjoint S F := hF.mono_left Finset.subset_union_right
  have he := mixed_coefficient_hybrid D s hp hc hg hcop hprimary R S F hRS hF hu j hRj hR u m n b hb
  obtain ⟨hr,hs,hf⟩ := marked_phases_eq D s hp hg j R S F hd u m
  rw [hr,hs,hf,marked_sourceColumn_eq D s hc hg j S F hd u m n b] at he
  exact he

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Transport
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι → Eis}

omit [Fintype ι] [Fintype κ] in
theorem residualWithFrozen_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (f : κ → ι) (hf : Function.Injective f) (R F : Finset κ) :
    residualWithFrozen (fun i => hp (f i)) (fun i => hg (f i)) c R F =
      residualWithFrozen hp hg c (R.image f) (F.image f) := by
  unfold residualWithFrozen
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf R i,Finset.prod_image hf.injOn,Finset.prod_image hf.injOn]
  rfl

omit [Fintype ι] [Fintype κ] in
theorem markedWithFrozen_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (f : κ → ι) (hf : Function.Injective f) (S F : Finset κ) :
    markedWithFrozen (fun i => hp (f i)) (fun i => hg (f i)) c S F =
      markedWithFrozen hp hg c (S.image f) (F.image f) := by
  unfold markedWithFrozen
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf S i,Finset.prod_image hf.injOn,Finset.prod_image hf.injOn]
  rfl

omit [Fintype ι] [Fintype κ] in
theorem ramifiedBlock_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (S : Finset κ) (u : Eisˣ) (m : ℕ) :
    ramifiedBlock (fun i => hg (f i)) (fun i => j (f i)) S u m =
      ramifiedBlock hg j (S.image f) u m := by
  unfold ramifiedBlock
  rw [Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem frozenArgument_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) :
    frozenArgument (fun i => hg (f i)) (fun i => j (f i)) F =
      frozenArgument hg j (F.image f) := by
  unfold frozenArgument
  rw [Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem sourceRowPhase_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (R F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s (fun i => hp (f i)) (fun i => hg (f i)) (fun i => j (f i)) R F u m =
      sourceRowPhase s hp hg j (R.image f) (F.image f) u m := by
  unfold sourceRowPhase
  rw [residualWithFrozen_transport hp hg c f hf R F,
    ramifiedBlock_transport hg (fun _ => 1) f hf R,
    frozenArgument_transport hg j f hf F,Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem sourceSlotPhase_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (S F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s (fun i => hp (f i)) (fun i => hg (f i)) (fun i => j (f i)) S F u m =
      sourceSlotPhase s hp hg j (S.image f) (F.image f) u m := by
  unfold sourceSlotPhase
  rw [markedWithFrozen_transport hp hg c f hf S F,
    ramifiedBlock_transport hg (fun _ => 0) f hf S,
    frozenArgument_transport hg j f hf F,Finset.prod_image hf.injOn]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Functions
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma sourceRowPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (R F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceRowPhase s hp hg j R F u m = sourceRowPhase s hq hqg j' R F u m := by
  subst q
  subst j'
  rfl

lemma sourceSlotPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (S F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceSlotPhase s hp hg j S F u m = sourceSlotPhase s hq hqg j' S F u m := by
  subst q
  subst j'
  rfl

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.SectorIndependence
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem frozenCore_transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) :
    frozenCore (fun i => hp (f i)) (fun i => hg (f i)) c (fun i => j (f i)) F =
      frozenCore hp hg c j (F.image f) := by
  unfold frozenCore
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf F i,Finset.prod_image hf.injOn]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Moving
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma reflected_indices_partition (φ ρ σ : Type*) [Fintype φ] [Fintype ρ] [Fintype σ] :
    Disjoint (residualIndices φ ρ σ) (slotIndices φ ρ σ) ∧
    Disjoint (residualIndices φ ρ σ ∪ slotIndices φ ρ σ) (frozenIndices φ ρ σ) ∧
    (residualIndices φ ρ σ ∪ slotIndices φ ρ σ) ∪ frozenIndices φ ρ σ = Finset.univ := by
  classical
  simp only [residualIndices, slotIndices, frozenIndices, Finset.disjoint_left,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Function.comp_apply]
  constructor
  · rintro i ⟨r, rfl⟩ ⟨s, h⟩
    cases h
  constructor
  · rintro i (⟨r, rfl⟩ | ⟨s, rfl⟩) ⟨f, h⟩ <;> cases h
  · ext i
    cases i with
    | inl f => simp
    | inr i => cases i with
      | inl r => simp
      | inr s => simp

lemma reflected_residual_exponent {φ ρ σ : Type*} [Fintype ρ] (jF : φ → ℕ) :
    ∀ i ∈ residualIndices φ ρ σ, reflectedExponent jF i = 1 := by
  let : DecidableEq (φ ⊕ (ρ ⊕ σ)) := Classical.decEq _
  rintro i hi
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
  rfl

namespace PrimeFamily
lemma reflected_residual_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i ∈ residualIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) = K := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  simp only [generator_span, residualIndices]
  rw [Finset.prod_image (Sum.inr_injective.comp Sum.inl_injective).injOn]
  exact residual_product K hK

lemma reflected_slot_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i ∈ slotIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) = ∏ i, S.ideal i := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  simp only [generator_span, slotIndices]
  rw [Finset.prod_image (Sum.inr_injective.comp Sum.inr_injective).injOn]
  rfl
end PrimeFamily

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Projections
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {a c : Eis} {mode : Bool}

omit [Fintype σ] in
theorem sourceRowPhase_eq_actual (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (residualIndices φ (PrimeIndex K) σ) (frozenIndices φ (PrimeIndex K) σ) u m =
      actualRowPhase F K hK jF s u m := by
  classical
  let f : φ ⊕ PrimeIndex K → φ ⊕ (PrimeIndex K ⊕ σ) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  have hf : Function.Injective f := by
    intro i k h
    cases i <;> cases k <;> simp_all [f]
  have he := sourceRowPhase_transport s (F.reflected K hK S).generator_ne_zero
    (F.reflected K hK S).generator_good (reflectedExponent jF) f hf
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m
  have hp : (fun i => (F.reflected K hK S).generator (f i)) =
      (F.sum (PrimeFamily.residual K hK)).generator := by
    funext i
    cases i <;> rfl
  have hj : (fun i => reflectedExponent jF (f i)) = Sum.elim jF (fun _ => 1) := by
    funext i
    cases i <;> rfl
  have hh := sourceRowPhase_congr_functions s
    (fun i => (F.reflected K hK S).generator_ne_zero (f i))
    (fun i => (F.reflected K hK S).generator_good (f i))
    (F.sum (PrimeFamily.residual K hK)).generator_ne_zero
    (F.sum (PrimeFamily.residual K hK)).generator_good
    _ _ (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m hp hj
  rw [he] at hh
  simpa only [actualRowPhase,residualIndices,frozenIndices,Finset.image_image,
    Function.comp_def,f,Sum.elim_inl,Sum.elim_inr] using hh

theorem sourceSlotPhase_eq_actual (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (frozenIndices φ (PrimeIndex K) σ) u m =
      actualSlotPhase F S jF s u m := by
  classical
  let f : φ ⊕ σ → φ ⊕ (PrimeIndex K ⊕ σ) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)
  have hf : Function.Injective f := by
    intro i k h
    cases i <;> cases k <;> simp_all [f]
  have he := sourceSlotPhase_transport s (F.reflected K hK S).generator_ne_zero
    (F.reflected K hK S).generator_good (reflectedExponent jF) f hf
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m
  have hp : (fun i => (F.reflected K hK S).generator (f i)) = (F.sum S).generator := by
    funext i
    cases i <;> rfl
  have hj : (fun i => reflectedExponent jF (f i)) = Sum.elim jF (fun _ => 0) := by
    funext i
    cases i <;> rfl
  have hh := sourceSlotPhase_congr_functions s
    (fun i => (F.reflected K hK S).generator_ne_zero (f i))
    (fun i => (F.reflected K hK S).generator_good (f i))
    (F.sum S).generator_ne_zero (F.sum S).generator_good
    _ _ (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m hp hj
  rw [he] at hh
  simpa only [actualSlotPhase,slotIndices,frozenIndices,Finset.image_image,
    Function.comp_def,f,Sum.elim_inl,Sum.elim_inr] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Actual
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem actualMixedCoefficient_factor (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    actualMixedCoefficient F K hK S jF D s hc u m n b =
      ((-1:ℂ)^(Fintype.card σ)*actualRowPhase F K hK jF s u m*actualSlotPhase F S jF s u m*
        sourceFrozenPhase D s (F.reflected K hK S).generator_ne_zero
          (F.reflected K hK S).generator_good (reflectedExponent jF)
          (frozenIndices φ (PrimeIndex K) σ) u m)*
      sourceColumn D s hc (F.reflected K hK S).generator_good (reflectedExponent jF)
        (frozenIndices φ (PrimeIndex K) σ) u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i, S.ideal i):ℝ):ℂ)⁻¹*
      quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel (∏ i, S.ideal i) n*
      (if IsCoprime (∏ i, S.ideal i) b then 1 else 0)*
      (if IsCoprime K (∏ i, S.ideal i) then 1 else 0) := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  obtain ⟨hRS,hF,hu⟩ := reflected_indices_partition φ (PrimeIndex K) σ
  have hF' : Disjoint (residualIndices φ (PrimeIndex K) σ ∪ slotIndices φ (PrimeIndex K) σ)
      (frozenIndices φ (PrimeIndex K) σ) := by
    simpa only [Finset.disjoint_left,Finset.mem_union] using hF
  have hu' : (residualIndices φ (PrimeIndex K) σ ∪ slotIndices φ (PrimeIndex K) σ) ∪
      frozenIndices φ (PrimeIndex K) σ = Finset.univ := by
    simpa only [Finset.ext_iff,Finset.mem_union] using hu
  have hcp : Pairwise (Function.onFun IsCoprime
      (fun i => Ideal.span {(F.reflected K hK S).generator i})) := by
    simpa only [PrimeFamily.generator_span] using hcop
  have hr : Admissible (∏ i ∈ residualIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) := by
    rw [F.reflected_residual_product K hK S]
    exact hK
  have he := mixed_coefficient_hybrid_original_exponents D s
    (F.reflected K hK S).generator_ne_zero hc (F.reflected K hK S).generator_good hcp
    (F.reflected K hK S).generator_primary _ _ _ hRS hF' hu'
    (reflectedExponent jF) (reflected_residual_exponent jF) hr u m n b hb
  have hcard : (slotIndices φ (PrimeIndex K) σ).card = Fintype.card σ := by
    rw [slotIndices,Finset.card_image_of_injective _ (Sum.inr_injective.comp Sum.inr_injective)]
    rfl
  rw [hcard,sourceRowPhase_eq_actual,sourceSlotPhase_eq_actual,
    F.reflected_residual_product K hK S,F.reflected_slot_product K hK S] at he
  exact he

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Columns
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι φ σ : Type*} [Fintype ι] [Fintype φ] [Fintype σ]
variable {p : ι → Eis} {N a c : Eis} {mode : Bool}

theorem sourceColumn_eq_sum_frozenBranches (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    sourceColumn D s hc (F.reflected K hK S).generator_good (reflectedExponent jF)
      (frozenIndices φ (PrimeIndex K) σ) u m n b =
      ∑ e : φ → Fin 3, frozenBranchColumn F jF e (actualCuspColumn D s hc u m) n b := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  unfold sourceColumn frozenIndices
  rw [Finset.prod_image Sum.inl_injective.injOn]
  change actualCuspColumn D s hc u m n b *
    (∏ i, bracket (actualSextic (Ideal.span {F.generator i}) (F.generator_good i)) (jF i)
      (Ideal.Quotient.mk _ (primaryGenerator n*(primaryGenerator b)^3))) = _
  exact (congrArg (actualCuspColumn D s hc u m n b * ·)
    (prod_bracket_eq_full_branches (fun i => Ideal.span {F.generator i}) F.generator_good
      jF (primaryGenerator n) (primaryGenerator b))).trans (Finset.mul_sum _ _ _)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.NormalizedColumns
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma sourceFrozenPhase_eq_actual (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) :
    sourceFrozenPhase D s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (frozenIndices φ (PrimeIndex K) σ) u m = actualFrozenPhase F jF D.fixedFactor s u m := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  unfold sourceFrozenPhase frozenIndices
  rw [← frozenCore_transport (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good c (reflectedExponent jF) Sum.inl Sum.inl_injective Finset.univ,
    ← ramifiedBlock_transport (F.reflected K hK S).generator_good
      (reflectedExponent jF) Sum.inl Sum.inl_injective Finset.univ]
  rfl

lemma frozenExtracted_ne_zero (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) (v : Fin 3) :
    frozenExtracted F jF e v ≠ 0 := by
  apply reflectionExtractedDivisor_ne_zero
  intro i
  rw [F.generator_span]
  exact NeZero.ne _

lemma frozenBranchScale_pos (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) :
    0 < frozenBranchScale F jF e := by
  have hn (v : Fin 3) : (0:ℝ) < Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  exact div_pos (mul_pos (Real.sqrt_pos.mpr (hn 1)) (Real.sqrt_pos.mpr (hn 2)))
    (Real.sqrt_pos.mpr (hn 0))

lemma frozenBranchColumn_eq_normalized (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) :
    frozenBranchColumn F jF e A n b =
      (frozenBranchScale F jF e : ℂ)*normalizedFrozenColumn F jF e A n b := by
  rw [normalizedFrozenColumn,← mul_assoc,mul_inv_cancel₀,one_mul]
  exact_mod_cast (frozenBranchScale_pos F jF e).ne'

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.FamilyFactorization
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem actualMixedCoefficient_common_branches (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal))
    (κ : ℂ) (A : Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ)
    (hκ : D.fixedFactor = κ)
    (hA : ∀ u m n b, actualCuspColumn D s hc u m n b = A u m n b)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    actualMixedCoefficient F K hK S jF D s hc u m n b =
      ∑ e : φ → Fin 3,
        ((-1:ℂ)^(Fintype.card σ)*actualRowPhase F K hK jF s u m*
          actualSlotPhase F S jF s u m*actualFrozenPhase F jF κ s u m)*
        (frozenBranchScale F jF e:ℂ)*normalizedFrozenColumn F jF e (A u m) n b*
        (Real.sqrt (Ideal.absNorm (∏ i, S.ideal i):ℝ):ℂ)⁻¹*
        quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel (∏ i, S.ideal i) n*
        (if IsCoprime (∏ i, S.ideal i) b then 1 else 0)*
        (if IsCoprime K (∏ i, S.ideal i) then 1 else 0) := by
  rw [actualMixedCoefficient_factor F K hK S jF D s hc hcop u m n b hb,
    sourceFrozenPhase_eq_actual,hκ,sourceColumn_eq_sum_frozenBranches]
  have hfun : actualCuspColumn D s hc u m = A u m := funext (fun n => funext (fun b => hA u m n b))
  rw [hfun,Finset.mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [frozenBranchColumn_eq_normalized]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.SourceSum
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ ι : Type*} [Fintype φ] [Fintype σ] [Fintype ι]
variable {N a c : Eis} {mode : Bool}

theorem masked_actual_coefficient (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (P : Ideal Eis) (hprod : (∏ i, S.ideal i) = P) (jF : φ → ℕ)
    (D : IsCoprime K P → ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (hcop : IsCoprime K P → Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal))
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hκ : ∀ h, (D h).fixedFactor = D0.fixedFactor)
    (hA : ∀ h u m n b, actualCuspColumn (D h) s hc u m n b = actualCuspColumn D0 s hc u m n b)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (if h : IsCoprime K P then actualMixedCoefficient F K hK S jF (D h) s hc u m n b else 0) =
      ∑ e : φ → Fin 3,
        ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
          actualRowPhaseExtension F jF s u m K)*
        (actualSlotPhase F S jF s u m / (Real.sqrt (Ideal.absNorm P:ℝ):ℂ))*
        (if IsCoprime K P then 1 else 0)*
        (frozenBranchColumn F jF e (actualCuspColumn D0 s hc u m) n b*
          quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*
          (if IsCoprime P b then 1 else 0)) := by
  by_cases hKP : IsCoprime K P
  · rw [dif_pos hKP]
    have hh := actualMixedCoefficient_common_branches F K hK S jF (D hKP) s hc (hcop hKP)
      D0.fixedFactor (actualCuspColumn D0 s hc) (hκ hKP) (hA hKP) u m n b hb
    rw [hprod] at hh
    rw [hh]
    apply Finset.sum_congr rfl
    intro e he
    rw [actualRowPhaseExtension,dif_pos hK,frozenBranchColumn_eq_normalized]
    simp only [if_pos hKP,div_eq_mul_inv]
    ring
  · simp only [dif_neg hKP,if_neg hKP,mul_zero,zero_mul,Finset.sum_const_zero]

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.WeightedSourceSum
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ ι : Type*} [Fintype φ] [Fintype σ] [Fintype ι]
variable {N a c : Eis} {mode : Bool}

theorem weightedPhysicalReflectedRow_eq_branches_oai (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (hcop : ∀ P : Pset, IsCoprime K P.val →
      Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal))
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hκ : ∀ P h, (D P h).fixedFactor = D0.fixedFactor)
    (hA : ∀ P h u m n b, actualCuspColumn (D P h) s hc u m n b = actualCuspColumn D0 s hc u m n b)
    (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ) :
    weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc r aw w u m =
      ∑ e : φ → Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K := by
  unfold weightedPhysicalReflectedRow
  have he (P : Pset) (n : Ideal Eis) (b : Ideal Eis) (hb' : b ∈ bset) :=
    masked_actual_coefficient F K hK (S P.val) P.val (hprod P.val P.property) jF
      (D P) (hcop P) G0 D0 s hc (hκ P) (hA P) u m n b (hb b hb')
  simp_rw [weightedReflectedBranchHybridRow,hybridRow,hybridInner,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_coe_sort Pset]
  apply Finset.sum_congr rfl
  intro P hP
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb'
  rw [he P n b hb',Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he'
  unfold frozenBranchColumn
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.SevenEighths.InverseReflectedPhase.weightedPhysicalReflectedRow_eq_branches_oai.{u_1, u_2, u_3} := @OAI.SevenEighths.InverseReflectedPhase.weightedPhysicalReflectedRow_eq_branches_oai.{u_1, u_2, u_3}
