-- Prove2me | solution 1 for OAI.SevenEighths.InverseReflectedPhase.integrated_filtered_actual_reflected_energy_type_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:38:37.618904+00:00
-- url     : https://prove2.me/submissions/1cd1df28-d1d7-4bf8-a40e-e26aaca4dbb4

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_InverseMoment_hybridRow_energy

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.MatrixPhases
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section

namespace ShortDraftGauss

open Complex
open scoped ComplexConjugate

variable {F : Type*} [Field F] [Fintype F]

theorem norm_normalized_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖((Real.sqrt (Fintype.card F) : ℝ) : ℂ)⁻¹ * gaussSum χ ψ‖ = 1 := by
  have hcard : (0 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hsqrt : Real.sqrt (Fintype.card F) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 hcard), norm_gaussSum_eq_sqrt_card χ ψ hχ hψ]
  exact inv_mul_cancel₀ hsqrt

end ShortDraftGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
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

open scoped BigOperators Classical

namespace CompletedGauss

section

open ActualEisensteinCubic

theorem primaryGenerator_norm_sq (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (primaryGenerator I)‖ ^ 2 = (Ideal.absNorm I : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, (primaryGenerator_spec I h).1]

open ActualEisensteinCubic

end
section

open ActualEisensteinCubic ConcreteTraceCRT

theorem primaryGenerator_norm (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    ‖eisEmbedding (primaryGenerator I)‖ = Real.sqrt (Ideal.absNorm I : ℝ) := by
  rw [← primaryGenerator_norm_sq I hI, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

end CompletedGauss

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

theorem norm_tau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ)
    (hχ : χ ^ j ≠ 1) (hψ : ψ.IsPrimitive) : ‖tau χ ψ j‖ = 1 :=
  ShortDraftGauss.norm_normalized_gaussSum (χ ^ j) ψ hχ hψ

theorem norm_bracket_nonexceptional (χ : MulChar F ℂ) (j : ℕ)
    (hj4 : j ≠ 4) (hj0 : j ≠ 0) (x : F) :
    ‖bracket χ j x‖ = if x = 0 then 0 else 1 := by
  simp only [bracket, if_neg hj4, if_neg hj0]
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx]
    exact FiniteRayExpansion.norm_char_unit ((χ ^ (j + 2))⁻¹) (Units.mk0 x hx)

theorem norm_bracket_zero (χ : MulChar F ℂ) (x : F) :
    ‖bracket χ 0 x‖ = (rootCard F)⁻¹ * if x = 0 then 0 else 1 := by
  simp only [bracket, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg rootCard_pos.le]
  congr 1
  by_cases hx : x = 0
  · simp [hx]
  · rw [if_neg hx]
    exact FiniteRayExpansion.norm_char_unit ((χ ^ 2)⁻¹) (Units.mk0 x hx)

end

section
variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
theorem shifted_power_nontrivial (χ : MulChar F ℂ) (h6 : χ ^ 6 = 1)
    (hn : ∀ k : ℕ, k ≠ 0 → k < 6 → χ ^ k ≠ 1)
    (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) (hj4 : j ≠ 4) : χ ^ (j + 2) ≠ 1 := by
  by_cases hj : j = 5
  · subst j
    have heq : χ ^ (5 + 2) = χ ^ 1 := by
      rw [show (5 + 2 : ℕ) = 6 + 1 by decide, pow_add, h6, one_mul]
    rw [heq]
    exact hn 1 (by decide) (by decide)
  · exact hn (j + 2) (by omega) (by omega)

theorem phase_norm (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (h6 : χ ^ 6 = 1) (hn : ∀ k : ℕ, k ≠ 0 → k < 6 → χ ^ k ≠ 1)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj6 : j < 6) (ε : Fˣ) :
    ‖phase χ ψ j ε‖ = 1 := by
  have hψminus : (ψ.mulShift (-1)).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one (hψ (a := (-1 : F)) (by simp))
  by_cases hj4 : j = 4
  · subst j
    simp only [phase, ↓reduceIte]
    exact norm_tau χ _ 4 (hn 4 (by decide) (by decide)) hψminus
  by_cases hj0 : j = 0
  · subst j
    simp only [phase, if_neg hj4, ↓reduceIte, norm_mul, norm_neg]
    rw [norm_tau χ ψ 2 (hn 2 (by decide) (by decide)) hψ,
      FiniteRayExpansion.norm_char_unit]
    norm_num
  · simp only [phase, if_neg hj4, if_neg hj0, norm_mul]
    rw [norm_tau χ _ j (hn j hj0 hj6) hψminus,
      norm_tau χ ψ (j + 2) (shifted_power_nontrivial χ h6 hn j hj0 hj6 hj4) hψ,
      FiniteRayExpansion.norm_char_unit]
    norm_num

end

open ActualEisensteinCubic

attribute [local instance] OAI.LocalReflectionBrackets.quotientField
attribute [local instance] OAI.LocalReflectionBrackets.quotientFintype
theorem canonical_phase_norm (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (ε : (O ⧸ P)ˣ) :
    ‖phase (canonicalSextic P hgood) ψ j ε‖ = 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  exact phase_norm (canonicalSextic P hgood) ψ (canonicalSextic_pow_six P hgood)
    (fun k hk0 hk6 => canonicalSextic_pow_ne_one P hgood hchar hk0 hk6) hψ j hj6 ε

end LocalReflectionBrackets

open scoped Classical BigOperators
open AddChar MulChar

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets
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

namespace LocalReflectionBrackets
open scoped Classical BigOperators
open AddChar MulChar

section
variable {F : Type*} [Field F] [Fintype F]

theorem norm_bracket_nonexceptional_le_one (χ : MulChar F ℂ) (j : ℕ)
    (hj4 : j ≠ 4) (hj0 : j ≠ 0) (x : F) : ‖bracket χ j x‖ ≤ 1 := by
  rw [norm_bracket_nonexceptional χ j hj4 hj0]
  split_ifs <;> norm_num

theorem norm_bracket_zero_le (χ : MulChar F ℂ) (x : F) :
    ‖bracket χ 0 x‖ ≤ (rootCard F)⁻¹ := by
  rw [norm_bracket_zero]
  split_ifs <;> simp only [mul_zero, mul_one, le_refl]
  exact inv_nonneg.mpr rootCard_pos.le

open ActualEisensteinCubic

end

variable {F : Type*} [Field F] [Fintype F]

open ActualEisensteinCubic

end LocalReflectionBrackets

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical

open scoped BigOperators Classical

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

theorem rootCard_eq_sqrt_absNorm (P : Ideal O) [P.IsMaximal] :
    rootCard (O ⧸ P)=Real.sqrt (Ideal.absNorm P:ℝ) := by
  rw [rootCard,←Nat.card_eq_fintype_card]
  rfl

theorem exceptionalPiece_norm_le (P : Ideal O) [P.IsMaximal]
    (e : Fin 3) (n b : O) :
    ‖exceptionalPiece P e n b‖≤(if e=0 then (rootCard (O ⧸ P))⁻¹ else rootCard (O ⧸ P)) := by
  have hr : 0≤ rootCard (O ⧸ P) := rootCard_pos.le
  fin_cases e <;> simp only [exceptionalPiece,Fin.isValue,Fin.zero_eta,↓reduceIte]
  · simp [abs_of_nonneg hr]
  · by_cases hn : n∈P <;> simp [hn,abs_of_nonneg hr,hr]
  · by_cases hn : n∉P ∧ b∈P <;> simp [hn,abs_of_nonneg hr,hr]

end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold

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

theorem reflectedLocalPiece_norm_le (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (j : ℕ) (e : Fin 3) (n b : O) :
    ‖reflectedLocalPiece P hg j e n b‖≤ reflectedLocalSize P j e := by
  have hr : 0< rootCard (O ⧸ P) := rootCard_pos
  by_cases hj4 : j=4
  · subst j
    simpa only [reflectedLocalPiece,reflectedLocalSize,ite_true] using exceptionalPiece_norm_le P e n b
  · by_cases he : e=0
    · rw [reflectedLocalPiece,if_neg hj4,if_pos he,reflectedLocalSize,if_neg hj4]
      by_cases hj0 : j=0
      · subst j
        simpa only [ite_true] using norm_bracket_zero_le (actualSextic P hg) (Ideal.Quotient.mk P (n*b^3))
      · rw [if_neg hj0]
        exact norm_bracket_nonexceptional_le_one _ j hj4 hj0 _
    · simp only [reflectedLocalPiece,if_neg hj4,if_neg he,norm_zero,reflectedLocalSize]
      split_ifs <;> positivity

theorem sqrt_norm_reflectionExtractedDivisor {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) :
    Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ)=
      ∏i,if (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) then rootCard (O ⧸ P i) else 1 := by
  rw [reflectionExtractedDivisor,map_prod,Nat.cast_prod,Real.sqrt_prod]
  · apply Finset.prod_congr rfl
    intro i _
    unfold reflectionExtractedPrime
    split_ifs
    · rw [rootCard_eq_sqrt_absNorm]
    · simp
  · intro i _
    exact Nat.cast_nonneg _

theorem reflectedBranch_norm_bound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) :
    ‖reflectedBranch P hg j e n b‖≤
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ) := by
  have hb : ‖reflectedBranch P hg j e n b‖≤∏i,reflectedLocalSize (P i) (j i) (e i) := by
    rw [reflectedBranch,norm_prod]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
      (fun i _ => reflectedLocalPiece_norm_le (P i) (hg i) (j i) (e i) n b)
  apply hb.trans_eq
  rw [sqrt_norm_reflectionExtractedDivisor,sqrt_norm_reflectionExtractedDivisor,
    sqrt_norm_reflectionExtractedDivisor,←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hj4 : j i=4
  · rw [hj4]
    generalize e i=x
    fin_cases x <;> simp [reflectedLocalSize]
  · by_cases hj0 : j i=0
    · simp [reflectedLocalSize,hj0]
    · simp [reflectedLocalSize,hj4,hj0]

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

theorem reflectedBranch_divisibility {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (hcop : Pairwise (fun i k => IsCoprime (P i) (P k)))
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) (hne : reflectedBranch P hg j e n b≠0) :
    reflectionExtractedDivisor P j e 1∣Ideal.span {n} ∧
    reflectionExtractedDivisor P j e 2∣Ideal.span {b} ∧
    (∀i,j i=4 → e i=2 → n∉P i) := by
  have hn i : reflectedLocalPiece (P i) (hg i) (j i) (e i) n b≠0 :=
    (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  have hmemn i (hj : j i=4) (he : e i=1) : n∈P i := by
    by_contra hz
    exact hn i (by simp [reflectedLocalPiece,exceptionalPiece,hj,he,hz])
  have hmemb i (hj : j i=4) (he : e i=2) : n∉P i ∧ b∈P i := by
    by_contra hz
    exact hn i (by simp [reflectedLocalPiece,exceptionalPiece,hj,he,hz])
  have hprod (v : Fin 3) (z : O)
      (hz : ∀i,(j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) → z∈P i) :
      reflectionExtractedDivisor P j e v∣Ideal.span {z} := by
    unfold reflectionExtractedDivisor reflectionExtractedPrime
    apply Fintype.prod_dvd_of_coprime
    · intro i k hik
      change IsCoprime (if (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) then P i else 1)
        (if (j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0) then P k else 1)
      by_cases hi : (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0)
      · rw [if_pos hi]
        by_cases hk : (j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0)
        · rw [if_pos hk]
          exact hcop hik
        · rw [if_neg hk]
          exact isCoprime_one_right
      · rw [if_neg hi]
        exact isCoprime_one_left
    · intro i
      split_ifs with hi
      · rw [Ideal.dvd_iff_le,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
        exact hz i hi
      · exact one_dvd _
  refine ⟨hprod 1 n ?_,hprod 2 b ?_,fun i hj he => (hmemb i hj he).1⟩
  · intro i hi
    rcases hi with ⟨hj,he⟩|⟨hj,he⟩
    · exact hmemn i hj he
    · norm_num at he
  · intro i hi
    rcases hi with ⟨hj,he⟩|⟨hj,he⟩
    · exact (hmemb i hj he).2
    · ((try simp  at he) <;> norm_num  at he)

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

theorem unitArgumentFactor_norm (χ : MulChar F ℂ) (j : ℕ) (z : F) (hz : z≠0) :
    ‖unitArgumentFactor χ j z‖=1 := by
  by_cases hj : j=4
  · simp [unitArgumentFactor,hj]
  · rw [unitArgumentFactor,if_neg hj]
    exact FiniteRayExpansion.norm_char_unit ((χ^(j+2))⁻¹) (Units.mk0 z hz)

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

end CompletedGauss

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ResidualCuspDecay
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

namespace ShortDraftCusp

open ActualEisensteinCubic CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem norm_embedded_cubic_symbol (x a : Eis)
    (ha : lambda^2∣a-1) (hcop : IsCoprime x a) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol x a)‖=1 := by
  have hcube : ConcreteTraceCRT.eisEmbedding (symbol x a)^3=1 := by
    rw [←map_pow,symbol_cube_of_isCoprime x a ha hcop,map_one]
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one] using congrArg norm hcube

theorem norm_A3_ramified_fixed_factor (a b c0 r d u : Eis)
    (hdet : a*d-b*(u*(c0*r))=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣a-u*b-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol (-u) (a-u*b)*symbol c0 a)‖=1 := by
  have hfirst : ‖ConcreteTraceCRT.eisEmbedding (symbol (-u) (a-u*b))‖=1 := by
    apply norm_embedded_cubic_symbol _ _ hA
    refine ⟨b*(c0*r-d),d,?_⟩
    linear_combination hdet
  have hsecond : ‖ConcreteTraceCRT.eisEmbedding (symbol c0 a)‖=1 := by
    apply norm_embedded_cubic_symbol _ _ ha
    refine ⟨-b*u*r,d,?_⟩
    linear_combination hdet
  rw [map_mul,norm_mul,hfirst,hsecond,one_mul]

theorem norm_A3_unramified_fixed_factor (a b c0 r d : Eis)
    (hdet : a*d-b*(c0*r)=1) (hc : lambda^2∣c0-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol a c0)‖=1 := by
  apply norm_embedded_cubic_symbol _ _ hc
  refine ⟨d,-b*r,?_⟩
  linear_combination hdet

end ShortDraftCusp

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedCuspArrays
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

namespace CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedCuspCoefficientBound_pos : 0<fixedCuspCoefficientBound :=
  (Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).1

lemma fixedCuspArrayWeight_pos (m:ℕ) (J:Ideal Eis) (hJ:primaryGenerator J≠0) :
    0<fixedCuspArrayWeight m J := by
  rw [fixedCuspArrayWeight,←primaryGenerator_norm J hJ]
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (norm_pos_iff.mpr (eisEmbedding_ne_zero hJ))

lemma sourceCuspCoefficients_squarefree_cube_bound (j:Fin 3) (u:Eisˣ) (m:ℕ)
    (I J:Ideal Eis) (helig:fixedCuspArrayEligible I J) :
    ‖(sourceCuspCoefficients j).value (fixedCuspArrayIndex u m I J)‖≤
      fixedCuspCoefficientBound*fixedCuspArrayWeight m J := by
  rcases helig with ⟨hsq,hI,hJ⟩
  have hb:=(Classical.choose_spec three_cusp_coefficients_squarefree_cube_bound).2
    I J hI hJ hsq u m
  rw [primaryGenerator_norm J hJ] at hb
  fin_cases j
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.1
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.2 false
  · simpa [sourceCuspCoefficients,sourceBesselCoefficients,ramifiedBesselCoefficients,fixedCuspCoefficientBound,fixedCuspArrayWeight,fixedCuspArrayIndex,mul_assoc] using hb.2 true

lemma fixedCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedCuspArray j u m I J‖≤1 := by
  by_cases h:fixedCuspArrayEligible I J
  · have hpos:=mul_pos fixedCuspCoefficientBound_pos (fixedCuspArrayWeight_pos m J h.2.2)
    rw [fixedCuspArray,if_pos h,norm_div,Complex.norm_real,Real.norm_of_nonneg hpos.le]
    exact (div_le_one hpos).mpr (sourceCuspCoefficients_squarefree_cube_bound j u m I J h)
  · simp only [fixedCuspArray,if_neg h,norm_zero,zero_le_one]

lemma fixedConjugateCuspArray_norm_le_one (j:Fin 3) (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    ‖fixedConjugateCuspArray j u m I J‖≤1 := by
  simpa only [fixedConjugateCuspArray,norm_star] using fixedCuspArray_norm_le_one j u m I J

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.WeylRepresentatives
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

namespace CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceFrequencyAngle_norm (h:Eis) (hh:h≠0) : ‖sourceFrequencyAngle h‖=1 := by
  rw [sourceFrequencyAngle,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hh))

end

open CompletedGauss CompletedDyadic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped Classical BigOperators

open scoped BigOperators Classical Matrix MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedConductor
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

open scoped Classical

open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma basePrimeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    ‖basePrimeRow I hI Q n‖≤1 := by
  change ‖∏P:BasePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.FixedCuspBranches
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

open scoped BigOperators Classical ContDiff

namespace CompletedGauss

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedCuspArrayWithPhase_norm_le_one (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (m:ℕ) (n b:Ideal Eis) : ‖fixedCuspArrayWithPhase cusp u phaseArray m n b‖≤1 := by
  rw [fixedCuspArrayWithPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m n b)).trans (fixedConjugateCuspArray_norm_le_one cusp u m n b)

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

end

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

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4PhaseFromResidue_norm (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}) (x:Eis) :
    ‖A4PhaseFromResidue c0 hc0 v x‖=1 := by
  let:Finite (Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}):=
    finite_quotient_span (A4_bad_modulus_ne_zero c0 hc0)
  unfold A4PhaseFromResidue
  exact AddChar.norm_apply _ _
end ShortDraftCusp

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss ShortDraftCusp ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceFrequencyAngle_norm_le_one (h:Eis) : ‖sourceFrequencyAngle h‖≤1 := by
  by_cases hh:h=0
  · simp only [hh,sourceFrequencyAngle,map_zero,norm_zero,Complex.ofReal_zero,div_zero]
    norm_num
  · exact (sourceFrequencyAngle_norm h hh).le

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

lemma reflectionStaticPhase_norm_le_one (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) : ‖s.reflectionStaticPhase c0 hc0 v dualNumerator u m I J‖≤1 := by
  simp only [reflectionStaticPhase,norm_mul,breveE_norm,A4PhaseFromResidue_norm,mul_one]
  exact sourceFrequencyAngle_norm_le_one _

end FixedCuspShape
end CubicEisenstein
end

open scoped Classical BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp

open ActualEisensteinCubic CubicEisenstein CubicKubota CubicJacobiGlobal ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A3_ramified_relative_primary (M:SL(2,Eis)) (u:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree) :
    lambda^2∣(M 0 0-u*M 0 1)-1 := by
  have hA:=levelThree_primary ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩
  change lambda^2∣(((M*(lowerCuspMatrix u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hA
  rw [A3_ramified_relative_matrix] at hA
  exact hA

end ShortDraftCusp

namespace CubicEisenstein

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

lemma determinant (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v 0 0*D.matrix v 1 1-D.matrix v 0 1*(c0*∏i,p i)=1 := by
  simpa only [Matrix.det_fin_two,D.denominator] using (D.matrix v).property

end ControlledStratumArithmetic
end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedFrequencyExpansion
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

namespace CubicEisenstein

section
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

theorem fixedFactor_norm (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1) : ‖D.fixedFactor‖=1 := by
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
    ((dvd_mul_right 9 c0).trans hN)
  cases mode
  · exact norm_A3_unramified_fixed_factor _ _ _ _ _ (D.determinant (fun _=>1)) hbase
  · apply norm_A3_ramified_fixed_factor _ _ 1 (∏i,p i) _ c0
    · simpa only [one_mul] using D.determinant (fun _=>1)
    · exact D.numerator_primary h3N hr hbase (fun _=>1)
    · exact A3_ramified_relative_primary (D.matrix (fun _=>1)) c0
        (D.ramified_relative h3N hr hbase c0 (by simp) (fun _=>1))

end ControlledStratumArithmetic
end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ResidualEquivalence
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

open scoped BigOperators Classical ContDiff

open scoped BigOperators Classical MatrixGroups

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion

section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

namespace GoodMaskRowData
variable {m f z:Eis} (D:GoodMaskRowData m f z)

lemma numeratorFactor_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1) (n:Eis) :
    ‖(Ψ*numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood
      D.numeratorSupported) n‖≤1 := by
  change ‖Ψ n*numeratorBadTwist _ _ _ _ _ n‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΨ n)).trans (numeratorBadTwist_norm _ _ _ _ _ n)

lemma fixedFactor_norm (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hΨ:∀n,‖Ψ n‖≤1) (n:Eis) :
    ‖D.fixedFactor Ψ Q n‖≤1 := by
  change ‖((Ψ*numeratorBadTwist _ _ _ _ _) n)*(basePrimeRow _ _ _ n)‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (D.numeratorFactor_norm Ψ hΨ n)).trans (basePrimeRow_norm _ _ _ n)

end GoodMaskRowData

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion

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

theorem idealKernel_norm_le_one (I J : Ideal Eis) : ‖idealKernel I J‖ ≤ 1 := by
  rw [idealKernel, ← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm (primaryGenerator J) I) 2).trans_eq (by norm_num)

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Gcd
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubic_admissible_of_dvd {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible D := by
  refine ⟨hI.1.squarefree_of_dvd hD, ?_⟩
  obtain ⟨J, he⟩ := hD
  have hp := hI.2
  rw [he, primaryGenerator_mul] at hp
  exact (mul_ne_zero_iff.mp hp).1

end
end SevenEighths.CubicSieve

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

theorem inverseCubicKernel_norm_le_one (P n : Ideal Eis) :
    ‖inverseCubicKernel P n‖ ≤ 1 := by
  simpa only [inverseCubicKernel, norm_star, CubicSieve.idealKernel] using
    CubicSieve.idealKernel_norm_le_one P n

theorem inverseCubicKernel_mul_right (P n m : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0) :
    inverseCubicKernel P (n * m) = inverseCubicKernel P n * inverseCubicKernel P m := by
  change star (CubicSieve.idealNumeratorHom P hP (n * m)) =
    star (CubicSieve.idealNumeratorHom P hP n) * star (CubicSieve.idealNumeratorHom P hP m)
  rw [map_mul, star_mul]
  ring

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Quotients
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem sum_quotientSupport {A : Type*} [AddCommMonoid A]
    (D : Ideal Eis) (S : Finset (Ideal Eis)) (f : Ideal Eis → A) :
    (∑ I ∈ S with D ∣ I, f I) = ∑ J ∈ quotientSupport D S, f (D * J) := by
  rw [quotientSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [idealQuotient_mul (Finset.mem_filter.mp hI).2]
  · intro I hI J hJ he
    exact idealQuotient_injective_on D (Finset.mem_filter.mp hI).2
      (Finset.mem_filter.mp hJ).2 he

theorem quotientSupport_cubic_admissible (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, CubicSieve.Admissible I)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    CubicSieve.Admissible J :=
  CubicSieve.cubic_admissible_of_dvd
    (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)) (dvd_mul_left _ _)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CommonMeasure
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open MeasureTheory CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem common_measure_energy {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (b : Ω → ℂ) (φ : κ → Ω → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖) μ)
    (hφ : ∀ k, Integrable (fun t => b t * φ k t) μ)
    (hbound : ∀ t, (∑ k, ‖φ k t‖ ^ 2) ≤ E) :
    (∑ k, ‖∫ t, b t * φ k t ∂μ‖ ^ 2) ≤ E * (∫ t, ‖b t‖ ∂μ) ^ 2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : Ω → EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t * φ k t)
  have hF (t : Ω) : ‖F t‖ ≤ ‖b t‖ * Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hE]
    change (∑ k, ‖b t * φ k t‖ ^ 2) ≤ ‖b t‖ ^ 2 * E
    simp only [norm_mul, mul_pow, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫ t, F t ∂μ) = e.symm (fun k => ∫ t, b t * φ k t ∂μ) := by
    rw [show F = (fun t => e.symm (fun k => b t * φ k t)) from rfl,
      e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫ t, b t * φ k t ∂μ)‖ ≤
      (∫ t, ‖b t‖ ∂μ) * Real.sqrt E := by
    rw [← he, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hE] at hs
  simpa [e, mul_comm] using hs

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
omit [Fintype ι] in
theorem frozenArgument_norm_le_one [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι) (z : Eis) :
    ‖frozenArgument hg j F z‖ ≤ 1 := by
  simp only [frozenArgument,MonoidHom.finsetProd_apply,norm_prod]
  apply Finset.prod_le_one
  · intro i hi; exact norm_nonneg _
  · intro i hi
    unfold frozenCofactorCharacter
    split_ifs
    · exact FiniteRayExpansion.norm_char_le_one (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        (Ideal.Quotient.mk (Ideal.span {p i}) z)
    · exact FiniteRayExpansion.norm_char_le_one ((actualSextic (Ideal.span {p i}) (hg i))^(2*j i+2))
        (Ideal.Quotient.mk (Ideal.span {p i}) z)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Norms
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.phaseNormField
attribute [local instance] OAI.SevenEighths.InverseReflectedPhase.phaseNormFinite
omit [Fintype ι] in
theorem crossSymbol_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) : ‖MixedCrossSeparation.crossSymbol p hg i k‖ = 1 := by
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  have h6 : MixedCrossSeparation.crossSymbol p hg i k ^ 6 = 1 := by
    simpa only [MixedCrossSeparation.crossSymbol,map_pow,if_neg hnot] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (6:ℕ) ≠ 0)).mp
  simpa only [norm_pow,norm_one] using congrArg norm h6

theorem local_phase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (i : ι) (j : ℕ) (hj : j < 6) :
    ‖(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) j (D.epsilon i)‖ = 1 := by
  rw [norm_mul,FiniteRayExpansion.norm_char_unit,one_mul]
  exact canonical_phase_norm (Ideal.span {p i}) (hg i) (hchar i) (quotientTrace (p i) (hp i))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) j hj (D.epsilon i)

theorem markedPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (i : ι) :
    ‖markedPrimeScalar (p i) c (hp i) (hg i)‖ = 1 := by
  have h := local_phase_norm D hp hg hchar i 0 (by decide)
  rw [controlled_marked_phase,norm_mul,norm_prod] at h
  have he : (∏ k ∈ Finset.univ.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k^2‖) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [norm_pow,crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  simpa only [he,mul_one] using h

theorem residualPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (i : ι) :
    ‖residualPrimeScalar (p i) c (hp i) (hg i)‖ = 1 := by
  have h := local_phase_norm D hp hg hchar i 1 (by decide)
  rw [controlled_residual_phase,norm_mul,norm_prod] at h
  have he : (∏ k ∈ Finset.univ.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k^4‖) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [norm_pow,crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  simpa only [he,mul_one] using h

theorem residualWithFrozen_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (R F : Finset ι) (hd : Disjoint R F) : ‖residualWithFrozen hp hg c R F‖ = 1 := by
  unfold residualWithFrozen
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [norm_mul,norm_prod,norm_pow,residualPrimeScalar_norm D hp hg hchar hcop i,one_mul]
  have hR : (∏ k ∈ R.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k‖^4) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  have hF : (∏ k ∈ F, ‖MixedCrossSeparation.crossSymbol p hg i k‖^4) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (fun h => Finset.disjoint_left.mp hd hi (h ▸ hk)),one_pow]
  rw [hR,hF,one_mul]

theorem markedWithFrozen_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (P F : Finset ι) (hd : Disjoint P F) : ‖markedWithFrozen hp hg c P F‖ = 1 := by
  unfold markedWithFrozen
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [norm_mul,norm_prod,norm_pow,markedPrimeScalar_norm D hp hg hchar hcop i,one_mul]
  have hP : (∏ k ∈ P.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k‖^2) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  have hF : (∏ k ∈ F, ‖MixedCrossSeparation.crossSymbol p hg i k‖^2) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (fun h => Finset.disjoint_left.mp hd hi (h ▸ hk)),one_pow]
  rw [hP,hF,one_mul]

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
theorem ramifiedBlock_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) :
    ‖ramifiedBlock hg j S u m‖ = 1 := by
  unfold ramifiedBlock
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  exact unitArgumentFactor_norm _ _ _ (unit_ramified_quotient_ne_zero _ (hg i) u m)

theorem sourceRowPhase_norm_le_one [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (j : ι → ℕ) (R F : Finset ι) (hd : Disjoint R F) (u : Eisˣ) (m : ℕ) :
    ‖sourceRowPhase s hp hg j R F u m‖ ≤ 1 := by
  rw [sourceRowPhase,norm_mul,norm_mul,residualWithFrozen_norm D hp hg hchar hcop R F hd,
    ramifiedBlock_norm,one_mul,one_mul]
  exact frozenArgument_norm_le_one hg j F _

theorem sourceSlotPhase_norm_le_one [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (j : ι → ℕ) (S F : Finset ι) (hd : Disjoint S F) (u : Eisˣ) (m : ℕ) :
    ‖sourceSlotPhase s hp hg j S F u m‖ ≤ 1 := by
  rw [sourceSlotPhase,norm_mul,norm_mul,markedWithFrozen_norm D hp hg hchar hcop S F hd,
    ramifiedBlock_norm,one_mul,one_mul]
  exact frozenArgument_norm_le_one hg j F _

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Rows
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι κ : Type*}

lemma sum_pairwise (G : PrimeFamily ι) (H : PrimeFamily κ)
    (hG : Pairwise (Function.onFun IsCoprime G.ideal))
    (hH : Pairwise (Function.onFun IsCoprime H.ideal))
    (hcross : ∀ i k, IsCoprime (G.ideal i) (H.ideal k)) :
    Pairwise (Function.onFun IsCoprime (G.sum H).ideal) := by
  intro i k hik
  cases i with
  | inl i => cases k with
    | inl k => exact hG (fun h => hik (congrArg Sum.inl h))
    | inr k => exact hcross i k
  | inr i => cases k with
    | inl k => exact (hcross k i).symm
    | inr k => exact hH (fun h => hik (congrArg Sum.inr h))

lemma residual_pairwise (K : Ideal Eis) (hK : Admissible K) :
    Pairwise (Function.onFun IsCoprime (residual K hK).ideal) := by
  intro P Q hPQ
  apply Ideal.isCoprime_of_isMaximal
  intro h
  exact hPQ (Subtype.ext h)

end PrimeFamily
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

lemma actualCuspColumn_norm_le_one (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ‖actualCuspColumn D s hc u m n b‖ ≤ 1 :=
  fixedCuspArrayWithPhase_norm_le_one s.index u _
    (s.reflectionStaticPhase_norm_le_one c hc _ _ u) m n b

theorem frozenBranchColumn_norm_le (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal Eis) :
    ‖frozenBranchColumn F jF e A n b‖ ≤ frozenBranchScale F jF e := by
  rw [frozenBranchColumn,norm_mul]
  calc
    _ ≤ 1*‖reflectedBranch (fun i => Ideal.span {F.generator i}) F.generator_good jF e
        (primaryGenerator n) (primaryGenerator b)‖ := mul_le_mul_of_nonneg_right (hA n b) (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact reflectedBranch_norm_bound _ F.generator_good jF e _ _

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.FrozenNorms
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} {p : ι → Eis} {N a c : Eis} {mode : Bool}

lemma frozenCofactorCharacter_cross_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) (j : ℕ) :
    ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (p k)‖ = 1 := by
  have hn := crossSymbol_norm hg hcop i k hik
  unfold frozenCofactorCharacter
  split_ifs
  · simp only [MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv',norm_pow,norm_inv]
    change ‖MixedCrossSeparation.crossSymbol p hg i k‖⁻¹^2 = 1
    rw [hn]; norm_num
  · simp only [MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by omega : 2*j+2 ≠ 0),norm_pow]
    change ‖MixedCrossSeparation.crossSymbol p hg i k‖^(2*j+2) = 1
    rw [hn,one_pow]

lemma frozenCofactorCharacter_product_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (S : Finset ι) (hi : i ∉ S) (j : ℕ) :
    ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (∏ k ∈ S, p k)‖ = 1 := by
  rw [map_prod,norm_prod]
  apply Finset.prod_eq_one
  intro k hk
  exact frozenCofactorCharacter_cross_norm hg hcop i k (fun h => hi (h ▸ hk)) j

variable [Fintype ι]

lemma frozenPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (j : ℕ) (hj : j < 6) : ‖frozenPrimeScalar (p i) c (hp i) (hg i) j‖ = 1 := by
  have hh := local_phase_norm D hp hg hchar i j hj
  rw [controlled_frozen_phase,norm_mul] at hh
  have hn : ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (cofactor p i)‖ = 1 := by
    exact frozenCofactorCharacter_product_norm hg hcop i (Finset.univ.erase i) (by simp) j
  simpa only [hn,mul_one] using hh

lemma frozenCore_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (j : ι → ℕ) (F : Finset ι) (hj : ∀ i ∈ F, j i < 6) : ‖frozenCore hp hg c j F‖ = 1 := by
  rw [frozenCore,norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [norm_mul,frozenPrimeScalar_norm D hp hg hchar hcop i (j i) (hj i hi),one_mul]
  exact frozenCofactorCharacter_product_norm hg hcop i (F.erase i) (by simp) (j i)

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

lemma normalizedFrozenColumn_norm_le_one (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal Eis) :
    ‖normalizedFrozenColumn F jF e A n b‖ ≤ 1 := by
  have hp := frozenBranchScale_pos F jF e
  rw [normalizedFrozenColumn,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  calc
    _ ≤ (frozenBranchScale F jF e)⁻¹*frozenBranchScale F jF e :=
      mul_le_mul_of_nonneg_left (frozenBranchColumn_norm_le F jF e A hA n b) (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.ActualBounds
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma two_block_phase_bounds (F : PrimeFamily φ) (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : Pairwise (Function.onFun IsCoprime (F.sum S).ideal))
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((F.sum S).ideal i))
    (hchar : ∀ i, ringChar (Eis ⧸ (F.sum S).ideal i) ≠ 2) (u : Eisˣ) (m : ℕ) :
    ‖sourceRowPhase s (F.sum S).generator_ne_zero (F.sum S).generator_good
      (Sum.elim jF (fun _ => 1)) (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m‖ ≤ 1 ∧
    ‖actualSlotPhase F S jF s u m‖ ≤ 1 := by
  classical
  obtain ⟨D⟩ := (F.sum S).exists_controlled N a c mode hc hN hbase hac hcop hNp
  have hcp : Pairwise (Function.onFun IsCoprime
      (fun i => Ideal.span {(F.sum S).generator i})) := by
    simpa only [PrimeFamily.generator_span] using hcop
  have hch : ∀ i, ringChar (Eis ⧸ Ideal.span {(F.sum S).generator i}) ≠ 2 := by
    intro i
    have he := congrArg (fun I : Ideal Eis => ringChar (Eis ⧸ I)) ((F.sum S).generator_span i)
    exact he.symm ▸ hchar i
  have hd : Disjoint (Finset.univ.image (Sum.inr : σ → φ ⊕ σ)) (Finset.univ.image Sum.inl) := by
    simp only [Finset.disjoint_left,Finset.mem_image,Finset.mem_univ,true_and]
    rintro i ⟨k,rfl⟩ ⟨f,h⟩
    cases h
  exact ⟨sourceRowPhase_norm_le_one D s _ _ hch hcp _ _ _ hd u m,
    sourceSlotPhase_norm_le_one D s _ _ hch hcp _ _ _ hd u m⟩

lemma actualRowPhase_norm_le_one (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (jF : φ → ℕ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hFK : ∀ f, IsCoprime (F.ideal f) K)
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hNK : IsCoprime (Ideal.span {N}) K)
    (hcharF : ∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) (u : Eisˣ) (m : ℕ) :
    ‖actualRowPhase F K hK jF s u m‖ ≤ 1 := by
  have hcp := PrimeFamily.sum_pairwise F (PrimeFamily.residual K hK) hF
    (PrimeFamily.residual_pairwise K hK) (fun f P =>
      (hFK f).of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK P))
  have hNp : ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (PrimeFamily.residual K hK)).ideal i) := by
    intro i
    cases i with
    | inl f => exact hNF f
    | inr P => exact hNK.of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK P)
  have hchar : ∀ i, ringChar (Eis ⧸ (F.sum (PrimeFamily.residual K hK)).ideal i) ≠ 2 := by
    intro i
    cases i with
    | inl f => exact hcharF f
    | inr P => exact (hK.2.2 P.val (Multiset.mem_toFinset.mp P.property)).2
  have hh := (two_block_phase_bounds F (PrimeFamily.residual K hK) jF s hc hN hbase hac hcp hNp hchar u m).1
  unfold actualRowPhase
  convert (preTransparency := .instances) hh using 1 ; congr 2 <;> ext i <;> simp

lemma actualFrozenPhase_norm_le_one (F : PrimeFamily φ) (jF : φ → ℕ) (κ : ℂ) (hκ : ‖κ‖ ≤ 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hcharF : ∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) (hj : ∀ f, jF f < 6) (u : Eisˣ) (m : ℕ) :
    ‖actualFrozenPhase F jF κ s u m‖ ≤ 1 := by
  obtain ⟨D⟩ := F.exists_controlled N a c mode hc hN hbase hac hF hNF
  have hcp : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {F.generator i})) := by
    simpa only [PrimeFamily.generator_span] using hF
  have hch : ∀ i, ringChar (Eis ⧸ Ideal.span {F.generator i}) ≠ 2 := by
    intro i
    have he := congrArg (fun I : Ideal Eis => ringChar (Eis ⧸ I)) (F.generator_span i)
    exact he.symm ▸ hcharF i
  rw [actualFrozenPhase,norm_mul,norm_mul,norm_star,
    frozenCore_norm D _ _ hch hcp _ _ (fun i _ => hj i),ramifiedBlock_norm,mul_one,mul_one]
  exact hκ

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.Extraction
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ]

lemma frozenBranchColumn_divisibility (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis)
    (hn : primaryGenerator n ≠ 0) (hb : primaryGenerator b ≠ 0)
    (hz : frozenBranchColumn F jF e A n b ≠ 0) :
    frozenExtracted F jF e 1 ∣ n ∧ frozenExtracted F jF e 2 ∣ b ∧
      ∀ i, jF i=4 → e i=2 → primaryGenerator n ∉ F.ideal i := by
  have hcp : Pairwise (fun i k => IsCoprime (Ideal.span {F.generator i}) (Ideal.span {F.generator k})) := by
    simpa only [PrimeFamily.generator_span] using hF
  have hh := reflectedBranch_divisibility (fun i => Ideal.span {F.generator i}) F.generator_good hcp
    jF e (primaryGenerator n) (primaryGenerator b) (mul_ne_zero_iff.mp hz).2
  simpa only [frozenExtracted,(primaryGenerator_spec n hn).1,(primaryGenerator_spec b hb).1,
    PrimeFamily.generator_span] using hh

lemma frozenBranchColumn_zero_of_not_dvd (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis)
    (hn : primaryGenerator n ≠ 0) (hb : primaryGenerator b ≠ 0)
    (hz : ¬ frozenExtracted F jF e 1 ∣ n ∨ ¬ frozenExtracted F jF e 2 ∣ b) :
    frozenBranchColumn F jF e A n b = 0 := by
  by_contra hh
  obtain ⟨hd1,hd2,_⟩ := frozenBranchColumn_divisibility F hF jF e A n b hn hb hh
  exact hz.elim (fun h => h hd1) (fun h => h hd2)

theorem frozenBranchColumn_dual_reindex (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A W : Ideal Eis → Ideal Eis → ℂ) (nset bset : Finset (Ideal Eis))
    (hn : ∀ n ∈ nset, primaryGenerator n ≠ 0) (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0) :
    (∑ n ∈ nset, ∑ b ∈ bset, frozenBranchColumn F jF e A n b*W n b) =
      ∑ n ∈ quotientSupport (frozenExtracted F jF e 1) nset,
        ∑ b ∈ quotientSupport (frozenExtracted F jF e 2) bset,
          frozenBranchColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)*
            W ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b) := by
  classical
  have hfilter :
      (∑ n ∈ nset, ∑ b ∈ bset, frozenBranchColumn F jF e A n b*W n b) =
      ∑ n ∈ nset with frozenExtracted F jF e 1 ∣ n,
        ∑ b ∈ bset with frozenExtracted F jF e 2 ∣ b, frozenBranchColumn F jF e A n b*W n b := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn'
    by_cases hd1 : frozenExtracted F jF e 1 ∣ n
    · rw [if_pos hd1]
      apply Finset.sum_congr rfl
      intro b hb'
      by_cases hd2 : frozenExtracted F jF e 2 ∣ b
      · rw [if_pos hd2]
      · rw [if_neg hd2,frozenBranchColumn_zero_of_not_dvd F hF jF e A n b (hn n hn') (hb b hb') (Or.inr hd2),zero_mul]
    · rw [if_neg hd1]
      apply Finset.sum_eq_zero
      intro b hb'
      rw [frozenBranchColumn_zero_of_not_dvd F hF jF e A n b (hn n hn') (hb b hb') (Or.inl hd1),zero_mul]
  rw [hfilter,sum_quotientSupport]
  apply Finset.sum_congr rfl
  intro n hn'
  exact sum_quotientSupport _ _ _

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.ExtractedKernel
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma extractedRowFactor_norm_le_one (D1 D2 K : Ideal Eis) : ‖extractedRowFactor D1 D2 K‖ ≤ 1 :=
  quadraticRow_norm_le_one K _

lemma extractedSlotFactor_norm_le_one (D1 D2 P : Ideal Eis) : ‖extractedSlotFactor D1 D2 P‖ ≤ 1 := by
  unfold extractedSlotFactor
  split_ifs
  · simpa only [mul_one] using inverseCubicKernel_norm_le_one P D1
  · simp

lemma coprime_product_mask (P D b : Ideal Eis) :
    (if IsCoprime P (D*b) then (1:ℂ) else 0) =
      (if IsCoprime P D then 1 else 0)*(if IsCoprime P b then 1 else 0) := by
  by_cases hD : IsCoprime P D <;> by_cases hb : IsCoprime P b
  · simp [hD,hb,hD.mul_right hb]
  · have hn : ¬IsCoprime P (D*b) := fun h => hb (h.of_isCoprime_of_dvd_right (dvd_mul_left _ _))
    simp [hD,hb,hn]
  · have hn : ¬IsCoprime P (D*b) := fun h => hD (h.of_isCoprime_of_dvd_right (dvd_mul_right _ _))
    simp [hD,hb,hn]
  · have hn : ¬IsCoprime P (D*b) := fun h => hD (h.of_isCoprime_of_dvd_right (dvd_mul_right _ _))
    simp [hD,hb,hn]

theorem forced_dual_kernel_factor (D1 D2 K P n b : Ideal Eis)
    (hK : Admissible K) (hP : primaryGenerator P ≠ 0) :
    quadraticRow K (primaryGenerator ((D1*n)*(D2*b)))*inverseCubicKernel P (D1*n)*
      (if IsCoprime P (D2*b) then 1 else 0)*(if IsCoprime K P then 1 else 0) =
      (extractedRowFactor D1 D2 K*extractedSlotFactor D1 D2 P)*
        quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*
        (if IsCoprime P b then 1 else 0)*(if IsCoprime K P then 1 else 0) := by
  rw [show (D1*n)*(D2*b)=(D1*D2)*(n*b) by ring,primaryGenerator_mul,
    canonical_quadraticRow_argument_mul K hK,inverseCubicKernel_mul_right P D1 n hP,
    coprime_product_mask]
  unfold extractedRowFactor extractedSlotFactor
  ring

lemma extractedFrozenColumn_norm_le_one {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
    (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal Eis → Ideal Eis → ℂ)
    (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal Eis) : ‖extractedFrozenColumn F jF e A n b‖ ≤ 1 :=
  normalizedFrozenColumn_norm_le_one F jF e A hA _ _

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.ExtractedRow
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ]

lemma hybridInner_frozen_dual_reindex (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (nset bset : Finset (Ideal Eis))
    (hn : ∀ n ∈ nset, primaryGenerator n ≠ 0) (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (K P : Ideal Eis) :
    hybridInner nset bset (frozenBranchColumn F jF e A) K P =
      ∑ n ∈ quotientSupport (frozenExtracted F jF e 1) nset,
        ∑ b ∈ quotientSupport (frozenExtracted F jF e 2) bset,
          frozenBranchColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)*
            quadraticRow K (primaryGenerator (((frozenExtracted F jF e 1)*n)*((frozenExtracted F jF e 2)*b)))*
            inverseCubicKernel P ((frozenExtracted F jF e 1)*n)*
            (if IsCoprime P ((frozenExtracted F jF e 2)*b) then 1 else 0) := by
  simpa only [hybridInner,mul_assoc] using frozenBranchColumn_dual_reindex F hF jF e A
    (fun n b => quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*(if IsCoprime P b then 1 else 0))
    nset bset hn hb

theorem hybridRow_frozen_extraction (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (nset bset Pset : Finset (Ideal Eis))
    (hn : ∀ n ∈ nset, primaryGenerator n ≠ 0) (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (aP : Ideal Eis → ℂ) (K : Ideal Eis) (hK : Admissible K)
    (hP : ∀ P ∈ Pset, primaryGenerator P ≠ 0) :
    hybridRow Pset nset bset aP (frozenBranchColumn F jF e A) K =
      ((frozenBranchScale F jF e:ℂ)*extractedRowFactor (frozenExtracted F jF e 1) (frozenExtracted F jF e 2) K)*
        hybridRow Pset (quotientSupport (frozenExtracted F jF e 1) nset)
          (quotientSupport (frozenExtracted F jF e 2) bset)
          (fun P => aP P*extractedSlotFactor (frozenExtracted F jF e 1) (frozenExtracted F jF e 2) P)
          (extractedFrozenColumn F jF e A) K := by
  unfold hybridRow
  simp_rw [hybridInner_frozen_dual_reindex F hF jF e A nset bset hn hb]
  simp only [hybridInner,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP'
  apply Finset.sum_congr rfl
  intro n hn'
  apply Finset.sum_congr rfl
  intro b hb'
  rw [frozenBranchColumn_eq_normalized]
  have hh := forced_dual_kernel_factor (frozenExtracted F jF e 1) (frozenExtracted F jF e 2)
    K P n b hK (hP P hP')
  have he := congrArg (fun z : ℂ => aP P/(Real.sqrt (Ideal.absNorm P:ℝ):ℂ)*
    (frozenBranchScale F jF e:ℂ)*extractedFrozenColumn F jF e A n b*z) hh
  convert (preTransparency := .instances) he using 1 <;> simp only [extractedFrozenColumn,div_eq_mul_inv] <;> ring

lemma quotientSupport_norm_div (D : Ideal Eis) (hD : D ≠ 0) (S : Finset (Ideal Eis)) (Y : ℝ)
    (hS : ∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ Y) (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    (Ideal.absNorm J:ℝ) ≤ Y/(Ideal.absNorm D:ℝ) := by
  have hpos : (0:ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hh := hS (D*J) ((mem_quotientSupport D J hD S).mp hJ)
  rw [map_mul,Nat.cast_mul] at hh
  exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hh)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.WeightedEnergy
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ ι : Type*} [Fintype φ] [Fintype ι] {N a c : Eis} {mode : Bool}

lemma actualCuspWeightedColumn_norm_le_one {ι : Type*} [Fintype ι]
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (w : Ideal Eis → Ideal Eis → ℂ)
    (hw : ∀ n b, ‖w n b‖ ≤ 1) (n b : Ideal Eis) :
    ‖actualCuspColumn D0 s hc u m n b*w n b‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (actualCuspColumn_norm_le_one D0 s hc u m n b)).trans (hw n b)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.WeightedMeasurable
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

lemma weightedReflectedBranchHybridRow_aestronglyMeasurable
    (μ : Measure Ω) (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (S : Ideal Eis → PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis → Ideal Eis → ℂ)
    (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ)
    (u : Eisˣ) (m : ℕ) (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis)
    (hr : AEStronglyMeasurable (fun t => r t K) μ)
    (ha : ∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ)
    (hw : ∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) :
    AEStronglyMeasurable (fun t => weightedReflectedBranchHybridRow F jF e S s κ A
      (r t) (aw t) (w t) u m Pset nset bset K) μ := by
  unfold weightedReflectedBranchHybridRow
  apply (hr.const_mul _).mul
  unfold hybridRow
  apply Finset.aestronglyMeasurable_fun_sum
  intro P hP
  simp only [div_eq_mul_inv]
  apply (((ha P hP).const_mul _).mul_const _ |>.mul_const _).mul
  unfold hybridInner
  apply Finset.aestronglyMeasurable_fun_sum
  intro n hn
  apply Finset.aestronglyMeasurable_fun_sum
  intro b hb
  unfold frozenBranchColumn
  exact (((((hw n hn b hb).const_mul _).mul_const _).mul_const _).mul_const _).mul_const _

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.UniformSieve
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v
variable {Ω : Type*} [MeasurableSpace Ω] {N a c : Eis} {mode : Bool}

theorem bounded_column_hybrid_energy_extracted_type_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {φ : Type u} [Fintype φ], ∀ X Y B L : ℝ, 1 ≤ X → 1 ≤ L →
    ∀ (F : PrimeFamily φ), Pairwise (Function.onFun IsCoprime F.ideal) →
    ∀ (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal Eis → Ideal Eis → ℂ),
      (∀ n b, ‖A n b‖ ≤ 1) →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (aP : Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ P ∈ Pset, ‖aP P‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖hybridRow Pset nset bset aP
        (frozenBranchColumn F jF e A) K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := hybridRow_energy ε hε
  refine ⟨C,hC,?_⟩
  intro φ _ X Y B L hX hL F hF jF e A hA rows nset bset Pset aP hrows hn hb hP ha
  let D1 := frozenExtracted F jF e 1
  let D2 := frozenExtracted F jF e 2
  let Yq := extractedDualScale D1 Y
  let Bq := extractedDualScale D2 B
  have hD1 : D1 ≠ 0 := frozenExtracted_ne_zero F jF e 1
  have hD2 : D2 ≠ 0 := frozenExtracted_ne_zero F jF e 2
  have hnq : ∀ n ∈ quotientSupport D1 nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Yq := by
    intro n hn'
    exact ⟨quotientSupport_cubic_admissible D1 hD1 nset (fun n h => (hn n h).1) n hn',
      (quotientSupport_norm_div D1 hD1 nset Y (fun n h => (hn n h).2) n hn').trans (le_max_right _ _)⟩
  have hbq : ∀ b ∈ quotientSupport D2 bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ Bq := by
    intro b hb'
    have hsource := hb (D2*b) ((mem_quotientSupport D2 b hD2 bset).mp hb')
    rw [primaryGenerator_mul] at hsource
    exact ⟨(mul_ne_zero_iff.mp hsource.1).2,
      (quotientSupport_norm_div D2 hD2 bset B (fun b h => (hb b h).2) b hb').trans (le_max_right _ _)⟩
  have hacoeff : ∀ P ∈ Pset, ‖aP P*extractedSlotFactor D1 D2 P‖ ≤ 1 := by
    intro P hP'
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha P hP')).trans (extractedSlotFactor_norm_le_one D1 D2 P)
  have hcolumn : ∀ n b, ‖extractedFrozenColumn F jF e A n b‖ ≤ 1 :=
    extractedFrozenColumn_norm_le_one F jF e A hA
  have hh := he X Yq Bq L hX (le_max_left _ _) (le_max_left _ _) hL rows
    (quotientSupport D1 nset) (quotientSupport D2 bset) Pset
    (fun P => aP P*extractedSlotFactor D1 D2 P)
    (extractedFrozenColumn F jF e A)
    hrows hnq hbq hP hacoeff (fun n _ b _ => hcolumn n b)
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    ((by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)) :
      (∑ K ∈ rows, (frozenBranchScale F jF e)^2*
        ‖hybridRow Pset (quotientSupport D1 nset) (quotientSupport D2 bset)
          (fun P => aP P*extractedSlotFactor D1 D2 P)
          (extractedFrozenColumn F jF e A) K‖^2) ≤ _)
  rw [hybridRow_frozen_extraction F hF jF e _ nset bset Pset
    (fun n h => (hn n h).1.2) (fun b h => (hb b h).1) aP K (hrows K hK).1
    (fun P h => (hP P h).1.2)]
  have hp := frozenBranchScale_pos F jF e
  have hs := extractedRowFactor_norm_le_one D1 D2 K
  have hs2 : ‖extractedRowFactor D1 D2 K‖^2 ≤ 1 := by
    have h0 := norm_nonneg (extractedRowFactor D1 D2 K)
    nlinarith
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,mul_pow]
  change (frozenBranchScale F jF e)^2*‖extractedRowFactor D1 D2 K‖^2* _ ≤ _
  calc
    _ ≤ ((frozenBranchScale F jF e)^2*1)*_ := by gcongr
    _ = _ := by rw [mul_one]

theorem actual_weighted_reflected_branch_energy_type_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ K ∈ rows, ‖r K‖ ≤ 1) → (∀ P ∈ Pset, ‖aw P‖ ≤ 1) → (∀ n b, ‖w n b‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := bounded_column_hybrid_energy_extracted_type_uniform  ε hε
  refine ⟨C,hC,?_⟩
  intro φ σ _ _ X Y B L hX _hY _hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop _hproducts hScop hSN hSchar hn hb hP hr haw hw
  have hfrozen : ‖actualFrozenPhase F jF D0.fixedFactor s u m‖ ≤ 1 :=
    actualFrozenPhase_norm_le_one F jF D0.fixedFactor (D0.fixedFactor_norm hN G0.generator_product_primary hbase).le
      s hc hN hbase hac hF hNF hcharF hj u m
  have hrow (K : Ideal Eis) (hK : K ∈ rows) : ‖actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    rw [actualRowPhaseExtension,dif_pos (hrows K hK).1]
    exact actualRowPhase_norm_le_one F K (hrows K hK).1 jF s hc hN hbase hac hF
      (hrowcop K hK).1 hNF (hrowcop K hK).2 hcharF u m
  have hslot (P : Ideal Eis) (hP : P ∈ Pset) : ‖actualSlotPhase F (S P) jF s u m*aw P‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (two_block_phase_bounds F (S P) jF s hc hN hbase hac (hScop P hP) (hSN P hP) (hSchar P hP) u m).2).trans
      (haw P hP)
  have hcol := actualCuspWeightedColumn_norm_le_one G0 D0 s hc u m w hw
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    (he X Y B L hX hL F hF jF e (fun n b => actualCuspColumn D0 s hc u m n b*w n b) hcol
      rows nset bset Pset (fun P => actualSlotPhase F (S P) jF s u m*aw P) hrows hn hb hP hslot)
  have hphase : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K*r K‖ ≤ 1 := by
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((mul_le_of_le_one_left (norm_nonneg _) hfrozen).trans (hrow K hK))).trans (hr K hK)
  have hphase0 := norm_nonneg ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K*r K)
  have hs : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K*r K‖^2 ≤ 1 := by nlinarith
  rw [weightedReflectedBranchHybridRow,norm_mul,mul_pow]
  exact (mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans_eq (one_mul _)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.UniformFiltered
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v
variable {Ω : Type*} [MeasurableSpace Ω] {N a c : Eis} {mode : Bool}

theorem filtered_actual_weighted_reflected_energy_type_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ) (E : Finset (φ→Fin 3))
      (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ K ∈ rows, ‖r K‖ ≤ 1) → (∀ P ∈ Pset, ‖aw P‖ ≤ 1) → (∀ n b, ‖w n b‖ ≤ 1) →
      (∑ K ∈ rows, ‖∑ e∈E, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2) ≤
      (E.card:ℝ) * ∑ e∈E,
        let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
        let Bq := extractedDualScale (frozenExtracted F jF e 2) B
        (frozenBranchScale F jF e)^2*
          (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := actual_weighted_reflected_branch_energy_type_uniform
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro φ σ _ _ X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S E r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP hr haw hw
  calc
    _ ≤ ∑ K ∈ rows, (E.card:ℝ)*
        ∑ e∈E, ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2 := by
      apply Finset.sum_le_sum
      intro K hK
      exact CubicEisenstein.norm_sum_sq_le_card E
        (fun e : φ→Fin 3 => weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K)
    _ = (E.card:ℝ)*∑ e∈E, ∑ K ∈ rows,
        ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
          (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he'
      exact he X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
        G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP hr haw hw

theorem integrated_filtered_actual_reflected_energy_type_uniform_oai (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ) (branches : Finset (φ→Fin 3))
      (μ : Measure Ω) (density : Ω → ℂ) (scalar : ℂ)
      (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      Integrable density μ →
      (∀ K ∈ rows, AEStronglyMeasurable (fun t => r t K) μ) →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ) →
      (∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) →
      (∀ t, ∀ K ∈ rows, ‖r t K‖ ≤ 1) → (∀ t, ∀ P ∈ Pset, ‖aw t P‖ ≤ 1) →
      (∀ t n b, ‖w t n b‖ ≤ 1) →
      (∑ K ∈ rows, ‖scalar * ∫ t, density t * (∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2) ≤
      ‖scalar‖^2*((branches.card:ℝ)*∑ e∈branches,
          let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
          let Bq := extractedDualScale (frozenExtracted F jF e 2) B
          (frozenBranchScale F jF e)^2*
            (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(∫ t, ‖density t‖ ∂μ)^2 := by
  obtain ⟨C,hC,he⟩ := filtered_actual_weighted_reflected_energy_type_uniform
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro φ σ _ _ X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S branches μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
  let E : ℝ := (branches.card:ℝ)*∑ e∈branches,
          let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
          let Bq := extractedDualScale (frozenExtracted F jF e 2) B
          (frozenBranchScale F jF e)^2*
            (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ)))
  have hE : 0 ≤ E := by
    dsimp only [E]
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro e he
    have hYq : 0 ≤ extractedDualScale (frozenExtracted F jF e 1) Y := le_trans zero_le_one (le_max_left _ _)
    have hBq : 0 ≤ extractedDualScale (frozenExtracted F jF e 2) B := le_trans zero_le_one (le_max_left _ _)
    positivity
  let ψ : rows → Ω → ℂ := fun K t => (∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val)
  have hbound (t : Ω) : (∑ K, ‖ψ K t‖^2) ≤ E := by
    change (∑ K : rows, ‖(∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val)‖^2) ≤ E
    rw [Finset.sum_coe_sort rows (fun K : Ideal Eis => ‖(∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K)‖^2)]
    exact he X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
      G0 D0 u m rows nset bset Pset S branches (r t) (aw t) (w t)
      hrows hrowcop hproducts hScop hSN hSchar hn hb hP (hr t) (haw t) (hw t)
  have hψM (K : rows) : AEStronglyMeasurable (ψ K) μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro e he
    exact weightedReflectedBranchHybridRow_aestronglyMeasurable μ F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K.val
      (hrM K.val K.property) hawM hwM
  have hpoint (K : rows) (t : Ω) : ‖ψ K t‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖ψ j t‖) (Finset.mem_univ K)).trans (hbound t)
  have hint (K : rows) : Integrable (fun t => density t*ψ K t) μ :=
    hdensity.mul_bdd (hψM K) (Filter.Eventually.of_forall (hpoint K))
  have hh := mul_le_mul_of_nonneg_left
    (common_measure_energy μ density ψ E hE hdensity.norm hint hbound) (sq_nonneg ‖scalar‖)
  have hsum : (∑ K : rows, ‖∫ t, density t*ψ K t ∂μ‖^2) =
      ∑ K ∈ rows, ‖∫ t, density t*(∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2 :=
    Finset.sum_coe_sort rows (fun K : Ideal Eis =>
      ‖∫ t, density t*(∑ e∈branches, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K) ∂μ‖^2)
  rw [hsum] at hh
  simp only [norm_mul,mul_pow,← Finset.mul_sum]
  simpa only [E,mul_assoc] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI
end

theorem solution.{u, v, u_1, u_2} : type_of% @OAI.SevenEighths.InverseReflectedPhase.integrated_filtered_actual_reflected_energy_type_uniform_oai.{u, v, u_1, u_2} := @OAI.SevenEighths.InverseReflectedPhase.integrated_filtered_actual_reflected_energy_type_uniform_oai.{u, v, u_1, u_2}
