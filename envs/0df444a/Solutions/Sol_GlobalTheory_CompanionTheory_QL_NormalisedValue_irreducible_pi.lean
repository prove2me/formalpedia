-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.NormalisedValue.irreducible_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:12.759498+00:00
-- url     : https://prove2.me/submissions/3ec3332c-22bc-4aba-aed9-608bbe855733

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
namespace GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
private theorem isUnit_iff_valuation_eq_one' (y : 𝒪[F]) : IsUnit y ↔ ValuativeRel.valuation F (y : F) = 1 := by
  first
    | exact (Valuation.integer.integers _).isUnit_iff_valuation_eq_one
    | simpa using (Valuation.integer.integers (ValuativeRel.valuation F)).isUnit_iff_valuation_eq_one (x := y)
end GlobalTheory.CompanionTheory.QL.NormalisedValue
end

set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.NormalisedValue
theorem _root_.solution (h : LF O ϖ nrm q) :
    Irreducible (⟨ϖ, (Valuation.mem_integer_iff _ _).2 (val_pi_lt_one h).le⟩ : 𝒪[F]) := by
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_valuation_eq_one']
    exact (val_pi_lt_one h).ne
  · intro a b hab
    by_cases ha : ValuativeRel.valuation F (a : F) = 1
    · left
      exact (isUnit_iff_valuation_eq_one' a).2 ha
    · right
      have ha1 : ValuativeRel.valuation F (a : F) < 1 :=
        lt_of_le_of_ne ((Valuation.mem_integer_iff _ _).1 a.2) ha
      obtain ⟨o, hoO, hao⟩ := (h.lt_one a).1 ha1
      have hab' : (ϖ : F) = (a : F) * (b : F) := congrArg Subtype.val hab
      have hoI : o ∈ 𝒪[F] := by
        rw [← h.O_eq]
        exact hoO
      have hob : (⟨o, hoI⟩ : 𝒪[F]) * b = 1 := by
        apply Subtype.ext
        show o * (b : F) = 1
        have hh : ϖ * 1 = ϖ * (o * (b : F)) := by
          rw [mul_one, ← mul_assoc, ← hao, ← hab']
        exact (mul_left_cancel₀ h.ne hh).symm
      exact ⟨⟨b, ⟨o, hoI⟩, (mul_comm _ _).trans hob, hob⟩, rfl⟩
end GlobalTheory.CompanionTheory.QL.NormalisedValue
