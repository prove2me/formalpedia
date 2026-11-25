-- Prove2me | solution 1 for GlobalTheory.SectionSum.liftS_fieldRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:40:52.9609+00:00
-- url     : https://prove2.me/submissions/b39cbe0f-61e4-44c6-90a8-e034c50fba1e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AemeasurableFinsumSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.SectionSum
open MvPolynomial MeasureTheory
namespace GlobalTheory.SectionSum
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    {j₀ : Fin (N + 1)} {x : Fin N → Ω} (h : Function.Injective (sHom (K := K) (D := D) j₀ x)) :
    (liftS h).fieldRange =
      (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x))).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield, liftS, IsFractionRing.lift_fieldRange]
  apply le_antisymm
  · rw [Subfield.closure_le]
    rintro _ ⟨p, rfl⟩
    induction p using MvPolynomial.induction_on
    next a =>
      exact Subfield.subset_closure (Or.inl ⟨a, by simp [sHom]⟩)
    next p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    next p i hp =>
      rw [map_mul]
      exact mul_mem hp (Subfield.subset_closure (Or.inr ⟨i, by simp [sHom]⟩))
  · rw [Subfield.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨i, rfl⟩)
    · exact Subfield.subset_closure ⟨MvPolynomial.C a, by simp [sHom]⟩
    · exact Subfield.subset_closure ⟨MvPolynomial.X i, by simp [sHom]⟩
end GlobalTheory.SectionSum
