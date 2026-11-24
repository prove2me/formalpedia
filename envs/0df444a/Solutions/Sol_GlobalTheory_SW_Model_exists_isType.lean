-- Prove2me | solution 1 for GlobalTheory.SW.Model.exists_isType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:28:21.878807+00:00
-- url     : https://prove2.me/submissions/3be38a52-a675-4793-ab0c-0c38bbd07fbd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Model
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Model
theorem _root_.solution : ∃ Ψ : Finset (E →+* ℂ), IsType Ψ ∧ Ψ.Nonempty := by
  classical
  let Ψ : Finset (E →+* ℂ) := Finset.univ.filter fun τ => (InfinitePlace.mk τ).embedding = τ
  have hT : IsType Ψ := by
    intro τ
    have hne : ComplexEmbedding.conjugate τ ≠ τ := IsTotallyComplex.complexEmbedding_not_isReal τ
    simp only [Ψ, Finset.mem_filter, Finset.mem_univ, true_and, InfinitePlace.mk_conjugate_eq]
    rcases InfinitePlace.mk_eq_iff.1 (InfinitePlace.mk_embedding (InfinitePlace.mk τ)) with h | h
    · rw [h]; simp [hne.symm]
    · have h2 : (InfinitePlace.mk τ).embedding = ComplexEmbedding.conjugate τ := by
        rw [← h]; ext x; simp
      rw [h2]; simp [hne]
  refine ⟨Ψ, hT, ?_⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ Ψ
  · exact ⟨τ, h⟩
  · exact ⟨_, by simpa [h] using (hT τ).not⟩
end GlobalTheory.SW.Model
