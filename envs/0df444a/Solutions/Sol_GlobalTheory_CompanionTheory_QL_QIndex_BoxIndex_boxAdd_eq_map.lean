-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.boxAdd_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:22.85915+00:00
-- url     : https://prove2.me/submissions/5c18141e-8a5a-4665-9b76-6270e251d99c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_BoxIndex_mem_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
open GlobalTheory.CompanionTheory.QL.NormalisedValue GlobalTheory.CompanionTheory.SplitRow.IdxV
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
theorem _root_.solution (O : Subring F) {n : ℕ} (β : Fin n → ℕ) (c : Fin n → Fin n → F) :
    boxAdd O β c =
      (AddSubgroup.pi Set.univ fun p : Idx β => line O (c p.1.1 p.1.2)).map (ext0 β) := by
  ext X
  constructor
  · rintro ⟨hX, hX'⟩
    refine AddSubgroup.mem_map.2 ⟨fun p => X p.1.1 p.1.2, ?_, ?_⟩
    · rw [AddSubgroup.mem_pi]
      intro p _
      exact mem_line.2 (hX' _ _)
    · ext a b
      by_cases hab : β a ≤ β b
      · simp [ext0, hab]
      · simp [ext0, hab, hX (not_le.1 hab)]
  · rintro h
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 h
    rw [AddSubgroup.mem_pi] at hx
    refine ⟨fun a b hab => ?_, fun a b => ?_⟩
    · simp [ext0, not_le.2 hab]
    · by_cases hab : β a ≤ β b
      · obtain ⟨o, ho, e⟩ := mem_line.1 (hx ⟨(a, b), hab⟩ (Set.mem_univ _))
        exact ⟨o, ho, by simpa [ext0, hab] using e⟩
      · exact ⟨0, O.zero_mem, by simp [ext0, hab]⟩
end GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
