-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.map_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:24.570704+00:00
-- url     : https://prove2.me/submissions/f134a579-363b-42b9-8cc0-a483459ad6bf

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
theorem _root_.solution (O : Subring F) (e c : F) :
    (line O c).map (AddMonoidHom.mulLeft e) = line O (e * c) := by
  ext x
  simp only [AddSubgroup.mem_map, mem_line, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
    exact ⟨o, ho, by ring⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨c * o, ⟨o, ho, rfl⟩, by ring⟩
end GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
