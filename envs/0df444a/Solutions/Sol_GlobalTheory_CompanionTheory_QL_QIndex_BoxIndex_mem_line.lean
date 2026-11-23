-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex.mem_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:58.312922+00:00
-- url     : https://prove2.me/submissions/eceb782e-35b9-43b3-bf8c-7f2223013df9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct

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
theorem _root_.solution {O : Subring F} {c x : F} : x ∈ line O c ↔ ∃ o ∈ O, x = c * o := by
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩
end GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
