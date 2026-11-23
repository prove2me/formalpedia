-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SplitRow.IdxV.mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:33.554487+00:00
-- url     : https://prove2.me/submissions/14a385b0-8d93-43f5-af99-90c333351c0a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_HasElemDiv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.FinHeis GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.SplitRow.IdxV
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.SplitRow.IdxV
theorem _root_.solution (c x : k) : x ∈ ball c ↔ x * c ∈ 𝒪[k] := Iff.rfl
end GlobalTheory.CompanionTheory.SplitRow.IdxV
