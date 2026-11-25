-- Prove2me | solution 1 for HostParam.Seam.exists_hostNF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:37:09.600502+00:00
-- url     : https://prove2.me/submissions/d7c60f97-ce88-4fba-a90f-ac7f3ff2ae8d

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_SecondSetNoRelation
import Theorems.Thm_HostParam_Seam_exists_cmType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HC Formalism.BasicNotions
open scoped Pointwise
noncomputable section
open HostParam HostParam.Seam
namespace HostParam.Seam
theorem _root_.solution (R : Ranks) (H : HostAx R.toFrame) {b : ℕ} (h : FieldRows H.toHostRaw b)
    (hq : 4 * R.t * R.r + 1 < H.q ∧ 4 * R.t * R.r + 1 < H.d) (c : Choices R.toFrame H.toHostRaw) :
    ∃ N : HostNF R, N.ax = H ∧ N.splitBound = b ∧ HEq N.ch c := by
  obtain ⟨s, hs1, hs2⟩ := h.sqq
  obtain ⟨ψ, hψ⟩ := exists_cmType H
  obtain ⟨𝔟, h1, h2, h3⟩ := H.der.principal
  exact ⟨⟨H, b, h, hq, s, hs1, hs2, ψ, hψ, 𝔟, ⟨h1, h2⟩, h3, c⟩, rfl, rfl, HEq.rfl⟩
end HostParam.Seam
