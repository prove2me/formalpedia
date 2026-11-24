-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.Dual.deg_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:00:58.46554+00:00
-- url     : https://prove2.me/submissions/7d8cd2de-1c78-4386-8cfb-cbfc2e5c7159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnramifiedQuadraticLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianDualInvAlgBaseChangeUnramifiedIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.Dual
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
namespace GlobalTheory.UnitLemma.Unr.Dual
theorem _root_.solution {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · exfalso
    have h1 := K'.card_res
    rw [hU.1, h, pow_zero, one_pow] at h1
    have : 1 < Nat.card (IsLocalRing.ResidueField K'.O) := Finite.one_lt_card
    omega
  · exact h
end GlobalTheory.UnitLemma.Unr.Dual
