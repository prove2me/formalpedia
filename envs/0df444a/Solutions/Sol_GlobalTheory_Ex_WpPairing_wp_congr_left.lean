-- Prove2me | solution 1 for GlobalTheory.Ex.WpPairing.wp_congr_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:29.155931+00:00
-- url     : https://prove2.me/submissions/242e5b4f-6d26-48ef-84ca-86e4f3b01890

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties
import Theorems.Thm_GlobalTheory_Ex_WpPairing_wp_qTriv
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.WpPairing
variable {O : Type} [CommRing O] (N : NumD O)
open scoped BigOperators
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O)
namespace GlobalTheory.Ex.WpPairing
namespace _root_.GlobalTheory.Ex.WpPairing
theorem _root_.solution {k : ℕ} {p p' : N.QT k} (h : N.QEq p p') (q : N.QT k) : N.wp p q = N.wp p' q := by
  obtain ⟨z, rfl⟩ := (N.qEq_iff p p').mp h
  rw [_root_.GlobalTheory.Ex.WpPairing.wp_mul_left, _root_.GlobalTheory.Ex.WpPairing.wp_qTriv, mul_one]
end _root_.GlobalTheory.Ex.WpPairing
end GlobalTheory.Ex.WpPairing
