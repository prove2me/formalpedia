-- Prove2me | solution 1 for GlobalTheory.Ex.PhiOp.phi_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:50:59.198437+00:00
-- url     : https://prove2.me/submissions/e336abb9-7ac7-478b-9ce3-60245edc72cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FeOfPhiTriv
import Theorems.Thm_GlobalTheory_Ex_PhiOp_phi_phi
import Theorems.Thm_GlobalTheory_Ex_PhiOp_phi_mul

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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.PhiOp
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.PhiOp
theorem _root_.solution {k : ℕ} (p p' : N.QT k) (w w' : Oˣ) (s : N.X → N.A → O) :
    N.phi p w (N.phi p' w' s) = (N.wp p p' : O) • N.phi p' w' (N.phi p w s) := by
  rw [phi_phi, phi_phi, ← phi_mul, mul_comm p' p, NumD.wp]
  congr 1
  rw [mul_comm w' w, mul_left_comm, div_mul_cancel]
end GlobalTheory.Ex.PhiOp
