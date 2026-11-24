-- Prove2me | solution 1 for GlobalTheory.Ex.PhiOp.phi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:44:37.444526+00:00
-- url     : https://prove2.me/submissions/8a257259-eac3-4135-9196-5d3f3d1f47dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FeOfPhiTriv

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
theorem _root_.solution {k : ℕ} (p : N.QT k) (u w : Oˣ) (s : N.X → N.A → O) :
    N.phi p (u * w) s = (u : O) • N.phi p w s := by
  funext α x
  simp only [NumD.phi, Pi.smul_apply, smul_eq_mul, Units.val_mul]
  ring
end GlobalTheory.Ex.PhiOp
