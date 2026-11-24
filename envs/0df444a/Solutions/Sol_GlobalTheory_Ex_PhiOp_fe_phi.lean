-- Prove2me | solution 1 for GlobalTheory.Ex.PhiOp.fe_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:17:09.919669+00:00
-- url     : https://prove2.me/submissions/1760dac5-e342-427b-bdb6-0e85fcdcbd64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FeOfPhiTriv
import Theorems.Thm_GlobalTheory_Ex_PhiOp_phi_comm
import Theorems.Thm_GlobalTheory_Ex_PhiOp_phi_triv
import Theorems.Thm_GlobalTheory_Ex_PhiOp_fe_of_phi_triv
import Theorems.Thm_GlobalTheory_Ex_PhiOp_wp_qTriv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
theorem _root_.solution {k : ℕ} (p : N.QT k) (w : Oˣ) (s : N.X → N.A → O) (hs : N.FE k s) : N.FE k (N.phi p w s) :=
  fe_of_phi_triv N _ fun z => by
    rw [phi_comm, wp_qTriv, phi_triv N _ s z hs rfl rfl, Units.val_one, one_smul]
end GlobalTheory.Ex.PhiOp
