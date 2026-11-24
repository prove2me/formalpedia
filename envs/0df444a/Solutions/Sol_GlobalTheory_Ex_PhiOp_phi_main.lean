-- Prove2me | solution 1 for GlobalTheory.Ex.PhiOp.phi_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:05:10.168439+00:00
-- url     : https://prove2.me/submissions/24324bf8-a222-4562-b507-9ee5da2cb8ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FeOfPhiTriv
import Theorems.Thm_GlobalTheory_Ex_PhiOp_phi_phi
import Theorems.Thm_GlobalTheory_Ex_PhiOp_phi_comm
import Theorems.Thm_GlobalTheory_Ex_PhiOp_phi_triv
import Theorems.Thm_GlobalTheory_Ex_PhiOp_fe_phi

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
theorem _root_.solution : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (p p' : N.QT k) (w w' : Oˣ) (s : N.X → N.A → O), (N.FE k s → N.FE k (N.phi p w s)) ∧ N.phi p w (N.phi p' w' s) = N.phi (p * p') (w * w' * N.tk p p') s ∧ N.phi p w (N.phi p' w' s) = (N.wp p p' : O) • N.phi p' w' (N.phi p w s) ∧ ∀ z : N.X, N.FE k s → p.1.1.toAdd = k • z → p.1.2 = N.io z → N.phi p (N.ψ z ^ k) s = s :=
  fun _ _ N _ p p' w w' s =>
    ⟨fe_phi N p w s, phi_phi N p p' w w' s, phi_comm N p p' w w' s, fun z => phi_triv N p s z⟩
end GlobalTheory.Ex.PhiOp
