-- Prove2me | solution 1 for GlobalTheory.Ex.PhiOp.fe_of_phi_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:30:13.485597+00:00
-- url     : https://prove2.me/submissions/c798436f-0b98-4087-98c1-64c1b35c1301

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
theorem _root_.solution {k : ℕ} (s : N.X → N.A → O) (h : ∀ z, N.phi (N.qTriv k z) (N.ψ z ^ k) s = s) :
    N.FE k s := by
  intro μ α x
  have := congrFun (congrFun (h μ) (α + k • μ)) x
  rw [← this]
  simp only [NumD.phi, NumD.qTriv, toAdd_ofAdd, add_sub_cancel_right, NumD.io_b, NumD.io_s]
  rw [mul_right_comm]
end GlobalTheory.Ex.PhiOp
