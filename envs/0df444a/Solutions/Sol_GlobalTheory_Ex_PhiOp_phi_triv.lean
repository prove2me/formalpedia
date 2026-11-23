-- Prove2me | solution 1 for GlobalTheory.Ex.PhiOp.phi_triv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:42:53.929062+00:00
-- url     : https://prove2.me/submissions/d7fd648b-b2be-435d-840a-363be13ed948

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
theorem _root_.solution {k : ℕ} (p : N.QT k) (s : N.X → N.A → O) (z : N.X) (hs : N.FE k s) (h₁ : p.1.1.toAdd = k • z)
    (h₂ : p.1.2 = N.io z) : N.phi p (N.ψ z ^ k) s = s := by
  funext α x
  have := hs z (α - k • z) x
  rw [sub_add_cancel] at this
  rw [this]
  simp only [NumD.phi, h₁, h₂, NumD.io_b, NumD.io_s]
  rw [mul_right_comm]
end GlobalTheory.Ex.PhiOp
