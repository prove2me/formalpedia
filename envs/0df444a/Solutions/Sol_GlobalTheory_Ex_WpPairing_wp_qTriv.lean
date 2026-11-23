-- Prove2me | solution 1 for GlobalTheory.Ex.WpPairing.wp_qTriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:47.876266+00:00
-- url     : https://prove2.me/submissions/69f22e60-a776-4d62-aacd-0b51fcea7c4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties
import Theorems.Thm_GlobalTheory_Ex_WpPairing_s_nsmul
import Theorems.Thm_GlobalTheory_Ex_NumD_Gt_pow_s


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
theorem _root_.solution {k : ℕ} (z : N.X) (q : N.QT k) : N.wp (N.qTriv k z) q = 1 := by
  have hq := N.mem_QT.mp q.2
  have h1 := _root_.GlobalTheory.Ex.WpPairing.s_nsmul N
    (q : Multiplicative N.X × N.Gt).2 k z
  have h2 := _root_.GlobalTheory.Ex.NumD.Gt.pow_s
    (q : Multiplicative N.X × N.Gt).2 k z
  rw [hq, _root_.GlobalTheory.Ex.NumD.io_s, _root_.GlobalTheory.Ex.NumD.τ_symm] at h2
  simp only [_root_.GlobalTheory.Ex.NumD.wp, _root_.GlobalTheory.Ex.NumD.tk,
    _root_.GlobalTheory.Ex.NumD.qTriv, _root_.GlobalTheory.Ex.NumD.io_s,
    _root_.GlobalTheory.Ex.NumD.io_b, toAdd_ofAdd, div_eq_one]
  rw [h1, h2]
end _root_.GlobalTheory.Ex.WpPairing
end GlobalTheory.Ex.WpPairing
