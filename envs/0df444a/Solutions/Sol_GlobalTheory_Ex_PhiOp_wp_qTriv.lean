-- Prove2me | solution 1 for GlobalTheory.Ex.PhiOp.wp_qTriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:08:02.264637+00:00
-- url     : https://prove2.me/submissions/3d4eecfe-3d47-430e-9cc5-858bbbc69b0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FeOfPhiTriv
import Theorems.Thm_GlobalTheory_Ex_PhiOp_s_nsmul
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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.PhiOp
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.PhiOp
theorem _root_.solution {k : ℕ} (z : N.X) (p : N.QT k) : N.wp (N.qTriv k z) p = 1 := by
  have a := NumD.Gt.pow_s p.1.2 k z
  rw [N.mem_QT.1 p.2, NumD.io_s, N.τ_symm] at a
  have b := s_nsmul N p.1.2 k z
  rw [NumD.wp, div_eq_one]
  exact a.trans b.symm
end GlobalTheory.Ex.PhiOp
