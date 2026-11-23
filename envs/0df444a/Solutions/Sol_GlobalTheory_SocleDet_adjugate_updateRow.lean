-- Prove2me | solution 1 for GlobalTheory.SocleDet.adjugate_updateRow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:59.835032+00:00
-- url     : https://prove2.me/submissions/2b46f588-6856-4a83-9ef2-3ffa8955fcc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SocleDet
open Matrix
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.SocleDet
theorem _root_.solution (M : Matrix n n R) (i l : n) (v : n → R) :
    (M.updateRow i v).adjugate l i = M.adjugate l i := by
  rw [adjugate_apply, adjugate_apply, updateRow_idem]
end GlobalTheory.SocleDet
