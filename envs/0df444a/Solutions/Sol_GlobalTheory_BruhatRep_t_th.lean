-- Prove2me | solution 1 for GlobalTheory.BruhatRep.t_th
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:21:39.354881+00:00
-- url     : https://prove2.me/submissions/e3c828ff-ad3b-4bc3-852c-a6d855d69487

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_weyl_mul_self_eq_extendUnitsMapByOneAtZero_neg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
variable {K : Type} [Field K]
variable {M : Type} [Monoid M]
variable (n : K → M) (m : Kˣ → M) (t : M)
namespace GlobalTheory.BruhatRep
theorem _root_.solution (htt : t * t = m (-1)) (X : M) : X * t * t = X * mx m (-1) := by
  rw [mul_assoc, weyl_mul_self_eq_extendUnitsMapByOneAtZero_neg_one m t htt]
end GlobalTheory.BruhatRep
