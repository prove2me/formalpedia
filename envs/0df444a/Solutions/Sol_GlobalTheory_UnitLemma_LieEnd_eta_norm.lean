-- Prove2me | solution 1 for GlobalTheory.UnitLemma.LieEnd.eta_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:03:09.218402+00:00
-- url     : https://prove2.me/submissions/ffde5cff-d946-4149-b65a-b7967c7472d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetEqOneOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GramDetEqNormMulGramDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaSelfAdjointLieOfCountLimitDescent
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_eta_mul
import Theorems.Thm_GlobalTheory_UnitLemma_LieEnd_eta_sq
import Theorems.Thm_GlobalTheory_T_gramDet_eq_norm_mul_gramDet_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.LieEnd
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ}
namespace GlobalTheory.UnitLemma.LieEnd
theorem _root_.solution (B : InvAlg K) (h : B.gramDet 1 ≠ 0) (x : B.A) (hx : IsUnit x) :
    K.eta (Algebra.norm K.E x) = K.eta (B.gramDet 1) * K.eta (B.gramDet x) := by
  have hn : Algebra.norm K.E x ≠ 0 := (hx.map (Algebra.norm K.E)).ne_zero
  rw [GlobalTheory.T.gramDet_eq_norm_mul_gramDet_one K B x, eta_mul K hn h, mul_left_comm, eta_sq, mul_one]
end GlobalTheory.UnitLemma.LieEnd
