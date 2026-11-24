-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SgnProd.eta_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:00:09.657909+00:00
-- url     : https://prove2.me/submissions/3192f5de-091d-4f05-aa77-23d138ca4bd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatProdEqEtaResultantMul
import Theorems.Thm_GlobalTheory_UnitLemma_SgnProd_val_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.SgnProd
namespace GlobalTheory.UnitLemma.SgnProd
theorem _root_.solution (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    K.eta (x * y) = K.eta x * K.eta y := by
  unfold UQ.eta
  rw [val_mul K hx hy, zpow_add₀ (by norm_num)]
end GlobalTheory.UnitLemma.SgnProd
