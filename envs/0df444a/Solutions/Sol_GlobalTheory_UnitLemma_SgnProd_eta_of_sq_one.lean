-- Prove2me | solution 1 for GlobalTheory.UnitLemma.SgnProd.eta_of_sq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:00:10.524219+00:00
-- url     : https://prove2.me/submissions/92adb802-1f23-4769-b1e7-0d579cb2ce12

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
theorem _root_.solution (K : UQ) {ε : K.E} (h : ε * ε = 1) (a : K.E) : K.eta (ε * a) = K.eta a := by
  have hε : ε ≠ 0 := by rintro rfl; simp at h
  have hv : val K.O ε = 0 := by
    have h1 := val_mul K hε hε
    rw [h] at h1
    have h0 : val K.O (1 : K.E) = 0 := by simp [val]
    omega
  unfold UQ.eta
  by_cases ha : a = 0
  · simp [ha]
  rw [val_mul K hε ha, hv, zero_add]
end GlobalTheory.UnitLemma.SgnProd
