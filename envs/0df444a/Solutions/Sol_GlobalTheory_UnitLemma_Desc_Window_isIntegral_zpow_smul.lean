-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.isIntegral_zpow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:06.4691+00:00
-- url     : https://prove2.me/submissions/be5d7f25-aa08-4fef-a702-d4cc0b2c1fd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_zpow_smul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology Classical
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.Window
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc.Window
theorem _root_.solution (a : K.O) {n : ℤ} (hn : 0 ≤ n) {y : B.A} (hy : IsIntegral K.O y) :
    IsIntegral K.O (al K a ^ n • y) := by
  rw [zpow_smul_eq B a n hn]
  exact isIntegral_algebraMap.mul hy
end GlobalTheory.UnitLemma.Desc.Window
