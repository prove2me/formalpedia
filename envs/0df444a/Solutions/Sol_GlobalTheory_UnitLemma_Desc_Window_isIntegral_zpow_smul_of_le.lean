-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.Window.isIntegral_zpow_smul_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:38.576557+00:00
-- url     : https://prove2.me/submissions/9293d8db-1f14-44ea-a187-80f02ea56814

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlternatingDifferenceTermWindow
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_al_ne_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_Window_isIntegral_zpow_smul

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
theorem _root_.solution {a : K.O} (ha : K.Small a) {c n : ℤ} (hcn : c ≤ n) {y : B.A}
    (hy : IsIntegral K.O (al K a ^ c • y)) : IsIntegral K.O (al K a ^ n • y) := by
  have : al K a ^ n • y = al K a ^ (n - c) • (al K a ^ c • y) := by
    rw [smul_smul, ← zpow_add₀ (al_ne_zero ha)]; congr 2; ring
  rw [this]
  exact isIntegral_zpow_smul B a (by omega) hy
end GlobalTheory.UnitLemma.Desc.Window
