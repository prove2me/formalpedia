-- Prove2me | solution 1 for GlobalTheory.CycEigen.chiC_hinf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:01:40.961466+00:00
-- url     : https://prove2.me/submissions/b98f41c5-c1e8-4c98-af80-96e5076801b8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrame
import Theorems.Thm_GlobalTheory_CycEigen_hinf_le_gj
import Theorems.Thm_GlobalTheory_CycEigen_gj_le
import Theorems.Thm_GlobalTheory_Cyc_cyc_basic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycEigen
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.CycEigen
theorem _root_.solution {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (K : FinExt l) (j : ℤ) {h : GQ l}
    (hh : h ∈ Hinf K) : chiC χ j h = 1 := by
  have : χ h = 1 :=
    ((GlobalTheory.Cyc.cyc_basic l χ hχ).2.2 K h (gj_le K 0 (hinf_le_gj K 0 hh))).2.1 hh
  simp [chiC, this]
end GlobalTheory.CycEigen
