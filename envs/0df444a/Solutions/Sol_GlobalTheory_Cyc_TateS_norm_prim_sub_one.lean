-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.norm_prim_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:26:02.645087+00:00
-- url     : https://prove2.me/submissions/61298bec-fb8e-40d9-8ef4-d40ba49572e0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_coe_inj
import Theorems.Thm_GlobalTheory_Cyc_TateS_norm_coe
import Theorems.Thm_GlobalTheory_Cyc_norm_primitiveRoot_sub_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.TateS
variable {l : ℕ} [Fact l.Prime]
variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
namespace GlobalTheory.Cyc.TateS
theorem _root_.solution {η : Om l} (h : IsPrimitiveRoot η l) :
    ‖η - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (1 - 1) * ((l : ℝ) - 1))) := by
  have h1 := GlobalTheory.Cyc.norm_primitiveRoot_sub_one l 1 le_rfl (algebraMap (Om l) (PadicComplex l) η)
    (by rw [pow_one]; exact h.map_of_injective (coe_inj (l := l)))
  rw [← h1, ← norm_coe, map_sub, map_one]
end GlobalTheory.Cyc.TateS
