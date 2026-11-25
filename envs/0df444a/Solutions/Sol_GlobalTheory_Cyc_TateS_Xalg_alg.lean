-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.Xalg_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:12:53.916544+00:00
-- url     : https://prove2.me/submissions/172e2cac-39b6-4fb1-823e-ca0caec9a3ff

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_root_mem
import Theorems.Thm_GlobalTheory_Cyc_TateS_coe_mem_algC
import Theorems.Thm_GlobalTheory_Cyc_TateS_Xalg_le_of
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_mono


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
namespace GlobalTheory.Cyc.TateS
theorem _root_.solution (K : FinExt l) (j : ℕ) {x : PadicComplex l} (hx : x ∈ Xalg K j) : x ∈ algC K :=
  Xalg_le_of K j (algC K).toAddSubgroup (fun i _ _ _ hz hy _ =>
    coe_mem_algC K (mul_mem (root_mem K hz.pow_eq_one) (Ks_mono K (Nat.sub_le i 1) hy))) hx
end GlobalTheory.Cyc.TateS
