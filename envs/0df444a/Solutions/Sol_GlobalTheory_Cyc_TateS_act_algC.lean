-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.act_algC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:44:20.359962+00:00
-- url     : https://prove2.me/submissions/e5a9eed5-ff10-43e5-8bf2-65b89189f47a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_Ks_stable
import Theorems.Thm_GlobalTheory_Cyc_TateS_coe_mem_algC
import Theorems.Thm_GlobalTheory_Cyc_TateS_act_coe

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
theorem _root_.solution (hact : IsActC act) (K : FinExt l) {g : GQ l} (hg : g ∈ (K0 K).fixingSubgroup)
    {x : PadicComplex l} (hx : x ∈ algC K) : act g x ∈ algC K := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨a, ha, rfl⟩ := mem_inC.1 hm
  rw [act_coe hact]
  exact coe_mem_algC K (Ks_stable K m hg ha)
end GlobalTheory.Cyc.TateS
