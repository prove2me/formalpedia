-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.mem_Xalg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:56:55.21624+00:00
-- url     : https://prove2.me/submissions/55fc223d-fcce-4307-8c4c-983cb7d32ef1

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
theorem _root_.solution (K : FinExt l) {j i : ℕ} (hi : j < i) {z y : Om l}
    (hz : IsPrimitiveRoot z (l ^ i)) (hy : y ∈ Ks K (i - 1)) (hy1 : ‖y‖ ≤ 1) :
    algebraMap (Om l) (PadicComplex l) (z * y) ∈ Xalg K j := by
  have h : Xlev K i ≤ Xalg K j := le_iSup₂_of_le (f := fun (i : ℕ) (_ : j < i) => Xlev K i) i hi le_rfl
  refine h (AddSubgroup.subset_closure ⟨_, _, hz.map_of_injective (coe_inj (l := l)),
    ⟨mem_inC.2 ⟨y, hy, rfl⟩, by rwa [norm_coe]⟩, map_mul _ _ _⟩)
end GlobalTheory.Cyc.TateS
