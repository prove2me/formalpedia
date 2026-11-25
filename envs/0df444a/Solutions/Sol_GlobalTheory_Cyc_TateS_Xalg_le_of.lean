-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.Xalg_le_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:00:55.072477+00:00
-- url     : https://prove2.me/submissions/d59a44ac-4058-4889-a1ef-a5abd642c416

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_prim_lift
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
theorem _root_.solution (K : FinExt l) (j : ℕ) (B : AddSubgroup (PadicComplex l))
    (h : ∀ i, j < i → ∀ z y : Om l, IsPrimitiveRoot z (l ^ i) → y ∈ Ks K (i - 1) → ‖y‖ ≤ 1 →
      algebraMap (Om l) (PadicComplex l) (z * y) ∈ B) : Xalg K j ≤ B := by
  refine iSup₂_le fun i hi => (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨ζ, y, hζ, ⟨hy, hy1⟩, rfl⟩
  obtain ⟨z, rfl, hz⟩ := prim_lift (pow_ne_zero i (Fact.out : l.Prime).ne_zero) hζ
  obtain ⟨y, hy', rfl⟩ := mem_inC.1 hy
  rw [norm_coe] at hy1
  rw [← map_mul]
  exact h i hi z y hz hy' hy1
end GlobalTheory.Cyc.TateS
