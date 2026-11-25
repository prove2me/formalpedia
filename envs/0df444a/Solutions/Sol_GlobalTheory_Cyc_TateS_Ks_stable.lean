-- Prove2me | solution 1 for GlobalTheory.Cyc.TateS.Ks_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:54.508963+00:00
-- url     : https://prove2.me/submissions/9ca5b90a-0051-4b22-a53a-a089754729d3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Theorems.Thm_GlobalTheory_Cyc_TateS_root_mem

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
theorem _root_.solution (K : FinExt l) (m : ℕ) {g : GQ l} (hg : g ∈ (K0 K).fixingSubgroup) {x : Om l}
    (hx : x ∈ Ks K m) : g x ∈ Ks K m := by
  have : Ks K m ≤ (Ks K m).comap (g : Om l →ₐ[ℚ_[l]] Om l) := by
    refine sup_le ?_ ?_
    · intro y hy
      have h1 : g y = y := hg ⟨y, hy⟩
      change g y ∈ Ks K m
      rw [h1]
      exact (le_sup_left : _ ≤ Ks K m) hy
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      change g y ∈ Ks K m
      apply root_mem
      have hy' : y ^ (l ^ m) = 1 := hy
      rw [← map_pow, hy', map_one]
  exact this hx
end GlobalTheory.Cyc.TateS
