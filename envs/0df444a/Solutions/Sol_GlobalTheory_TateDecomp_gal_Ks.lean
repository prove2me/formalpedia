-- Prove2me | solution 1 for GlobalTheory.TateDecomp.gal_Ks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:52:11.878535+00:00
-- url     : https://prove2.me/submissions/e14d7034-da2e-4b75-91b6-b309dbc2290d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_root_mem_Ks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.TateDecomp
theorem _root_.solution {K : FinExt l} {g : GQ l} (hg : g ∈ (K0 K).fixingSubgroup) (i : ℕ) {w : Om l}
    (hw : w ∈ Ks K i) : g w ∈ Ks K i := by
  have h : Ks K i ≤ (Ks K i).comap (g : Om l →ₐ[ℚ_[l]] Om l) := by
    refine sup_le (fun x hx => ?_) ?_
    · have : g x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x hx
      change g x ∈ Ks K i
      rw [this]
      exact (le_sup_left : _ ≤ Ks K i) hx
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      change g x ∈ Ks K i
      refine root_mem_Ks K ?_
      have hx' : x ^ (l ^ i) = 1 := hx
      rw [← map_pow, hx', map_one]
  exact h hw
end GlobalTheory.TateDecomp
