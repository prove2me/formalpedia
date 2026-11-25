-- Prove2me | solution 1 for GlobalTheory.TateDecomp.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:03:23.710937+00:00
-- url     : https://prove2.me/submissions/5bce1af3-295b-4318-b2c8-7284e18e71a8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_mono
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
theorem _root_.solution (K : FinExt l) {x : Om l} (hx : x ∈ Kinf K) : ∃ i, x ∈ Ks K i := by
  have h : Kinf K ≤ ⨆ i, Ks K i := by
    refine sup_le (le_trans (le_sup_left : _ ≤ Ks K 0) (le_iSup (Ks K) 0)) ?_
    rw [IntermediateField.adjoin_le_iff]
    rintro y ⟨i, hy⟩
    exact le_iSup (Ks K) i (root_mem_Ks K hy)
  have h2 := h hx
  have hd : Directed (· ≤ ·) (Ks K) := Monotone.directed_le fun _ _ h => Ks_mono K h
  have h3 : x ∈ ((⨆ i, Ks K i : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := h2
  rw [IntermediateField.coe_iSup_of_directed hd] at h3
  simpa using h3
end GlobalTheory.TateDecomp
