-- Prove2me | solution 1 for GroundTheory.Automorphic.isCompl_skewPart_hermPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:41:54.676621+00:00
-- url     : https://prove2.me/submissions/0b15e0bc-a6a0-49b4-adbf-189cffc2cfeb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Theorems.Thm_GroundTheory_Automorphic_mem_skewPart
import Theorems.Thm_GroundTheory_Automorphic_mem_hermPart
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))
variable {L}
namespace GroundTheory.Automorphic
theorem _root_.solution (hstar : ∀ X ∈ L, Xᴴ ∈ L) :
    IsCompl (skewPart L) (hermPart L) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro X hk hp
    rw [mem_skewPart] at hk
    rw [mem_hermPart] at hp
    have h2 : (X : Matrix ι ι 𝕜) = -(X : Matrix ι ι 𝕜) := hp.symm.trans hk
    have h3 : (2 : ℝ) • (X : Matrix ι ι 𝕜) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h2]
      exact add_neg_cancel _
    exact Subtype.ext ((smul_eq_zero.1 h3).resolve_left two_ne_zero)
  · rw [codisjoint_iff, eq_top_iff]
    intro X _
    set Xs : L := ⟨(X : Matrix ι ι 𝕜)ᴴ, hstar _ X.2⟩
    refine Submodule.mem_sup.2 ⟨(1 / 2 : ℝ) • (X - Xs), ?_, (1 / 2 : ℝ) • (X + Xs), ?_, ?_⟩
    · rw [mem_skewPart]
      change ((1 / 2 : ℝ) • ((X : Matrix ι ι 𝕜) - (X : Matrix ι ι 𝕜)ᴴ))ᴴ =
        -((1 / 2 : ℝ) • ((X : Matrix ι ι 𝕜) - (X : Matrix ι ι 𝕜)ᴴ))
      rw [conjTranspose_smul, star_trivial, conjTranspose_sub, conjTranspose_conjTranspose,
        ← smul_neg, neg_sub]
    · rw [mem_hermPart]
      change ((1 / 2 : ℝ) • ((X : Matrix ι ι 𝕜) + (X : Matrix ι ι 𝕜)ᴴ))ᴴ =
        ((1 / 2 : ℝ) • ((X : Matrix ι ι 𝕜) + (X : Matrix ι ι 𝕜)ᴴ))
      rw [conjTranspose_smul, star_trivial, conjTranspose_add, conjTranspose_conjTranspose,
        add_comm]
    · apply Subtype.ext
      change (1 / 2 : ℝ) • ((X : Matrix ι ι 𝕜) - (X : Matrix ι ι 𝕜)ᴴ) +
        (1 / 2 : ℝ) • ((X : Matrix ι ι 𝕜) + (X : Matrix ι ι 𝕜)ᴴ) = X
      module
end GroundTheory.Automorphic
