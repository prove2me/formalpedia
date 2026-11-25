-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_maxCompact_indefiniteUnitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:11.490802+00:00
-- url     : https://prove2.me/submissions/69229039-f4d1-4aa3-bc41-8d9b671bcdd1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Theorems.Thm_GroundTheory_Automorphic_mem_maxCompact
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
open NormedSpace
open scoped Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
theorem _root_.solution {p q : ℕ} {g : indefiniteUnitaryGroup p q} :
    g ∈ maxCompact (indefiniteUnitaryGroup p q) ↔
      ((g : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) ∈
          Matrix.unitaryGroup (Fin p ⊕ Fin q) ℂ ∧
        ((g : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂ = 0 ∧
        ((g : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ = 0 := by
  rw [mem_maxCompact]
  refine ⟨fun hu => ⟨hu, ?_⟩, fun h => h.1⟩
  set u := ((g : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
  have hG : uᴴ * indefJ p q * u = indefJ p q := g.2
  have h1 : u * uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hu
  have hcomm : indefJ p q * u = u * indefJ p q := by
    calc indefJ p q * u = (u * uᴴ) * indefJ p q * u := by rw [h1, Matrix.one_mul]
      _ = u * (uᴴ * indefJ p q * u) := by simp only [Matrix.mul_assoc]
      _ = u * indefJ p q := by rw [hG]
  have hent : ∀ i j, indefJ p q i i * u i j = u i j * indefJ p q j j := by
    intro i j
    have := congrFun (congrFun hcomm i) j
    simpa [indefJ, diagonal_mul, mul_diagonal] using this
  refine ⟨?_, ?_⟩
  · ext i j
    have := hent (Sum.inl i) (Sum.inr j)
    simp only [indefJ, diagonal_apply_eq, Sum.elim_inl, Sum.elim_inr, one_mul, mul_neg,
      mul_one] at this
    simp only [toBlocks₁₂, of_apply, Matrix.zero_apply]
    linear_combination (1 / 2 : ℂ) * this
  · ext i j
    have := hent (Sum.inr i) (Sum.inl j)
    simp only [indefJ, diagonal_apply_eq, Sum.elim_inl, Sum.elim_inr, one_mul, neg_mul,
      mul_one] at this
    simp only [toBlocks₂₁, of_apply, Matrix.zero_apply]
    linear_combination (-1 / 2 : ℂ) * this
end GroundTheory.Automorphic
