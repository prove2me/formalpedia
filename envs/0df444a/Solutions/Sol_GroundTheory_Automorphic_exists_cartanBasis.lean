-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_cartanBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:11.163262+00:00
-- url     : https://prove2.me/submissions/e928f073-8e65-4c60-9d42-26b940b68c86

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Theorems.Thm_GroundTheory_Automorphic_traceForm_symm
import Theorems.Thm_GroundTheory_Automorphic_isCompl_skewPart_hermPart
import Theorems.Thm_GroundTheory_Automorphic_traceForm_neg_of_mem_skewPart
import Theorems.Thm_GroundTheory_Automorphic_traceForm_pos_of_mem_hermPart
import Theorems.Thm_GroundTheory_Automorphic_traceForm_eq_zero_of_skew_herm
import Theorems.Thm_GroundTheory_Automorphic_exists_signed_basis
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
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
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))
variable {L}
namespace GroundTheory.Automorphic
theorem _root_.solution (hstar : ∀ X ∈ L, Xᴴ ∈ L) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ L) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ i j, traceForm L (b i) (b j) = if i = j then ε i else 0) ∧
      ∀ i, ε i = -1 → ((b i : Matrix ι ι 𝕜))ᴴ = -(b i : Matrix ι ι 𝕜) := by
  classical
  have : FiniteDimensional ℝ L := Module.Finite.of_injective
    ((L.incl : L →ₗ⁅ℝ⁆ Matrix ι ι 𝕜) : L →ₗ[ℝ] Matrix ι ι 𝕜) Subtype.val_injective
  have hc := isCompl_skewPart_hermPart hstar
  obtain ⟨bk, hbk⟩ := exists_signed_basis ((traceForm L).restrict (skewPart L))
    (fun x y => traceForm_symm (x : L) y) (s := -1) (by norm_num) (fun v hv => by
      have h0 : (v : L) ≠ 0 := fun e => hv (Subtype.ext e)
      have := traceForm_neg_of_mem_skewPart v.2 h0
      change 0 < _ * traceForm L (v : L) (v : L)
      linarith)
  obtain ⟨bp, hbp⟩ := exists_signed_basis ((traceForm L).restrict (hermPart L))
    (fun x y => traceForm_symm (x : L) y) (s := 1) (by norm_num) (fun v hv => by
      have h0 : (v : L) ≠ 0 := fun e => hv (Subtype.ext e)
      have := traceForm_pos_of_mem_hermPart v.2 h0
      change 0 < _ * traceForm L (v : L) (v : L)
      linarith)
  set e := Submodule.prodEquivOfIsCompl (skewPart L) (hermPart L) hc
  set b0 := (bk.prod bp).map e
  set f : Fin (Module.finrank ℝ (skewPart L)) ⊕ Fin (Module.finrank ℝ (hermPart L)) → L :=
    Sum.elim (fun i => (bk i : L)) (fun j => (bp j : L))
  have hb0 : ∀ x, b0 x = f x := by
    rintro (i | j)
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
  set ε0 : Fin (Module.finrank ℝ (skewPart L)) ⊕ Fin (Module.finrank ℝ (hermPart L)) → ℝ :=
    Sum.elim (fun _ => -1) (fun _ => 1)
  have horth : ∀ x y, traceForm L (b0 x) (b0 y) = if x = y then ε0 x else 0 := by
    intro x y
    rw [hb0, hb0]
    rcases x with i | i <;> rcases y with j | j
    · have := hbk i j
      change traceForm L _ _ = _ at this
      simp only [f, ε0, Sum.elim_inl, Sum.inl.injEq]
      exact this
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact traceForm_eq_zero_of_skew_herm (bk i).2 (bp j).2
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      rw [traceForm_symm]
      exact traceForm_eq_zero_of_skew_herm (bk j).2 (bp i).2
    · have := hbp i j
      change traceForm L _ _ = _ at this
      simp only [f, ε0, Sum.elim_inr, Sum.inr.injEq]
      exact this
  set σ := finSumFinEquiv (m := Module.finrank ℝ (skewPart L)) (n := Module.finrank ℝ (hermPart L))
  refine ⟨_, b0.reindex σ, ε0 ∘ σ.symm, fun i => ?_, fun i j => ?_, fun i hi => ?_⟩
  · rcases hx : σ.symm i with k | k <;> simp [ε0, hx]
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, horth]
    simp only [Function.comp_apply, σ.symm.injective.eq_iff]
  · rw [Module.Basis.reindex_apply, hb0]
    simp only [Function.comp_apply] at hi
    rcases hx : σ.symm i with k | k
    · rw [hx] at hi
      simp only [f, Sum.elim_inl]
      exact (bk k).2
    · rw [hx] at hi
      simp [ε0] at hi
      norm_num at hi
end GroundTheory.Automorphic
