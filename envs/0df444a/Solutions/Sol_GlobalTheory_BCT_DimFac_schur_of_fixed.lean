-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.schur_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:01:38.136604+00:00
-- url     : https://prove2.me/submissions/e9a7d8ac-7d0b-4e3b-a54a-ef914e18c35d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GlobalTheory_BCT_DimFac_mem_fix
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GroundTheory.Automorphic.RestrictedTensor Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.DimFac
variable {Γ V W M : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.BCT.DimFac
theorem _root_.solution {σ : Representation ℂ Γ W} (hσ : σ.IsIrreducible) (U : Subgroup Γ) (h0 : fixed σ U ≠ ⊥)
    [FiniteDimensional ℂ (fixed σ U)] (T : End ℂ W) (hT : ∀ g, T * σ g = σ g * T) : ∃ c : ℂ, T = c • 1 := by
  have hT' : ∀ g x, T (σ g x) = σ g (T x) := fun g x => LinearMap.congr_fun (hT g) x
  have hm : ∀ x ∈ fixed σ U, T x ∈ fixed σ U := fun x hx => mem_fix.2 fun g hg => by
    rw [← hT', mem_fix.1 hx g hg]
  haveI : Nontrivial (fixed σ U) := Submodule.nontrivial_iff_ne_bot.2 h0
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hm)
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  have hx1 : T x.1 = c • x.1 := congrArg Subtype.val hx.apply_eq_smul
  refine ⟨c, ?_⟩
  rcases ((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ).2 (LinearMap.ker (T - c • 1)) (fun g v hv => by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hv ⊢
    rw [hT', hv, map_smul]) with h | h
  · have : x.1 ∈ LinearMap.ker (T - c • 1) := by simp [hx1]
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hx.2
  · exact sub_eq_zero.1 (LinearMap.ker_eq_top.1 h)
end GlobalTheory.BCT.DimFac
