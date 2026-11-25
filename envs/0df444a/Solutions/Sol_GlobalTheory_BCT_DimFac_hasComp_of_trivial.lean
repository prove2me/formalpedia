-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.hasComp_of_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:27:33.672697+00:00
-- url     : https://prove2.me/submissions/78c45fa3-09d3-4983-8605-3ede8d144837

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
theorem _root_.solution {τ : Representation ℂ Γ M} (h : τ.IsIrreducible) {e : Γ →* Γ} (hτ : ∀ g, τ (e g) = 1)
    (L : Subgroup Γ) : HasComp τ e L 1 := by
  haveI := ((GlobalTheory.CuspRep.isIrreducible_iff τ).1 h).1
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  refine ⟨ℂ, inferInstance, inferInstance, 1, (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨inferInstance, fun N _ =>
    eq_bot_or_eq_top N⟩, fun T _ => ⟨T 1, LinearMap.ext_ring (by simp)⟩, fun _ => rfl,
    ⟨LinearMap.toSpanSingleton ℂ M m, fun h => hm (by simpa using LinearMap.congr_fun h 1), fun g x => by simp [hτ]⟩, ?_⟩
  have : fixed (1 : Representation ℂ Γ ℂ) L = ⊤ := Submodule.eq_top_iff'.2 fun x => mem_fix.2 fun _ _ => rfl
  rw [this, finrank_top, finrank_self]
end GlobalTheory.BCT.DimFac
