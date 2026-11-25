-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.distribution_sigma_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:46.950946+00:00
-- url     : https://prove2.me/submissions/e015e697-bcfc-4f6c-91f8-29f35a8cd867

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_biAction_smul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_chi_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_sigma_mem_rel
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_rel_le
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_GoodPiece_smul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
attribute [local instance] totallyDisconnectedSpace_localField
attribute [local instance] continuousSMul_biAction
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1)
    (D : Module.Dual ℂ (locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ))
    (hD : ∀ (f : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) (u₁ u₂ : GL (Fin n) F)
      (_ : u₁ ∈ Iwasawa.unipotent F n) (_ : u₂ ∈ Iwasawa.unipotent F n),
      D ⟨fun x => (f : GL (Fin n) F → ℂ) (u₁⁻¹ * x * u₂), twoSided_mem f.2 u₁ u₂⟩ =
        psiN ψ₀ u₁ * (psiN ψ₀ u₂)⁻¹ * D f)
    (f : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    D ⟨fun x => (f : GL (Fin n) F → ℂ) (sigma x), comp_sigma_mem f.2⟩ = D f := by
  have hrel : ∀ r (hr : r ∈ rel n ψ₀), D ⟨r, rel_le ψ₀ hr⟩ = 0 := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, g, hg, rfl⟩ := hx
      have e : (⟨transl k g - chi ψ₀ k • g, rel_le ψ₀ (Submodule.subset_span ⟨k, g, hg, rfl⟩)⟩ :
          locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) =
          ⟨fun x => g ((k.1 : GL (Fin n) F)⁻¹ * x * (k.2 : GL (Fin n) F)),
            twoSided_mem hg.1 _ _⟩ - chi ψ₀ k • ⟨g, hg.1⟩ := by
        refine Subtype.ext ?_
        funext x
        simp [biAction_smul]
      rw [e, map_sub, map_smul, hD ⟨g, hg.1⟩ _ _ k.1.2 k.2.2, chi_apply, smul_eq_mul, sub_self]
    | zero =>
      have : (⟨0, rel_le ψ₀ (zero_mem _)⟩ : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = 0 :=
        rfl
      rw [this, map_zero]
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, rel_le ψ₀ (add_mem hx hy)⟩ :
          locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) =
          ⟨x, rel_le ψ₀ hx⟩ + ⟨y, rel_le ψ₀ hy⟩ := rfl
      rw [this, map_add, ihx, ihy, add_zero]
    | smul c x hx ihx =>
      have : (⟨c • x, rel_le ψ₀ (Submodule.smul_mem _ c hx)⟩ :
          locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = c • ⟨x, rel_le ψ₀ hx⟩ := rfl
      rw [this, map_smul, ihx, smul_zero]
  have h := hrel _ (sub_sigma_mem_rel ψ₀ hψ hψ₁ f.2)
  have e : (⟨(f : GL (Fin n) F → ℂ) - sigmaL f, rel_le ψ₀ (sub_sigma_mem_rel ψ₀ hψ hψ₁ f.2)⟩ :
      locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) =
      f - ⟨fun x => (f : GL (Fin n) F → ℂ) (sigma x), comp_sigma_mem f.2⟩ := rfl
  rw [e, map_sub, sub_eq_zero] at h
  exact h.symm
end GroundTheory.Automorphic.Whittaker
