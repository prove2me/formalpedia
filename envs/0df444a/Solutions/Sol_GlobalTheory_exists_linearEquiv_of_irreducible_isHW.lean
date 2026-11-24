-- Prove2me | solution 1 for GlobalTheory.exists_linearEquiv_of_irreducible_isHW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:20.119935+00:00
-- url     : https://prove2.me/submissions/c1f4950c-0be8-46fa-b06f-39373d3bf0f8

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsStableSubmoduleTopWeightLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLinearEquivOfIrreducibleIsHW
import Theorems.Thm_GlobalTheory_stable_submodule_proj_bijective
import Theorems.Thm_GlobalTheory_exists_stable_submodule_topWeight_line
import Theorems.Thm_GlobalTheory_glRel_apply_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁) (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ) (v₁ : V₁) (v₂ : V₂), GlRel E₁ → GlRel E₂ → (∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ S : Submodule ℂ V₂, (∀ a b, ∀ x ∈ S, E₂ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → IsHW E₁ ν v₁ → IsHW E₂ ν v₂ → v₁ ≠ 0 → v₂ ≠ 0 → ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by
  intro V₁ _ _ V₂ _ _ n E₁ E₂ ν v₁ v₂ hE₁ hE₂ h₁ h₂ hw₁ hw₂ hv₁ hv₂
  let E : Fin n → Fin n → Module.End ℂ (V₁ × V₂) := fun a b => (E₁ a b).prodMap (E₂ a b)
  have hEap : ∀ a b (x : V₁ × V₂), E a b x = (E₁ a b x.1, E₂ a b x.2) := fun _ _ _ => rfl
  have hE : GlRel E := by
    intro a b c d
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hEap]
    rw [glRel_apply_comm hE₁ a b c d, glRel_apply_comm hE₂ a b c d]
    split_ifs <;> simp [hEap]
    all_goals (constructor <;> abel)
  have hw : IsHW E ν (v₁, v₂) := by
    refine ⟨fun a => ?_, fun a b h => ?_⟩
    · rw [hEap, hw₁.1, hw₂.1]; rfl
    · rw [hEap, hw₁.2 a b h, hw₂.2 a b h]; rfl
  obtain ⟨S, hS, hvS, htop⟩ := exists_stable_submodule_topWeight_line _ n E ν _ hE hw
  have b₂ := stable_submodule_proj_bijective E E₁ E₂ ν (v₁, v₂) (LinearMap.fst ℂ V₁ V₂)
    (LinearMap.snd ℂ V₁ V₂) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x h h' => Prod.ext h h') h₁ h₂ hw₁.1 hv₁ hv₂ S hS hvS htop
  have b₁ := stable_submodule_proj_bijective E E₂ E₁ ν (v₁, v₂) (LinearMap.snd ℂ V₁ V₂)
    (LinearMap.fst ℂ V₁ V₂) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x h h' => Prod.ext h' h) h₂ h₁ hw₂.1 hv₂ hv₁ S hS hvS htop
  refine ⟨(LinearEquiv.ofBijective _ b₁).symm.trans (LinearEquiv.ofBijective _ b₂), ?_⟩
  intro a b x
  obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective _ b₁).surjective x
  have h : E₁ a b (LinearEquiv.ofBijective _ b₁ y)
      = LinearEquiv.ofBijective _ b₁ ⟨E a b y, hS a b y y.2⟩ := rfl
  rw [h]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl
end GlobalTheory
