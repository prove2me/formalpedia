-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.isometric_of_prod_isometric_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:44.563519+00:00
-- url     : https://prove2.me/submissions/15360f12-783e-4122-82bd-3b5239565f82

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_isometric_prod_ofUnit
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isometric_of_prod_ofUnit
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_refl
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_apply_self_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isometric_prod_assoc
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isometric_prod_comm
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_self_mem_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution [Algebra.IsSeparable F E] [FiniteDimensional E V₂]
    [FiniteDimensional E V] (h₁ : HermitianForm F E V₁) (h₂ : HermitianForm F E V₂)
    (h : HermitianForm F E V) (H : Isometric (h₁.prod h) (h₂.prod h)) : Isometric h₁ h₂ := by
  suffices key : ∀ n : ℕ, ∀ (U : Type _) [AddCommGroup U] [Module E U] [FiniteDimensional E U],
      finrank E U = n → ∀ k : HermitianForm F E U, Isometric (h₁.prod k) (h₂.prod k) →
        Isometric h₁ h₂ from key _ V rfl h H
  intro n
  induction n with
  | zero =>
    intro U _ _ _ hU k Hk
    have : Subsingleton U := Module.finrank_zero_iff.1 hU
    letI : Unique U := uniqueOfSubsingleton 0
    have e1 : Isometric (h₁.prod k) h₁ := ⟨LinearEquiv.prodUnique, fun p q => by
      rw [prod_apply, Subsingleton.elim p.2 0, map_zero, LinearMap.zero_apply, add_zero]; rfl⟩
    have e2 : Isometric (h₂.prod k) h₂ := ⟨LinearEquiv.prodUnique, fun p q => by
      rw [prod_apply, Subsingleton.elim p.2 0, map_zero, LinearMap.zero_apply, add_zero]; rfl⟩
    exact (e1.symm.trans Hk).trans e2
  | succ n ih =>
    intro U _ _ _ hU k Hk
    have : Nontrivial U := Module.nontrivial_of_finrank_eq_succ hU
    obtain ⟨v, hv⟩ := k.exists_apply_self_ne_zero
    obtain ⟨c, hc⟩ := k.toSesq_self_mem_range v
    have hc0 : c ≠ 0 := by rintro rfl; rw [map_zero] at hc; exact hv hc.symm
    obtain ⟨W, k₀, hk, hW⟩ := k.exists_isometric_prod_ofUnit (a := Units.mk0 c hc0) hc.symm
    have hWn : finrank E W = n := by have := hW inferInstance; omega
    have step1 : Isometric (h₁.prod k) ((h₁.prod k₀).prod (ofUnit (E := E) (Units.mk0 c hc0))) :=
      ((Isometric.refl h₁).prod (hk.symm.trans (isometric_prod_comm _ _))).trans
        (isometric_prod_assoc _ _ _).symm
    have step2 : Isometric (h₂.prod k) ((h₂.prod k₀).prod (ofUnit (E := E) (Units.mk0 c hc0))) :=
      ((Isometric.refl h₂).prod (hk.symm.trans (isometric_prod_comm _ _))).trans
        (isometric_prod_assoc _ _ _).symm
    have H2 := isometric_of_prod_ofUnit _ _ _ ((step1.symm.trans Hk).trans step2)
    exact ih W hWn k₀ H2
end GroundTheory.Automorphic.HermitianForm
