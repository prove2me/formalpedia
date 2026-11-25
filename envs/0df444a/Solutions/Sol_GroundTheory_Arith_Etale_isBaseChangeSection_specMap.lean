-- Prove2me | solution 1 for GroundTheory.Arith.Etale.isBaseChangeSection_specMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:59:31.370724+00:00
-- url     : https://prove2.me/submissions/601db963-8e0e-49bd-b469-c6367efef61f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Theorems.Thm_GroundTheory_Arith_Etale_existsUnique_hom_app_top
import Theorems.Thm_GroundTheory_Arith_Etale_exists_modules_linearEquiv
import Theorems.Thm_P2M_GroundTheory_Arith_Etale_isIso_fromTilde__pullback_bd383a36a3f6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
namespace GroundTheory.Arith.Etale
theorem _root_.solution {A R : CommRingCat.{u}} (φ : A ⟶ R) (N : (Spec A).Modules)
    [IsIso N.fromTildeΓ] : IsBaseChangeSection (Spec.map φ) N := by
  intro Q _ _ ψ hψ
  set g := Spec.map φ with hg
  have := isIso_fromTildeΓ_pullback φ N
  obtain ⟨P, ⟨e⟩⟩ := exists_modules_linearEquiv R Q
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  let f : Γ(N, ⊤) →ₗ[Γ(Spec A, ⊤)] Γ((Scheme.Modules.pushforward g).obj P, ⊤) :=
    { toFun := fun n => e.symm (ψ n)
      map_add' := fun x y => by
        rw [map_add, map_add]
        rfl
      map_smul' := fun a x => by
        rw [hψ, map_smul]
        rfl }
  have hf : ∀ n, f n = e.symm (ψ n) := fun _ => rfl
  obtain ⟨θ, hθ, uθ⟩ := existsUnique_hom_app_top N _ f
  have key : ∀ (h : (Scheme.Modules.pullback g).obj N ⟶ P) (n : Γ(N, ⊤)),
      (adj.homEquiv _ _ h).app ⊤ n = h.app ⊤ (pullbackSection g N n) := fun h n => by
    rw [Adjunction.homEquiv_unit]
    rfl
  let θ' := (adj.homEquiv _ _).symm θ
  refine ⟨e.toLinearMap ∘ₗ sectionLinear θ', fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · have := key θ' n
    rw [Equiv.apply_symm_apply, hθ, hf] at this
    simp only [LinearMap.comp_apply, sectionLinear_apply, LinearEquiv.coe_coe]
    erw [← this]
    simp
  · obtain ⟨h, hh, -⟩ := existsUnique_hom_app_top _ P (e.symm.toLinearMap ∘ₗ ψ'')
    have : adj.homEquiv _ _ h = θ := uθ _ (fun n => by
      rw [key, hh, hf]
      simp [hψ''])
    have hθ' : h = θ' := by simp [θ', ← this]
    ext x
    simp [← hθ', hh]
end GroundTheory.Arith.Etale
