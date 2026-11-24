-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.exists_asAlgebraHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:55.137457+00:00
-- url     : https://prove2.me/submissions/7b9e67b3-8ef5-4b51-80b5-ad1ae41f76ae

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_OuterTensor

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
open GroundTheory.Automorphic.RestrictedTensor
open Module Set TensorProduct
open scoped TensorProduct
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ρ₂ : Representation ℂ M₂ V₂} (hirr : ρ₂.IsIrreducible)
    (hschur : ∀ T : End ℂ V₂, (∀ m, T * ρ₂ m = ρ₂ m * T) → ∃ c : ℂ, T = c • 1)
    (A : End ℂ V₂) (s : Finset V₂) :
    ∃ r : MonoidAlgebra ℂ M₂, ∀ v ∈ s, ρ₂.asAlgebraHom r v = A v := by
  classical
  set R := MonoidAlgebra ℂ M₂
  have hsimple : IsSimpleModule R ρ₂.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ₂).1 hirr
  set E := ρ₂.asModuleEquiv

  have hsc : ∀ φ : Module.End R ρ₂.asModule, ∃ c : ℂ, ∀ x, E (φ x) = c • E x := by
    intro φ
    let T : End ℂ V₂ :=
      { toFun := fun v => E (φ (E.symm v))
        map_add' := fun a b => by simp
        map_smul' := fun c v => by
          rw [RingHom.id_apply, Representation.asModuleEquiv_symm_map_smul, map_smul,
            Representation.asModuleEquiv_map_smul, AlgHom.commutes,
            Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply] }
    obtain ⟨c, hc⟩ := hschur T fun m => by
      ext v
      simp only [Module.End.mul_apply, T, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Representation.asModuleEquiv_symm_map_rho, map_smul,
        Representation.asModuleEquiv_map_smul, MonoidAlgebra.of_apply,
        Representation.asAlgebraHom_single_one]
    refine ⟨c, fun x => ?_⟩
    have := congrArg (fun F : End ℂ V₂ => F (E x)) hc
    simpa [T] using this
  let f : Module.End (Module.End R ρ₂.asModule) ρ₂.asModule :=
    { toFun := fun x => E.symm (A (E x))
      map_add' := fun a b => by simp
      map_smul' := fun φ x => by
        obtain ⟨c, hc⟩ := hsc φ
        show E.symm (A (E (φ x))) = φ (E.symm (A (E x)))
        apply E.injective
        rw [hc, hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f (s.image E.symm)
  refine ⟨r, fun v hv => ?_⟩
  have := hr (E.symm v) (Finset.mem_image_of_mem _ hv)
  have h2 := congrArg E this
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply] at h2
  rw [h2, Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]
end GroundTheory.Automorphic.RestrictedTensor
