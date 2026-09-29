-- Prove2me | solution 1 for Module.exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/713a1d08-52b9-5451-bfc5-2da9cd271f8d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural

set_option autoImplicit false

universe u

open TensorProduct

namespace FormalHomHelpers

variable {R : Type u} [CommRing R]

section one
variable {K : Type u} [AddCommGroup K] [Module R K] [Module.Finite R K] [Module.Free R K]

noncomputable def Φ (B : Type u) [AddCommGroup B] [Module R B] :
    B ⊗[R] K ≃ₗ[R] (Module.Dual R K →ₗ[R] B) :=
  (TensorProduct.comm R B K).trans
    ((TensorProduct.congr (Module.evalEquiv R K) (LinearEquiv.refl R B)).trans
      (dualTensorHomEquiv R (Module.Dual R K) B))

theorem Φ_tmul (B : Type u) [AddCommGroup B] [Module R B] (b : B) (x : K) (φ : Module.Dual R K) :
    Φ B (b ⊗ₜ[R] x) φ = φ x • b := by
  simp [Φ, dualTensorHomEquivOfBasis_apply, dualTensorHom_apply]

theorem Φ_apply_eq_rid_lTensor (B : Type u) [AddCommGroup B] [Module R B] (s : B ⊗[R] K) (φ : Module.Dual R K) :
    Φ B s φ = TensorProduct.rid R B (φ.lTensor B s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => rw [Φ_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  | add s t hs ht => rw [map_add, LinearMap.add_apply, hs, ht, map_add, map_add]

theorem Φ_naturality (B B' : Type u) [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (u : B →ₗ[R] B') (s : B ⊗[R] K) : Φ B' (u.rTensor K s) = u ∘ₗ Φ B s := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    apply LinearMap.ext; intro φ
    rw [LinearMap.rTensor_tmul, Φ_tmul, LinearMap.comp_apply, Φ_tmul, map_smul]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, LinearMap.comp_add]

end one

variable {K₀ K₁ : Type u} [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Free R K₀]
  [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Free R K₁]

theorem Φ_comp_dualMap (d : K₀ →ₗ[R] K₁) (B : Type u) [AddCommGroup B] [Module R B] (s : B ⊗[R] K₀) :
    (Φ B s) ∘ₗ d.dualMap = Φ B (d.lTensor B s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    apply LinearMap.ext; intro ψ
    rw [LinearMap.comp_apply, Φ_tmul, LinearMap.dualMap_apply, LinearMap.lTensor_tmul, Φ_tmul]
  | add s t hs ht => rw [map_add, LinearMap.add_comp, hs, ht, map_add, map_add]

theorem comp_dualMap_eq_zero_iff (d : K₀ →ₗ[R] K₁) (B : Type u) [AddCommGroup B] [Module R B] (s : B ⊗[R] K₀) :
    (Φ B s) ∘ₗ d.dualMap = 0 ↔ d.lTensor B s = 0 := by
  rw [Φ_comp_dualMap, LinearEquiv.map_eq_zero_iff]

end FormalHomHelpers

open FormalHomHelpers in
theorem solution
    (R : Type u) [CommRing R]
    (K₀ K₁ : Type u) [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Free R K₀]
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Free R K₁]
    (d : K₀ →ₗ[R] K₁) :
    ∃ e : ∀ (B : Type u) [AddCommGroup B] [Module R B],
        ((Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) →ₗ[R] B) ≃ₗ[R] LinearMap.ker (d.lTensor B),
      (∀ (B B' : Type u) [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B'] (u : B →ₗ[R] B')
          (g : (Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) →ₗ[R] B),
          ((e B' (u ∘ₗ g) : LinearMap.ker (d.lTensor B')) : B' ⊗[R] K₀) =
            u.rTensor K₀ ((e B g : LinearMap.ker (d.lTensor B)) : B ⊗[R] K₀)) ∧
      (∀ (B : Type u) [AddCommGroup B] [Module R B] (t : LinearMap.ker (d.lTensor B)) (φ : Module.Dual R K₀),
          (e B).symm t (Submodule.Quotient.mk φ) = TensorProduct.rid R B (φ.lTensor B (t : B ⊗[R] K₀))) := by
  have hker : ∀ (B : Type u) [AddCommGroup B] [Module R B]
      (g : (Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) →ₗ[R] B),
      d.lTensor B ((Φ B).symm (g ∘ₗ (LinearMap.range d.dualMap).mkQ)) = 0 := by
    intro B _ _ g
    rw [← comp_dualMap_eq_zero_iff, LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro ψ
    show g ((LinearMap.range d.dualMap).mkQ (d.dualMap ψ)) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range.mpr ⟨ψ, rfl⟩), map_zero]
  have hle : ∀ (B : Type u) [AddCommGroup B] [Module R B] (t : LinearMap.ker (d.lTensor B)),
      LinearMap.range d.dualMap ≤ LinearMap.ker (Φ B (t : B ⊗[R] K₀)) := by
    intro B _ _ t x hx
    obtain ⟨ψ, rfl⟩ := LinearMap.mem_range.mp hx
    have h := (comp_dualMap_eq_zero_iff d B (t : B ⊗[R] K₀)).mpr t.2
    exact congrArg (fun f : Module.Dual R K₁ →ₗ[R] B => f ψ) h
  let e : ∀ (B : Type u) [AddCommGroup B] [Module R B],
      ((Module.Dual R K₀ ⧸ LinearMap.range d.dualMap) →ₗ[R] B) ≃ₗ[R] LinearMap.ker (d.lTensor B) :=
    fun B _ _ =>
    { toFun := fun g => ⟨(Φ B).symm (g ∘ₗ (LinearMap.range d.dualMap).mkQ), hker B g⟩
      map_add' := fun g g' => Subtype.ext (by simp [LinearMap.add_comp])
      map_smul' := fun r g => Subtype.ext (by simp [LinearMap.smul_comp])
      invFun := fun t => (LinearMap.range d.dualMap).liftQ (Φ B (t : B ⊗[R] K₀)) (hle B t)
      left_inv := fun g => by
        apply LinearMap.ext
        intro q
        obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        simp [Submodule.liftQ_apply]
      right_inv := fun t => by
        apply Subtype.ext
        show (Φ B).symm ((LinearMap.range d.dualMap).liftQ (Φ B (t : B ⊗[R] K₀)) (hle B t) ∘ₗ
          (LinearMap.range d.dualMap).mkQ) = t
        rw [Submodule.liftQ_mkQ, LinearEquiv.symm_apply_apply] }
  refine ⟨e, ?_, ?_⟩
  · intro B B' _ _ _ _ u g
    show (Φ B').symm ((u ∘ₗ g) ∘ₗ (LinearMap.range d.dualMap).mkQ) =
      u.rTensor K₀ ((Φ B).symm (g ∘ₗ (LinearMap.range d.dualMap).mkQ))
    apply (Φ B').injective
    rw [LinearEquiv.apply_symm_apply, Φ_naturality, LinearEquiv.apply_symm_apply, LinearMap.comp_assoc]
  · intro B _ _ t φ
    show (LinearMap.range d.dualMap).liftQ (Φ B (t : B ⊗[R] K₀)) (hle B t) (Submodule.Quotient.mk φ) = _
    rw [Submodule.liftQ_apply]
    exact Φ_apply_eq_rid_lTensor B (t : B ⊗[R] K₀) φ

end S_Module_exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural
end P2MW
export P2MW.S_Module_exists_hom_dual_quotient_range_dualMap_linearEquiv_ker_lTensor_natural (solution)
