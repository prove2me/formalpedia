-- Prove2me | solution 1 for GlobalTheory.char_eq_one_of_inverse_det_one_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:10:16.061981+00:00
-- url     : https://prove2.me/submissions/d3a57c6e-9de2-45d4-9aab-64c4ef74fced

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetCharacterReductionInvariant
import Theorems.Thm_GlobalTheory_generalLinearGroup_char_eq_one_of_det_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory
open scoped TensorProduct
namespace GlobalTheory
theorem _root_.solution {R S V Q A : Type} [CommRing R] [CommRing S] [Finite S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V] [AddCommGroup Q] [Module R Q] [CommGroup A]
    {r : ℕ} (b : Module.Basis (Fin r) S V) (e : Q ≃ₗ[R] V) (ψ : (Q ≃ₗ[R] Q) →* A)
    (h4 : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → 4 ≤ Nat.card (S ⧸ 𝔪)) (f : V →ₗ[S] V) (hf : LinearMap.det f = 1)
    (k : Q ≃ₗ[R] Q) (hk : ∀ q, f (e (k q)) = e q) : ψ k = 1 := by
  classical
  let φ2 : Module.End S V →* Module.End R V :=
    { toFun := fun g => g.restrictScalars R, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let φ4 : (V ≃ₗ[R] V) →* (Q ≃ₗ[R] Q) :=
    { toFun := fun u => e.trans (u.trans e.symm)
      map_one' := by ext q; simp
      map_mul' := by intro u v; ext q; simp }
  let Φ : GL (Fin r) S →* (Q ≃ₗ[R] Q) :=
    φ4.comp ((LinearMap.GeneralLinearGroup.generalLinearEquiv R V).toMonoidHom.comp
      ((Units.map φ2).comp (Units.map ((Matrix.toLinAlgEquiv b :
        Matrix (Fin r) (Fin r) S ≃ₐ[S] Module.End S V) : Matrix (Fin r) (Fin r) S →* Module.End S V))))
  have hdet : IsUnit (LinearMap.toMatrix b b f).det := by
    rw [LinearMap.det_toMatrix, hf]; exact isUnit_one
  let g : GL (Fin r) S := Matrix.nonsingInvUnit _ hdet
  have hg : (g : Matrix (Fin r) (Fin r) S).det = 1 := by
    show (LinearMap.toMatrix b b f).det = 1
    rw [LinearMap.det_toMatrix, hf]
  have h1 : (ψ.comp Φ) g = 1 := generalLinearGroup_char_eq_one_of_det_eq_one S r A (ψ.comp Φ) h4 g hg
  have h2 : Φ g * k = 1 := by
    ext q
    show e.symm ((Matrix.toLinAlgEquiv b (LinearMap.toMatrix b b f)) (e (k q))) = q
    rw [show LinearMap.toMatrix b b f = LinearMap.toMatrixAlgEquiv b f from rfl,
      Matrix.toLinAlgEquiv_toMatrixAlgEquiv, hk, LinearEquiv.symm_apply_apply]
  have h3 := congrArg ψ h2
  rw [map_mul, map_one] at h3
  simp only [MonoidHom.comp_apply] at h1
  rw [h1, one_mul] at h3
  exact h3
end GlobalTheory
