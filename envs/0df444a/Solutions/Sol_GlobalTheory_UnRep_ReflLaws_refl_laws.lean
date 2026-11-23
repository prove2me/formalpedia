-- Prove2me | solution 1 for GlobalTheory.UnRep.ReflLaws.refl_laws
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:59.483893+00:00
-- url     : https://prove2.me/submissions/ae71313e-2334-45fa-b4dc-2e14fcdda2b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLaws
import Theorems.Thm_GlobalTheory_UnRep_ReflLaws_hermE_eq_dot
import Theorems.Thm_GlobalTheory_UnRep_ReflLaws_refl_mulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
namespace GlobalTheory.UnRep.ReflLaws
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E)
open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E) in
private theorem hermE_add_smul_left' (v x y : Fin n → E) (t : E) :
    _root_.GlobalTheory.UnRep.hermE c G (v + t • x) y =
      _root_.GlobalTheory.UnRep.hermE c G v y + t * _root_.GlobalTheory.UnRep.hermE c G x y := by
  simp only [_root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E) in
private theorem hermE_conj_eq_swap_of_involutive_of_conj_symm (hinv : ∀ z : E, c (c z) = z) (hG : ∀ a b, c (G a b) = G b a)
    (a b : Fin n → E) :
    c (_root_.GlobalTheory.UnRep.hermE c G a b) = _root_.GlobalTheory.UnRep.hermE c G b a := by
  unfold _root_.GlobalTheory.UnRep.hermE
  simp only [map_sum, map_mul, hinv, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E) in
private theorem hermE_add_smul_right' (v x y : Fin n → E) (t : E) :
    _root_.GlobalTheory.UnRep.hermE c G v (y + t • x) =
      _root_.GlobalTheory.UnRep.hermE c G v y + c t * _root_.GlobalTheory.UnRep.hermE c G v x := by
  have hfun : (fun b => c ((y + t • x) b)) = (fun b => c (y b)) + c t • fun b => c (x b) := by
    funext b
    simp [map_add, map_mul]
  simp only [_root_.GlobalTheory.UnRep.ReflLaws.hermE_eq_dot, hfun, Matrix.mulVec_add,
    Matrix.mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]
end GlobalTheory.UnRep.ReflLaws
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.ReflLaws
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E)
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ}
  (G : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.UnRep.ReflLaws
namespace _root_.GlobalTheory.UnRep.ReflLaws
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E),
    _root_.GlobalTheory.UnRep.IsHermForm c G → ∀ x : Fin n → E,
    _root_.GlobalTheory.UnRep.hermE c G x x ≠ 0 →
    (∀ u v, _root_.GlobalTheory.UnRep.refl c G x u *ᵥ v =
      v + ((u - 1) * _root_.GlobalTheory.UnRep.hermE c G v x /
        _root_.GlobalTheory.UnRep.hermE c G x x) • x) ∧
    _root_.GlobalTheory.UnRep.refl c G x 1 = 1 ∧
    (∀ u u', _root_.GlobalTheory.UnRep.refl c G x u * _root_.GlobalTheory.UnRep.refl c G x u' =
      _root_.GlobalTheory.UnRep.refl c G x (u * u')) ∧
    ∀ u, u * c u = 1 → _root_.GlobalTheory.UnRep.IsUnE c G (_root_.GlobalTheory.UnRep.refl c G x u) := by
  intro F E _ _ _ _ _ c n G hG x hx
  obtain ⟨hinv, -, hsym, -⟩ := hG
  refine ⟨_root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec c G x, ?_, ?_, ?_⟩
  · unfold _root_.GlobalTheory.UnRep.refl
    simp
  · intro u u'
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, _root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec,
      hermE_add_smul_left']
    rw [add_assoc, ← add_smul]
    congr 2
    field_simp
    ring
  · intro u hu
    unfold _root_.GlobalTheory.UnRep.IsUnE
    intro v y
    have hxx : c (_root_.GlobalTheory.UnRep.hermE c G x x) = _root_.GlobalTheory.UnRep.hermE c G x x :=
      hermE_conj_eq_swap_of_involutive_of_conj_symm c G hinv hsym x x
    have hyx : c (_root_.GlobalTheory.UnRep.hermE c G y x) = _root_.GlobalTheory.UnRep.hermE c G x y :=
      hermE_conj_eq_swap_of_involutive_of_conj_symm c G hinv hsym y x
    simp only [_root_.GlobalTheory.UnRep.ReflLaws.refl_mulVec, hermE_add_smul_left', hermE_add_smul_right',
      map_div₀, map_mul, map_sub, map_one, hxx, hyx]
    field_simp
    linear_combination (_root_.GlobalTheory.UnRep.hermE c G v x * _root_.GlobalTheory.UnRep.hermE c G x y *
      1) * hu
end _root_.GlobalTheory.UnRep.ReflLaws
end GlobalTheory.UnRep.ReflLaws
