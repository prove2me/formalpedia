-- Prove2me | solution 1 for GlobalTheory.SqZeroPow.exists_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:10:53.830916+00:00
-- url     : https://prove2.me/submissions/b8143767-6d7c-4ba1-82a6-50ed75867b1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRingSqZeroNilpotentAugmented
import Theorems.Thm_GlobalTheory_SqZeroPow_dual_decomp
import Theorems.Thm_GlobalTheory_SqZeroPow_dual_fst_of_eps_mul
import Theorems.Thm_GlobalTheory_SqZeroPow_dual_inl_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SqZeroPow
namespace GlobalTheory.SqZeroPow
theorem _root_.solution (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (m : ℕ) (hm : 0 < m) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (j : A →ₐ[O] B) (π : B →ₐ[O] A) (x y : B),
      (∀ a, π (j a) = a) ∧ (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) ∧ π x = 0 ∧ π y = 0 ∧
      x * x = 0 ∧ y ^ m = 0 ∧ ∀ f, x * y ^ (m - 1) * f = 0 → π f = 0 := by
  classical
  have h0 : (X ^ m : A[X]).eval₂ (AlgHom.id O A : A →+* A) 0 = 0 := by
    simp [zero_pow (Nat.pos_iff_ne_zero.mp hm)]
  obtain ⟨g, hg⟩ : ∃ g : AdjoinRoot (X ^ m : A[X]) →ₐ[O] A,
      ∀ p : A[X], g (AdjoinRoot.mk _ p) = p.coeff 0 :=
    ⟨AdjoinRoot.liftAlgHom _ (AlgHom.id O A) 0 h0, fun p => by
      rw [AdjoinRoot.liftAlgHom_mk, Polynomial.eval₂_at_zero]
      rfl⟩
  have hroot : (AdjoinRoot.root (X ^ m : A[X])) ^ m = 0 := by
    have hself : AdjoinRoot.mk (X ^ m : A[X]) (X ^ m) = 0 := AdjoinRoot.mk_self
    rwa [map_pow, AdjoinRoot.mk_X] at hself
  refine ⟨DualNumber (AdjoinRoot (X ^ m : A[X])), inferInstance, inferInstance,
    (TrivSqZeroExt.inlAlgHom O _ _).comp (IsScalarTower.toAlgHom O A _),
    g.comp (TrivSqZeroExt.fstHom O _ _),
    DualNumber.eps, TrivSqZeroExt.inl (AdjoinRoot.root _), ?_, ?_, ?_, ?_,
    DualNumber.eps_mul_eps, dual_inl_pow _ _ hroot, ?_⟩
  · intro a
    simp only [AlgHom.comp_apply, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.fstHom_apply,
      TrivSqZeroExt.fst_inl, IsScalarTower.toAlgHom_apply]
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, hg, Polynomial.coeff_C_zero]
  · intro b hb
    simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply] at hb
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective b.fst
    rw [← hp, hg] at hb
    obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.mpr hb
    have hq : AdjoinRoot.root (X ^ m : A[X]) * AdjoinRoot.mk _ q = b.fst := by
      rw [← hp, map_mul, AdjoinRoot.mk_X]
    have e := dual_decomp b _ _ hq
    rw [← e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)) <;> simp
  · simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, DualNumber.fst_eps, map_zero]
  · simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.fst_inl]
    rw [← AdjoinRoot.mk_X, hg, Polynomial.coeff_X_zero]
  · intro f hf
    have h1 := dual_fst_of_eps_mul f _ (m - 1) hf
    simp only [AlgHom.comp_apply, TrivSqZeroExt.fstHom_apply]
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective f.fst
    have e : AdjoinRoot.root (X ^ m : A[X]) ^ (m - 1) * AdjoinRoot.mk _ p
        = AdjoinRoot.mk _ (X ^ (m - 1) * p) := by
      rw [map_mul, map_pow, AdjoinRoot.mk_X]
    rw [← hp, e, AdjoinRoot.mk_eq_zero, Polynomial.X_pow_dvd_iff] at h1
    have h2 := h1 (m - 1) (Nat.sub_lt hm Nat.one_pos)
    rw [Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self] at h2
    rw [← hp, hg]
    exact h2
end GlobalTheory.SqZeroPow
