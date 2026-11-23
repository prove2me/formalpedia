-- Prove2me | solution 1 for GlobalTheory.SimilarTranspose.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:16.801459+00:00
-- url     : https://prove2.me/submissions/478b5eaa-5dd4-4cac-9bca-d46e32413fe2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBilinCyclic
import Theorems.Thm_GlobalTheory_SimilarTranspose_exists_form
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
namespace GlobalTheory.SimilarTranspose
open Polynomial in
private theorem exists_nondegenerate_X_symmetric_form_quotient {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ G : (k[X] ⧸ (k[X] ∙ f)) →ₗ[k] (k[X] ⧸ (k[X] ∙ f)) →ₗ[k] k,
      (∀ x y, G ((X : k[X]) • x) y = G x ((X : k[X]) • y)) ∧ ∀ x, (∀ y, G x y = 0) → x = 0 := by
  obtain ⟨l, h1, h2⟩ := _root_.GlobalTheory.SimilarTranspose.exists_form f hf
  have hsurj := Submodule.Quotient.mk_surjective (k[X] ∙ f)
  let rep := Function.surjInv hsurj
  have hrep : ∀ x, Submodule.Quotient.mk (p := k[X] ∙ f) (rep x) = x := Function.surjInv_eq hsurj
  have hdiff : ∀ a a' : k[X], Submodule.Quotient.mk (p := k[X] ∙ f) a =
      Submodule.Quotient.mk (p := k[X] ∙ f) a' → f ∣ a - a' := by
    intro a a' h
    rw [Submodule.Quotient.eq, Submodule.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩
  let g : (k[X] ⧸ (k[X] ∙ f)) → (k[X] ⧸ (k[X] ∙ f)) → k := fun x y => l (rep x * rep y)
  have hg : ∀ a b, g (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = l (a * b) := by
    intro a b
    have ha := hdiff _ _ (hrep (Submodule.Quotient.mk a))
    have hb := hdiff _ _ (hrep (Submodule.Quotient.mk b))
    have : rep (Submodule.Quotient.mk a) * rep (Submodule.Quotient.mk b) - a * b =
        (rep (Submodule.Quotient.mk a) - a) * rep (Submodule.Quotient.mk b) +
          a * (rep (Submodule.Quotient.mk b) - b) := by ring
    have h0 := h1 _ (this ▸ dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hb _))
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  refine ⟨LinearMap.mk₂ k g ?_ ?_ ?_ ?_, ?_, ?_⟩
  · intro x y z
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    obtain ⟨c, rfl⟩ := hsurj z
    rw [← Submodule.Quotient.mk_add, hg, hg, hg, add_mul, map_add]
  · intro c x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    rw [← Submodule.Quotient.mk_smul, hg, hg, smul_mul_assoc, map_smul]
  · intro x y z
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    obtain ⟨c, rfl⟩ := hsurj z
    rw [← Submodule.Quotient.mk_add, hg, hg, hg, mul_add, map_add]
  · intro c x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    rw [← Submodule.Quotient.mk_smul, hg, hg, mul_smul_comm, map_smul]
  · intro x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    simp only [LinearMap.mk₂_apply]
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hg, hg, smul_eq_mul,
      smul_eq_mul, mul_assoc, mul_left_comm]
  · intro x hx
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨c, hc⟩ := h2 a fun b => by
      have := hx (Submodule.Quotient.mk b)
      rw [LinearMap.mk₂_apply, hg] at this
      exact this
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    exact ⟨c, by rw [hc, smul_eq_mul, mul_comm]⟩
open Polynomial in
private theorem exists_nondegenerate_X_symmetric_form_torsion {k : Type} [Field k] {M : Type} [AddCommGroup M]
    [Module k[X] M] [Module k M] [IsScalarTower k k[X] M] [Module.Finite k[X] M]
    (hM : Module.IsTorsion k[X] M) :
    ∃ B : M →ₗ[k] M →ₗ[k] k, (∀ m n, B ((X : k[X]) • m) n = B m ((X : k[X]) • n)) ∧
      ∀ m, (∀ n, B m n = 0) → m = 0 := by
  classical
  obtain ⟨ι, _, p, hp, e, ⟨φ⟩⟩ := Module.equiv_directSum_of_isTorsion hM
  have hne : ∀ i, p i ^ e i ≠ 0 := fun i => pow_ne_zero _ (hp i).ne_zero
  choose G hGX hGn using fun i => exists_nondegenerate_X_symmetric_form_quotient (p i ^ e i) (hne i)
  let ψ : M →ₗ[k] (DirectSum ι fun i => k[X] ⧸ k[X] ∙ p i ^ e i) :=
    φ.toLinearMap.restrictScalars k
  have hψ : ∀ m, ψ m = φ m := fun m => rfl
  have happ : ∀ m n, (∑ i, (G i).compl₁₂ ((DirectSum.component k ι _ i).comp ψ)
      ((DirectSum.component k ι _ i).comp ψ)) m n = ∑ i, G i (φ m i) (φ n i) := by
    intro m n
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.comp_apply, hψ]
    rfl
  refine ⟨∑ i, (G i).compl₁₂ ((DirectSum.component k ι _ i).comp ψ)
      ((DirectSum.component k ι _ i).comp ψ), ?_, ?_⟩
  · intro m n
    rw [happ, happ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, DirectSum.smul_apply, DirectSum.smul_apply, hGX]
  · intro m hm
    apply φ.injective
    rw [map_zero]
    refine DFinsupp.ext fun i => ?_
    apply hGn i
    intro y
    have h := hm (φ.symm (DirectSum.of _ i y))
    rw [happ, LinearEquiv.apply_symm_apply, Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hji
      rw [DirectSum.of_eq_of_ne _ _ _ hji, map_zero]
    · simp
end GlobalTheory.SimilarTranspose
end

set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SimilarTranspose
open Polynomial
namespace GlobalTheory.SimilarTranspose
namespace _root_.GlobalTheory.SimilarTranspose
theorem _root_.solution : ∀ (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι k),
    ∃ P : Matrix ι ι k, IsUnit P ∧ P * A = A.transpose * P := by
  intro k ι _ _ _ A
  have hT := Module.AEval.isTorsion_of_finiteDimensional k (ι → k) (Matrix.toLin' A)
  obtain ⟨B, hBX, hBn⟩ := exists_nondegenerate_X_symmetric_form_torsion (M := Module.AEval' (Matrix.toLin' A)) hT
  let o := Module.AEval'.of (Matrix.toLin' A)
  let Q : (ι → k) →ₗ[k] (ι → k) →ₗ[k] k := B.compl₁₂ o.toLinearMap o.toLinearMap
  have hQ : Q.compl₁₂ (Matrix.toLin' A) LinearMap.id = Q.compl₁₂ LinearMap.id (Matrix.toLin' A) := by
    refine LinearMap.ext₂ fun v w => ?_
    simp only [Q, LinearMap.compl₁₂_apply, LinearMap.id_apply, LinearEquiv.coe_coe, o]
    rw [← Module.AEval'.X_smul_of, ← Module.AEval'.X_smul_of, hBX]
  have hQP : ∀ v w, Q v w = Matrix.vecMul v (LinearMap.toMatrix₂' k Q) ⬝ᵥ w := by
    intro v w
    rw [← Matrix.dotProduct_mulVec, ← Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_toMatrix']
  refine ⟨LinearMap.toMatrix₂' k Q, ?_, ?_⟩
  · rw [← Matrix.vecMul_injective_iff_isUnit]
    intro v w hvw
    have h0 : ∀ u, Q (v - w) u = 0 := by
      intro u
      rw [hQP, Matrix.sub_vecMul]
      simp only at hvw
      rw [hvw, sub_self, zero_dotProduct]
    have := hBn (o (v - w)) fun n => by
      have := h0 (o.symm n)
      simpa [Q] using this
    rw [map_eq_zero_iff _ o.injective, sub_eq_zero] at this
    exact this
  · have := congrArg (LinearMap.toMatrix₂' k) hQ
    rw [LinearMap.toMatrix₂'_compl₁₂, LinearMap.toMatrix₂'_compl₁₂] at this
    simpa [LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] using this.symm
end _root_.GlobalTheory.SimilarTranspose
end GlobalTheory.SimilarTranspose
