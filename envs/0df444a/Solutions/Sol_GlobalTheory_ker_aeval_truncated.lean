-- Prove2me | solution 1 for GlobalTheory.ker_aeval_truncated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:14.378019+00:00
-- url     : https://prove2.me/submissions/3b947de1-49aa-4e96-8e6e-8c820f91545c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalTruncatedPolynomialPresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (n : ℕ), 0 < n → ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (d : ℕ) (x : Fin d → A) (b : Fin d → B), (∀ i, x i ^ n = algebraMap B A (b i)) → LinearIndependent B (fun a : Fin d → Fin n => ∏ i, x i ^ (a i : ℕ)) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) = Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) := by
  intro n hn B A _ _ _ d x b hx hli
  set J : Ideal (MvPolynomial (Fin d) B) := Ideal.span (Set.range fun i : Fin d =>
    (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) with hJ
  have hJker : J ≤ RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) := by
    rw [hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker, hx]
  refine le_antisymm ?_ hJker
  let q : MvPolynomial (Fin d) B →ₐ[B] (MvPolynomial (Fin d) B ⧸ J) := Ideal.Quotient.mkₐ B J
  have hq : ∀ F G, q F = q G ↔ F - G ∈ J := fun F G => by
    simp only [q, Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq
  let y : Fin d → (MvPolynomial (Fin d) B ⧸ J) := fun i => q (MvPolynomial.X i)
  let v : (Fin d → Fin n) → (MvPolynomial (Fin d) B ⧸ J) := fun a => ∏ i, y i ^ (a i : ℕ)
  have hqv : ∀ a, q (∏ i, MvPolynomial.X i ^ (a i : ℕ)) = v a := fun a => by
    simp [v, y, map_prod, map_pow]
  have hyn : ∀ i, y i ^ n = algebraMap B _ (b i) := by
    intro i
    have h1 : q (MvPolynomial.X i ^ n) = q (MvPolynomial.C (b i)) :=
      (hq _ _).mpr (Ideal.subset_span ⟨i, rfl⟩)
    simp only [y]
    rw [← map_pow, h1, ← MvPolynomial.algebraMap_eq, q.commutes]
  have hsplit : ∀ (a : Fin d → Fin n) (i : Fin d) (k : Fin n),
      v (Function.update a i k) = y i ^ (k : ℕ) * ∏ j ∈ Finset.univ.erase i, y j ^ (a j : ℕ) := by
    intro a i k
    simp only [v]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
  have hsplit0 : ∀ (a : Fin d → Fin n) (i : Fin d),
      v a = y i ^ (a i : ℕ) * ∏ j ∈ Finset.univ.erase i, y j ^ (a j : ℕ) := by
    intro a i
    have := hsplit a i (a i)
    rwa [Function.update_eq_self] at this
  let S := Submodule.span B (Set.range v)
  have hgen : ∀ (a : Fin d → Fin n) (i : Fin d), v a * y i ∈ S := by
    intro a i
    by_cases h : (a i : ℕ) + 1 < n
    · have : v a * y i = v (Function.update a i ⟨a i + 1, h⟩) := by
        rw [hsplit, hsplit0 a i, pow_succ]; ring
      rw [this]; exact Submodule.subset_span ⟨_, rfl⟩
    · have h' : (a i : ℕ) + 1 = n := by have := (a i).isLt; omega
      have : v a * y i = b i • v (Function.update a i ⟨0, hn⟩) := by
        have hp : y i ^ n = y i ^ ((a i : ℕ) + 1) := by rw [h']
        rw [hsplit, hsplit0 a i, Algebra.smul_def, ← hyn, hp, pow_succ]; simp; ring
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hmulX : ∀ i, ∀ s ∈ S, s * y i ∈ S := by
    intro i s hs
    induction hs using Submodule.span_induction with
    | mem s hs => obtain ⟨a, rfl⟩ := hs; exact hgen a i
    | zero => simp
    | add s t _ _ hs ht => rw [add_mul]; exact add_mem hs ht
    | smul c s _ hs => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hs
  have hall : ∀ F, q F ∈ S := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C c =>
      have : q (MvPolynomial.C c) = c • v (fun _ => ⟨0, hn⟩) := by
        rw [← MvPolynomial.algebraMap_eq, q.commutes, Algebra.algebraMap_eq_smul_one]
        simp [v]
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | add p r hp hr => rw [map_add]; exact add_mem hp hr
    | mul_X p i hp => rw [map_mul]; exact hmulX i _ hp
  intro F hF
  rw [RingHom.mem_ker] at hF
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp (hall F)
  set G : MvPolynomial (Fin d) B := ∑ a, c a • ∏ i, MvPolynomial.X i ^ (a i : ℕ) with hG
  have hqG : q G = q F := by
    rw [← hc, hG, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hqv]
  have hFG : F - G ∈ J := (hq F G).mp hqG.symm
  have hevG : MvPolynomial.aeval x G = 0 := by
    have h0 := hJker hFG
    rw [RingHom.mem_ker, map_sub, hF] at h0
    simpa using h0
  have hsum : ∑ a, c a • ∏ i, x i ^ (a i : ℕ) = 0 := by
    rw [← hevG, hG, map_sum]
    exact Finset.sum_congr rfl fun a _ => by simp [map_prod, map_pow]
  have hc0 := Fintype.linearIndependent_iff.mp hli c hsum
  have hG0 : G = 0 := by rw [hG]; simp [hc0]
  simpa [hG0] using hFG
end GlobalTheory
