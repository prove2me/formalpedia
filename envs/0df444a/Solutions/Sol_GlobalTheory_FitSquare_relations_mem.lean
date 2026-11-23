-- Prove2me | solution 1 for GlobalTheory.FitSquare.relations_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:31.728999+00:00
-- url     : https://prove2.me/submissions/8e9d72aa-376d-4941-bff8-62ccff67f869

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetMemSpanAdjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
namespace GlobalTheory.FitSquare
variable {R : Type} [CommRing R]
section blocks
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_updateRow_mem_span_adjugate_entries {α : Type} [Fintype α] [DecidableEq α]
    (Φ : Matrix α α R) (k : α) (w : α → R) :
    (Φ.updateRow k w).det ∈ Ideal.span (Set.range fun p : α × α => Φ.adjugate p.1 p.2) := by
  rw [← det_transpose, ← updateCol_transpose, ← cramer_apply, cramer_eq_adjugate_mulVec,
    ← adjugate_transpose]
  simp only [mulVec, dotProduct, transpose_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨(l, k), rfl⟩)
open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_mem_span_adjugate_entries {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (Φ : Matrix α α R) :
    Φ.det ∈ Ideal.span (Set.range fun p : α × α => Φ.adjugate p.1 p.2) := by
  obtain ⟨i⟩ := ‹Nonempty α›
  have h := det_updateRow_mem_span_adjugate_entries Φ i (Φ i)
  rwa [updateRow_eq_self] at h
open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_eq_mul_of_toBlocks₂₁_eq_zero {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix (α ⊕ β) (α ⊕ β) R) (h : M.toBlocks₂₁ = 0) :
    M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks M, h]
  exact det_fromBlocks_zero₂₁ _ _ _
open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_eq_mul_of_toBlocks₁₂_eq_zero {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix (α ⊕ β) (α ⊕ β) R) (h : M.toBlocks₁₂ = 0) :
    M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks M, h]
  exact det_fromBlocks_zero₁₂ _ _ _
end blocks
end GlobalTheory.FitSquare
end

set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.FitSquare
variable {R : Type} [CommRing R]
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
open Matrix
variable {R : Type} [CommRing R]
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
namespace GlobalTheory.FitSquare
namespace _root_.GlobalTheory.FitSquare
theorem _root_.solution {M : Type} [AddCommGroup M] [Module R M]
    (π : (n → R) →ₗ[R] M) (hπ : Function.Surjective π) (Φ : Matrix n n R)
    (hΦ : ∀ y, π y = 0 → ∃ z, Φ *ᵥ z = y)
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q) (T : Matrix m m R)
    (hT : ∀ y, q (T *ᵥ y) = 0) :
    T.det ∈ Ideal.span {Φ.det} ∧ (Nonempty n → ∀ i j, T.adjugate i j ∈
      Ideal.span (Set.range fun p : n × n => Φ.adjugate p.1 p.2)) := by
  choose a ha using fun j : m => hπ (q (Pi.single j 1))
  choose b hb using fun i : n => hq (π (Pi.single i 1))
  let A : Matrix n m R := Matrix.of fun i j => a j i
  let B : Matrix m n R := Matrix.of fun j i => b i j
  have hA : ∀ v, π (A *ᵥ v) = q v := by
    have h : π ∘ₗ A.mulVecLin = q := by
      ext j
      simp only [LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply, LinearMap.single_apply,
        mulVec_single_one]
      rw [← ha j]
      rfl
    intro v
    exact LinearMap.congr_fun h v
  let U : Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks 1 (-A) 0 1
  let D : Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks Φ 0 0 1
  let N : Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks 1 0 (-B) T
  have hker : ∀ u v, π u + q v = 0 → ∃ w, (U * D) *ᵥ w = Sum.elim u v := by
    intro u v h
    obtain ⟨z, hz⟩ := hΦ (u + A *ᵥ v) (by rw [map_add, hA, h])
    refine ⟨Sum.elim z v, ?_⟩
    rw [← mulVec_mulVec]
    simp [U, D, fromBlocks_mulVec, hz, neg_mulVec]
  have hcol : ∀ c, ∃ w, (U * D) *ᵥ w = fun r => N r c := by
    rintro (i | j)
    · obtain ⟨w, hw⟩ := hker (Pi.single i 1) (-b i) (by rw [map_neg, hb, add_neg_cancel])
      refine ⟨w, hw.trans ?_⟩
      ext (r | r) <;> simp [N, B, Pi.single_apply, one_apply]
    · obtain ⟨w, hw⟩ := hker 0 (fun r => T r j) (by
        have h := hT (Pi.single j 1)
        rw [mulVec_single_one] at h
        rw [map_zero, zero_add]
        exact h)
      refine ⟨w, hw.trans ?_⟩
      ext (r | r) <;> simp [N]
  choose w hw using hcol
  have hN : N = U * D * Matrix.of fun r c => w c r := by
    ext r c
    exact (congrFun (hw c) r).symm
  have hdetN : N.det = T.det := by simp [N, det_fromBlocks_zero₁₂]
  have hdetUD : (U * D).det = Φ.det := by simp [U, D, det_fromBlocks_zero₂₁, det_mul]
  refine ⟨?_, ?_⟩
  · rw [← hdetN, hN, det_mul, hdetUD]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · intro hn p p'
    have hdetJ := det_mem_span_adjugate_entries Φ
    have hD : ∀ x y, D.adjugate x y ∈
        Ideal.span (Set.range fun p : n × n => Φ.adjugate p.1 p.2) := by
      intro x y
      rw [adjugate_apply]
      rcases y with k | k
      · rw [det_eq_mul_of_toBlocks₂₁_eq_zero]
        · have h : (D.updateRow (Sum.inl k) (Pi.single x 1)).toBlocks₁₁ =
              Φ.updateRow k (fun l => (Pi.single x 1 : n ⊕ m → R) (Sum.inl l)) := by
            ext s t
            by_cases hs : s = k <;> simp [D, toBlocks₁₁, updateRow_apply, hs]
          rw [h]
          exact Ideal.mul_mem_right _ _ (det_updateRow_mem_span_adjugate_entries _ _ _)
        · ext s t
          simp [D, toBlocks₂₁, updateRow_apply]
      · rw [det_eq_mul_of_toBlocks₁₂_eq_zero]
        · have h : (D.updateRow (Sum.inr k) (Pi.single x 1)).toBlocks₁₁ = Φ := by
            ext s t
            simp [D, toBlocks₁₁, updateRow_apply]
          rw [h]
          exact Ideal.mul_mem_right _ _ hdetJ
        · ext s t
          simp [D, toBlocks₁₂, updateRow_apply]
    have hadj : T.adjugate p p' = N.adjugate (Sum.inr p) (Sum.inr p') := by
      rw [adjugate_apply, adjugate_apply, det_eq_mul_of_toBlocks₁₂_eq_zero]
      · have h₁ : (N.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₁₁ = 1 := by
          ext s t
          simp [N, toBlocks₁₁, updateRow_apply]
        have h₂ : (N.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₂₂ =
            T.updateRow p' (Pi.single p 1) := by
          ext s t
          by_cases hs : s = p' <;> simp [N, toBlocks₂₂, updateRow_apply, hs, Pi.single_apply]
        rw [h₁, h₂, det_one, one_mul]
      · ext s t
        simp [N, toBlocks₁₂, updateRow_apply]
    rw [hadj, hN, adjugate_mul_distrib, adjugate_mul_distrib, mul_apply]
    refine Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ ?_
    rw [mul_apply]
    exact Ideal.sum_mem _ fun y _ => Ideal.mul_mem_right _ _ (hD x y)
end _root_.GlobalTheory.FitSquare
end GlobalTheory.FitSquare
