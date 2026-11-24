-- Prove2me | solution 1 for GlobalTheory.exists_integral_pivot_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:55:31.516343+00:00
-- url     : https://prove2.me/submissions/e0692a20-b93b-47e6-990f-fbe0be781259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIntegralPivotDecomposition
import Theorems.Thm_GlobalTheory_exists_pivot_entry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
open Matrix
private theorem exists_pivot_unipotent_mul_triangular {L : Type} [Field L] (W : ValuationSubring L) {n : ℕ} :
    ∀ (r : ℕ) (g : Matrix (Fin n) (Fin r) L), LinearIndependent L g.transpose →
      ∃ (ι : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) L) (b : Matrix (Fin r) (Fin r) L),
        (∀ i j, u i j ∈ W) ∧ (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧
        (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, b i i ≠ 0) ∧ g = u * b := by
  intro r
  induction r with
  | zero =>
    intro g _
    refine ⟨⟨Fin.elim0, fun a => Fin.elim0 a⟩, 0, 0, fun _ j => Fin.elim0 j, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    ext _ j
    exact Fin.elim0 j
  | succ r ih =>
    intro g hg
    let cols' : Fin r → Fin n → L := fun i a => g a i.castSucc
    let g' : Matrix (Fin n) (Fin r) L := Matrix.of fun a i => cols' i a
    let x : Fin n → L := fun a => g a (Fin.last r)
    have hsplit : (Fin.snoc cols' x : Fin (r + 1) → Fin n → L) = fun i a => g a i := by
      funext i a
      cases i using Fin.lastCases with
      | last => simp [x]
      | cast i => simp [cols']
    have hg2 : LinearIndependent L (Fin.snoc cols' x : Fin (r + 1) → Fin n → L) := by
      rw [hsplit]
      exact hg
    rw [linearIndependent_finSnoc] at hg2
    obtain ⟨hg'ind, hxspan⟩ := hg2
    obtain ⟨ι', u', b', hu'W, hu'zero, hu'one, hb'tri, hb'diag, hgub⟩ := ih g' hg'ind
    have hb'det : IsUnit b'.det := by
      rw [Matrix.det_of_isUpperTriangular hb'tri]
      exact (Finset.prod_ne_zero_iff.2 fun i _ => hb'diag i).isUnit
    let M : Matrix (Fin r) (Fin r) L := Matrix.of fun l i => u' (ι' l) i
    have hMtri : M.BlockTriangular OrderDual.toDual := by
      intro l i hli
      simpa [M] using hu'zero l i (OrderDual.toDual_lt_toDual.1 hli)
    have hMdet : IsUnit M.det := by
      rw [Matrix.det_of_isLowerTriangular M hMtri]
      simp [M, hu'one]
    let c : Fin r → L := M⁻¹ *ᵥ (fun l => x (ι' l))
    let v : Fin n → L := x - u' *ᵥ c
    have hvpiv : ∀ l, v (ι' l) = 0 := by
      intro l
      have h1 : (u' *ᵥ c) (ι' l) = (M *ᵥ c) l := rfl
      have h2 : M *ᵥ c = fun l => x (ι' l) := by
        simp only [c]
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hMdet, Matrix.one_mulVec]
      show x (ι' l) - (u' *ᵥ c) (ι' l) = 0
      rw [h1, h2, sub_self]
    have hv0 : v ≠ 0 := by
      intro h0
      apply hxspan
      have hxv : x - u' *ᵥ c = 0 := h0
      have hu' : u' = g' * b'⁻¹ := by
        rw [hgub]
        exact (Matrix.mul_nonsing_inv_cancel_right (B := u') (h := hb'det)).symm
      have hxe : x = g' *ᵥ (b'⁻¹ *ᵥ c) := by
        rw [Matrix.mulVec_mulVec, ← hu']
        exact sub_eq_zero.1 hxv
      have hmem := LinearMap.mem_range_self g'.mulVecLin (b'⁻¹ *ᵥ c)
      rw [Matrix.range_mulVecLin] at hmem
      rw [hxe]
      exact hmem
    obtain ⟨k, hvk, hkW⟩ := exists_pivot_entry W v hv0
    have hk : ∀ l, ι' l ≠ k := fun l hl => hvk (hl ▸ hvpiv l)
    let ιf : Fin (r + 1) → Fin n := Fin.lastCases (motive := fun _ => Fin n) k (fun i => ι' i)
    have hιf : Function.Injective ιf := by
      intro i j hij
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => rfl
        | cast j =>
          simp only [ιf, Fin.lastCases_last, Fin.lastCases_castSucc] at hij
          exact absurd hij.symm (hk j)
      | cast i =>
        cases j using Fin.lastCases with
        | last =>
          simp only [ιf, Fin.lastCases_last, Fin.lastCases_castSucc] at hij
          exact absurd hij (hk i)
        | cast j =>
          simp only [ιf, Fin.lastCases_castSucc] at hij
          rw [ι'.injective hij]
    let u : Matrix (Fin n) (Fin (r + 1)) L :=
      Matrix.of fun a => Fin.snoc (α := fun _ => L) (u' a) (v a / v k)
    let b : Matrix (Fin (r + 1)) (Fin (r + 1)) L := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => L)
        (Fin.lastCases (motive := fun _ => L) (v k) (fun i' => c i') i)
        (fun j' => Fin.lastCases (motive := fun _ => L) 0 (fun i' => b' i' j') i) j
    refine ⟨⟨ιf, hιf⟩, u, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a j
      cases j using Fin.lastCases with
      | last => simpa [u] using hkW a
      | cast j => simpa [u] using hu'W a j
    · intro i j hij
      cases i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i =>
        cases j using Fin.lastCases with
        | last =>
          simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc,
            Fin.snoc_last]
          rw [hvpiv i, zero_div]
        | cast j =>
          simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc,
            Fin.snoc_castSucc]
          exact hu'zero i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · intro i
      cases i using Fin.lastCases with
      | last =>
        simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_last,
          Fin.snoc_last]
        exact div_self hvk
      | cast i =>
        simp only [u, ιf, Function.Embedding.coeFn_mk, Matrix.of_apply, Fin.lastCases_castSucc,
          Fin.snoc_castSucc]
        exact hu'one i
    · intro i j hji
      cases i using Fin.lastCases with
      | last =>
        cases j using Fin.lastCases with
        | last => exact absurd hji (lt_irrefl _)
        | cast j => simp [b]
      | cast i =>
        cases j using Fin.lastCases with
        | last => exact absurd hji (not_lt.2 (Fin.le_last _))
        | cast j =>
          simp only [b, Matrix.of_apply, Fin.lastCases_castSucc]
          exact hb'tri (Fin.castSucc_lt_castSucc_iff.1 hji)
    · intro i
      cases i using Fin.lastCases with
      | last => simpa [b] using hvk
      | cast i => simpa [b] using hb'diag i
    · ext a j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      cases j using Fin.lastCases with
      | last =>
        simp only [u, b, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last, Fin.lastCases_last,
          Fin.lastCases_castSucc]
        rw [div_mul_cancel₀ _ hvk]
        show x a = _ + (x a - (u' *ᵥ c) a)
        simp only [Matrix.mulVec, dotProduct]
        ring
      | cast j =>
        simp only [u, b, Matrix.of_apply, Fin.snoc_castSucc, Fin.lastCases_last,
          Fin.lastCases_castSucc, mul_zero, add_zero]
        have hentry := congrFun (congrFun hgub a) j
        simpa [g', cols', Matrix.mul_apply] using hentry
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution :
    ∀ (L : Type) [Field L] (W : ValuationSubring L) (n r : ℕ) (g : Matrix (Fin n) (Fin r) L),
      LinearIndependent L g.transpose →
      ∃ (ι : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) L) (b : Matrix (Fin r) (Fin r) L),
        (∀ i j, u i j ∈ W) ∧ (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧
        (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, b i i ≠ 0) ∧ g = u * b := by
  intro L _ W n r g hg
  exact exists_pivot_unipotent_mul_triangular W r g hg
end GlobalTheory
