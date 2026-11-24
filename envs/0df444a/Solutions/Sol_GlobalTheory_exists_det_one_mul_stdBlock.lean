-- Prove2me | solution 1 for GlobalTheory.exists_det_one_mul_stdBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:40:19.405604+00:00
-- url     : https://prove2.me/submissions/72da20e8-232d-4673-b568-69c018e8b98c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDetOneMulStdBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] {n r : ℕ} (hrn : r < n)
    (y : Matrix (Fin n) (Fin r) K) (hy : y.rank = r) :
    ∃ g : GL (Fin n) K, Matrix.GeneralLinearGroup.det g = 1 ∧
      g.val * (Matrix.of fun (a : Fin n) (b : Fin r) => if (a : ℕ) = (b : ℕ) then (1 : K) else 0) = y := by
  classical
  have hli : LinearIndependent K y.col := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    rw [Matrix.rank_eq_finrank_span_cols] at hy
    exact hy.symm
  let b := Module.Basis.sumExtend hli
  have hfin : Finite (Fin r ⊕ Module.Basis.sumExtendIndex hli) := Module.Finite.finite_basis b
  have : Finite (Module.Basis.sumExtendIndex hli) := Finite.of_injective (Sum.inr : _ → Fin r ⊕ _) Sum.inr_injective
  have : Fintype (Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
  have hcard : Fintype.card (Fin r ⊕ Module.Basis.sumExtendIndex hli) = n := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  have hb : ∀ i, b (Sum.inl i) = y.col i := by
    intro i
    simp only [b, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl
  have hS : Fintype.card (Module.Basis.sumExtendIndex hli) = n - r := by
    rw [Fintype.card_sum, Fintype.card_fin] at hcard; omega
  let e : Fin (n - r) ≃ Module.Basis.sumExtendIndex hli := (Fintype.equivFinOfCardEq hS).symm
  let τ : Fin n → Fin r ⊕ Module.Basis.sumExtendIndex hli := fun c =>
    if h : (c : ℕ) < r then Sum.inl ⟨c, h⟩ else Sum.inr (e ⟨c - r, by omega⟩)
  have hτ : Function.Injective τ := by
    intro c c' h
    simp only [τ] at h
    split_ifs at h
    all_goals first
      | (simp only [Sum.inl.injEq, Fin.mk.injEq] at h; ext; omega)
      | (simp only [Sum.inr.injEq, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq] at h; ext; omega)
      | exact absurd h Sum.inl_ne_inr
      | exact absurd h.symm Sum.inl_ne_inr
  let s : Fin n → Fin n → K := b ∘ τ
  have hs : LinearIndependent K s := b.linearIndependent.comp τ hτ
  let g₀ : Matrix (Fin n) (Fin n) K := Matrix.of fun i a => s a i
  have hg₀col : g₀.col = s := by ext a i; rfl
  have hu : IsUnit g₀ := Matrix.linearIndependent_cols_iff_isUnit.mp (hg₀col ▸ hs)
  have hdet : g₀.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  let last : Fin n := ⟨n - 1, by omega⟩
  let D : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun a => if a = last then g₀.det⁻¹ else 1
  let g := g₀ * D
  have hgdet : g.det = 1 := by
    simp only [g, D, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    exact mul_inv_cancel₀ hdet
  have hU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (by rw [hgdet]; exact isUnit_one)
  refine ⟨hU.unit, ?_, ?_⟩
  · ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, hgdet]
  · have hE : ∀ (a : Fin n) (c : Fin r), ((a : ℕ) = (c : ℕ)) ↔ a = Fin.castLE hrn.le c := by
      intro a c; rw [Fin.ext_iff, Fin.coe_castLE]
    have hτc : ∀ c : Fin r, τ (Fin.castLE hrn.le c) = Sum.inl c := by
      intro c
      simp only [τ, Fin.coe_castLE, dif_pos c.isLt]
    rw [IsUnit.unit_spec]
    ext i c
    simp only [g, D, Matrix.mul_assoc, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply, hE]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hne : Fin.castLE hrn.le c ≠ last := by
      intro h
      have h2 := congrArg Fin.val h
      simp only [Fin.coe_castLE, last] at h2
      omega
    simp only [if_neg hne, mul_one]
    show b (τ (Fin.castLE hrn.le c)) i = y i c
    rw [hτc, hb]
    rfl
end GlobalTheory
