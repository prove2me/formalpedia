-- Prove2me | solution 1 for GlobalTheory.FunObj.DiagLattice.exists_symR_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:08:42.83317+00:00
-- url     : https://prove2.me/submissions/469295d3-ed7d-41d3-ad73-8ab45b1e7a09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Theorems.Thm_GlobalTheory_FunObj_DiagLattice_exists_KO_of_det
import Theorems.Thm_GlobalTheory_FunObj_DiagLattice_exists_unip
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.DiagLattice
namespace GlobalTheory.FunObj.DiagLattice
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (d : Fin c → kˣ) (H : GL (n ⊕ Fin c) k),
  (∀ i : Fin c, ∃ v : n ⊕ Fin c → k, v (Sum.inr i) = 1 ∧ (∀ l : Fin c, i < l → v (Sum.inr l) = 0) ∧ (i.val < (c + 1) / 2 → ∀ r, v (Sum.inl r) = 0) ∧ ∀ t, ((H⁻¹).val *ᵥ ((d i : k) • v)) t ∈ 𝒪[k]) →
  (∀ (i : Fin c) (y : n ⊕ Fin c → k), (∀ t, y t ∈ 𝒪[k]) → (∀ l : Fin c, i < l → (H.val *ᵥ y) (Sum.inr l) = 0) → (i.val < c / 2 → ∀ r, (H.val *ᵥ y) (Sum.inl r) = 0) → valuation k ((H.val *ᵥ y) (Sum.inr i)) ≤ valuation k (d i : k)) →
  ∃ r ∈ symR k n c, ∃ w ∈ KO k (n ⊕ Fin c), H = r * diagGL (Sum.elim (fun _ => 1) d) * w := by
  intro k _ _ _ _ n _ _ c d H hA hB
  choose v v1 v2 v3 v4 using hA
  obtain ⟨u, hu, uc, uX⟩ := exists_unip ((c + 1) / 2) v v1 v2 v3
  let lv : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * (c / 2)) (fun i => 2 * i.val + 1)
  obtain ⟨b, hb, w, hw, hbw⟩ := iwasawa_blockTriangular k (n ⊕ Fin c) lv (u⁻¹ * H)
  have hbi : (b⁻¹).val.BlockTriangular lv := by
    rw [Matrix.coe_units_inv]
    haveI := b.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hH : H = u * b * w := by rw [mul_assoc, ← hbw]; simp
  obtain ⟨w1, w2⟩ := (mem_KO_iff w).1 hw
  have hdiag : ∀ i, (b⁻¹).val (Sum.inr i) (Sum.inr i) * b.val (Sum.inr i) (Sum.inr i) = 1 := by
    intro i
    have h := congrFun (congrFun b.inv_mul (Sum.inr i)) (Sum.inr i)
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)] at h
    · simpa using h
    · intro t _ ht
      rcases lt_trichotomy (lv t) (lv (Sum.inr i)) with e | e | e
      · rw [hbi e, zero_mul]
      · exfalso
        rcases t with t | t
        · simp only [lv, Sum.elim_inl, Sum.elim_inr] at e; omega
        · simp only [lv, Sum.elim_inr] at e; exact ht (congrArg _ (Fin.ext (by omega)))
      · rw [hb e, mul_zero]
    · simp
  have hbl : ∀ i l : Fin c, i < l → b.val (Sum.inr l) (Sum.inr i) = 0 := fun i l h =>
    hb (by simp only [lv, Sum.elim_inr]; rw [Fin.lt_def] at h; omega)
  have h3 : ∀ i, valuation k (b.val (Sum.inr i) (Sum.inr i)) ≤ valuation k (d i : k) := by
    intro i
    have key : ∀ t, (H.val *ᵥ fun s => (w⁻¹).val s (Sum.inr i)) t =
        ∑ s, u.val t (Sum.inl s) * b.val (Sum.inl s) (Sum.inr i) + ∑ l, v l t * b.val (Sum.inr l) (Sum.inr i) := by
      intro t
      have : (H * w⁻¹).val t (Sum.inr i) = (u * b).val t (Sum.inr i) := by rw [hH]; simp
      rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type
        (fun j => u.val t j * b.val j (Sum.inr i))] at this
      simp only [uc] at this
      exact this
    have h := hB i (fun s => (w⁻¹).val s (Sum.inr i)) (fun t => w2 _ _) ?_ ?_
    · rw [key, Finset.sum_eq_single i] at h
      · simpa [uX, v1] using h
      · intro l _ hl
        rcases lt_or_gt_of_ne hl with e | e
        · rw [v2 l i e, zero_mul]
        · rw [hbl i l e, mul_zero]
      · simp
    · intro l hl
      rw [key, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
      · intro m _
        rcases lt_or_ge m l with e | e
        · rw [v2 m l e, zero_mul]
        · rw [hbl i m (hl.trans_le e), mul_zero]
      · intro s _; simp [uX]
    · intro hi r
      rw [key, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
      · intro m _
        rcases lt_or_ge i m with e | e
        · rw [hbl i m e, mul_zero]
        · rw [v3 m (by rw [Fin.le_def] at e; omega), zero_mul]
      · intro s _
        rw [hb (show lv (Sum.inr i) < lv (Sum.inl s) by simp only [lv, Sum.elim_inr, Sum.elim_inl]; omega), mul_zero]
  have h4 : ∀ t i, (b⁻¹).val t (Sum.inr i) * (d i : k) ∈ 𝒪[k] := by
    intro t i
    have e : b⁻¹ = w * H⁻¹ * u := by rw [hH]; group
    have : (b⁻¹).val t (Sum.inr i) * (d i : k) = (w.val *ᵥ ((H⁻¹).val *ᵥ ((d i : k) • v i))) t := by
      rw [Matrix.mulVec_mulVec, e, Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_mul]
      simp only [Matrix.mulVec, dotProduct, uc, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact sum_mem fun j _ => mul_mem (w1 _ _) (v4 i j)
  let A : Matrix (Fin c) (Fin c) k := Matrix.of fun l i => (b⁻¹).val (Sum.inr l) (Sum.inr i) * d i
  let β : Matrix n (Fin c) k := Matrix.of fun r i => (b⁻¹).val (Sum.inl r) (Sum.inr i) * d i
  have hAtri : A.BlockTriangular id := fun l i h => by
    simp only [A, of_apply]
    rw [hbi (by simp only [lv, Sum.elim_inr]; rw [id, id, Fin.lt_def] at h; omega), zero_mul]
  obtain ⟨κ, hκ, hκv⟩ := exists_KO_of_det (fromBlocks 1 β 0 A) (by
    rintro (r | r) (s | s)
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp
    · exact h4 _ _
    · exact zero_mem _
    · exact h4 _ _) (by
    rw [det_fromBlocks_zero₂₁, det_one, one_mul, det_of_upperTriangular hAtri, map_prod]
    refine Finset.prod_eq_one fun i _ => le_antisymm (h4 (Sum.inr i) i) ?_
    simp only [A, of_apply, map_mul]
    calc (1 : ValueGroupWithZero k) = valuation k ((b⁻¹).val (Sum.inr i) (Sum.inr i)) *
          valuation k (b.val (Sum.inr i) (Sum.inr i)) := by rw [← map_mul, hdiag, map_one]
      _ ≤ _ := mul_le_mul_right (h3 i) _)
  have hB : (b * κ).val = fromBlocks b.val.toBlocks₁₁ 0 b.val.toBlocks₂₁ (diagonal fun i => (d i : k)) := by
    have col : ∀ t i, (b * κ).val t (Sum.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) t (Sum.inr i) * d i := by
      intro t i
      rw [← b.mul_inv, Units.val_mul, hκv, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      rintro (j | j) _ <;> simp [A, β, mul_assoc]
    ext (r | r) (s | s)
    · simp [hκv, Matrix.mul_apply, Matrix.one_apply, toBlocks₁₁]
    · rw [col]; simp
    · simp [hκv, Matrix.mul_apply, Matrix.one_apply, toBlocks₂₁]
    · rw [col]
      by_cases h : r = s
      · subst h; simp
      · simp [h]
  have hg : b.val.toBlocks₁₁.det ≠ 0 := by
    have := Matrix.GeneralLinearGroup.det_ne_zero (b * κ)
    rw [hB, det_fromBlocks_zero₁₂] at this
    exact left_ne_zero_of_mul this
  let g : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hg
  have hlow : lowU b.val.toBlocks₂₁ ∈ N k n c (c / 2 + 1) := by
    rw [Model.mem_N_iff]
    rintro (r | r) (s | s) h
    · simp [lowU, Matrix.one_apply]
    · simp [lowU]
    · simp only [lev, Sum.elim_inl, Sum.elim_inr] at h
      simp only [lowU, fromBlocks_apply₂₁, toBlocks₂₁, of_apply]
      rw [hb (show lv (Sum.inl s) < lv (Sum.inr r) by simp only [lv, Sum.elim_inr, Sum.elim_inl]; omega)]
      simp
    · simp [lowU, Matrix.one_apply]
  have hfac : b * κ = embX c g * lowU b.val.toBlocks₂₁ * diagGL (Sum.elim (fun _ => 1) d) := by
    refine Units.ext ?_
    have hD : (diagGL (Sum.elim (fun _ : n => (1 : kˣ)) d)).val = fromBlocks 1 0 0 (diagonal fun i => (d i : k)) := by
      rw [diagGL_val, ← diagonal_one, fromBlocks_diagonal]
      congr 1
      funext x; rcases x with x | x <;> simp
    rw [hB, Units.val_mul, Units.val_mul, hD]
    show _ = fromBlocks b.val.toBlocks₁₁ 0 0 1 * fromBlocks 1 0 b.val.toBlocks₂₁ 1 * _
    simp [fromBlocks_multiply]
  refine ⟨u * (embX c g * lowU b.val.toBlocks₂₁), ?_, κ⁻¹ * w, mul_mem (inv_mem hκ) hw, ?_⟩
  · exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_left hu))
      (mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right (Subgroup.mem_sup_right hlow)))
  · rw [mul_assoc u, ← hfac, hH]; group
end GlobalTheory.FunObj.DiagLattice
