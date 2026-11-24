-- Prove2me | solution 1 for GlobalTheory.SuperCusp.false_of_infinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:13:38.706313+00:00
-- url     : https://prove2.me/submissions/acf1467a-553d-49de-a8e2-0e49d821c5cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCuspidalOfIsSupercuspidal
import Theorems.Thm_GlobalTheory_SuperCusp_val_le_one_of_mem_cong
import Theorems.Thm_GlobalTheory_SuperCusp_val_mul_le_one
import Theorems.Thm_GlobalTheory_CentralExponent_isOpen_cong
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_P2M_GlobalTheory_CentralExponent_val_emb__scalar_9fecca134d59


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
noncomputable section
open GlobalTheory GlobalTheory.SuperCusp
namespace GlobalTheory.SuperCusp
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n a b : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : a ⊕ b ≃ n) (i : a) (j : b) {z : kˣ} (hz : valuation k (z : k) < 1)
    {C : Set (GL n k)} (hC : IsCompact C) {S : Set ℕ} (hS : S.Infinite)
    (h : ∀ r ∈ S, ∃ ζ ∈ Subgroup.center (GL n k), ∃ c ∈ C,
      emb₂ k e (GeneralLinearGroup.scalar a z, 1) ^ r = ζ * c) : False := by
  set K' := CentralExponent.cong n (1 : (ValueGroupWithZero k)ˣ) le_rfl with hK'
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hC (V := (K' : Set (GL n k)))
    (by rw [(CentralExponent.isOpen_cong _ _).interior_eq]; exact ⟨1, one_mem _⟩)
  have hne : e (Sum.inr j) ≠ e (Sum.inl i) := by simp
  obtain ⟨y, hyv⟩ : ∃ y : GL n k, (y : Matrix n n k) = Matrix.transvection (e (.inr j)) (e (.inl i)) 1 :=
    ⟨⟨Matrix.transvection (e (.inr j)) (e (.inl i)) 1,
      Matrix.transvection (e (.inr j)) (e (.inl i)) (-1),
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp,
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp⟩, rfl⟩
  have hy : ∀ p q, valuation k ((y : Matrix n n k) p q) ≤ 1 := by
    intro p q
    rw [hyv, Matrix.transvection, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · rw [Matrix.single_apply]; split_ifs <;> simp

  have key : ∀ d : ℕ, 0 < d → ∀ ζ ∈ Subgroup.center (GL n k), ∀ κ ∈ K',
      emb₂ k e (GeneralLinearGroup.scalar a z, 1) ^ d ≠ ζ * κ := by
    intro d hd ζ hζ κ hκ hAd
    have hpow : emb₂ k e (GeneralLinearGroup.scalar a z, 1) ^ d =
        emb₂ k e (GeneralLinearGroup.scalar a (z ^ d), 1) := by
      rw [← map_pow, Prod.pow_mk, one_pow, ← map_pow]
    have hinv : (emb₂ k e (GeneralLinearGroup.scalar a (z ^ d), 1))⁻¹ =
        emb₂ k e (GeneralLinearGroup.scalar a (z ^ d)⁻¹, 1) := by
      rw [← map_inv, Prod.inv_mk, inv_one, ← map_inv]
    rw [hpow] at hAd
    have hconj : emb₂ k e (GeneralLinearGroup.scalar a (z ^ d), 1) * y *
        emb₂ k e (GeneralLinearGroup.scalar a (z ^ d)⁻¹, 1) = κ * y * κ⁻¹ := by
      have hc : ∀ g, g * ζ = ζ * g := Subgroup.mem_center_iff.1 hζ
      rw [← hinv, hAd, _root_.mul_inv_rev,
        show ζ * κ * y * (κ⁻¹ * ζ⁻¹) = (ζ * (κ * y * κ⁻¹)) * ζ⁻¹ by group, ← hc, mul_inv_cancel_right]
    have hL : ((emb₂ k e (GeneralLinearGroup.scalar a (z ^ d), 1) * y *
        emb₂ k e (GeneralLinearGroup.scalar a (z ^ d)⁻¹, 1) : GL n k) : Matrix n n k)
          (e (.inr j)) (e (.inl i)) = (((z ^ d)⁻¹ : kˣ) : k) := by
      rw [Units.val_mul, Units.val_mul, CentralExponent.val_emb₂_scalar,
        CentralExponent.val_emb₂_scalar, Matrix.mul_diagonal, Matrix.diagonal_mul, hyv]
      simp [Matrix.transvection, Matrix.one_apply_ne hne]
    have hR : valuation k (((κ * y * κ⁻¹ : GL n k) : Matrix n n k) (e (.inr j)) (e (.inl i))) ≤ 1 := by
      rw [Units.val_mul, Units.val_mul]
      exact val_mul_le_one (val_mul_le_one (val_le_one_of_mem_cong hκ) hy)
        (val_le_one_of_mem_cong (inv_mem hκ)) _ _
    rw [← hconj, hL] at hR
    have h1 : valuation k ((z ^ d : kˣ) : k) < 1 := by
      obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_lt hd
      rw [Units.val_pow_eq_pow_val, map_pow, zero_add, pow_succ]
      exact mul_lt_of_le_one_of_lt (pow_le_one' hz.le d') hz
    have h2 : valuation k ((z ^ d : kˣ) : k) * valuation k (((z ^ d)⁻¹ : kˣ) : k) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h3 := mul_le_mul_right hR (valuation k ((z ^ d : kˣ) : k))
    rw [h2, mul_one] at h3
    exact absurd (h3.trans_lt h1) (lt_irrefl _)
  set A := emb₂ k e (GeneralLinearGroup.scalar a z, 1) with hA
  have hch : ∀ r : S, ∃ g : t, ∃ ζ ∈ Subgroup.center (GL n k), ∃ c : GL n k,
      A ^ (r : ℕ) = ζ * c ∧ (g : GL n k) * c ∈ K' := by
    intro r
    obtain ⟨ζ, hζ, c, hc, hrc⟩ := h r r.2
    have := ht hc
    simp only [Set.mem_iUnion, Set.mem_preimage] at this
    obtain ⟨g, hg, hgc⟩ := this
    exact ⟨⟨g, hg⟩, ζ, hζ, c, hrc, hgc⟩
  choose g ζ hζ c hAc hgc using hch
  haveI : Infinite S := hS.to_subtype
  obtain ⟨g0, hg0⟩ := Finite.exists_infinite_fiber g
  have two : ∀ r₁ r₂ : S, g r₁ = g r₂ → (r₁ : ℕ) < r₂ → False := by
    intro r₁ r₂ hg hlt
    refine key ((r₂ : ℕ) - r₁) (Nat.sub_pos_of_lt hlt) ((ζ r₁)⁻¹ * ζ r₂)
      (mul_mem (inv_mem (hζ r₁)) (hζ r₂)) ((c r₁)⁻¹ * c r₂) ?_ ?_
    · have h1 := hgc r₁
      have h2 := hgc r₂
      rw [hg] at h1
      have := mul_mem (inv_mem h1) h2
      simpa [mul_assoc] using this
    · have hc : ∀ g, g * ((ζ r₁)⁻¹ * ζ r₂) = ((ζ r₁)⁻¹ * ζ r₂) * g :=
        Subgroup.mem_center_iff.1 (mul_mem (inv_mem (hζ r₁)) (hζ r₂))
      have e1 : (A ^ (r₁ : ℕ))⁻¹ * A ^ (r₂ : ℕ) = A ^ ((r₂ : ℕ) - r₁) := by
        rw [inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [← e1, hAc, hAc, _root_.mul_inv_rev,
        show (c r₁)⁻¹ * (ζ r₁)⁻¹ * (ζ r₂ * c r₂) = (c r₁)⁻¹ * ((ζ r₁)⁻¹ * ζ r₂) * c r₂ by group, hc]
      group
  obtain ⟨x, hx, x', hx', hxx⟩ := Set.Infinite.nontrivial (Set.infinite_coe_iff.1 hg0)
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
  rcases lt_or_gt_of_ne (fun h => hxx (Subtype.ext h)) with hl | hl
  · exact two x x' (hx.trans hx'.symm) hl
  · exact two x' x (hx'.trans hx.symm) hl
end GlobalTheory.SuperCusp
