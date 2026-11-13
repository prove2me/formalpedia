-- Prove2me | solution 1 for ListHashFurstenberg.Main.corollary_2_14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T19:17:39.766116+00:00
-- url     : https://prove2.me/submissions/9396b466-c3d7-47f9-a4bb-581d6d807024

import Mathlib
import Definitions.Def_ListHashFurstenberg_Main_Furstenberg
import Theorems.Thm_ListHashFurstenberg_Main_theorem_2_8

section
set_option autoImplicit false

namespace ListHashFurstenberg.Main.Dev.Cor214

open ListHashFurstenberg.Main

open Classical in
/-- A positive rich fraction yields a rich shifted subspace; its count is at most `|S|` and
at most `q^r`. -/
theorem rich_le {F : Type*} [Field F] [Fintype F] {n r : ℕ} {T : ℝ}
    {S : Finset (Fin n → F)} (h : 0 < richFraction n r T S) :
    T ≤ (S.card : ℝ) ∧ T ≤ (Fintype.card F : ℝ) ^ r := by
  unfold richFraction at h
  have hnum : Nat.card {V : Submodule F (Fin n → F) // Module.finrank F V = r ∧
      ∃ x : Fin n → F, T ≤ ((S.filter fun s => s - x ∈ V).card : ℝ)} ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  have : Finite (Submodule F (Fin n → F)) :=
    Finite.of_injective (fun V : Submodule F (Fin n → F) => (V : Set (Fin n → F)))
      SetLike.coe_injective
  obtain ⟨⟨V, hV, x, hx⟩⟩ := (Nat.card_ne_zero.mp hnum).1
  refine ⟨hx.trans (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)), ?_⟩
  refine hx.trans ?_
  have hinj : Nat.card {s // s ∈ S.filter fun s => s - x ∈ V} ≤ Nat.card V := by
    refine Nat.card_le_card_of_injective
      (fun s => (⟨s.1 - x, (Finset.mem_filter.mp s.2).2⟩ : V)) ?_
    intro a b hab
    apply Subtype.ext
    simpa using congrArg Subtype.val hab
  rw [Nat.card_eq_finsetCard, Module.natCard_eq_pow_finrank (K := F), hV,
    Nat.card_eq_fintype_card] at hinj
  exact_mod_cast hinj

theorem pow_sub_pow_ge (n : ℕ) (x y : ℝ) (hy : 0 ≤ y) (hxy : y ≤ x) :
    n * y ^ (n - 1) * (x - y) ≤ x ^ n - y ^ n := by
  rw [← geom_sum₂_mul]
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  have : ∀ i ∈ Finset.range n, y ^ (n - 1) ≤ x ^ i * y ^ (n - 1 - i) := by
    intro i hi
    have hi' : i ≤ n - 1 := by have := Finset.mem_range.mp hi; omega
    calc y ^ (n - 1) = y ^ i * y ^ (n - 1 - i) := by rw [← pow_add]; congr 1; omega
      _ ≤ x ^ i * y ^ (n - 1 - i) := by
        gcongr
  calc (n : ℝ) * y ^ (n - 1) = ∑ i ∈ Finset.range n, y ^ (n - 1) := by simp
    _ ≤ _ := Finset.sum_le_sum this

theorem one_sub_ge_exp (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    Real.exp (-2 * u) ≤ 1 - u := by
  have h1 := Real.add_one_le_exp (2 * u)
  have h2 : 1 ≤ (1 - u) * Real.exp (2 * u) := by nlinarith
  rw [show -2 * u = -(2 * u) by ring, Real.exp_neg]
  rw [inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  exact h2

theorem real_core (n : ℕ) (hn : 1 ≤ n) (q Q δ α C Sc : ℝ) (hq : 2 ≤ q) (hQ : 0 < Q)
    (hδ : 0 < δ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hC1 : 1 < C)
    (hC2 : C ≤ α * δ * (Q / q) / 2)
    (h28 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      q ^ n * ((δ * (α + (1 - ε) * (1 - α)) * Q / (δ * Q + q - 1)) ^ n - (1 - ε) ^ n) /
        (1 - (1 - ε) ^ n) ≤ Sc) :
    Real.exp (-(2 * C * n) / (δ * α * (Q / q))) * (1 - 1 / C) * α ≤ Sc / q ^ n := by
  have hq0 : 0 < q := by linarith
  have hδQ : 0 < δ * Q := mul_pos hδ hQ
  set γ := (q - 1) / (δ * Q) with hγ
  have hγ0 : 0 < γ := div_pos (by linarith) hδQ
  have hC2' : C * q ≤ α * δ * Q / 2 := by
    have := mul_le_mul_of_nonneg_right hC2 hq0.le
    calc C * q ≤ α * δ * (Q / q) / 2 * q := this
      _ = α * δ * Q / 2 := by field_simp
  have hCγ : C * γ ≤ α / 2 := by
    rw [hγ, mul_div_assoc', div_le_iff₀ hδQ]
    nlinarith
  set ε := C * γ / (α + γ) with hε
  have hαγ : 0 < α + γ := by linarith
  have hε0 : 0 < ε := div_pos (by positivity) hαγ
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one hαγ]; linarith
  set u := C * γ / α with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 / 2 := by rw [hu, div_le_iff₀ hα0]; linarith
  have hεu : ε ≤ u := div_le_div_of_nonneg_left (by positivity) hα0 (by linarith)
  set y := 1 - ε with hy
  have hy0 : 0 ≤ y := by linarith
  have hy1 : y < 1 := by linarith
  set K := (1 - 1 / C) * ((α + γ) / (1 + γ)) with hK
  have hC0 : 0 < C := by linarith
  have hK1 : (1 - 1 / C) * α ≤ K := by
    have : 0 ≤ 1 - 1 / C := by rw [sub_nonneg, div_le_one hC0]; linarith
    apply mul_le_mul_of_nonneg_left _ this
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hK0 : 0 ≤ K := le_trans (by
    have : 0 ≤ 1 - 1 / C := by rw [sub_nonneg, div_le_one hC0]; linarith
    positivity) hK1
  have hA : δ * (α + (1 - ε) * (1 - α)) * Q / (δ * Q + q - 1) = y + ε * K := by
    have hden' : δ * Q + q - 1 = δ * Q * (1 + γ) := by
      rw [hγ]; field_simp; ring
    have h1γ : (1 + γ) ≠ 0 := by linarith
    rw [hden', hy, hε, hK]
    field_simp
    ring
  have key := h28 ε hε0 hε1
  rw [hA] at key
  -- lower bound of the quotient
  have hyn : y ^ n < 1 := pow_lt_one₀ hy0 hy1 (by omega)
  have hbern : 1 - y ^ n ≤ n * ε := by
    have := one_add_mul_le_pow (a := -ε) (by linarith) n
    rw [hy, show (1 : ℝ) - ε = 1 + -ε by ring]
    linarith
  have hgap := pow_sub_pow_ge n (y + ε * K) y hy0 (by nlinarith)
  have hquot : K * y ^ (n - 1) ≤ ((y + ε * K) ^ n - y ^ n) / (1 - y ^ n) := by
    rw [le_div_iff₀ (by linarith)]
    have : 0 ≤ K * y ^ (n - 1) := by positivity
    calc K * y ^ (n - 1) * (1 - y ^ n) ≤ K * y ^ (n - 1) * (n * ε) :=
          mul_le_mul_of_nonneg_left hbern this
      _ = n * y ^ (n - 1) * (y + ε * K - y) := by ring
      _ ≤ _ := hgap
  have hS : K * y ^ (n - 1) ≤ Sc / q ^ n := by
    rw [le_div_iff₀ (by positivity)]
    calc K * y ^ (n - 1) * q ^ n ≤ q ^ n * (((y + ε * K) ^ n - y ^ n) / (1 - y ^ n)) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hquot (by positivity)
      _ = _ := by rw [mul_div_assoc]
      _ ≤ Sc := key
  -- exponential lower bound for y^(n-1)
  have hexp : Real.exp (-(2 * C * n) / (δ * α * (Q / q))) ≤ y ^ (n - 1) := by
    have h1 : Real.exp (-2 * u) ≤ y :=
      (one_sub_ge_exp u hu0 hu1).trans (by linarith)
    have h2 : Real.exp (-2 * u) ^ (n - 1) ≤ y ^ (n - 1) :=
      pow_le_pow_left₀ (Real.exp_pos _).le h1 _
    rw [← Real.exp_nat_mul] at h2
    refine le_trans (Real.exp_le_exp.mpr ?_) h2
    have hun : u ≤ C / (δ * α * (Q / q)) := by
      rw [hu, hγ]
      rw [show C * ((q - 1) / (δ * Q)) / α = C * (q - 1) / (δ * α * Q) by
        field_simp]
      rw [show C / (δ * α * (Q / q)) = C * q / (δ * α * Q) by field_simp]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    have hn1 : ((n - 1 : ℕ) : ℝ) ≤ n := by
      rw [Nat.cast_sub hn]; linarith
    rw [show -(2 * C * n) / (δ * α * (Q / q)) = -2 * n * (C / (δ * α * (Q / q))) by ring]
    have hn0 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul hn1 hun hu0 (by positivity : (0 : ℝ) ≤ n)]
  have hexp0 := (Real.exp_pos (-(2 * C * n) / (δ * α * (Q / q)))).le
  calc Real.exp (-(2 * C * n) / (δ * α * (Q / q))) * (1 - 1 / C) * α
      = Real.exp (-(2 * C * n) / (δ * α * (Q / q))) * ((1 - 1 / C) * α) := by ring
    _ ≤ y ^ (n - 1) * K := mul_le_mul hexp hK1 (by
        have : 0 ≤ 1 - 1 / C := by rw [sub_nonneg, div_le_one hC0]; linarith
        positivity) (by positivity)
    _ = K * y ^ (n - 1) := by ring
    _ ≤ Sc / q ^ n := hS

end ListHashFurstenberg.Main.Dev.Cor214

namespace ListHashFurstenberg.Main

open ListHashFurstenberg.Main.Dev.Cor214 in
theorem chk_corollary_2_14 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (n r : ℕ) (δ α C : ℝ) (S : Finset (Fin n → F))
    (hS : IsFurstenberg δ n r (α * (Fintype.card F : ℝ) ^ r) S)
    (hC1 : 1 < C) (hC2 : C ≤ α * δ * (Fintype.card F : ℝ) ^ ((r : ℤ) - 1) / 2) :
    Real.exp (-(2 * C * n) / (δ * α * (Fintype.card F : ℝ) ^ ((r : ℤ) - 1))) *
        (1 - 1 / C) * α ≤
      (S.card : ℝ) / (Fintype.card F : ℝ) ^ n := by
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hq2 : (2 : ℝ) ≤ q := by
    rw [hqdef]; exact_mod_cast Fintype.one_lt_card (α := F)
  have hq0 : 0 < q := by linarith
  have hQ : 0 < q ^ r := by positivity
  have hzp : q ^ ((r : ℤ) - 1) = q ^ r / q := by
    rw [zpow_sub_one₀ hq0.ne', zpow_natCast, div_eq_mul_inv]
  rw [hzp] at hC2 ⊢
  have hRHS : 0 ≤ (S.card : ℝ) / q ^ n := by positivity
  have hexp0 := Real.exp_pos (-(2 * C * n) / (δ * α * (q ^ r / q)))
  have hC0 : 0 < C := by linarith
  have hCC : 0 ≤ 1 - 1 / C := by rw [sub_nonneg, div_le_one hC0]; linarith
  rcases le_or_gt α 0 with hα | hα
  · have : Real.exp (-(2 * C * n) / (δ * α * (q ^ r / q))) * (1 - 1 / C) * α ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hα
    linarith
  have hδ : 0 < δ := by
    by_contra hδ
    rw [not_lt] at hδ
    have : α * δ * (q ^ r / q) / 2 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hα.le hδ)
        (by positivity)
    linarith
  obtain ⟨hTS, hTq⟩ := rich_le (lt_of_lt_of_le hδ hS)
  have hα1 : α ≤ 1 := by
    have := hTq
    nlinarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, mul_zero, neg_zero, zero_div, Real.exp_zero, one_mul, pow_zero,
      div_one]
    have h1 : α ≤ α * q ^ r := le_mul_of_one_le_right hα.le (one_le_pow₀ (by linarith))
    have h2 : (1 - 1 / C) * α ≤ α := by
      have : 1 / C ≤ 1 := by rw [div_le_one hC0]; linarith
      nlinarith [one_div_pos.mpr hC0]
    linarith
  exact real_core n hn q (q ^ r) δ α C S.card hq2 hQ hδ hα hα1 hC1 hC2
    (fun ε hε0 hε1 => (theorem_2_8 n r hn δ α ε hδ.le hα.le S hS hε0 hε1).1)

end ListHashFurstenberg.Main
end

theorem solution : type_of% @ListHashFurstenberg.Main.chk_corollary_2_14 := @ListHashFurstenberg.Main.chk_corollary_2_14
