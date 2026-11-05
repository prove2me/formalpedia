-- Prove2me | solution 1 for LL_Decomp1543a.square_expand
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:29.243504+00:00
-- url     : https://prove2.me/submissions/78677600-b14c-4480-a7d6-30c56867d4c0

import Mathlib
import Definitions.Def_LL_Decomp1543a_e
import Definitions.Def_LL_Decomp1543a_nint
import Definitions.Def_LL_Decomp1543a_minK
import Definitions.Def_LL_Decomp1543a_am
import Definitions.Def_LL_Decomp1543a_tBlock
import Definitions.Def_LL_Decomp1543a_mRange
import Definitions.Def_LL_Decomp1543a_inner
import Definitions.Def_LL_Decomp1543a_lRange

open Real Finset ArithmeticFunction

namespace VaAAux
open LL_Decomp1543a

theorem conj_e (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem e_add (x y : ℝ) : e x * e y = e (x + y) := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem am_nonneg (U : ℝ) (m : ℕ) : 0 ≤ am U m :=
  sum_nonneg (fun r _ => vonMangoldt_nonneg)

end VaAAux

open LL_Decomp1543a in
theorem solution (c : ℝ) (N : ℕ) (U M α : ℝ) (hU : 0 ≤ U) (hM : 1 ≤ M)
    (hgeom : ∀ θ : ℝ, ∀ A B : ℤ, ⌊M⌋ ≤ A → B ≤ ⌊2 * M⌋ →
      ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ minK (M + 1 / 2) θ) :
    ∑ t ∈ tBlock N M, ‖inner c N U α t‖ ^ 2 ≤
      ∑ m ∈ lRange N U (N / M), am U m ^ 2 *
        ∑ l ∈ lRange N U (N / M), minK (M + 1 / 2) (α * ((m : ℝ) - l)) := by
  set L := lRange N U (N / M) with hL
  set T := tBlock N M with hT
  have hMpos : 0 < M := by linarith
  have hX : (0 : ℝ) ≤ M + 1 / 2 := by linarith
  have hKnn : ∀ θ : ℝ, 0 ≤ minK (M + 1 / 2) θ := by
    intro θ
    unfold minK
    split_ifs
    · exact hX
    · exact le_min hX (div_nonneg zero_le_one (mul_nonneg zero_le_two (abs_nonneg _)))
  have hKsym : ∀ θ : ℝ, minK (M + 1 / 2) (-θ) = minK (M + 1 / 2) θ := by
    intro θ
    have : nint (-θ) = nint θ := by
      unfold nint
      apply le_antisymm
      · refine (round_le (-θ) (-round θ)).trans (le_of_eq ?_)
        rw [show -θ - ((-round θ : ℤ) : ℝ) = -(θ - round θ) by push_cast; ring, abs_neg]
      · have h := round_le θ (-round (-θ))
        refine h.trans (le_of_eq ?_)
        rw [← abs_neg]
        congr 1
        push_cast
        ring
    unfold minK
    rw [this]
  -- S t ⊆ L
  have hSL : ∀ t ∈ T, mRange c N U t ⊆ L := by
    intro t ht m hm
    obtain ⟨ht1, ht2⟩ := mem_filter.1 ht
    obtain ⟨ht3, ht4⟩ := mem_Icc.1 ht1
    obtain ⟨hm1, hm2, hm3, hm4⟩ := mem_filter.1 hm
    obtain ⟨hm5, hm6⟩ := mem_Icc.1 hm1
    refine mem_filter.2 ⟨hm1, hm4, ?_⟩
    rw [le_div_iff₀ hMpos]
    have h1 : (m : ℝ) * t ≤ N := by exact_mod_cast hm3
    have h2 : (1 : ℝ) ≤ m := by exact_mod_cast hm5
    nlinarith [ht2.1]
  set g : ℕ → ℕ → ℂ := fun t m =>
    if m ∈ mRange c N U t then (am U m : ℂ) * e (α * ((m * t : ℕ) : ℝ)) else 0 with hg
  have hz : ∀ t ∈ T, inner c N U α t = ∑ m ∈ L, g t m := by
    intro t ht
    unfold LL_Decomp1543a.inner
    rw [hg]
    simp only []
    rw [sum_ite_mem, inter_eq_right.2 (hSL t ht)]
  have hsq : ∀ t ∈ T, ((‖inner c N U α t‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ L, ∑ l ∈ L, g t m * (starRingEnd ℂ) (g t l) := by
    intro t ht
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hz t ht, map_sum, sum_mul_sum]
  have hterm : ∀ t m l : ℕ, g t m * (starRingEnd ℂ) (g t l) =
      if (m ∈ mRange c N U t ∧ l ∈ mRange c N U t) then
        ((am U m * am U l : ℝ) : ℂ) * e ((α * ((m : ℝ) - l)) * (((t : ℕ) : ℤ) : ℝ)) else 0 := by
    intro t m l
    by_cases hm : m ∈ mRange c N U t
    · by_cases hl : l ∈ mRange c N U t
      · rw [if_pos ⟨hm, hl⟩]
        simp only [hg, if_pos hm, if_pos hl, map_mul, Complex.conj_ofReal,
          VaAAux.conj_e]
        rw [mul_mul_mul_comm, VaAAux.e_add]
        push_cast
        congr 2
        push_cast
        ring
      · simp [hg, hm, hl]
    · simp [hg, hm]
  have hpt : ∀ m ∈ L, ∀ l ∈ L, ‖∑ t ∈ T, g t m * (starRingEnd ℂ) (g t l)‖ ≤
      am U m * am U l * minK (M + 1 / 2) (α * ((m : ℝ) - l)) := by
    intro m hm l hl
    obtain ⟨hm1, hm2, hm3⟩ := mem_filter.1 hm
    obtain ⟨hl1, hl2, hl3⟩ := mem_filter.1 hl
    obtain ⟨hm4, hm5⟩ := mem_Icc.1 hm1
    obtain ⟨hl4, hl5⟩ := mem_Icc.1 hl1
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm4
    have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl4
    have hmPos : (0 : ℝ) < m := by linarith
    have hlPos : (0 : ℝ) < l := by linarith
    set A : ℤ := max ⌊M⌋ (max ⌊c * N / m⌋ ⌊c * N / l⌋) with hA
    set B : ℤ := min ⌊2 * M⌋ (min ⌊(N : ℝ) / m⌋ ⌊(N : ℝ) / l⌋) with hB
    have hmem : ∀ t : ℕ, (t ∈ T ∧ (m ∈ mRange c N U t ∧ l ∈ mRange c N U t)) ↔
        ((t : ℤ) ∈ Ioc A B) := by
      intro t
      simp only [hT, tBlock, mRange, mem_filter, mem_Icc, mem_Ioc, hA, hB, max_lt_iff, le_min_iff,
        Int.floor_lt, Int.le_floor]
      push_cast
      rw [div_lt_iff₀ hmPos, div_lt_iff₀ hlPos, le_div_iff₀ hmPos, le_div_iff₀ hlPos]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨_, h5, h6, _⟩, ⟨_, h7, h8, _⟩⟩
        have h6' : (m : ℝ) * t ≤ N := by exact_mod_cast h6
        have h8' : (l : ℝ) * t ≤ N := by exact_mod_cast h8
        refine ⟨⟨h3, ?_, ?_⟩, h4, ?_, ?_⟩ <;> nlinarith
      · rintro ⟨⟨h3, h5, h7⟩, h4, h6, h8⟩
        have ht1 : 1 ≤ t := by
          have : (1 : ℝ) < t := by linarith
          exact_mod_cast this.le
        have h6' : m * t ≤ N := by
          have : (m : ℝ) * t ≤ N := by nlinarith
          exact_mod_cast this
        have h8' : l * t ≤ N := by
          have : (l : ℝ) * t ≤ N := by nlinarith
          exact_mod_cast this
        have htN : t ≤ N := le_trans (Nat.le_mul_of_pos_left t hm4) h6'
        refine ⟨⟨⟨ht1, htN⟩, h3, h4⟩, ⟨⟨hm4, hm5⟩, ?_, h6', hm2⟩, ⟨⟨hl4, hl5⟩, ?_, h8', hl2⟩⟩
        · push_cast; nlinarith
        · push_cast; nlinarith
    have himg : ((T.filter (fun t => m ∈ mRange c N U t ∧ l ∈ mRange c N U t)).image
        (Nat.cast : ℕ → ℤ)) = Ioc A B := by
      ext x
      simp only [mem_image, mem_filter]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact (hmem t).1 ht
      · intro hx
        have hA1 : (1 : ℤ) ≤ ⌊M⌋ := Int.le_floor.2 (by simpa using hM)
        have hAA : ⌊M⌋ ≤ A := le_max_left _ _
        have hx0 : 0 ≤ x := by have := (mem_Ioc.1 hx).1; omega
        lift x to ℕ using hx0
        exact ⟨x, (hmem x).2 hx, rfl⟩
    have hsum : ∑ t ∈ T, g t m * (starRingEnd ℂ) (g t l) =
        ((am U m * am U l : ℝ) : ℂ) * ∑ x ∈ Ioc A B, e ((α * ((m : ℝ) - l)) * x) := by
      rw [sum_congr rfl (fun t _ => hterm t m l), ← sum_filter, ← himg,
        sum_image (fun a _ b _ h => Nat.cast_injective h), mul_sum]
    have hnn : 0 ≤ am U m * am U l := mul_nonneg (VaAAux.am_nonneg U m) (VaAAux.am_nonneg U l)
    rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left (hgeom _ A B (le_max_left _ _) (min_le_left _ _)) hnn
  have hLr : ∑ t ∈ T, ‖LL_Decomp1543a.inner c N U α t‖ ^ 2 ≤
      ∑ m ∈ L, ∑ l ∈ L, am U m * am U l * minK (M + 1 / 2) (α * ((m : ℝ) - l)) := by
    have h1 : ((∑ t ∈ T, ‖LL_Decomp1543a.inner c N U α t‖ ^ 2 : ℝ) : ℂ) =
        ∑ m ∈ L, ∑ l ∈ L, ∑ t ∈ T, g t m * (starRingEnd ℂ) (g t l) := by
      rw [Complex.ofReal_sum, sum_congr rfl hsq, sum_comm]
      apply sum_congr rfl
      intro m _
      rw [sum_comm]
    calc ∑ t ∈ T, ‖LL_Decomp1543a.inner c N U α t‖ ^ 2
        = ‖((∑ t ∈ T, ‖LL_Decomp1543a.inner c N U α t‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sum_nonneg fun _ _ => by positivity)]
      _ = ‖∑ m ∈ L, ∑ l ∈ L, ∑ t ∈ T, g t m * (starRingEnd ℂ) (g t l)‖ := by rw [h1]
      _ ≤ ∑ m ∈ L, ‖∑ l ∈ L, ∑ t ∈ T, g t m * (starRingEnd ℂ) (g t l)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ L, ∑ l ∈ L, ‖∑ t ∈ T, g t m * (starRingEnd ℂ) (g t l)‖ :=
          sum_le_sum (fun m _ => norm_sum_le _ _)
      _ ≤ _ := sum_le_sum (fun m hm => sum_le_sum (fun l hl => hpt m hm l hl))
  refine hLr.trans ?_
  have hsw : ∑ m ∈ L, ∑ l ∈ L, am U l ^ 2 * minK (M + 1 / 2) (α * ((m : ℝ) - l)) =
      ∑ m ∈ L, am U m ^ 2 * ∑ l ∈ L, minK (M + 1 / 2) (α * ((m : ℝ) - l)) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro m _
    rw [mul_sum]
    apply sum_congr rfl
    intro l _
    rw [show α * ((l : ℝ) - m) = -(α * ((m : ℝ) - l)) by ring, hKsym]
  have hpw : ∀ m l : ℕ, am U m * am U l * minK (M + 1 / 2) (α * ((m : ℝ) - l)) ≤
      (1 / 2) * (am U m ^ 2 * minK (M + 1 / 2) (α * ((m : ℝ) - l))) +
        (1 / 2) * (am U l ^ 2 * minK (M + 1 / 2) (α * ((m : ℝ) - l))) := by
    intro m l
    have := mul_nonneg (sq_nonneg (am U m - am U l)) (hKnn (α * ((m : ℝ) - l)))
    nlinarith [this]
  calc ∑ m ∈ L, ∑ l ∈ L, am U m * am U l * minK (M + 1 / 2) (α * ((m : ℝ) - l))
      ≤ ∑ m ∈ L, ∑ l ∈ L, ((1 / 2) * (am U m ^ 2 * minK (M + 1 / 2) (α * ((m : ℝ) - l))) +
        (1 / 2) * (am U l ^ 2 * minK (M + 1 / 2) (α * ((m : ℝ) - l)))) :=
        sum_le_sum fun m _ => sum_le_sum fun l _ => hpw m l
    _ = (1 / 2) * ∑ m ∈ L, am U m ^ 2 * ∑ l ∈ L, minK (M + 1 / 2) (α * ((m : ℝ) - l)) +
        (1 / 2) * ∑ m ∈ L, ∑ l ∈ L, am U l ^ 2 * minK (M + 1 / 2) (α * ((m : ℝ) - l)) := by
        simp only [sum_add_distrib, ← mul_sum]
    _ = _ := by rw [hsw]; ring
