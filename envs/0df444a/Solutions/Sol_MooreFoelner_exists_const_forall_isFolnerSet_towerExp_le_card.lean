-- Prove2me | solution 1 for MooreFoelner.exists_const_forall_isFolnerSet_towerExp_le_card
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T02:13:33.334981+00:00
-- url     : https://prove2.me/submissions/58eeacba-b7df-4d25-87bc-636a453e3786

import Theorems.Thm_MooreFoelner_closure_x0_x1_eq_top
import Theorems.Thm_MooreFoelner_exists_isConnected_isFolnerSet_one_mem
import Theorems.Thm_MooreFoelner_exists_const_isFolnerSet_of_isFolnerSet
import Theorems.Thm_MooreFoelner_exists_const_isFolnerSet_exists_towerExp_le_card_Rf
import Theorems.Thm_MooreFoelner_card_Rf_sub_two_le_three_mul_wordLength
import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

section
namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

section
/-!
# Moore 2013, §5 end (group Goal): Claim 5.14, Theorem 1.1 and its "in particular", and the
F-amenability reference goal
-/

namespace MooreFoelner.Dev.Goal

open Classical CannonFloydParry MooreFoelner

/-! ## Generic facts about (weighted) Følner sets -/

theorem isFolnerSet_mono {G : Type*} [Group G] {Γ A : Finset G} {ε ε' : ℝ}
    (h : IsFolnerSet Γ A ε) (hle : ε ≤ ε') : IsFolnerSet Γ A ε' :=
  lt_of_lt_of_le h (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _))

/-! ## Trees -/

/-! ## The tower function -/

open ThompsonAmenability in
theorem towerExp_succ (p m : ℕ) : towerExp (p + 1) m = 2 ^ towerExp p m := rfl

theorem three_mul_le_two_pow_succ (e : ℕ) : 3 * e ≤ 2 ^ (e + 1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rcases Nat.eq_zero_or_pos e with rfl | he
    · norm_num
    · have : 3 ≤ 2 ^ (e + 1) := by
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ]; omega

open ThompsonAmenability in
theorem three_mul_towerExp_le (n : ℕ) : 3 * towerExp n 0 ≤ towerExp (n + 2) 0 + 1 := by
  rw [towerExp_succ, towerExp_succ]
  have h1 := three_mul_le_two_pow_succ (towerExp n 0)
  have h2 : 2 ^ (towerExp n 0 + 1) ≤ 2 ^ 2 ^ towerExp n 0 :=
    Nat.pow_le_pow_right (by norm_num) Nat.lt_two_pow_self
  omega

/-! ## Claim 5.14 -/

end MooreFoelner.Dev.Goal

namespace MooreFoelner

open Classical CannonFloydParry
open MooreFoelner.Dev.Goal

end MooreFoelner

/-! ## Word length along a chain, and the generators `x₀, x₁` -/

namespace MooreFoelner.Dev.Goal

open Classical CannonFloydParry MooreFoelner

theorem wordLength_one_eq {G : Type*} [Group G] (Γ : Finset G) : wordLength Γ 1 = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨[], rfl, by simp, by simp⟩)

theorem wordLength_mul_le {G : Type*} [Group G] {Γ : Finset G} {x γ : G} (hγ : γ ∈ Γ)
    (hx : ∃ w : List G, (∀ γ ∈ w, γ ∈ Γ) ∧ w.prod = x) :
    wordLength Γ (x * γ) ≤ wordLength Γ x + 1 := by
  obtain ⟨w, hw, rfl⟩ := hx
  have hne : {n | ∃ w' : List G, w'.length = n ∧ (∀ γ ∈ w', γ ∈ Γ) ∧ w'.prod = w.prod}.Nonempty :=
    ⟨_, w, rfl, hw, rfl⟩
  obtain ⟨w', hlen, hw', hprod⟩ := Nat.sInf_mem hne
  apply Nat.sInf_le
  refine ⟨w' ++ [γ], ?_, ?_, by simp [hprod]⟩
  · rw [List.length_append, hlen]; rfl
  · intro y hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact hw' y hy
    · exact hγ

/-- A `Γ`-connected finite `B` containing `1` and `a` has at least `d_a + 1` elements: along a
chain in `B` from `1` to `a`, the word length rises by at most one per step, so it takes every
value from `0` to `d_a`. -/
theorem wordLength_add_one_le_card {G : Type*} [Group G] {Γ B : Finset G}
    (hB : IsConnected rightMul Γ (B : Set G)) (h1 : (1 : G) ∈ B) {a : G} (ha : a ∈ B) :
    wordLength Γ a + 1 ≤ B.card := by
  obtain ⟨l, p, hp0, hpl, hpB, hstep⟩ := hB 1 h1 a ha
  let q : ℕ → G := fun i => if h : i < l + 1 then p ⟨i, h⟩ else a
  have hq : ∀ i (h : i < l + 1), q i = p ⟨i, h⟩ := fun i h => dif_pos h
  have hq0 : q 0 = 1 := by rw [hq 0 (by omega)]; exact hp0
  have hql : q l = a := by rw [hq l (by omega)]; exact hpl
  have hqB : ∀ i ≤ l, q i ∈ B := fun i hi => by rw [hq i (by omega)]; exact hpB _
  have hqstep : ∀ i < l, ∃ γ ∈ Γ, q (i + 1) = q i * γ := by
    intro i hi
    obtain ⟨γ, hγ, hγ'⟩ := hstep ⟨i, hi⟩
    refine ⟨γ, hγ, ?_⟩
    rw [hq i (by omega), hq (i + 1) (by omega)]
    simp only [rightMul, Option.some.injEq] at hγ'
    exact hγ'.symm
  have hqword : ∀ i ≤ l, ∃ w : List G, (∀ γ ∈ w, γ ∈ Γ) ∧ w.prod = q i := by
    intro i
    induction i with
    | zero => intro _; exact ⟨[], by simp, by simp [hq0]⟩
    | succ i ih =>
      intro hi
      obtain ⟨w, hw, hwp⟩ := ih (by omega)
      obtain ⟨γ, hγ, hqi⟩ := hqstep i (by omega)
      refine ⟨w ++ [γ], ?_, by simp [hwp, hqi]⟩
      intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact hw y hy
      · exact hγ
  have hlip : ∀ i < l, wordLength Γ (q (i + 1)) ≤ wordLength Γ (q i) + 1 := by
    intro i hi
    obtain ⟨γ, hγ, hqi⟩ := hqstep i hi
    rw [hqi]
    exact wordLength_mul_le hγ (hqword i hi.le)
  have hivt : ∀ i ≤ l, ∀ k ≤ wordLength Γ (q i), ∃ j ≤ i, wordLength Γ (q j) = k := by
    intro i
    induction i with
    | zero =>
      intro _ k hk
      rw [hq0, wordLength_one_eq] at hk
      exact ⟨0, le_rfl, by rw [hq0, wordLength_one_eq]; omega⟩
    | succ i ih =>
      intro hi k hk
      by_cases hk' : k ≤ wordLength Γ (q i)
      · obtain ⟨j, hj, hjk⟩ := ih (by omega) k hk'
        exact ⟨j, by omega, hjk⟩
      · have := hlip i (by omega)
        exact ⟨i + 1, le_rfl, by omega⟩
  have hsub : Finset.range (wordLength Γ a + 1) ⊆ B.image (wordLength Γ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨j, hj, hjk⟩ := hivt l le_rfl k (by rw [hql]; omega)
    exact Finset.mem_image.mpr ⟨q j, hqB j hj, hjk⟩
  calc wordLength Γ a + 1 = (Finset.range (wordLength Γ a + 1)).card := by simp
    _ ≤ (B.image (wordLength Γ)).card := Finset.card_le_card hsub
    _ ≤ B.card := Finset.card_image_le

/-- `gens ⊇ {x₀, x₁}`, which generate Moore's `F` (p. 4). -/
theorem closure_gens_eq_top : Subgroup.closure (gens : Set MooreF) = ⊤ := by
  refine eq_top_iff.mpr (le_trans (le_of_eq closure_x0_x1_eq_top.symm) (Subgroup.closure_mono ?_))
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  simp only [gens, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  rcases hx with rfl | rfl <;> simp

theorem gens_symm : ∀ γ ∈ gens, γ⁻¹ ∈ gens := by
  intro γ hγ
  simp only [gens, Finset.mem_insert, Finset.mem_singleton] at hγ ⊢
  rcases hγ with rfl | rfl | rfl | rfl <;> simp

end MooreFoelner.Dev.Goal

namespace MooreFoelner

open Classical CannonFloydParry
open MooreFoelner.Dev.Goal

end MooreFoelner

namespace ThompsonAmenability

end ThompsonAmenability
end

open MooreFoelner in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry in
open MooreFoelner.Dev.Goal in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry in
open MooreFoelner.Dev.Goal in
theorem solution (Γ : Finset MooreF)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set MooreF) = ⊤) :
    ∃ C : ℝ, 1 < C ∧ ∀ (n : ℕ) (A : Finset MooreF),
      IsFolnerSet Γ A (C ^ (-(n : ℤ))) → ThompsonAmenability.towerExp n 0 ≤ A.card := by
  obtain ⟨K, hK, h28⟩ := exists_const_isFolnerSet_exists_towerExp_le_card_Rf
  obtain ⟨K', hK'0, h7⟩ := exists_const_isFolnerSet_of_isFolnerSet Γ hgen
  set M : ℝ := max K' 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hK'M : K' ≤ M := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hMpos : 0 < M := by linarith
  refine ⟨M * K ^ 3, ?_, ?_⟩
  · have : 1 < K ^ 3 := one_lt_pow₀ hK (by norm_num)
    nlinarith
  intro n A hA
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ThompsonAmenability.towerExp]
  -- change of generating set (#7), then a connected Følner set containing `1` (#16)
  have hAg := h7 A _ hA
  obtain ⟨B, hBF, hBc, hB1, hBA⟩ :=
    exists_isConnected_isFolnerSet_one_mem gens gens_symm closure_gens_eq_top _ A hAg
  have hle : K' * (M * K ^ 3) ^ (-(n : ℤ)) ≤ K ^ (-((n + 2 : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← div_eq_mul_inv, ← one_div,
      div_le_div_iff₀ (pow_pos (mul_pos hMpos (pow_pos hK0 3)) _) (pow_pos hK0 _), one_mul,
      mul_pow, ← pow_mul]
    exact mul_le_mul (le_trans hK'M (le_self_pow₀ hM1 (by omega)))
      (pow_le_pow_right₀ hK.le (by omega)) (by positivity) (by positivity)
  -- Claim 5.14 with `n + 2`, then Burillo–Cleary–Stein (#27) and the chain in `B`
  obtain ⟨a, haB, -, haR⟩ := h28 (n + 2) B (isFolnerSet_mono hBF hle)
  have h27 := card_Rf_sub_two_le_three_mul_wordLength a
  have hpath := wordLength_add_one_le_card hBc hB1 haB
  have h3 := three_mul_towerExp_le n
  have hR : (Rf (toMap a)).card ≤ 3 * wordLength gens a + 2 := by
    have : ((Rf (toMap a)).card : ℝ) ≤ 3 * wordLength gens a + 2 := by linarith
    exact_mod_cast this
  omega
