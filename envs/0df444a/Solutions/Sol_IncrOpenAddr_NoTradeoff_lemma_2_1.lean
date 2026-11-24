-- Prove2me | solution 1 for IncrOpenAddr.NoTradeoff.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T20:05:04.78017+00:00
-- url     : https://prove2.me/submissions/0df8ad16-0a57-4787-a3a1-a0465d7748c9

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout

namespace SolIncrOpenAddrL21

open IncrOpenAddr.NoTradeoff

/-! ## Generic list facts -/

theorem range_split (a : ℕ) : ∀ m, a < m → ∃ rest, List.range m = List.range a ++ a :: rest
  | 0, h => absurd h (Nat.not_lt_zero _)
  | m + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
    · obtain ⟨rest, hr⟩ := range_split a m h'
      exact ⟨rest ++ [m], by rw [List.range_succ, hr]; simp⟩
    · subst h'; exact ⟨[], by rw [List.range_succ]⟩

theorem len_filter_range (p : ℕ → Bool) :
    ∀ N, ((List.range N).filter p).length = ((Finset.range N).filter (fun r => p r = true)).card
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, Finset.range_add_one,
      Finset.filter_insert, len_filter_range p N]
    by_cases h : p N = true
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      simp [h]
    · rw [if_neg h]
      simp [h]

/-- The relation along the list of tree sizes: non-increasing, by a factor at most two. -/
def R (x y : ℕ) : Prop := x ≤ 2 * y ∧ y ≤ x

theorem chain_blocks (B : ℕ) (cnt : ℕ → ℕ) (hc : ∀ t, 1 ≤ cnt t) :
    ∀ K, K + 1 ≤ B →
      List.IsChain R ((List.range K).flatMap fun t => List.replicate (cnt t) (2 ^ (B - t))) ∧
      (∀ x ∈ (List.range K).flatMap (fun t => List.replicate (cnt t) (2 ^ (B - t))), 4 ≤ x) ∧
      (1 ≤ K → ((List.range K).flatMap fun t => List.replicate (cnt t) (2 ^ (B - t))).getLast?
        = some (2 ^ (B - (K - 1))))
  | 0, _ => by simp
  | K + 1, hK => by
    obtain ⟨ih1, ih2, ih3⟩ := chain_blocks B cnt hc K (by omega)
    have hsplit : (List.range (K + 1)).flatMap (fun t => List.replicate (cnt t) (2 ^ (B - t)))
        = (List.range K).flatMap (fun t => List.replicate (cnt t) (2 ^ (B - t)))
          ++ List.replicate (cnt K) (2 ^ (B - K)) := by
      rw [List.range_succ, List.flatMap_append]; simp
    have hne : cnt K ≠ 0 := by have := hc K; omega
    rw [hsplit]
    refine ⟨?_, ?_, ?_⟩
    · apply List.IsChain.append ih1 (List.isChain_replicate_of_rel _ ⟨by omega, le_rfl⟩)
      intro x hx y hy
      rcases Nat.eq_zero_or_pos K with h0 | h0
      · subst h0; simp at hx
      · rw [ih3 h0] at hx
        rw [List.head?_replicate, if_neg hne] at hy
        simp only [Option.mem_def, Option.some.injEq] at hx hy
        subst hx; subst hy
        rw [show B - (K - 1) = (B - K) + 1 by omega, pow_succ]
        constructor <;> omega
    · intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact ih2 x hx
      · rw [List.eq_of_mem_replicate hx]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (B - K) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · intro _
      rw [List.getLast?_append, List.getLast?_replicate, if_neg hne]
      simp

/-! ## Sum of the tree sizes -/

theorem bits_sum (m : ℕ) : ∀ N, ∑ j ∈ Finset.range N,
    (if m.testBit (j + 2) then 1 else 0) * 2 ^ (j + 2) + m % 4 = m % 2 ^ (N + 2)
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, add_right_comm, bits_sum m N,
      show N + 1 + 2 = (N + 2) + 1 by omega, Nat.mod_pow_succ (x := m) (b := 2) (k := N + 2),
      Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ (N + 2)) with h | h
    · simp [h]
    · simp [h]

theorem geom_sum4 : ∀ N, ∑ j ∈ Finset.range N, 2 ^ (j + 2) + 4 = 2 ^ (N + 2)
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, add_right_comm, geom_sum4 N, show N + 1 + 2 = (N + 2) + 1 by omega,
      pow_succ]
    ring

theorem eq2_sum : ∀ N, 1 ≤ N → ∑ j ∈ Finset.range N, (if j + 2 = 2 then 1 else 0) * 2 ^ (j + 2) = 4
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp
  | N + 2, _ => by
    rw [Finset.sum_range_succ, eq2_sum (N + 1) (by omega)]
    simp

theorem blocks_sum (B : ℕ) (cnt : ℕ → ℕ) : ∀ K,
    ((List.range K).flatMap fun t => List.replicate (cnt t) (2 ^ (B - t))).sum
      = ∑ t ∈ Finset.range K, cnt t * 2 ^ (B - t)
  | 0 => by simp
  | K + 1 => by
    rw [List.range_succ, List.flatMap_append, List.sum_append, Finset.sum_range_succ,
      blocks_sum B cnt K]
    simp

/-! ## Structure of the layout -/

structure Layout (n : ℕ) : Prop where
  min4 : ∀ j, 1 ≤ j → j < numTrees n → 4 ≤ treeSize n j
  ratio : ∀ i, 2 ≤ i → i < numTrees n → treeSize n (i - 1) ≤ 2 * treeSize n i
  last : 2 ≤ numTrees n → treeSize n (numTrees n - 1) ≤ 5 * treeSize n (numTrees n)
  total : 1 ≤ numTrees n → treeOffset n (numTrees n) + treeSize n (numTrees n) = n
  offset : ∀ j, 1 ≤ j → j ≤ numTrees n → treeOffset n (j + 1) = treeOffset n j + treeSize n j

theorem layout (n : ℕ) (hn : 8 ≤ n) : Layout n := by
  set L := Nat.log 2 n with hL
  set m := n - 2 ^ L with hm
  have hL1 : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hL2 : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hL3 : 3 ≤ L := by
    have : 2 ^ 3 ≤ n := by norm_num; omega
    exact Nat.le_log_of_pow_le (by norm_num) this
  set cnt : ℕ → ℕ := fun t => 1 + (if m.testBit (L - 1 - t) then 1 else 0)
    + (if L - 1 - t = 2 then 1 else 0) with hcnt
  set A := (List.range (L - 2)).flatMap (fun t => List.replicate (cnt t) (2 ^ (L - 1 - t))) with hA
  set O : List ℕ := if n % 4 = 0 then [] else [n % 4] with hO
  have hts : treeSizes n = A ++ O := rfl
  obtain ⟨hch, h4, hlast⟩ := chain_blocks (L - 1) cnt (fun t => by simp [hcnt]; omega) (L - 2)
    (by omega)
  have hlast4 : A.getLast? = some 4 := by
    rw [hlast (by omega), show L - 1 - (L - 2 - 1) = 2 by omega]; norm_num
  clear_value A O cnt
  rw [← hA] at hch h4
  have hAne : A ≠ [] := by intro h; rw [h] at hlast4; simp at hlast4
  have hAlen : 1 ≤ A.length := by
    rcases A with _ | ⟨x, l⟩
    · exact absurd rfl hAne
    · simp
  have hOlen : O.length ≤ 1 := by rw [hO]; split_ifs <;> simp
  have hα : numTrees n = A.length + O.length := by
    simp only [numTrees, hts, List.length_append]
  have hTs : ∀ j, 1 ≤ j → (h : j - 1 < A.length) → treeSize n j = A[j - 1] := by
    intro j hj h
    rw [treeSize, if_neg (by omega), hts, List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_append_left h]
  -- the sum
  have hsum : (treeSizes n).sum = n := by
    rw [hts, List.sum_append, hA, blocks_sum]
    have hrefl := Finset.sum_range_reflect (fun j => cnt (L - 2 - 1 - j) * 2 ^ (L - 1 - (L - 2 - 1 - j)))
      (L - 2)
    have e1 : ∑ t ∈ Finset.range (L - 2), cnt t * 2 ^ (L - 1 - t)
        = ∑ j ∈ Finset.range (L - 2), (1 + (if m.testBit (j + 2) then 1 else 0)
            + (if j + 2 = 2 then 1 else 0)) * 2 ^ (j + 2) := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp only [hcnt]
      rw [show L - 1 - (L - 2 - 1 - j) = j + 2 by omega]
    rw [e1]
    simp only [add_mul, one_mul, Finset.sum_add_distrib]
    have g1 := geom_sum4 (L - 2)
    have g2 := bits_sum m (L - 2)
    have g3 := eq2_sum (L - 2) (by omega)
    rw [show L - 2 + 2 = L by omega] at g1 g2
    have hmL : m < 2 ^ L := by
      have : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
      omega
    rw [Nat.mod_eq_of_lt hmL] at g2
    have h4L : 2 ^ L = 4 * 2 ^ (L - 2) := by
      rw [show L = (L - 2) + 2 by omega, pow_add]; norm_num; ring
    have hmod : m % 4 = n % 4 := by omega
    have hOs : O.sum = n % 4 := by rw [hO]; split_ifs with h <;> simp [h]
    rw [hOs]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- min4
    intro j hj hjα
    have hjA : j - 1 < A.length := by omega
    rw [hTs j hj hjA]
    exact h4 _ (List.getElem_mem _)
  · -- ratio
    intro i hi hiα
    have hiA : i - 1 < A.length := by omega
    rw [hTs i (by omega) hiA, hTs (i - 1) (by omega) (by omega)]
    have := (List.isChain_iff_getElem.1 hch) (i - 1 - 1) (by omega)
    simp only [show i - 1 - 1 + 1 = i - 1 by omega] at this
    exact this.1
  · -- last
    intro hα2
    by_cases hO0 : O = []
    · have hαA : numTrees n = A.length := by rw [hα, hO0]; simp
      rw [hTs _ (by omega) (by omega), hTs _ (by omega) (by omega)]
      have := (List.isChain_iff_getElem.1 hch) (numTrees n - 1 - 1) (by omega)
      simp only [show numTrees n - 1 - 1 + 1 = numTrees n - 1 by omega] at this
      have h1 := this.1
      omega
    · have hOv : O = [n % 4] := by
        rw [hO] at hO0 ⊢
        by_cases h : n % 4 = 0
        · rw [if_pos h] at hO0; exact absurd rfl hO0
        · rw [if_neg h]
      have hn4 : n % 4 ≠ 0 := by intro h; rw [hO, if_pos h] at hO0; exact hO0 rfl
      have hαA : numTrees n = A.length + 1 := by rw [hα, hOv]; simp
      have hTα : treeSize n (numTrees n) = n % 4 := by
        rw [treeSize, if_neg (by omega), hts, List.getD_eq_getElem _ _ (by simp; omega),
          List.getElem_append_right (by omega)]
        simp [hOv, hαA]
      have hTα1 : treeSize n (numTrees n - 1) = 4 := by
        rw [hTs _ (by omega) (by omega)]
        have hg : A[numTrees n - 1 - 1]? = some 4 := by
          rw [show numTrees n - 1 - 1 = A.length - 1 by omega, ← List.getLast?_eq_getElem?]
          exact hlast4
        rw [List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some.inj hg
      rw [hTα, hTα1]; omega
  · -- total
    intro hα1
    have hlen : numTrees n = (treeSizes n).length := rfl
    rw [treeOffset, treeSize, if_neg (by omega),
      List.getD_eq_getElem _ _ (by rw [← hlen]; omega)]
    have := List.sum_take_succ (treeSizes n) (numTrees n - 1) (by rw [← hlen]; omega)
    rw [← this, show numTrees n - 1 + 1 = (treeSizes n).length by rw [← hlen]; omega,
      List.take_length, hsum]
  · -- offset
    intro j hj hjα
    have hlen : numTrees n = (treeSizes n).length := rfl
    rw [treeOffset, treeOffset, treeSize, if_neg (by omega),
      List.getD_eq_getElem _ _ (by rw [← hlen]; omega),
      show j + 1 - 1 = (j - 1) + 1 by omega]
    exact List.sum_take_succ _ _ _


/-! ## Monotonicity of the offsets and the epoch boundaries -/

theorem off_mono {n : ℕ} (hL : Layout n) (a : ℕ) (ha : 1 ≤ a) :
    ∀ d, a + d ≤ numTrees n → treeOffset n a ≤ treeOffset n (a + d)
  | 0, _ => le_rfl
  | d + 1, h => by
    have := off_mono hL a ha d (by omega)
    rw [← add_assoc, hL.offset (a + d) (by omega) (by omega)]
    omega

theorem floor_le_self (η : ℝ) (hη : 0 ≤ η) (T : ℕ) : ⌊(1 - η) * (T : ℝ)⌋₊ ≤ T :=
  Nat.floor_le_of_le (by nlinarith [mul_nonneg hη (Nat.cast_nonneg (α := ℝ) T)])

theorem epochEnd_mid (n : ℕ) (η : ℝ) (k : ℕ) (hk : 1 ≤ k) (hkα : k < numTrees n) :
    epochEnd n η k = treeOffset n k + ⌊(1 - η) * (treeSize n k : ℝ)⌋₊ := by
  unfold epochEnd; rw [if_neg (by omega), if_neg (by omega)]

theorem epochOf_eq (n : ℕ) (η : ℝ) (c i : ℕ) (hi1 : 1 ≤ i) (hiα : i ≤ numTrees n)
    (hlt : c < epochEnd n η i) (hle : ∀ k, 1 ≤ k → k < i → epochEnd n η k ≤ c) :
    epochOf n η c = i := by
  obtain ⟨rest, hr⟩ := range_split (i - 1) (numTrees n) (by omega)
  unfold epochOf
  rw [hr, List.map_append, List.find?_append, List.find?_eq_none.2, Option.none_or,
    List.map_cons, List.find?_cons_of_pos]
  · simp only [Option.getD_some]; omega
  · simpa [show i - 1 + 1 = i by omega] using hlt
  · intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simpa using hle (k + 1) (by omega) (by omega)

/-! ## Phases as a function of the position in the epoch -/

/-- The phase of the insertion with `r` insertions already made in the epoch. -/
def pf (T h r : ℕ) : ℕ := if T ≤ 5 * r then h + 1 else min (h + 1) (T / (T - 5 * r))

/-- `⌈jT / (5(j+1))⌉`: the number of insertions of an epoch in phases `≤ j`. -/
def B (T k : ℕ) : ℕ := (k * T + 5 * (k + 1) - 1) / (5 * (k + 1))

theorem lt_B (T k r : ℕ) : r < B T k ↔ (k + 1) * (5 * r) < k * T := by
  unfold B
  rw [← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by positivity)]
  have e : (r + 1) * (5 * (k + 1)) = (k + 1) * (5 * r) + 5 * (k + 1) := by ring
  rw [e]
  generalize (k + 1) * (5 * r) = X
  generalize k * T = Y
  omega

theorem B_spec (T k : ℕ) :
    k * T ≤ (k + 1) * (5 * B T k) ∧ (k + 1) * (5 * B T k) < k * T + 5 * (k + 1) := by
  constructor
  · have := (lt_B T k (B T k)).not.1 (lt_irrefl _); omega
  · rcases Nat.eq_zero_or_pos (B T k) with h0 | h0
    · rw [h0, mul_zero, mul_zero]; omega
    · obtain ⟨b, hb⟩ : ∃ b, B T k = b + 1 := ⟨B T k - 1, by omega⟩
      have := (lt_B T k b).1 (by omega)
      rw [hb]; nlinarith

theorem div_le_iff' (T r j : ℕ) (hr : 5 * r < T) :
    T / (T - 5 * r) ≤ j ↔ (j + 1) * (5 * r) < j * T := by
  obtain ⟨s, rfl⟩ : ∃ s, T = s + 5 * r := ⟨T - 5 * r, by omega⟩
  rw [show s + 5 * r - 5 * r = s by omega, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by omega)]
  constructor <;> intro h <;> nlinarith

theorem pf_eq_iff (T h j r : ℕ) (hT : 0 < T) (hj : 1 ≤ j) (hjh : j ≤ h) :
    pf T h r = j ↔ B T (j - 1) ≤ r ∧ r < B T j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel, lt_B, ← not_lt, lt_B]
  unfold pf
  split_ifs with h5
  · constructor
    · intro; omega
    · rintro ⟨_, h2⟩; nlinarith
  · have e1 := div_le_iff' T r (k + 1) (by omega)
    have e2 := div_le_iff' T r k (by omega)
    generalize T / (T - 5 * r) = Q at e1 e2 ⊢
    rw [← e1, ← e2]
    omega

theorem count_bounds (T j : ℕ) (hj : 1 ≤ j) :
    T / (10 * j ^ 2) ≤ B T j - B T (j - 1) ∧
      ((B T j - B T (j - 1) : ℕ) : ℝ) ≤ (T : ℝ) / (5 * (j : ℝ) ^ 2) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  obtain ⟨a1, a2⟩ := B_spec T k
  obtain ⟨b1, b2⟩ := B_spec T (k + 1)
  generalize B T k = A at a1 a2 ⊢
  generalize B T (k + 1) = Bj at b1 b2 ⊢
  constructor
  · have hq : 10 * (k + 1) ^ 2 * (T / (10 * (k + 1) ^ 2)) ≤ T := Nat.mul_div_le T _
    generalize T / (10 * (k + 1) ^ 2) = q at hq ⊢
    by_contra hcon
    have hlt : Bj + 1 ≤ A + q := by omega
    have m1 : (k + 1) * (k + 2) * (5 * (Bj + 1)) ≤ (k + 1) * (k + 2) * (5 * (A + q)) :=
      Nat.mul_le_mul_left _ (by omega)
    have m2 : (k + 1) * ((k + 1) * T) ≤ (k + 1) * ((k + 1 + 1) * (5 * Bj)) :=
      Nat.mul_le_mul_left _ b1
    have m3 : (k + 2) * ((k + 1) * (5 * A)) < (k + 2) * (k * T + 5 * (k + 1)) :=
      mul_lt_mul_of_pos_left a2 (by omega)
    have m4 : 5 * (k + 1) * (k + 2) * q ≤ 10 * (k + 1) ^ 2 * q :=
      Nat.mul_le_mul_right _ (by nlinarith)
    nlinarith
  · rcases le_or_gt Bj A with hle | hlt
    · rw [Nat.sub_eq_zero_of_le hle, Nat.cast_zero]; positivity
    · rw [Nat.cast_sub hlt.le]
      have a1' : (k : ℝ) * T ≤ (k + 1) * (5 * A) := by exact_mod_cast a1
      have b2' : ((k : ℝ) + 1 + 1) * (5 * Bj) < (k + 1) * T + 5 * (k + 1 + 1) := by
        exact_mod_cast b2
      have hgt : (A : ℝ) + 1 ≤ Bj := by exact_mod_cast hlt
      push_cast
      have hpos : (0 : ℝ) < 5 * ((k : ℝ) + 1) ^ 2 := by positivity
      rw [div_add_one hpos.ne', le_div_iff₀ hpos]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [mul_lt_mul_of_pos_left b2' (by linarith : (0 : ℝ) < k + 1),
        mul_le_mul_of_nonneg_left a1' (by linarith : (0 : ℝ) ≤ k + 2),
        mul_nonneg (by linarith : (0 : ℝ) ≤ k + 1) (by linarith : (0 : ℝ) ≤ Bj - A - 1)]

/-! ## The lemma -/

theorem main_thm (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) (n : ℕ) (hn : 8 ≤ n) (i : ℕ)
    (hi2 : 2 ≤ i) (hiα : i ≤ numTrees n) :
    (∀ j : ℕ, 1 ≤ j → j ≤ height n (i - 1) →
      treeSize n (i - 1) / (10 * j ^ 2) ≤ phaseLength n η i j ∧
      (phaseLength n η i j : ℝ) ≤ (treeSize n (i - 1) : ℝ) / (5 * (j : ℝ) ^ 2) + 1) ∧
    treeSize n (i - 1) - ⌊(1 - η) * (treeSize n (i - 1) : ℝ)⌋₊ ≤
      phaseLength n η i (height n (i - 1) + 1) := by
  have hL := layout n hn
  have hT4 : 4 ≤ treeSize n (i - 1) := hL.min4 _ (by omega) (by omega)
  have hFle := floor_le_self η hη0.le (treeSize n (i - 1))
  have hE1 := epochEnd_mid n η (i - 1) (by omega) (by omega)
  have hoff := hL.offset (i - 1) (by omega) (by omega)
  rw [show i - 1 + 1 = i by omega] at hoff
  obtain ⟨X, hX5, hEi⟩ : ∃ X, treeSize n (i - 1) ≤ 5 * X ∧ epochEnd n η i =
      epochEnd n η (i - 1) + (treeSize n (i - 1) - ⌊(1 - η) * (treeSize n (i - 1) : ℝ)⌋₊) + X := by
    by_cases hia : i = numTrees n
    · refine ⟨treeSize n i, ?_, ?_⟩
      · have := hL.last (by omega); rw [← hia] at this; exact this
      · have htot := hL.total (by omega)
        rw [← hia] at htot
        have : epochEnd n η i = n := by unfold epochEnd; rw [if_neg (by omega), if_pos (by omega)]
        omega
    · refine ⟨⌊(1 - η) * (treeSize n i : ℝ)⌋₊, ?_, ?_⟩
      · have hr := hL.ratio i hi2 (by omega)
        have h4 := hL.min4 i (by omega) (by omega)
        have hfl := Nat.lt_floor_add_one ((1 - η) * (treeSize n i : ℝ))
        have h4' : (4 : ℝ) ≤ treeSize n i := by exact_mod_cast h4
        have : (2 * treeSize n i : ℝ) < 5 * ⌊(1 - η) * (treeSize n i : ℝ)⌋₊ + 1 := by
          nlinarith
        have : 2 * treeSize n i < 5 * ⌊(1 - η) * (treeSize n i : ℝ)⌋₊ + 1 := by
          exact_mod_cast this
        omega
      · rw [epochEnd_mid n η i (by omega) (by omega)]
        omega
  -- the phases
  have hphase : ∀ r, r < epochEnd n η i - epochEnd n η (i - 1) →
      phaseOf n η (epochEnd n η (i - 1) + r) = pf (treeSize n (i - 1)) (height n (i - 1)) r := by
    intro r hr
    have he : epochOf n η (epochEnd n η (i - 1) + r) = i := by
      apply epochOf_eq n η _ i (by omega) hiα (by omega)
      intro k hk1 hki
      rcases Nat.lt_or_ge k (i - 1) with hk | hk
      · have h1 := epochEnd_mid n η k hk1 (by omega)
        have h2 := floor_le_self η hη0.le (treeSize n k)
        have h3 := hL.offset k hk1 (by omega)
        have h4 := off_mono hL (k + 1) (by omega) (i - 1 - (k + 1)) (by omega)
        rw [show k + 1 + (i - 1 - (k + 1)) = i - 1 by omega] at h4
        omega
      · rw [show k = i - 1 by omega]; omega
    unfold phaseOf
    simp only [he, show ¬ i ≤ 1 by omega, if_false, ↓reduceIte, Nat.add_sub_cancel_left]
    rfl
  have hPL : ∀ j, phaseLength n η i j = ((Finset.range (epochEnd n η i - epochEnd n η (i - 1))).filter
      (fun r => pf (treeSize n (i - 1)) (height n (i - 1)) r = j)).card := by
    intro j
    unfold phaseLength
    rw [len_filter_range]
    congr 1
    apply Finset.filter_congr
    intro r hr
    rw [Finset.mem_range] at hr
    rw [decide_eq_true_eq, hphase r hr]
  constructor
  · intro j hj hjh
    have hset : (Finset.range (epochEnd n η i - epochEnd n η (i - 1))).filter
        (fun r => pf (treeSize n (i - 1)) (height n (i - 1)) r = j) =
        Finset.Ico (B (treeSize n (i - 1)) (j - 1)) (B (treeSize n (i - 1)) j) := by
      ext r
      rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
        pf_eq_iff _ _ _ _ (by omega) hj hjh]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        have := (lt_B _ _ _).1 h.2
        have h5 : 5 * r < treeSize n (i - 1) := by
          by_contra hc
          push_neg at hc
          nlinarith
        omega
    rw [hPL, hset, Nat.card_Ico]
    exact count_bounds _ j hj
  · rw [hPL]
    calc treeSize n (i - 1) - ⌊(1 - η) * (treeSize n (i - 1) : ℝ)⌋₊
        = (Finset.Ico X (epochEnd n η i - epochEnd n η (i - 1))).card := by
          rw [Nat.card_Ico]; omega
      _ ≤ _ := by
          apply Finset.card_le_card
          intro r hr
          rw [Finset.mem_Ico] at hr
          rw [Finset.mem_filter, Finset.mem_range]
          refine ⟨hr.2, ?_⟩
          unfold pf
          rw [if_pos (by omega)]

end SolIncrOpenAddrL21

open IncrOpenAddr.NoTradeoff in
theorem solution :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ n : ℕ, 8 ≤ n → ∀ i : ℕ, 2 ≤ i → i ≤ numTrees n →
        (∀ j : ℕ, 1 ≤ j → j ≤ height n (i - 1) →
          treeSize n (i - 1) / (10 * j ^ 2) ≤ phaseLength n η i j ∧
          (phaseLength n η i j : ℝ) ≤ (treeSize n (i - 1) : ℝ) / (5 * (j : ℝ) ^ 2) + 1) ∧
        treeSize n (i - 1) - ⌊(1 - η) * (treeSize n (i - 1) : ℝ)⌋₊ ≤
          phaseLength n η i (height n (i - 1) + 1) :=
  ⟨1 / 10, by norm_num, fun η hη0 hη1 n hn i hi2 hiα =>
    SolIncrOpenAddrL21.main_thm η hη0 hη1 n hn i hi2 hiα⟩
