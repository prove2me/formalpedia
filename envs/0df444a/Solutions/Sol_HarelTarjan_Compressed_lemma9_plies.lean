-- Prove2me | solution 1 for HarelTarjan.Compressed.lemma9_plies
-- status  : ACCEPTED   (prove)
-- author  : @walker
-- created : 2026-09-28T07:16:50.09416+00:00
-- url     : https://prove2.me/submissions/ba901202-1b83-4d74-a3c9-53e74b55d25c

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree
import Definitions.Def_HarelTarjan_Compressed_HeavyPath
import Definitions.Def_HarelTarjan_Compressed_CompressedTree
import Definitions.Def_HarelTarjan_Compressed_Plies
import Theorems.Thm_HarelTarjan_Compressed_lemma6_sizeC_doubles
import Theorems.Thm_HarelTarjan_Compressed_rank_ge_count

open HarelTarjan.Compressed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Local helpers

Two groups: the order theory of `size_C` along the `C`-parent chain (needed for the "ply one is
closed under `C`-descendants" clause), and the arithmetic bridging `Nat.log` to `Real.logb`. -/

/-! #### `size_C` is monotone downwards in `C` -/

lemma p2m_pC_root (T : RootedTree V) : pC T T.root = T.root := by
  rw [pC, if_pos rfl]

lemma p2m_sizeC_le_pC (T : RootedTree V) (x : V) : sizeC T x ≤ sizeC T (pC T x) := by
  by_cases hx : x = T.root
  · rw [hx, p2m_pC_root]
  · have h := lemma6_sizeC_doubles T x hx
    omega

lemma p2m_sizeC_iterate_le (T : RootedTree V) (x : V) (k : ℕ) :
    sizeC T x ≤ sizeC T ((pC T)^[k] x) := by
  induction k with
  | zero => simp
  | succ j ih =>
    calc sizeC T x ≤ sizeC T ((pC T)^[j] x) := ih
      _ ≤ sizeC T (pC T ((pC T)^[j] x)) := p2m_sizeC_le_pC T _
      _ = sizeC T ((pC T)^[j + 1] x) := by rw [Function.iterate_succ_apply']

/-- A `C`-ancestor has no larger rank. -/
lemma p2m_rank_le_of_isAncestorC (T : RootedTree V) {v u : V} (h : IsAncestorC T v u) :
    rank T u ≤ rank T v := by
  obtain ⟨i, hi⟩ := h
  have hs : sizeC T u ≤ sizeC T v := by
    rw [← hi]
    exact p2m_sizeC_iterate_le T u i
  exact Nat.log_mono_right hs

lemma p2m_sizeC_pos (T : RootedTree V) (v : V) : sizeC T v ≠ 0 := by
  classical
  intro h0
  have hmem : v ∈ Finset.univ.filter (fun u => IsAncestorC T v u) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨0, by simp⟩
  have : 0 < sizeC T v := Finset.card_pos.mpr ⟨v, hmem⟩
  omega

/-! #### Bridging `Nat.log` and `Real.logb` -/

lemma p2m_L2_eq (N : ℕ) : L2 N = Nat.log 2 (Nat.log 2 N) := rfl

lemma p2m_L3_eq (N : ℕ) : L3 N = Nat.log 2 (Nat.log 2 (Nat.log 2 N)) := rfl

/-- `2 ^ (n + 1) = 2 * 2 ^ n` over the naturals. -/
lemma p2m_nat_pow_succ (n : ℕ) : 2 ^ (n + 1) = 2 ^ n * 2 := by
  rw [pow_succ']
  ring

/-- `2 ^ (n + 1) = 2 ^ n * 2` over the reals, with the exponent written as a real. -/
lemma p2m_rpow_succ_cast (n : ℕ) :
    (2 : ℝ) ^ ((n : ℝ) + 1) = (2 : ℝ) ^ n * 2 := by
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, Real.rpow_natCast]

/-- `Nat.log 2 N ≤ Real.logb 2 N` for `N > 0`. -/
lemma p2m_natLog_le_logb (N : ℕ) (hN : 0 < N) :
    (Nat.log 2 N : ℝ) ≤ Real.logb 2 (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  refine (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2)
    hNpos).mpr ?_
  rw [Real.rpow_natCast]
  exact_mod_cast (Nat.pow_log_le_self 2 hN.ne')

/-- **Key arithmetic bound (ply three).** For `N ≥ 4`, `lg N ≤ 2 · 2 ^ ⌊lg ⌊lg N⌋⌋`. -/
lemma p2m_logb_le_two_mul_pow_L2 (N : ℕ) (hN : 4 ≤ N) :
    Real.logb 2 (N : ℝ) ≤ (2 : ℝ) ^ L2 N * 2 := by
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  -- `N < 2 ^ (⌊lg N⌋ + 1)`
  have hsucc : N < 2 ^ (Nat.log 2 N + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
    rwa [Nat.succ_eq_add_one] at h
  have ha_lt : N < 2 ^ Nat.log 2 N * 2 := by
    rw [p2m_nat_pow_succ] at hsucc
    exact hsucc
  have h1 : Real.logb 2 (N : ℝ) < (Nat.log 2 N : ℝ) + 1 := by
    refine (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ) < 2)
      hNpos).mpr ?_
    rw [p2m_rpow_succ_cast]
    exact_mod_cast ha_lt
  -- `⌊lg N⌋ + 1 ≤ 2 ^ ⌊lg ⌊lg N⌋⌋ * 2`
  have hb_lt : Nat.log 2 N < 2 ^ L2 N * 2 := by
    rw [p2m_L2_eq]
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (Nat.log 2 N)
    rw [Nat.succ_eq_add_one, p2m_nat_pow_succ] at h
    exact h
  have h2 : (Nat.log 2 N : ℝ) + 1 ≤ (2 : ℝ) ^ L2 N * 2 := by
    have : Nat.log 2 N + 1 ≤ 2 ^ L2 N * 2 := by omega
    exact_mod_cast this
  linarith

/-- **Key arithmetic bound (ply two).** For `N ≥ 4`, `lg lg N ≤ 2 · 2 ^ ⌊lg ⌊lg ⌊lg N⌋⌋⌋`. -/
lemma p2m_logb_logb_le_two_mul_pow_L3 (N : ℕ) (hN : 4 ≤ N) :
    Real.logb 2 (Real.logb 2 (N : ℝ)) ≤ (2 : ℝ) ^ L3 N * 2 := by
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hlogNpos : 0 < Real.logb 2 (N : ℝ) :=
    Real.logb_pos (by norm_num : (1:ℝ) < 2)
      (by exact_mod_cast (by omega : 1 < N))
  have hsucc : N < 2 ^ (Nat.log 2 N + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
    rwa [Nat.succ_eq_add_one] at h
  have ha_lt : N < 2 ^ Nat.log 2 N * 2 := by
    rw [p2m_nat_pow_succ] at hsucc
    exact hsucc
  have h1 : Real.logb 2 (N : ℝ) < (Nat.log 2 N : ℝ) + 1 := by
    refine (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ) < 2)
      hNpos).mpr ?_
    rw [p2m_rpow_succ_cast]
    exact_mod_cast ha_lt
  have hb_lt : Nat.log 2 N < 2 ^ L2 N * 2 := by
    rw [p2m_L2_eq]
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (Nat.log 2 N)
    rw [Nat.succ_eq_add_one, p2m_nat_pow_succ] at h
    exact h
  have h2 : (Nat.log 2 N : ℝ) + 1 ≤ (2 : ℝ) ^ L2 N * 2 := by
    have : Nat.log 2 N + 1 ≤ 2 ^ L2 N * 2 := by omega
    exact_mod_cast this
  have h3 : Real.logb 2 (N : ℝ) < (2 : ℝ) ^ ((L2 N : ℝ) + 1) := by
    rw [p2m_rpow_succ_cast]
    linarith
  have h4 : Real.logb 2 (Real.logb 2 (N : ℝ)) < (L2 N : ℝ) + 1 :=
    (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ) < 2)
      hlogNpos).mpr h3
  have h5 : (L2 N : ℝ) + 1 ≤ (2 : ℝ) ^ L3 N * 2 := by
    rw [p2m_L3_eq]
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (Nat.log 2 (Nat.log 2 N))
    rw [Nat.succ_eq_add_one, p2m_nat_pow_succ] at h
    have : Nat.log 2 (Nat.log 2 N) + 1 ≤ 2 ^ Nat.log 2 (Nat.log 2 (Nat.log 2 N)) * 2 := by
      omega
    exact_mod_cast this
  linarith

/-- **Key arithmetic bound (ply one).** For `N ≥ 4`, `2 ^ ⌊lg ⌊lg ⌊lg N⌋⌋⌋ ≤ lg lg N`. -/
lemma p2m_pow_L3_le_logb_logb (N : ℕ) (hN : 4 ≤ N) :
    (2 : ℝ) ^ L3 N ≤ Real.logb 2 (Real.logb 2 (N : ℝ)) := by
  have hN2 : 2 ≤ N := by omega
  have ha2 : 2 ≤ Nat.log 2 N :=
    Nat.le_log_of_pow_le (by norm_num : 1 < (2:ℕ)) (by omega : 2 ^ 2 ≤ N)
  have hb0 : 0 < Nat.log 2 (Nat.log 2 N) := Nat.log_pos (by norm_num) ha2
  have ha0 : 0 < Nat.log 2 N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlogNpos : 0 < Real.logb 2 (N : ℝ) :=
    Real.logb_pos (by norm_num : (1:ℝ) < 2)
      (by exact_mod_cast (by omega : 1 < N))
  -- `2 ^ ⌊lg ⌊lg N⌋⌋ ≤ ⌊lg N⌋`
  have h1 : 2 ^ L3 N ≤ Nat.log 2 (Nat.log 2 N) := by
    rw [p2m_L3_eq]
    exact Nat.pow_log_le_self 2 hb0.ne'
  -- `⌊lg ⌊lg N⌋⌋ ≤ lg ⌊lg N⌋`
  have h2 : (Nat.log 2 (Nat.log 2 N) : ℝ) ≤ Real.logb 2 (Nat.log 2 N : ℝ) :=
    p2m_natLog_le_logb (Nat.log 2 N) ha0
  -- `⌊lg N⌋ ≤ lg N`
  have h3 : (Nat.log 2 N : ℝ) ≤ Real.logb 2 (N : ℝ) := p2m_natLog_le_logb N (by omega)
  -- `lg ⌊lg N⌋ ≤ lg lg N`
  have h4 : Real.logb 2 (Nat.log 2 N : ℝ) ≤ Real.logb 2 (Real.logb 2 (N : ℝ)) := by
    have hpos : 0 < (Nat.log 2 N : ℝ) := by exact_mod_cast ha0
    have := (Real.logb_le_logb (b := 2) (by norm_num : (1:ℝ) < 2)
      hpos hlogNpos).mpr h3
    exact this
  have h5 : (2 : ℝ) ^ L3 N ≤ (Nat.log 2 (Nat.log 2 N) : ℝ) := by exact_mod_cast h1
  linarith

/-! ### Lemma 9 -/

/-- **Lemma 9** (Harel–Tarjan, §4, p. 345, explicit constants). The compressed tree `C` splits
into three plies by rank: ply three has at most `4n / lg n` vertices, ply two at most
`4n / lg lg n`, and ply one is closed under `C`-descendants with `size_C ≤ lg lg n`. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (hn : 4 ≤ Fintype.card V) :
    ((ply3 T).card : ℝ) ≤ 4 * (Fintype.card V : ℝ) / Real.logb 2 (Fintype.card V) ∧
    ((ply2 T).card : ℝ) ≤
      4 * (Fintype.card V : ℝ) / Real.logb 2 (Real.logb 2 (Fintype.card V)) ∧
    ∀ v ∈ ply1 T,
      (∀ u : V, IsAncestorC T v u → u ∈ ply1 T) ∧
      (sizeC T v : ℝ) ≤ Real.logb 2 (Real.logb 2 (Fintype.card V)) := by
  classical
  set N : ℕ := Fintype.card V with hN
  have hN4 : 4 ≤ N := by rw [hN]; exact hn
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  refine ⟨?_, ?_, ?_⟩
  · -- Ply three: `|ply3| · 2 ^ L2 N ≤ 2n` and `lg n ≤ 2 · 2 ^ L2 N`.
    have h3 : (ply3 T).card * 2 ^ L2 N ≤ 2 * N := by
      have h := rank_ge_count T (L2 N)
      rw [← hN] at h
      simpa only [ply3] using h
    have hPpos : 0 < (2 : ℝ) ^ L2 N := by positivity
    have hLpos : 0 < Real.logb 2 (N : ℝ) :=
      Real.logb_pos (by norm_num : (1:ℝ) < 2)
        (by exact_mod_cast (by omega : 1 < N))
    have hcrux : Real.logb 2 (N : ℝ) ≤ (2 : ℝ) ^ L2 N * 2 :=
      p2m_logb_le_two_mul_pow_L2 N hN4
    have h3r : ((ply3 T).card : ℝ) * (2 : ℝ) ^ L2 N ≤ 2 * (N : ℝ) := by
      exact_mod_cast h3
    have hA : ((ply3 T).card : ℝ) ≤ 2 * (N : ℝ) / (2 : ℝ) ^ L2 N :=
      (le_div_iff₀ hPpos).mpr h3r
    have hB : 2 * (N : ℝ) / (2 : ℝ) ^ L2 N ≤
        4 * (N : ℝ) / Real.logb 2 (N : ℝ) := by
      rw [div_le_div_iff₀ hPpos hLpos]
      nlinarith [hcrux, hNpos]
    linarith
  · -- Ply two: `ply2 ⊆ {rank ≥ L3 N}` and `lg lg n ≤ 2 · 2 ^ L3 N`.
    have h4 : (Finset.univ.filter (fun v => L3 N ≤ rank T v)).card * 2 ^ L3 N ≤ 2 * N := by
      have h := rank_ge_count T (L3 N)
      rw [← hN] at h
      exact h
    have hsub : ply2 T ⊆ Finset.univ.filter (fun v => L3 N ≤ rank T v) := by
      intro v hv
      rw [ply2, Finset.mem_filter] at hv
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ v, hv.2.1⟩
    have hcard : (ply2 T).card ≤ (Finset.univ.filter (fun v => L3 N ≤ rank T v)).card :=
      Finset.card_le_card hsub
    have hPpos : 0 < (2 : ℝ) ^ L3 N := by positivity
    have hlogNgt1 : 1 < Real.logb 2 (N : ℝ) := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num : (1:ℝ) < 2)
        hNpos, Real.rpow_one]
      exact_mod_cast (by omega : 2 < N)
    have hLpos : 0 < Real.logb 2 (Real.logb 2 (N : ℝ)) :=
      Real.logb_pos (by norm_num : (1:ℝ) < 2) hlogNgt1
    have hcrux : Real.logb 2 (Real.logb 2 (N : ℝ)) ≤ (2 : ℝ) ^ L3 N * 2 :=
      p2m_logb_logb_le_two_mul_pow_L3 N hN4
    have h4r : ((Finset.univ.filter (fun v => L3 N ≤ rank T v)).card : ℝ) * (2 : ℝ) ^ L3 N
        ≤ 2 * (N : ℝ) := by
      exact_mod_cast h4
    have hA : ((Finset.univ.filter (fun v => L3 N ≤ rank T v)).card : ℝ) ≤
        2 * (N : ℝ) / (2 : ℝ) ^ L3 N :=
      (le_div_iff₀ hPpos).mpr h4r
    have hB : 2 * (N : ℝ) / (2 : ℝ) ^ L3 N ≤
        4 * (N : ℝ) / Real.logb 2 (Real.logb 2 (N : ℝ)) := by
      rw [div_le_div_iff₀ hPpos hLpos]
      nlinarith [hcrux, hNpos]
    have hcast : ((ply2 T).card : ℝ) ≤
        ((Finset.univ.filter (fun v => L3 N ≤ rank T v)).card : ℝ) := by
      exact_mod_cast hcard
    linarith
  · -- Ply one: closed under `C`-descendants, and `size_C ≤ lg lg n`.
    intro v hv1
    have hv : rank T v < L3 N := by
      rw [ply1, Finset.mem_filter] at hv1
      exact hv1.2
    constructor
    · intro u hu
      rw [ply1, Finset.mem_filter]
      exact ⟨Finset.mem_univ u, lt_of_le_of_lt (p2m_rank_le_of_isAncestorC T hu) hv⟩
    · have hsz : sizeC T v ≠ 0 := p2m_sizeC_pos T v
      have hlt : sizeC T v < 2 ^ L3 N :=
        (Nat.log_lt_iff_lt_pow (by norm_num : 1 < (2:ℕ)) hsz).mp hv
      have hcast : (sizeC T v : ℝ) < (2 : ℝ) ^ L3 N := by exact_mod_cast hlt
      exact le_trans hcast.le (p2m_pow_L3_le_logb_logb N hN4)
