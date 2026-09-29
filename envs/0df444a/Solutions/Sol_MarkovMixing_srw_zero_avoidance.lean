-- Prove2me | solution 1 for MarkovMixing.srw_zero_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-22T22:37:45.2745+00:00
-- url     : https://prove2.me/submissions/e9aa33b3-37a9-4772-a680-47c74d6ec33f

import Definitions.Def_mm_classical
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Theorems.Thm_MarkovMixing_reflection_principle

/-!
# Zero avoidance for simple random walk (LPW Theorem 2.17)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

/-- `(3m+1)·C(2m,m)² ≤ 16^m`. -/
private lemma central_sq (m : ℕ) :
    (3 * m + 1) * (Nat.centralBinom m) ^ 2 ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ p ih =>
      have hkey := Nat.succ_mul_centralBinom_succ p
      have hpos : 0 < (p + 1) ^ 2 * (3 * p + 1) := by positivity
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      have h1 : (3 * (p + 1) + 1) * (Nat.centralBinom (p + 1)) ^ 2
            * ((p + 1) ^ 2 * (3 * p + 1))
          = (3 * p + 4) * ((p + 1) * Nat.centralBinom (p + 1)) ^ 2 * (3 * p + 1) := by
        ring
      rw [h1, hkey]
      have h2 : (3 * p + 4) * (2 * (2 * p + 1) * Nat.centralBinom p) ^ 2 * (3 * p + 1)
          = ((3 * p + 4) * 4 * (2 * p + 1) ^ 2)
            * ((3 * p + 1) * (Nat.centralBinom p) ^ 2) := by ring
      rw [h2]
      have hstep : (3 * p + 4) * 4 * (2 * p + 1) ^ 2
          ≤ 16 * ((p + 1) ^ 2 * (3 * p + 1)) := by nlinarith
      calc ((3 * p + 4) * 4 * (2 * p + 1) ^ 2)
              * ((3 * p + 1) * (Nat.centralBinom p) ^ 2)
          ≤ ((3 * p + 4) * 4 * (2 * p + 1) ^ 2) * 16 ^ p :=
            Nat.mul_le_mul_left _ ih
        _ ≤ (16 * ((p + 1) ^ 2 * (3 * p + 1))) * 16 ^ p :=
            Nat.mul_le_mul_right _ hstep
        _ = 16 ^ (p + 1) * ((p + 1) ^ 2 * (3 * p + 1)) := by ring

/-- `2·C(2m+1,m) = C(2m+2,m+1)`. -/
private lemma two_mul_choose_odd (m : ℕ) :
    2 * (2 * m + 1).choose m = Nat.centralBinom (m + 1) := by
  have hsym : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
    have h : (2 * m + 1).choose (2 * m + 1 - (m + 1)) = (2 * m + 1).choose (m + 1) :=
      Nat.choose_symm (by omega)
    have h2 : 2 * m + 1 - (m + 1) = m := by omega
    rw [h2] at h
    exact h.symm
  have hpas : (2 * m + 2).choose (m + 1) = (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) :=
    Nat.choose_succ_succ (2 * m + 1) m
  have hc : Nat.centralBinom (m + 1) = (2 * m + 2).choose (m + 1) := by
    have hmm : 2 * (m + 1) = 2 * m + 2 := by ring
    rw [Nat.centralBinom_eq_two_mul_choose, hmm]
  rw [hc, hpas, hsym]
  ring

/-- `r · C(r, ⌊r/2⌋)² ≤ 4^r`. -/
private lemma middle_sq (r : ℕ) : r * (r.choose (r / 2)) ^ 2 ≤ 4 ^ r := by
  rcases Nat.even_or_odd r with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have hdiv : (m + m) / 2 = m := by omega
    have hcb : (m + m).choose ((m + m) / 2) = Nat.centralBinom m := by
      have h2m : 2 * m = m + m := by ring
      rw [hdiv, Nat.centralBinom_eq_two_mul_choose, h2m]
    rw [hcb]
    calc (m + m) * (Nat.centralBinom m) ^ 2
        ≤ (3 * m + 1) * (Nat.centralBinom m) ^ 2 :=
          Nat.mul_le_mul_right _ (by omega)
      _ ≤ 16 ^ m := central_sq m
      _ = 4 ^ (m + m) := by
          rw [pow_add 4 m m, ← Nat.mul_pow]
  · subst hm
    have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]
    have hfour : (4 : ℕ) * ((2 * m + 1) * ((2 * m + 1).choose m) ^ 2)
        = (2 * m + 1) * (2 * (2 * m + 1).choose m) ^ 2 := by ring
    have hbound : (2 * m + 1) * (2 * (2 * m + 1).choose m) ^ 2 ≤ 16 * 16 ^ m := by
      rw [two_mul_choose_odd m]
      calc (2 * m + 1) * (Nat.centralBinom (m + 1)) ^ 2
          ≤ (3 * (m + 1) + 1) * (Nat.centralBinom (m + 1)) ^ 2 :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 16 ^ (m + 1) := central_sq (m + 1)
        _ = 16 * 16 ^ m := by rw [pow_succ]; ring
    have hpow : (4 : ℕ) * 4 ^ (2 * m + 1) = 16 * 16 ^ m := by
      have h16 : (4 : ℕ) ^ (2 * m) = 16 ^ m := by rw [pow_mul]; norm_num
      rw [pow_succ, ← h16]
      ring
    have h4 : (4 : ℕ) * ((2 * m + 1) * ((2 * m + 1).choose m) ^ 2)
        ≤ 4 * 4 ^ (2 * m + 1) := by
      rw [hfour, hpow]
      exact hbound
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)

/-- The number of `+1` steps in a sign sequence. -/
private def cnt {r : ℕ} (ω : Fin r → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin r => ω i = true).card

private lemma pos_last {r : ℕ} (k : ℤ) (ω : Fin r → Bool) :
    srwPos k ω r = k + 2 * (cnt ω : ℤ) - r := by
  classical
  simp only [srwPos]
  have h1 : ∀ i : Fin r, (if (i : ℕ) < r then (if ω i then (1 : ℤ) else -1) else 0)
      = 2 * (if ω i = true then (1 : ℤ) else 0) - 1 := by
    intro i
    rw [if_pos i.isLt]
    cases h : ω i <;> simp [h]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h2 : ∑ i : Fin r, (if ω i = true then (1 : ℤ) else 0) = (cnt ω : ℤ) := by
    simp [cnt, Finset.sum_boole]
  rw [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- Each level set of the endpoint has at most `C(r, ⌊r/2⌋)` elements. -/
private lemma card_level_le {r : ℕ} (k j : ℤ) :
    (Finset.univ.filter fun ω : Fin r → Bool => srwPos k ω r = j).card
      ≤ r.choose (r / 2) := by
  classical
  by_cases hne : (Finset.univ.filter fun ω : Fin r → Bool => srwPos k ω r = j).Nonempty
  · obtain ⟨ω₀, hω₀⟩ := hne
    rw [Finset.mem_filter] at hω₀
    obtain ⟨-, hval⟩ := hω₀
    have hM : ∀ ω : Fin r → Bool, srwPos k ω r = j → cnt ω = cnt ω₀ := by
      intro ω hω
      have h1 := pos_last k ω
      have h2 := pos_last k ω₀
      rw [hω] at h1
      rw [hval] at h2
      have : (cnt ω : ℤ) = (cnt ω₀ : ℤ) := by omega
      exact_mod_cast this
    have hkey : ∀ (u v : Fin r → Bool) (i : Fin r),
        (Finset.univ.filter fun i : Fin r => u i = true)
          = (Finset.univ.filter fun i : Fin r => v i = true) →
        u i = true → v i = true := by
      intro u v i huv hu
      have hmem : i ∈ Finset.univ.filter fun i : Fin r => u i = true := by simp [hu]
      rw [huv] at hmem
      simpa using hmem
    have hinj : Set.InjOn (fun ω : Fin r → Bool =>
        Finset.univ.filter fun i : Fin r => ω i = true)
        ↑(Finset.univ.filter fun ω : Fin r → Bool => srwPos k ω r = j) := by
      intro a _ b _ hab
      have hab' : (Finset.univ.filter fun i : Fin r => a i = true)
          = (Finset.univ.filter fun i : Fin r => b i = true) := hab
      funext i
      cases hA : a i
      · cases hB : b i
        · rfl
        · exact absurd (hkey b a i hab'.symm hB) (by rw [hA]; simp)
      · cases hB : b i
        · exact absurd (hkey a b i hab' hA) (by rw [hB]; simp)
        · rfl
    have hmaps : ∀ ω ∈ (Finset.univ.filter fun ω : Fin r → Bool => srwPos k ω r = j),
        (Finset.univ.filter fun i : Fin r => ω i = true)
          ∈ Finset.powersetCard (cnt ω₀) (Finset.univ : Finset (Fin r)) := by
      intro ω hω
      rw [Finset.mem_filter] at hω
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.filter_subset _ _, hM ω hω.2⟩
    calc (Finset.univ.filter fun ω : Fin r → Bool => srwPos k ω r = j).card
        ≤ (Finset.powersetCard (cnt ω₀) (Finset.univ : Finset (Fin r))).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = r.choose (cnt ω₀) := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      _ ≤ r.choose (r / 2) := Nat.choose_le_middle _ _
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

private lemma pos_zero {r : ℕ} (k : ℤ) (ω : Fin r → Bool) : srwPos k ω 0 = k := by
  simp [srwPos]

private lemma pos_step {r : ℕ} (k : ℤ) (ω : Fin r → Bool) (t : ℕ) (ht : t < r) :
    srwPos k ω (t + 1)
      = srwPos k ω t + (if ω ⟨t, ht⟩ = true then (1 : ℤ) else -1) := by
  classical
  simp only [srwPos]
  have h : ∀ i : Fin r,
      (if (i : ℕ) < t + 1 then (if ω i = true then (1 : ℤ) else -1) else 0)
        = (if (i : ℕ) < t then (if ω i = true then (1 : ℤ) else -1) else 0)
          + (if i = (⟨t, ht⟩ : Fin r) then (if ω i = true then (1 : ℤ) else -1)
              else 0) := by
    intro i
    by_cases hi : (i : ℕ) < t
    · have hne : i ≠ (⟨t, ht⟩ : Fin r) := by
        intro hh; rw [hh] at hi; simp at hi
      rw [if_pos (by omega), if_pos hi, if_neg hne, add_zero]
    · by_cases hi2 : (i : ℕ) = t
      · have heq : i = (⟨t, ht⟩ : Fin r) := Fin.ext hi2
        rw [if_pos (by omega), if_neg hi, if_pos heq, zero_add]
      · have hne : i ≠ (⟨t, ht⟩ : Fin r) := by
          intro hh; rw [hh] at hi2; simp at hi2
        rw [if_neg (by omega), if_neg hi, if_neg hne, add_zero]
  have hsingle : (∑ i : Fin r,
      if i = (⟨t, ht⟩ : Fin r) then (if ω i = true then (1 : ℤ) else -1) else 0)
      = (if ω ⟨t, ht⟩ = true then (1 : ℤ) else -1) := by
    rw [Finset.sum_eq_single (⟨t, ht⟩ : Fin r)]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, hsingle]
  ring

private lemma cross_zero {r : ℕ} (k : ℤ) (hk : 0 < k) (ω : Fin r → Bool)
    (hneg : srwPos k ω r < 0) : ∃ t ≤ r, srwPos k ω t = 0 := by
  classical
  obtain ⟨T, hTdef⟩ : ∃ T : Finset ℕ,
      T = (Finset.range (r + 1)).filter (fun t => srwPos k ω t ≤ 0) := ⟨_, rfl⟩
  have hmemT : ∀ t : ℕ, t ∈ T ↔ (t < r + 1 ∧ srwPos k ω t ≤ 0) := by
    intro t; rw [hTdef, Finset.mem_filter, Finset.mem_range]
  have hne : T.Nonempty := ⟨r, (hmemT r).mpr ⟨by omega, by omega⟩⟩
  obtain ⟨ht0r, ht0le⟩ := (hmemT _).mp (T.min'_mem hne)
  have ht0ne : T.min' hne ≠ 0 := by
    intro h
    rw [h, pos_zero] at ht0le
    omega
  obtain ⟨u, hu⟩ : ∃ u, T.min' hne = u + 1 := ⟨T.min' hne - 1, by omega⟩
  have hur : u < r := by omega
  have hupos : 0 < srwPos k ω u := by
    by_contra hc
    have hmem : u ∈ T := (hmemT u).mpr ⟨by omega, by omega⟩
    have := T.min'_le u hmem
    omega
  have hstep := pos_step k ω u hur
  have hsgn : (if ω ⟨u, hur⟩ = true then (1 : ℤ) else -1) = 1
      ∨ (if ω ⟨u, hur⟩ = true then (1 : ℤ) else -1) = -1 := by
    by_cases h : ω ⟨u, hur⟩ = true
    · exact Or.inl (by rw [if_pos h])
    · exact Or.inr (by rw [if_neg h])
  rw [hu, hstep] at ht0le
  refine ⟨u + 1, by omega, ?_⟩
  rw [hstep]
  omega

private lemma cnt_flip {r : ℕ} (ω : Fin r → Bool) :
    cnt (fun i => !(ω i)) + cnt ω = r := by
  classical
  have hset : (Finset.univ.filter fun i : Fin r => (!(ω i)) = true)
      = Finset.univ.filter fun i : Fin r => ¬(ω i = true) := by
    ext i; simp
  simp only [cnt, hset]
  rw [Nat.add_comm]
  have := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin r))) (fun i => ω i = true)
  rw [this, Finset.card_univ, Fintype.card_fin]

private lemma pos_flip {r : ℕ} (k : ℤ) (ω : Fin r → Bool) :
    srwPos k (fun i => !(ω i)) r = 2 * k - srwPos k ω r := by
  rw [pos_last, pos_last]
  have h := cnt_flip ω
  have h2 : (cnt (fun i => !(ω i)) : ℤ) + (cnt ω : ℤ) = (r : ℤ) := by exact_mod_cast h
  omega

private lemma neg_card_eq_big {r : ℕ} (k : ℤ) :
    (Finset.univ.filter fun ω : Fin r → Bool => srwPos k ω r < 0).card
      = (Finset.univ.filter fun ω : Fin r → Bool => 2 * k < srwPos k ω r).card := by
  classical
  refine Finset.card_nbij' (fun ω => fun i => !(ω i)) (fun ω => fun i => !(ω i))
    ?_ ?_ ?_ ?_
  · intro ω hω
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hω ⊢
    rw [pos_flip]; omega
  · intro ω hω
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hω ⊢
    rw [pos_flip]; omega
  · intro ω _; funext i; simp
  · intro ω _; funext i; simp

end

end MarkovMixing

open MarkovMixing

/-- **Theorem 2.17** (LPW): zero avoidance for simple random walk. -/
theorem solution (r : ℕ) (hr : 0 < r) (k : ℤ) (hk : 0 < k) :
    ((Finset.univ.filter fun ω : Fin r → Bool =>
        ∀ t ≤ r, srwPos k ω t ≠ 0).card : ℝ) / 2 ^ r ≤
      12 * (k : ℝ) / Real.sqrt r := by
  classical
  -- the avoidance event is "ends positive, never hit zero earlier"
  have hA : (Finset.univ.filter fun ω : Fin r → Bool => ∀ t ≤ r, srwPos k ω t ≠ 0)
      = (Finset.univ.filter fun ω : Fin r → Bool => 0 < srwPos k ω r)
        \ (Finset.univ.filter fun ω : Fin r → Bool =>
            (∃ s < r, srwPos k ω s = 0) ∧ 0 < srwPos k ω r) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro h
      have hpos : 0 < srwPos k ω r := by
        rcases lt_trichotomy (srwPos k ω r) 0 with hlt | heq | hgt
        · obtain ⟨t, htr, ht0⟩ := cross_zero k hk ω hlt
          exact absurd ht0 (h t htr)
        · exact absurd heq (h r le_rfl)
        · exact hgt
      exact ⟨hpos, fun hc => absurd hc.1.choose_spec.2 (h _ (le_of_lt hc.1.choose_spec.1))⟩
    · rintro ⟨hpos, hnot⟩ t htr h0
      rcases lt_or_eq_of_le htr with hlt | heq
      · exact hnot ⟨⟨t, hlt, h0⟩, hpos⟩
      · rw [heq] at h0; omega
  have hsub : (Finset.univ.filter fun ω : Fin r → Bool =>
        (∃ s < r, srwPos k ω s = 0) ∧ 0 < srwPos k ω r)
      ⊆ Finset.univ.filter fun ω : Fin r → Bool => 0 < srwPos k ω r := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact hω.2
  have hbigsub : (Finset.univ.filter fun ω : Fin r → Bool => 2 * k < srwPos k ω r)
      ⊆ Finset.univ.filter fun ω : Fin r → Bool => 0 < srwPos k ω r := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    omega
  have hMid : (Finset.univ.filter fun ω : Fin r → Bool =>
        0 < srwPos k ω r ∧ srwPos k ω r ≤ 2 * k)
      = (Finset.univ.filter fun ω : Fin r → Bool => 0 < srwPos k ω r)
        \ (Finset.univ.filter fun ω : Fin r → Bool => 2 * k < srwPos k ω r) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  have hrefl := (reflection_principle r k 1 hk (by norm_num)).2
  have hAeq : (Finset.univ.filter fun ω : Fin r → Bool =>
        ∀ t ≤ r, srwPos k ω t ≠ 0).card
      = (Finset.univ.filter fun ω : Fin r → Bool =>
        0 < srwPos k ω r ∧ srwPos k ω r ≤ 2 * k).card := by
    rw [hA, Finset.card_sdiff_of_subset hsub, hMid,
      Finset.card_sdiff_of_subset hbigsub, hrefl,
      neg_card_eq_big k]
  -- the middle band has at most `2k` levels, each of size at most `C(r,⌊r/2⌋)`
  have hMidbound : (Finset.univ.filter fun ω : Fin r → Bool =>
        0 < srwPos k ω r ∧ srwPos k ω r ≤ 2 * k).card
      ≤ (2 * k).toNat * r.choose (r / 2) := by
    have hmaps : Set.MapsTo (fun ω : Fin r → Bool => srwPos k ω r)
        ((Finset.univ.filter fun ω : Fin r → Bool =>
          0 < srwPos k ω r ∧ srwPos k ω r ≤ 2 * k : Finset (Fin r → Bool)) :
          Set (Fin r → Bool))
        ((Finset.Icc (1 : ℤ) (2 * k) : Finset ℤ) : Set ℤ) := by
      intro ω hω
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hω
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc ∑ j ∈ Finset.Icc (1 : ℤ) (2 * k),
            ((Finset.univ.filter fun ω : Fin r → Bool =>
              0 < srwPos k ω r ∧ srwPos k ω r ≤ 2 * k).filter
              fun ω => srwPos k ω r = j).card
        ≤ ∑ _j ∈ Finset.Icc (1 : ℤ) (2 * k), r.choose (r / 2) := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine le_trans (Finset.card_le_card ?_) (card_level_le k j)
          intro ω hω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
          exact hω.2
      _ = (2 * k).toNat * r.choose (r / 2) := by
          rw [Finset.sum_const, Int.card_Icc, smul_eq_mul]
          congr 2
          omega
  -- the maximal binomial coefficient
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hsr : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr hrR
  have hCr : (r.choose (r / 2) : ℝ) * Real.sqrt r ≤ 2 ^ r := by
    have hnat : (r : ℝ) * ((r.choose (r / 2) : ℝ)) ^ 2 ≤ 4 ^ r := by
      exact_mod_cast middle_sq r
    have hpow : ((2 : ℝ) ^ r) ^ 2 = 4 ^ r := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hsq : ((r.choose (r / 2) : ℝ) * Real.sqrt r) ^ 2 ≤ ((2 : ℝ) ^ r) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hrR), hpow]
      calc ((r.choose (r / 2) : ℝ)) ^ 2 * (r : ℝ)
          = (r : ℝ) * ((r.choose (r / 2) : ℝ)) ^ 2 := by ring
        _ ≤ 4 ^ r := hnat
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq
  have hCdiv : (r.choose (r / 2) : ℝ) / 2 ^ r ≤ 1 / Real.sqrt r := by
    rw [div_le_div_iff₀ h2r hsr]
    linarith
  -- assemble
  have hcast : (((2 * k).toNat : ℕ) : ℝ) = 2 * (k : ℝ) := by
    have : ((2 * k).toNat : ℤ) = 2 * k := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have hAle : ((Finset.univ.filter fun ω : Fin r → Bool =>
        ∀ t ≤ r, srwPos k ω t ≠ 0).card : ℝ)
      ≤ 2 * (k : ℝ) * (r.choose (r / 2) : ℝ) := by
    rw [hAeq]
    have := hMidbound
    have hc : (((Finset.univ.filter fun ω : Fin r → Bool =>
        0 < srwPos k ω r ∧ srwPos k ω r ≤ 2 * k).card : ℕ) : ℝ)
        ≤ (((2 * k).toNat * r.choose (r / 2) : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_mul, hcast] at hc
    exact hc
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_of_lt hk
  calc ((Finset.univ.filter fun ω : Fin r → Bool =>
        ∀ t ≤ r, srwPos k ω t ≠ 0).card : ℝ) / 2 ^ r
      ≤ (2 * (k : ℝ) * (r.choose (r / 2) : ℝ)) / 2 ^ r := by gcongr
    _ = 2 * (k : ℝ) * ((r.choose (r / 2) : ℝ) / 2 ^ r) := by ring
    _ ≤ 2 * (k : ℝ) * (1 / Real.sqrt r) := by
        have h2k : (0 : ℝ) ≤ 2 * (k : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_left hCdiv h2k
    _ = 2 * (k : ℝ) / Real.sqrt r := by ring
    _ ≤ 12 * (k : ℝ) / Real.sqrt r := by
        gcongr
        linarith
