-- Prove2me | solution 1 for NonsmoothQN.Secant.theorem_5_2_secant_iterates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T15:55:40.50217+00:00
-- url     : https://prove2.me/submissions/0ee3d1e9-10de-4b54-90df-852958e62949

import Mathlib
import Definitions.Def_NonsmoothQN_Secant_Basic
import Definitions.Def_NonsmoothQN_Secant_Expansion

set_option autoImplicit false

namespace NQN0e89

open NonsmoothQN.Secant Filter Topology

/-! ## The line search (Algorithm 4.6) with `A(t) : t < 2ρ`, `W(t) : ρ ≤ t` -/

lemma lsStep_notA (A W : ℝ → Prop) (s : LSState) (h : ¬ A s.t) :
    lsStep A W s = { α := s.α, β := (s.t : WithTop ℝ), t := (s.α + s.t) / 2 } := by
  unfold lsStep
  rw [if_pos h]

lemma lsStep_notW_top (A W : ℝ → Prop) (s : LSState) (h1 : A s.t) (h2 : ¬ W s.t)
    (hβ : s.β = ⊤) : lsStep A W s = { α := s.t, β := ⊤, t := 2 * s.t } := by
  unfold lsStep
  rw [if_neg (not_not.mpr h1), if_pos h2]
  split <;> simp_all

lemma stopIndex_eq (A W : ℝ → Prop) (n : ℕ) (hn : A (lsRun A W n).t ∧ W (lsRun A W n).t)
    (hlt : ∀ i < n, ¬ (A (lsRun A W i).t ∧ W (lsRun A W i).t)) : lsStopIndex A W = n := by
  unfold lsStopIndex
  apply le_antisymm (Nat.sInf_le hn)
  apply le_csInf ⟨n, hn⟩
  intro b hb
  by_contra h
  push_neg at h
  exact hlt b h hb

lemma ls_halving (A W : ℝ → Prop) (ρ : ℝ) (hA : ∀ t, A t ↔ t < 2 * ρ)
    (n : ℕ) (h2 : ρ ≤ (2:ℝ) ^ (-(n:ℤ))) :
    ∀ i ≤ n, (lsRun A W i).α = 0 ∧ (lsRun A W i).t = (2:ℝ) ^ (-(i:ℤ)) := by
  intro i
  induction i with
  | zero => intro _; simp [lsRun]
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2'⟩ := ih (by omega)
    have hnotA : ¬ A (lsRun A W i).t := by
      rw [hA, h2']
      push_neg
      have h3 : (2:ℝ) ^ (-(n:ℤ) + 1) = 2 * 2 ^ (-(n:ℤ)) := by
        rw [zpow_add₀ two_ne_zero, zpow_one]; ring
      have h4 : (2:ℝ) ^ (-(n:ℤ) + 1) ≤ 2 ^ (-(i:ℤ)) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      linarith
    show (lsStep A W (lsRun A W i)).α = 0 ∧ (lsStep A W (lsRun A W i)).t = _
    rw [lsStep_notA A W _ hnotA]
    refine ⟨h1, ?_⟩
    show ((lsRun A W i).α + (lsRun A W i).t) / 2 = _
    rw [h1, h2', zero_add]
    rw [show (-((i + 1 : ℕ) : ℤ)) = -(i:ℤ) + (-1) by push_cast; ring, zpow_add₀ two_ne_zero]
    rw [zpow_neg_one]
    ring

lemma ls_doubling (A W : ℝ → Prop) (ρ : ℝ) (hA : ∀ t, A t ↔ t < 2 * ρ)
    (hW : ∀ t, W t ↔ ρ ≤ t) (n : ℕ) (h1 : (2:ℝ) ^ ((n:ℤ) - 1) < ρ) :
    ∀ i ≤ n, (lsRun A W i).β = ⊤ ∧ (lsRun A W i).t = (2:ℝ) ^ (i:ℤ) := by
  intro i
  induction i with
  | zero => intro _; simp [lsRun]
  | succ i ih =>
    intro hi
    obtain ⟨hb, ht⟩ := ih (by omega)
    have hlt : (2:ℝ) ^ (i:ℤ) < ρ :=
      lt_of_le_of_lt (zpow_le_zpow_right₀ (by norm_num) (by omega)) h1
    have hpos : (0:ℝ) < 2 ^ (i:ℤ) := zpow_pos (by norm_num) _
    have hAi : A (lsRun A W i).t := by rw [hA, ht]; linarith
    have hWi : ¬ W (lsRun A W i).t := by rw [hW, ht]; push_neg; exact hlt
    show (lsStep A W (lsRun A W i)).β = ⊤ ∧ (lsStep A W (lsRun A W i)).t = _
    rw [lsStep_notW_top A W _ hAi hWi hb]
    refine ⟨rfl, ?_⟩
    show 2 * (lsRun A W i).t = _
    rw [ht]
    push_cast
    rw [zpow_add₀ two_ne_zero, zpow_one]
    ring

lemma ls_main (A W : ℝ → Prop) (ρ : ℝ) (hA : ∀ t, A t ↔ t < 2 * ρ) (hW : ∀ t, W t ↔ ρ ≤ t)
    (e : ℤ) (h1 : (2:ℝ) ^ (e - 1) < ρ) (h2 : ρ ≤ (2:ℝ) ^ e) :
    lsTerminates A W ∧ lsStopIndex A W = e.natAbs ∧ lsResult A W = (2:ℝ) ^ e ∧
    ∀ i ≤ e.natAbs, 0 < (lsRun A W i).t ∧ (lsRun A W i).t ≤ (2:ℝ) ^ (max e 0) ∧
      (e ≤ 0 → (lsRun A W i).t = (2:ℝ) ^ (-(i:ℤ))) := by
  rcases le_or_gt e 0 with he | he
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, e = -(n:ℤ) := ⟨e.natAbs, by omega⟩
    have hn : (-(n:ℤ)).natAbs = n := by simp
    rw [hn]
    have hrun := ls_halving A W ρ hA n h2
    have hstop : A (lsRun A W n).t ∧ W (lsRun A W n).t := by
      rw [(hrun n le_rfl).2, hA, hW]
      refine ⟨?_, h2⟩
      have : (2:ℝ) ^ (-(n:ℤ)) = 2 * 2 ^ (-(n:ℤ) - 1) := by
        rw [zpow_sub₀ two_ne_zero, zpow_one]; field_simp
      rw [this]; linarith
    have hlt : ∀ i < n, ¬ (A (lsRun A W i).t ∧ W (lsRun A W i).t) := by
      intro i hi ⟨hAi, _⟩
      rw [(hrun i hi.le).2, hA] at hAi
      have h4 : (2:ℝ) ^ (-(n:ℤ) + 1) ≤ 2 ^ (-(i:ℤ)) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h3 : (2:ℝ) ^ (-(n:ℤ) + 1) = 2 * 2 ^ (-(n:ℤ)) := by
        rw [zpow_add₀ two_ne_zero, zpow_one]; ring
      linarith
    have hidx := stopIndex_eq A W n hstop hlt
    refine ⟨⟨n, hstop⟩, hidx, ?_, ?_⟩
    · unfold lsResult; rw [hidx, (hrun n le_rfl).2]
    · intro i hi
      rw [(hrun i hi).2]
      refine ⟨zpow_pos (by norm_num) _, ?_, fun _ => rfl⟩
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, e = (n:ℤ) := ⟨e.natAbs, by omega⟩
    have hn : ((n:ℤ)).natAbs = n := by simp
    rw [hn]
    have hrun := ls_doubling A W ρ hA hW n h1
    have hρ : 0 < ρ := lt_trans (zpow_pos (by norm_num) _) h1
    have hstop : A (lsRun A W n).t ∧ W (lsRun A W n).t := by
      rw [(hrun n le_rfl).2, hA, hW]
      refine ⟨?_, h2⟩
      have : (2:ℝ) ^ (n:ℤ) = 2 * 2 ^ ((n:ℤ) - 1) := by
        rw [zpow_sub₀ two_ne_zero, zpow_one]; field_simp
      rw [this]; linarith
    have hlt : ∀ i < n, ¬ (A (lsRun A W i).t ∧ W (lsRun A W i).t) := by
      intro i hi ⟨_, hWi⟩
      rw [(hrun i hi.le).2, hW] at hWi
      have h4 : (2:ℝ) ^ (i:ℤ) ≤ 2 ^ ((n:ℤ) - 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      linarith
    have hidx := stopIndex_eq A W n hstop hlt
    refine ⟨⟨n, hstop⟩, hidx, ?_, ?_⟩
    · unfold lsResult; rw [hidx, (hrun n le_rfl).2]
    · intro i hi
      rw [(hrun i hi).2]
      refine ⟨zpow_pos (by norm_num) _, ?_, fun h => absurd h (by omega)⟩
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)

/-! ## The alternating binary expansion -/

section tail

variable {x₀ : ℝ} {m : ℕ∞} {a : ℕ → ℤ}

lemma tail_summable (hexp : IsAltBinExpansion x₀ m a) (k : ℕ) :
    Summable (fun j : ℕ => if k ≤ j then altTerm m a j else 0) := by
  have := (hexp.2.summable).indicator {j : ℕ | k ≤ j}
  have hfun : (fun j : ℕ => if k ≤ j then altTerm m a j else 0) =
      {j : ℕ | k ≤ j}.indicator (altTerm m a) := by
    funext j
    simp [Set.indicator]
  rw [hfun]
  exact this

lemma tailSum_succ (hexp : IsAltBinExpansion x₀ m a) (k : ℕ) :
    tailSum m a k = altTerm m a k + tailSum m a (k + 1) := by
  have h := (hasSum_ite_eq k (altTerm m a k)).add (tail_summable hexp (k + 1)).hasSum
  have hfun : (fun j : ℕ => (if j = k then altTerm m a k else 0) +
      (if k + 1 ≤ j then altTerm m a j else 0)) =
      fun j : ℕ => if k ≤ j then altTerm m a j else 0 := by
    funext j
    rcases lt_trichotomy j k with hj | hj | hj
    · simp [show ¬ k ≤ j by omega, show j ≠ k by omega, show ¬ k + 1 ≤ j by omega]
    · subst hj; simp
    · simp [show k ≤ j by omega, show j ≠ k by omega, show k + 1 ≤ j by omega]
  rw [hfun] at h
  exact h.tsum_eq

lemma tailSum_zero (hexp : IsAltBinExpansion x₀ m a) : tailSum m a 0 = x₀ := by
  unfold tailSum
  simp only [Nat.zero_le, ↓reduceIte]
  exact hexp.2.tsum_eq

lemma tailSum_beyond (k : ℕ) (hk : ¬ (k : ℕ∞) ≤ m) : tailSum m a k = 0 := by
  unfold tailSum
  have : (fun j : ℕ => if k ≤ j then altTerm m a j else 0) = fun _ => 0 := by
    funext j
    split_ifs with h
    · unfold altTerm
      rw [if_neg]
      intro hj
      exact hk (le_trans (by exact_mod_cast h) hj)
    · rfl
  rw [this, tsum_zero]

lemma enat_eq_of (k : ℕ) (hk : (k : ℕ∞) ≤ m) (hk1 : ¬ ((k + 1 : ℕ) : ℕ∞) ≤ m) :
    m = k := by
  induction m using ENat.recTopCoe with
  | top => exact absurd le_top hk1
  | coe n =>
    have h1 : k ≤ n := by exact_mod_cast hk
    have h2 : ¬ k + 1 ≤ n := by exact_mod_cast hk1
    have : n = k := by omega
    rw [this]

lemma tail_bounds (hexp : IsAltBinExpansion x₀ m a) (hcan : IsCanonicalExpansion m a)
    (k : ℕ) (hk : (k : ℕ∞) ≤ m) :
    (2:ℝ) ^ (-a k - 1) < (-1) ^ k * tailSum m a k ∧
      (-1) ^ k * tailSum m a k ≤ (2:ℝ) ^ (-a k) := by
  have hmono : ∀ i j : ℕ, i < j → ((j : ℕ) : ℕ∞) ≤ m → a i < a j := by
    intro i j hij hj
    exact hexp.1 (show i ∈ {j : ℕ | (j : ℕ∞) ≤ m} from
      le_trans (by exact_mod_cast hij.le) hj) (show j ∈ {j : ℕ | (j : ℕ∞) ≤ m} from hj) hij
  set f : ℕ → ℝ := fun i => if ((k + i : ℕ) : ℕ∞) ≤ m then (2:ℝ) ^ (-a (k + i)) else 0
    with hf
  have hf_nonneg : ∀ i, 0 ≤ f i := by
    intro i; simp only [hf]; split_ifs
    · exact (zpow_pos (by norm_num) _).le
    · exact le_rfl
  have hanti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro i
    by_cases h : ((k + (i + 1) : ℕ) : ℕ∞) ≤ m
    · have h' : ((k + i : ℕ) : ℕ∞) ≤ m :=
        le_trans (by exact_mod_cast (by omega : k + i ≤ k + (i + 1))) h
      simp only [hf, h, h', ↓reduceIte]
      have := hmono (k + i) (k + (i + 1)) (by omega) h
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    · simp only [hf, h, ↓reduceIte]
      exact hf_nonneg i
  have hg : HasSum (fun j : ℕ => if k ≤ j then altTerm m a j else 0) (tailSum m a k) :=
    (tail_summable hexp k).hasSum
  have hg2 := (hasSum_nat_add_iff' k).mpr hg
  have hz : ∑ i ∈ Finset.range k, (if k ≤ i then altTerm m a i else 0) = 0 :=
    Finset.sum_eq_zero (fun i hi => by
      simp only [Finset.mem_range] at hi
      simp [show ¬ k ≤ i by omega])
  rw [hz, sub_zero] at hg2
  have hsum : HasSum (fun i => (-1:ℝ) ^ i * f i) ((-1) ^ k * tailSum m a k) := by
    have := hg2.mul_left ((-1:ℝ) ^ k)
    have hfun : (fun i => (-1:ℝ) ^ i * f i) =
        fun i => (-1:ℝ) ^ k * if k ≤ i + k then altTerm m a (i + k) else 0 := by
      funext i
      have hki : k ≤ i + k := by omega
      rw [if_pos hki, show i + k = k + i by omega]
      simp only [hf, altTerm]
      split_ifs
      · have hsq : ((-1:ℝ) ^ k * (-1) ^ k) = 1 := by rw [← mul_pow]; norm_num
        rw [pow_add]
        calc (-1:ℝ) ^ i * 2 ^ (-a (k + i))
            = ((-1) ^ k * (-1) ^ k) * (-1) ^ i * 2 ^ (-a (k + i)) := by rw [hsq]; ring
          _ = _ := by ring
      · simp
    rw [hfun]
    exact this
  have hl := hsum.tendsto_sum_nat
  have hup := Antitone.tendsto_le_alternating_series hl hanti 0
  have hlo := Antitone.alternating_series_le_tendsto hl hanti 2
  norm_num [Finset.sum_range_succ] at hup hlo
  have hf0 : f 0 = (2:ℝ) ^ (-a k) := by simp [hf, hk]
  have hP : (0:ℝ) < 2 ^ (-a k) := zpow_pos (by norm_num) _
  have hhalf : (2:ℝ) ^ (-a k - 1) = 2 ^ (-a k) / 2 := by
    rw [zpow_sub₀ two_ne_zero, zpow_one]
  rw [hhalf]
  rw [hf0] at hup hlo
  have hf1 : f 1 = if ((k + 1 : ℕ) : ℕ∞) ≤ m then (2:ℝ) ^ (-a (k + 1)) else 0 := rfl
  have hf2 : f 2 = if ((k + 2 : ℕ) : ℕ∞) ≤ m then (2:ℝ) ^ (-a (k + 2)) else 0 := rfl
  have hf3 : f 3 = if ((k + 3 : ℕ) : ℕ∞) ≤ m then (2:ℝ) ^ (-a (k + 3)) else 0 := rfl
  refine ⟨?_, hup⟩
  by_cases h1 : ((k + 1 : ℕ) : ℕ∞) ≤ m
  · have hlt1 := hmono k (k + 1) (by omega) h1
    by_cases h2 : ((k + 2 : ℕ) : ℕ∞) ≤ m
    · have hlt2 := hmono (k + 1) (k + 2) (by omega) h2
      have e1 : f 1 ≤ 2 ^ (-a k) / 2 := by
        rw [hf1, if_pos h1, ← hhalf]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have e2 : f 3 < f 2 := by
        rw [hf2, hf3, if_pos h2]
        split_ifs with h3
        · have := hmono (k + 2) (k + 3) (by omega) h3
          exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
        · exact zpow_pos (by norm_num) _
      linarith
    · have hm : m = ((k + 1 : ℕ) : ℕ∞) := enat_eq_of (k + 1) h1 h2
      have hc := hcan (k + 1) hm (by omega)
      simp only [Nat.add_sub_cancel] at hc
      have h3 : ¬ ((k + 3 : ℕ) : ℕ∞) ≤ m := by
        rw [hm]; intro h; have : k + 3 ≤ k + 1 := by exact_mod_cast h
        omega
      have e1 : f 1 ≤ 2 ^ (-a k) / 4 := by
        rw [hf1, if_pos h1]
        have : (2:ℝ) ^ (-a k) / 4 = 2 ^ (-a k - 2) := by
          rw [zpow_sub₀ two_ne_zero]; norm_num
        rw [this]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have e2 : f 2 = 0 := by rw [hf2, if_neg h2]
      have e3 : f 3 = 0 := by rw [hf3, if_neg h3]
      linarith
  · have h2 : ¬ ((k + 2 : ℕ) : ℕ∞) ≤ m := fun h =>
      h1 (le_trans (by exact_mod_cast (by omega : k + 1 ≤ k + 2)) h)
    have h3 : ¬ ((k + 3 : ℕ) : ℕ∞) ≤ m := fun h =>
      h1 (le_trans (by exact_mod_cast (by omega : k + 1 ≤ k + 3)) h)
    have e1 : f 1 = 0 := by rw [hf1, if_neg h1]
    have e2 : f 2 = 0 := by rw [hf2, if_neg h2]
    have e3 : f 3 = 0 := by rw [hf3, if_neg h3]
    linarith

end tail

/-! ## One step of the secant method -/

lemma neg_one_pow_mul_self (k : ℕ) (y : ℝ) : (-1:ℝ) ^ k * ((-1) ^ k * y) = y := by
  rw [← mul_assoc, ← mul_pow]; norm_num

lemma sign_alt (k : ℕ) (u : ℝ) (hu : 0 < u) : Real.sign ((-1:ℝ) ^ k * u) = (-1) ^ k := by
  rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h]
  · rw [one_mul, Real.sign_of_pos hu]
  · rw [Real.sign_of_neg (by linarith)]

section step

variable {x₀ : ℝ} {m : ℕ∞} {a : ℕ → ℤ}

lemma sec_step (hexp : IsAltBinExpansion x₀ m a) (hcan : IsCanonicalExpansion m a)
    (k : ℕ) (hk : (k : ℕ∞) ≤ m) (s : SecState) (c : ℤ)
    (hx : s.x = tailSum m a k) (hH : s.H = (2:ℝ) ^ c) :
    lsTerminates (secA s.x (secDir s)) (secW s.x (secDir s)) ∧
    lsTrials (secA s.x (secDir s)) (secW s.x (secDir s)) = (-a k - c).natAbs + 1 ∧
    (secStep s).x = tailSum m a (k + 1) ∧
    (((k + 1 : ℕ) : ℕ∞) ≤ m → (secStep s).H = (2:ℝ) ^ (-a k - 1)) ∧
    (∀ i ≤ (-a k - c).natAbs,
      |s.x + (lsRun (secA s.x (secDir s)) (secW s.x (secDir s)) i).t * secDir s| ≤
        max ((2:ℝ) ^ (-a k)) ((lsRun (secA s.x (secDir s)) (secW s.x (secDir s)) i).t * 2 ^ c) ∧
      0 < (lsRun (secA s.x (secDir s)) (secW s.x (secDir s)) i).t ∧
      (lsRun (secA s.x (secDir s)) (secW s.x (secDir s)) i).t ≤ (2:ℝ) ^ (max (-a k - c) 0) ∧
      (-a k - c ≤ 0 →
        (lsRun (secA s.x (secDir s)) (secW s.x (secDir s)) i).t = (2:ℝ) ^ (-(i:ℤ)))) := by
  obtain ⟨hb1, hb2⟩ := tail_bounds hexp hcan k hk
  have hT : tailSum m a k = (-1:ℝ) ^ k * ((-1:ℝ) ^ k * tailSum m a k) :=
    (neg_one_pow_mul_self k _).symm
  set σ : ℝ := (-1) ^ k with hσ
  set u : ℝ := σ * tailSum m a k with hu
  have hupos : 0 < u := lt_trans (zpow_pos (by norm_num) _) hb1
  have hσsq : σ * σ = 1 := by rw [hσ, ← mul_pow]; norm_num
  have hσne : σ ≠ 0 := by intro h; rw [h] at hσsq; simp at hσsq
  have hσabs : |σ| = 1 := by rw [hσ, abs_pow, abs_neg, abs_one, one_pow]
  have hxu : s.x = σ * u := by rw [hx]; exact hT
  have hsgn : Real.sign s.x = σ := by rw [hxu, hσ]; exact sign_alt k u hupos
  have hc : (0:ℝ) < 2 ^ c := zpow_pos (by norm_num) _
  have hcne : (2:ℝ) ^ c ≠ 0 := hc.ne'
  have hdir : secDir s = -(2 ^ c) * σ := by unfold secDir; rw [hH, hsgn]
  have hA : ∀ t, secA s.x (secDir s) t ↔ t < 2 * (u / 2 ^ c) := by
    intro t; unfold secA
    have : -2 * s.x / secDir s = 2 * (u / 2 ^ c) := by
      rw [hxu, hdir, div_eq_iff (mul_ne_zero (neg_ne_zero.mpr hcne) hσne)]
      field_simp
    rw [this]
  have hW : ∀ t, secW s.x (secDir s) t ↔ u / 2 ^ c ≤ t := by
    intro t; unfold secW
    have : -s.x / secDir s = u / 2 ^ c := by
      rw [hxu, hdir, div_eq_iff (mul_ne_zero (neg_ne_zero.mpr hcne) hσne)]
      field_simp
    rw [this]
  have he1 : (2:ℝ) ^ ((-a k - c) - 1) < u / 2 ^ c := by
    rw [lt_div_iff₀ hc, ← zpow_add₀ two_ne_zero]
    have : -a k - c - 1 + c = -a k - 1 := by ring
    rw [this]; exact hb1
  have he2 : u / 2 ^ c ≤ (2:ℝ) ^ (-a k - c) := by
    rw [div_le_iff₀ hc, ← zpow_add₀ two_ne_zero]
    have : -a k - c + c = -a k := by ring
    rw [this]; exact hb2
  obtain ⟨hterm, hidx, hres, htr⟩ := ls_main _ _ (u / 2 ^ c) hA hW (-a k - c) he1 he2
  have hsize : secStepSize s = (2:ℝ) ^ (-a k - c) := hres
  have hpow : (2:ℝ) ^ (-a k - c) * 2 ^ c = 2 ^ (-a k) := by
    rw [← zpow_add₀ two_ne_zero]; ring_nf
  have hx0 : s.x ≠ 0 := by rw [hxu]; exact mul_ne_zero hσne hupos.ne'
  have hnext : s.x + secStepSize s * secDir s = tailSum m a (k + 1) := by
    have h1 := tailSum_succ hexp k
    have h2 : altTerm m a k = σ * 2 ^ (-a k) := by unfold altTerm; rw [if_pos hk]
    have h3 : tailSum m a k = σ * u := by rw [← hxu, hx]
    rw [hsize, hdir, hxu]
    linear_combination h1 - h3 + h2 - σ * hpow
  have hxstep : (secStep s).x = s.x + secStepSize s * secDir s := by
    unfold secStep; rw [if_neg hx0]; split_ifs <;> rfl
  refine ⟨hterm, by unfold lsTrials; rw [hidx], by rw [hxstep, hnext], ?_, ?_⟩
  · intro hk1
    obtain ⟨hb1', _⟩ := tail_bounds hexp hcan (k + 1) hk1
    have hu'pos : 0 < (-1:ℝ) ^ (k + 1) * tailSum m a (k + 1) :=
      lt_trans (zpow_pos (by norm_num) _) hb1'
    have hsgn' : Real.sign (tailSum m a (k + 1)) = -σ := by
      rw [show tailSum m a (k + 1) = (-1:ℝ) ^ (k + 1) * ((-1:ℝ) ^ (k + 1) * tailSum m a (k + 1))
        from (neg_one_pow_mul_self _ _).symm, sign_alt (k + 1) _ hu'pos, pow_succ, ← hσ]
      ring
    have hne : s.x + secStepSize s * secDir s ≠ 0 := by
      rw [hnext]; intro h0; rw [h0, Real.sign_zero] at hsgn'
      exact hσne (by linarith)
    have hHs : (secStep s).H = secStepSize s * secDir s /
        (Real.sign (s.x + secStepSize s * secDir s) - Real.sign s.x) := by
      unfold secStep; rw [if_neg hx0, if_neg hne]
    rw [hHs, hnext, hsgn', hsgn, hsize, hdir]
    have hd : -σ - σ ≠ 0 := by
      intro h; apply hσne; linarith
    have hh : (2:ℝ) ^ (-a k - 1) = 2 ^ (-a k) / 2 := by
      rw [zpow_sub₀ two_ne_zero, zpow_one]
    rw [hh, ← hpow, div_eq_iff hd]
    ring
  · intro i hi
    obtain ⟨htpos, htle, hteq⟩ := htr i hi
    refine ⟨?_, htpos, htle, hteq⟩
    set t := (lsRun (secA s.x (secDir s)) (secW s.x (secDir s)) i).t with ht
    have heq : s.x + t * secDir s = σ * (u - t * 2 ^ c) := by rw [hxu, hdir]; ring
    rw [heq, abs_mul, hσabs, one_mul]
    have htc : 0 < t * 2 ^ c := mul_pos htpos hc
    have m1 := le_max_left ((2:ℝ) ^ (-a k)) (t * 2 ^ c)
    have m2 := le_max_right ((2:ℝ) ^ (-a k)) (t * 2 ^ c)
    rw [abs_le]
    constructor <;> linarith

/-- The exponent of `H_k = 2 ^ Hc a k`. -/
def Hc (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => -a k - 1

lemma run_state (hexp : IsAltBinExpansion x₀ m a) (hcan : IsCanonicalExpansion m a) :
    ∀ k : ℕ, (k : ℕ∞) ≤ m →
      (secRun x₀ 1 k).x = tailSum m a k ∧ (secRun x₀ 1 k).H = (2:ℝ) ^ (Hc a k) := by
  intro k
  induction k with
  | zero => intro _; simp [secRun, Hc, tailSum_zero hexp]
  | succ k ih =>
    intro hk1
    have hk : (k : ℕ∞) ≤ m := le_trans (by exact_mod_cast Nat.le_succ k) hk1
    obtain ⟨hx, hH⟩ := ih hk
    obtain ⟨-, -, hx', hH', -⟩ := sec_step hexp hcan k hk (secRun x₀ 1 k) (Hc a k) hx hH
    exact ⟨hx', hH' hk1⟩

end step

end NQN0e89

open NonsmoothQN.Secant Filter Topology in
theorem solution (x₀ : ℝ) (hx₀ : 0 < x₀) (m : ℕ∞) (a : ℕ → ℤ)
    (hexp : IsAltBinExpansion x₀ m a) (hcan : IsCanonicalExpansion m a) :
    (∀ k : ℕ, (k : ℕ∞) ≤ m → secX x₀ 1 k = tailSum m a k) ∧
    (secLSTerminates x₀ 1 0 ∧ (secTrials x₀ 1 0 : ℤ) = 1 + |a 0|) ∧
    (∀ k : ℕ, 1 ≤ k → (k : ℕ∞) < m →
      secLSTerminates x₀ 1 k ∧ (secTrials x₀ 1 k : ℤ) = a k - a (k - 1)) ∧
    (m ≠ ⊤ → ∃ K : ℕ, secX x₀ 1 K = 0 ∧ ∀ k < K, secLSTerminates x₀ 1 k) ∧
    (m = ⊤ → IsRLinear (fun j => |allTrial x₀ 1 j|) 0 (1 / 2)) := by
  have hrun := NQN0e89.run_state hexp hcan
  have hstep := fun (k : ℕ) (hk : (k : ℕ∞) ≤ m) =>
    NQN0e89.sec_step hexp hcan k hk (secRun x₀ 1 k) (NQN0e89.Hc a k) (hrun k hk).1 (hrun k hk).2
  refine ⟨fun k hk => (hrun k hk).1, ?_, ?_, ?_, ?_⟩
  · -- the first line search
    obtain ⟨hterm, htr, -⟩ := hstep 0 (by simp)
    refine ⟨hterm, ?_⟩
    have htr' : secTrials x₀ 1 0 = (-a 0 - NQN0e89.Hc a 0).natAbs + 1 := htr
    rw [htr']
    simp only [NQN0e89.Hc, sub_zero]
    push_cast
    rw [abs_neg]
    ring
  · -- the later line searches
    intro k hk1 hkm
    have hk : (k : ℕ∞) ≤ m := hkm.le
    obtain ⟨hterm, htr, -⟩ := hstep k hk
    refine ⟨hterm, ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hlt : a j < a (j + 1) :=
      hexp.1 (show j ∈ {i : ℕ | (i : ℕ∞) ≤ m} from
        le_trans (by exact_mod_cast Nat.le_succ j) hk)
        (show j + 1 ∈ {i : ℕ | (i : ℕ∞) ≤ m} from hk) (Nat.lt_succ_self j)
    have htr' : secTrials x₀ 1 (j + 1) = (-a (j + 1) - NQN0e89.Hc a (j + 1)).natAbs + 1 := htr
    rw [htr']
    simp only [NQN0e89.Hc, Nat.add_sub_cancel]
    push_cast
    rw [abs_of_nonpos (by omega)]
    ring
  · -- finite expansions: termination at zero
    intro hm
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, (ENat.natCast_toNat hm).symm⟩
    refine ⟨n + 1, ?_, ?_⟩
    · obtain ⟨-, -, hx', -⟩ := hstep n le_rfl
      have hx'' : secX x₀ 1 (n + 1) = tailSum (n : ℕ∞) a (n + 1) := hx'
      rw [hx'']
      exact NQN0e89.tailSum_beyond (n + 1) (by
        intro h; have : n + 1 ≤ n := by exact_mod_cast h
        omega)
    · intro k hk
      exact (hstep k (by exact_mod_cast (show k ≤ n by omega))).1
  · -- infinite expansions: R-linear convergence of the trial values
    intro hm
    subst hm
    have hN : ∀ k, secTrials x₀ 1 k = (-a k - NQN0e89.Hc a k).natAbs + 1 :=
      fun k => (hstep k le_top).2.1
    have hnu_succ : ∀ k, secNu x₀ 1 (k + 1) = secNu x₀ 1 k + secTrials x₀ 1 k :=
      fun k => Finset.sum_range_succ _ _
    have hnu0 : secNu x₀ 1 0 = 0 := by simp [secNu]
    have hamono : ∀ k, a k < a (k + 1) := fun k =>
      hexp.1 (show k ∈ {i : ℕ | (i : ℕ∞) ≤ ⊤} by simp)
        (show k + 1 ∈ {i : ℕ | (i : ℕ∞) ≤ ⊤} by simp) (Nat.lt_succ_self k)
    have hnu : ∀ k, (secNu x₀ 1 (k + 1) : ℤ) = 1 + |a 0| + a k - a 0 := by
      intro k
      induction k with
      | zero =>
        rw [hnu_succ, hN, hnu0]
        simp only [NQN0e89.Hc, sub_zero]
        push_cast
        rw [abs_neg]
        ring
      | succ k ih =>
        rw [hnu_succ, Nat.cast_add, ih, hN]
        simp only [NQN0e89.Hc]
        push_cast
        have := hamono k
        rw [abs_of_nonpos (show -a (k + 1) - (-a k - 1) ≤ 0 by omega)]
        ring
    have hnu_ge : ∀ k, k ≤ secNu x₀ 1 k := by
      intro k
      induction k with
      | zero => exact Nat.zero_le _
      | succ k ih => rw [hnu_succ, hN]; omega
    have hidx : ∀ j : ℕ, ∃ K i, i < secTrials x₀ 1 K ∧ j = secNu x₀ 1 K + i ∧
        allTrial x₀ 1 j = secTrialPoint x₀ 1 K i := by
      intro j
      have hne : ({k : ℕ | j < secNu x₀ 1 (k + 1)}).Nonempty :=
        ⟨j, by have := hnu_ge (j + 1); simp only [Set.mem_setOf_eq]; omega⟩
      have hK1 : j < secNu x₀ 1 (secLSIndex x₀ 1 j + 1) := Nat.sInf_mem hne
      have hK2 : secNu x₀ 1 (secLSIndex x₀ 1 j) ≤ j := by
        rcases Nat.eq_zero_or_pos (secLSIndex x₀ 1 j) with h0 | hpos
        · rw [h0, hnu0]; exact Nat.zero_le _
        · obtain ⟨K', hK'⟩ : ∃ K', secLSIndex x₀ 1 j = K' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
          have hlt' : K' < sInf {k : ℕ | j < secNu x₀ 1 (k + 1)} := by
            show K' < secLSIndex x₀ 1 j
            omega
          have := Nat.notMem_of_lt_sInf hlt'
          simp only [Set.mem_setOf_eq, not_lt] at this
          rw [hK']; exact this
      refine ⟨secLSIndex x₀ 1 j, j - secNu x₀ 1 (secLSIndex x₀ 1 j), ?_, ?_, rfl⟩
      · rw [hnu_succ] at hK1; omega
      · omega
    have habs0 : 0 ≤ |a 0| := abs_nonneg _
    have habs1 : -|a 0| ≤ a 0 := neg_abs_le _
    have habs2 : a 0 ≤ |a 0| := le_abs_self _
    have hbound : ∀ j : ℕ, |allTrial x₀ 1 j| ≤ (2:ℝ) ^ (2 * |a 0| - (j:ℤ)) := by
      intro j
      obtain ⟨K, i, hi, hj, heq⟩ := hidx j
      rw [heq]
      obtain ⟨-, -, -, -, htb⟩ := hstep K le_top
      have hiK : i ≤ (-a K - NQN0e89.Hc a K).natAbs := by have := hN K; omega
      obtain ⟨hab, htpos, htle, hteq⟩ := htb i hiK
      have hTP : secTrialPoint x₀ 1 K i = (secRun x₀ 1 K).x +
          (lsRun (secA (secRun x₀ 1 K).x (secDir (secRun x₀ 1 K)))
            (secW (secRun x₀ 1 K).x (secDir (secRun x₀ 1 K))) i).t * secDir (secRun x₀ 1 K) := rfl
      rw [hTP]
      refine le_trans hab ?_
      have hiZ : (i : ℤ) ≤ |-a K - NQN0e89.Hc a K| := by
        rw [← Int.natCast_natAbs]; exact_mod_cast hiK
      cases K with
      | zero =>
        rw [hnu0, zero_add] at hj
        subst hj
        simp only [NQN0e89.Hc, sub_zero, abs_neg] at hiZ htle ⊢
        rw [zpow_zero, mul_one]
        apply max_le
        · exact zpow_le_zpow_right₀ (by norm_num) (by linarith)
        · refine le_trans htle (zpow_le_zpow_right₀ (by norm_num) ?_)
          apply max_le <;> linarith
      | succ K' =>
        have hlt := hamono K'
        have hnK := hnu K'
        simp only [NQN0e89.Hc] at hiZ hteq ⊢
        have he : -a (K' + 1) - (-a K' - 1) ≤ 0 := by omega
        rw [hteq he]
        rw [abs_of_nonpos he] at hiZ
        have hjZ : (j : ℤ) = 1 + |a 0| + a K' - a 0 + i := by rw [hj]; push_cast; rw [hnK]
        rw [← zpow_add₀ two_ne_zero]
        apply max_le
        · exact zpow_le_zpow_right₀ (by norm_num) (by rw [hjZ]; linarith)
        · exact zpow_le_zpow_right₀ (by norm_num) (by rw [hjZ]; linarith)
    have hτ : ∀ j : ℕ, (2:ℝ) ^ (2 * |a 0| - (j:ℤ)) = (2:ℝ) ^ (2 * |a 0|) * (1 / 2 : ℝ) ^ j := by
      intro j
      rw [zpow_sub₀ two_ne_zero, zpow_natCast, one_div, inv_pow, div_eq_mul_inv]
    have hC : (0:ℝ) < (2:ℝ) ^ (2 * |a 0|) := zpow_pos (by norm_num) _
    refine ⟨fun j => (2:ℝ) ^ (2 * |a 0|) * (1 / 2 : ℝ) ^ j, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro j; positivity
    · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul ((2:ℝ) ^ (2 * |a 0|))
      simpa using this
    · have hr : ∀ j : ℕ, (1 / 2 : ℝ) = |(2:ℝ) ^ (2 * |a 0|) * (1 / 2 : ℝ) ^ (j + 1) - 0| /
          |(2:ℝ) ^ (2 * |a 0|) * (1 / 2 : ℝ) ^ j - 0| := by
        intro j
        have p1 : (0:ℝ) < 2 ^ (2 * |a 0|) * (1 / 2 : ℝ) ^ (j + 1) := by positivity
        have p2 : (0:ℝ) < 2 ^ (2 * |a 0|) * (1 / 2 : ℝ) ^ j := by positivity
        rw [sub_zero, sub_zero, abs_of_pos p1, abs_of_pos p2, pow_succ]
        field_simp
      exact tendsto_const_nhds.congr hr
    · intro j
      simp only [sub_zero, abs_abs]
      rw [abs_of_pos (show (0:ℝ) < 2 ^ (2 * |a 0|) * (1 / 2 : ℝ) ^ j by positivity), ← hτ]
      exact hbound j
