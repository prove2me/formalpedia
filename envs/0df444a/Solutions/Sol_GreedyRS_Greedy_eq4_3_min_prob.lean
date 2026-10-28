-- Prove2me | solution 1 for GreedyRS.Greedy.eq4_3_min_prob
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:48:12.594044+00:00
-- url     : https://prove2.me/submissions/ff450b74-62aa-4a2f-ab4a-315d6c6f5b52

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting
import Theorems.Thm_GreedyRS_Budget_ec2_4_normal_tail_bound

section Sp1
open Finset
attribute [local instance] Classical.propDecidable

namespace A3Sp

/-- partial sums -/
def W (a : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ range j, a i

/-- strict ascending ladder indices in `[1, n]` -/
noncomputable def L (n : ℕ) (a : ℕ → ℝ) : Finset ℕ :=
  (Icc 1 n).filter (fun j => ∀ i < j, W a i < W a j)

noncomputable def g (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  if n ∈ L n a then 1 / ((L n a).card : ℝ) else 0

def rot (n r : ℕ) (a : ℕ → ℝ) : ℕ → ℝ := fun i => if i < n then a ((i + r) % n) else a i

lemma periodic_sum {f : ℕ → ℝ} {n : ℕ} (hf : ∀ q, f (q + n) = f q) (r : ℕ) :
    ∑ j ∈ range n, f (r + j) = ∑ j ∈ range n, f j := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    have e1 := Finset.sum_range_succ (fun j => f (r + j)) n
    have e2 := Finset.sum_range_succ' (fun j => f (r + j)) n
    have : f (r + n) = f (r + 0) := by rw [hf, add_zero]
    have e3 : ∑ j ∈ range n, f (r + 1 + j) = ∑ j ∈ range n, f (r + (j + 1)) :=
      Finset.sum_congr rfl fun j _ => by rw [add_assoc, add_comm 1 j]
    rw [e3]; linarith

section
variable (n : ℕ) (a : ℕ → ℝ)

/-- partial sums of the periodic extension -/
def S (i : ℕ) : ℝ := ∑ j ∈ range i, a (j % n)

lemma S_add (i j : ℕ) : S n a (i + j) = S n a i + ∑ k ∈ range j, a ((i + k) % n) := by
  unfold S; rw [Finset.sum_range_add]

lemma S_eq_W {j : ℕ} (hj : j ≤ n) : S n a j = W a j := by
  unfold S W
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)]

lemma S_period (_hn : 0 < n) (i : ℕ) : S n a (i + n) = S n a i + W a n := by
  rw [S_add, periodic_sum (f := fun q => a (q % n)) (fun q => by simp) i]
  rw [← S_eq_W n a le_rfl]; rfl

lemma W_rot {r j : ℕ} (hj : j ≤ n) : W (rot n r a) j = S n a (r + j) - S n a r := by
  rw [S_add]; simp only [add_sub_cancel_left, W, rot]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [if_pos (lt_of_lt_of_le (Finset.mem_range.mp hi) hj), add_comm i r]

/-- `r` is good: the rotation starting at `r` has `n` as a strict ladder index -/
def G (r : ℕ) : Prop := ∀ i, r ≤ i → i < r + n → S n a i < S n a (r + n)

lemma G_period (hn : 0 < n) (r : ℕ) : G n a (r + n) ↔ G n a r := by
  constructor
  · intro h i h1 h2
    have := h (i + n) (by omega) (by omega)
    rw [S_period n a hn, show r + n + n = (r + n) + n by ring, S_period n a hn] at this
    linarith
  · intro h i h1 h2
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + n := ⟨i - n, by omega⟩
    have := h i' (by omega) (by omega)
    rw [S_period n a hn, show r + n + n = (r + n) + n by ring, S_period n a hn]
    linarith

lemma mem_L_rot_n (hn : 0 < n) {r : ℕ} : n ∈ L n (rot n r a) ↔ G n a r := by
  simp only [L, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨-, h⟩ i h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, i = r + k := ⟨i - r, by omega⟩
    have := h k (by omega)
    rw [W_rot n a (by omega), W_rot n a le_rfl] at this
    linarith
  · intro h
    refine ⟨⟨hn, le_rfl⟩, fun k hk => ?_⟩
    rw [W_rot n a hk.le, W_rot n a le_rfl]
    have := h (r + k) (by omega) (by omega)
    linarith

lemma mem_L_rot (hn : 0 < n) {r : ℕ} (hr : G n a r) (j : ℕ) :
    j ∈ L n (rot n r a) ↔ j ∈ Icc 1 n ∧ G n a (r + j) := by
  simp only [L, Finset.mem_filter]
  refine and_congr_right fun hj => ?_
  rw [Finset.mem_Icc] at hj
  constructor
  · intro h i h1 h2
    have hr0 : S n a r < S n a (r + j) := by
      have := h 0 (by omega); rw [W_rot n a (by omega), W_rot n a hj.2] at this; simpa using this
    rw [S_period n a hn]
    by_cases hi : i < r + n
    · have := hr i (by omega) hi
      rw [S_period n a hn] at this; linarith
    · obtain ⟨i', rfl⟩ : ∃ i', i = r + i' + n := ⟨i - r - n, by omega⟩
      have := h i' (by omega)
      rw [W_rot n a (by omega), W_rot n a hj.2] at this
      rw [S_period n a hn]; linarith
  · intro h k hk
    rw [W_rot n a (by omega), W_rot n a hj.2]
    have := h (r + k + n) (by omega) (by omega)
    rw [S_period n a hn, S_period n a hn] at this
    linarith

/-- number of good residues -/
noncomputable def K : ℝ := ∑ q ∈ range n, if G n a q then (1 : ℝ) else 0

lemma card_L_rot (hn : 0 < n) {r : ℕ} (hr : G n a r) : ((L n (rot n r a)).card : ℝ) = K n a := by
  classical
  have : L n (rot n r a) = (Icc 1 n).filter (fun j => G n a (r + j)) := by
    ext j; rw [mem_L_rot n a hn hr, Finset.mem_filter]
  rw [this, Finset.natCast_card_filter]
  have hIcc : Icc 1 n = Ico 1 (n + 1) := rfl
  rw [hIcc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  have := periodic_sum (n := n) (f := fun q => if G n a q then (1 : ℝ) else 0)
    (fun q => by simp only [G_period n a hn]) (r + 1)
  rw [K, ← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show r + (1 + j) = r + 1 + j by ring]

lemma not_G_of_nonpos (hn : 0 < n) (hT : W a n ≤ 0) (r : ℕ) : ¬ G n a r := by
  intro h
  have := h r le_rfl (by omega)
  rw [S_period n a hn] at this; linarith

lemma exists_G (hn : 0 < n) (hT : 0 < W a n) : ∃ r < n, G n a r := by
  classical
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (range n) (S n a) ⟨0, by simpa using hn⟩
  let P := (range n).filter (fun r => S n a r = S n a m)
  have hP : P.Nonempty := ⟨m, by simp [P, hm]⟩
  obtain ⟨r, hrP, hrmin⟩ := Finset.exists_min_image P id hP
  simp only [P, Finset.mem_filter, Finset.mem_range] at hrP
  refine ⟨r, hrP.1, fun i h1 h2 => ?_⟩
  rw [S_period n a hn]
  by_cases hi : i < n
  · have := hmax i (Finset.mem_range.mpr hi); linarith
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + n := ⟨i - n, by omega⟩
    rw [S_period n a hn]
    have hle := hmax i' (Finset.mem_range.mpr (by omega))
    have hne : S n a i' ≠ S n a m := by
      intro he
      have := hrmin i' (by simp [P, he]; omega)
      simp at this; omega
    have : S n a i' < S n a r := by rw [hrP.2]; exact lt_of_le_of_ne hle hne
    linarith

theorem cyclic (hn : 0 < n) :
    ∑ r ∈ range n, g n (rot n r a) = if 0 < W a n then 1 else 0 := by
  classical
  have h1 : ∀ r ∈ range n, g n (rot n r a) = (if G n a r then (1 : ℝ) else 0) / K n a := by
    intro r _
    unfold g
    by_cases hr : G n a r
    · rw [if_pos ((mem_L_rot_n n a hn).mpr hr), if_pos hr, card_L_rot n a hn hr]
    · rw [if_neg (fun h => hr ((mem_L_rot_n n a hn).mp h)), if_neg hr, zero_div]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_div]
  split_ifs with hT
  · obtain ⟨r, hr, hG⟩ := exists_G n a hn hT
    have : K n a ≠ 0 := by
      unfold K
      apply ne_of_gt
      exact Finset.sum_pos' (fun _ _ => by split_ifs <;> norm_num)
        ⟨r, Finset.mem_range.mpr hr, by rw [if_pos hG]; norm_num⟩
    exact div_self this
  · rw [Finset.sum_eq_zero fun r _ => if_neg (not_G_of_nonpos n a hn (not_lt.mp hT) r), zero_div]

end

end A3Sp
end Sp1

section Sp2
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace A3Sp

/-! ### Deterministic ladder facts -/

lemma W_zero (a : ℕ → ℝ) : W a 0 = 0 := by simp [W]

def shift (m : ℕ) (a : ℕ → ℝ) : ℕ → ℝ := fun j => a (m + j)

lemma W_shift (m : ℕ) (a : ℕ → ℝ) (j : ℕ) : W (shift m a) j = W a (m + j) - W a m := by
  simp only [W, shift, Finset.sum_range_add]; ring

lemma mem_L {n : ℕ} {a : ℕ → ℝ} {j : ℕ} :
    j ∈ L n a ↔ 1 ≤ j ∧ j ≤ n ∧ ∀ i < j, W a i < W a j := by
  simp [L, Finset.mem_filter, Finset.mem_Icc, and_assoc]

lemma L_mono {m n : ℕ} (a : ℕ → ℝ) (h : m ≤ n) : L m a = (L n a).filter (· ≤ m) := by
  ext j; simp only [Finset.mem_filter, mem_L]; constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2.trans h, h3⟩, h2⟩
  · rintro ⟨⟨h1, -, h3⟩, h2⟩; exact ⟨h1, h2, h3⟩

/-- if `W a j > W a m` for some `j ∈ (m, n]` and `m` is a ladder index (or `m = 0`), there is a
ladder index in `(m, j]` -/
lemma exists_ladder_between {a : ℕ → ℝ} {m j : ℕ} (hm : ∀ i < m, W a i < W a m)
    (hj : m < j) (hW : W a m < W a j) :
    ∃ l, m < l ∧ l ≤ j ∧ W a m < W a l ∧ (∀ i < l, W a i < W a l) := by
  classical
  have hex : ∃ l, m < l ∧ W a m < W a l := ⟨j, hj, hW⟩
  let l := Nat.find hex
  have hl : m < l ∧ W a m < W a l := Nat.find_spec hex
  have hmin : ∀ i, m < i → i < l → W a i ≤ W a m := fun i h1 h2 =>
    not_lt.mp fun h => Nat.find_min hex h2 ⟨h1, h⟩
  refine ⟨l, hl.1, Nat.find_min' hex ⟨hj, hW⟩, hl.2, fun i hi => ?_⟩
  rcases lt_trichotomy i m with h | h | h
  · exact (hm i h).trans hl.2
  · rw [h]; exact hl.2
  · exact lt_of_le_of_lt (hmin i h hi) hl.2

lemma first_iff {n : ℕ} {a : ℕ → ℝ} :
    (n ∈ L n a ∧ (L n a).card = 1) ↔ (1 ≤ n ∧ 0 < W a n ∧ ∀ j, 1 ≤ j → j < n → W a j ≤ 0) := by
  constructor
  · rintro ⟨hn, hc⟩
    rw [mem_L] at hn
    have h0 : 0 < W a n := by have := hn.2.2 0 (by omega); rwa [W_zero] at this
    refine ⟨hn.1, h0, fun j hj1 hj2 => not_lt.mp fun hpos => ?_⟩
    obtain ⟨l, hl1, hl2, -, hl4⟩ := exists_ladder_between (a := a) (m := 0) (j := j)
      (by simp) (by omega) (by rwa [W_zero])
    have hlL : l ∈ L n a := mem_L.mpr ⟨by omega, by omega, hl4⟩
    have hnL : n ∈ L n a := mem_L.mpr hn
    have : ({l, n} : Finset ℕ) ⊆ L n a := by
      intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
    have := Finset.card_le_card this
    rw [Finset.card_pair (by omega)] at this; omega
  · rintro ⟨h1, h2, h3⟩
    have hnL : n ∈ L n a := by
      refine mem_L.mpr ⟨h1, le_rfl, fun i hi => ?_⟩
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rwa [W_zero]
      · exact lt_of_le_of_lt (h3 i hi0 hi) h2
    refine ⟨hnL, Finset.card_eq_one.mpr ⟨n, ?_⟩⟩
    ext j; simp only [Finset.mem_singleton]; constructor
    · intro hj; rw [mem_L] at hj
      by_contra hne
      have := hj.2.2 0 (by omega); rw [W_zero] at this
      have := h3 j hj.1 (by omega); linarith
    · rintro rfl; exact hnL

/-- the event "the `k`-th strict ascending ladder epoch is `n`" (as a predicate on paths) -/
def Ev (n k : ℕ) (a : ℕ → ℝ) : Prop := n ∈ L n a ∧ (L n a).card = k

lemma renewal_iff {n k : ℕ} (hk : 1 ≤ k) {a : ℕ → ℝ} :
    Ev n (k + 1) a ↔ ∃ m, m < n ∧ Ev m k a ∧ Ev (n - m) 1 (shift m a) := by
  constructor
  · rintro ⟨hn, hc⟩
    have hne : ((L n a).erase n).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hn]; omega
    set m := ((L n a).erase n).max' hne with hm_def
    have hmmem : m ∈ (L n a).erase n := Finset.max'_mem _ hne
    have hmL := Finset.mem_of_mem_erase hmmem
    have hmn : m < n := lt_of_le_of_ne (mem_L.mp hmL).2.1 (Finset.ne_of_mem_erase hmmem)
    have hmax : ∀ l ∈ L n a, l ≠ n → l ≤ m := fun l hl hln =>
      Finset.le_max' _ _ (Finset.mem_erase.mpr ⟨hln, hl⟩)
    have hLm : L m a = (L n a).erase n := by
      rw [L_mono a hmn.le]; ext l
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, hmax l h2 h1⟩
    refine ⟨m, hmn, ⟨?_, ?_⟩, ?_⟩
    · rw [hLm]; exact hmmem
    · rw [hLm, Finset.card_erase_of_mem hn, hc]; rfl
    · rw [Ev, first_iff]
      have hmW := (mem_L.mp hmL).2.2
      have hnW := (mem_L.mp hn).2.2
      refine ⟨by omega, ?_, fun j hj1 hj2 => ?_⟩
      · rw [W_shift, Nat.add_sub_cancel' hmn.le]; linarith [hnW m hmn]
      · rw [W_shift]
        by_contra hpos; push_neg at hpos
        obtain ⟨l, hl1, hl2, -, hl4⟩ := exists_ladder_between hmW (by omega : m < m + j)
          (by linarith)
        have : l ∈ L n a := mem_L.mpr ⟨by omega, by omega, hl4⟩
        have := hmax l this (by omega); omega
  · rintro ⟨m, hmn, ⟨hmL, hmc⟩, hsh⟩
    rw [Ev, first_iff] at hsh
    obtain ⟨-, hpos, hle⟩ := hsh
    rw [W_shift, Nat.add_sub_cancel' hmn.le] at hpos
    have hmW := (mem_L.mp hmL).2.2
    have hle' : ∀ i, m < i → i < n → W a i ≤ W a m := fun i h1 h2 => by
      have := hle (i - m) (by omega) (by omega)
      rw [W_shift, Nat.add_sub_cancel' h1.le] at this; linarith
    have hnL : n ∈ L n a := by
      refine mem_L.mpr ⟨by have := (mem_L.mp hmL).1; omega, le_rfl, fun i hi => ?_⟩
      rcases lt_trichotomy i m with h | h | h
      · linarith [hmW i h]
      · rw [h]; linarith
      · linarith [hle' i h hi]
    have hLn : L n a = insert n (L m a) := by
      ext l; rw [Finset.mem_insert]; constructor
      · intro hl
        by_cases hln : l = n
        · exact Or.inl hln
        · right
          rw [L_mono a hmn.le, Finset.mem_filter]
          refine ⟨hl, not_lt.mp fun hlm => ?_⟩
          have h1 := (mem_L.mp hl).2.2 m hlm
          have h2 := hle' l hlm (lt_of_le_of_ne (mem_L.mp hl).2.1 hln)
          linarith
      · rintro (rfl | hl)
        · exact hnL
        · rw [L_mono a hmn.le, Finset.mem_filter] at hl; exact hl.1
    refine ⟨hnL, ?_⟩
    rw [hLn, Finset.card_insert_of_notMem, hmc]
    intro h; have := (mem_L.mp h).2.1; omega

lemma renewal_unique {n k : ℕ} {a : ℕ → ℝ} {m m' : ℕ} (hm : m < n) (hm' : m' < n)
    (h1 : Ev m k a ∧ Ev (n - m) 1 (shift m a)) (h2 : Ev m' k a ∧ Ev (n - m') 1 (shift m' a)) :
    m = m' := by
  have key : ∀ m m', m < m' → m' < n → Ev (n - m) 1 (shift m a) → Ev m' k a → False := by
    intro m m' hlt hm'n hsh hEv
    rw [Ev, first_iff] at hsh
    have := hsh.2.2 (m' - m) (by omega) (by omega)
    rw [W_shift, Nat.add_sub_cancel' hlt.le] at this
    have := (mem_L.mp hEv.1).2.2 m hlt
    linarith
  rcases lt_trichotomy m m' with h | h | h
  · exact (key m m' h hm' h1.2 h2.1).elim
  · exact h
  · exact (key m' m h hm h2.2 h1.1).elim

lemma Ev_zero (n : ℕ) (a : ℕ → ℝ) : ¬ Ev n 0 a := by
  rintro ⟨h, hc⟩; rw [Finset.card_eq_zero] at hc; rw [hc] at h; simp at h

lemma Ev_n_zero (k : ℕ) (a : ℕ → ℝ) : ¬ Ev 0 k a := by
  rintro ⟨h, -⟩; have := (mem_L.mp h).1; omega

end A3Sp
end Sp2

section Sp3
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace A3Sp

variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

noncomputable abbrev PP : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => ν)

lemma map_inj {e : ℕ → ℕ} (he : Function.Injective e) :
    (PP ν).map (fun a i => a (e i)) = PP ν := by
  have hmeas : Measurable (fun (a : ℕ → ℝ) i => a (e i)) := measurable_pi_lambda _ fun i => measurable_pi_apply _
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi (Set.to_countable _) fun i _ => ht i)]
  let t' : ℕ → Set ℝ := fun j => if h : ∃ i ∈ s, e i = j then t (Classical.choose h) else Set.univ
  have ht' : ∀ i ∈ s, t' (e i) = t i := by
    intro i hi
    have h : ∃ i' ∈ s, e i' = e i := ⟨i, hi, rfl⟩
    simp only [t', dif_pos h]
    rw [he (Classical.choose_spec h).2]
  have hpre : (fun (a : ℕ → ℝ) i => a (e i)) ⁻¹' Set.pi (↑s) t =
      Set.pi (↑(s.map ⟨e, he⟩)) t' := by
    ext a
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro h j ⟨i, hi, rfl⟩; rw [ht' i hi]; exact h i hi
    · intro h i hi; rw [← ht' i hi]; exact h (e i) ⟨i, hi, rfl⟩
  rw [hpre, Measure.infinitePi_pi]
  · rw [Finset.prod_map]
    exact Finset.prod_congr rfl fun i hi => by simp only [Function.Embedding.coeFn_mk, ht' i hi]
  · intro j _
    simp only [t']; split_ifs
    · exact ht _
    · exact MeasurableSet.univ

lemma measurePreserving_inj {e : ℕ → ℕ} (he : Function.Injective e) :
    MeasurePreserving (fun (a : ℕ → ℝ) i => a (e i)) (PP ν) (PP ν) :=
  ⟨measurable_pi_lambda _ fun i => measurable_pi_apply _, map_inj ν he⟩

/-! ### coordinate σ-algebras -/

def s (j : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  MeasurableSpace.comap (fun z : ℕ → ℝ => z j) inferInstance

lemma s_le (j : ℕ) : s j ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  (measurable_pi_apply j).comap_le

lemma iIndep_s : iIndep s (PP ν) :=
  (iIndepFun_iff_iIndep _ _ _).1
    (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ x => x) (fun _ => measurable_id))

lemma meas_W (mm : MeasurableSpace (ℕ → ℝ)) {n : ℕ} (h : ∀ i < n, s i ≤ mm) {j : ℕ} (hj : j ≤ n) :
    Measurable[mm] (fun a => W a j) := by
  letI := mm
  unfold W
  refine Finset.measurable_sum _ fun i hi => ?_
  exact Measurable.of_comap_le (h i (by have := Finset.mem_range.1 hi; omega))

lemma meas_p (mm : MeasurableSpace (ℕ → ℝ)) {n : ℕ} (h : ∀ i < n, s i ≤ mm) {j : ℕ} (hj : j ≤ n) :
    MeasurableSet[mm] {a : ℕ → ℝ | ∀ i < j, W a i < W a j} := by
  letI := mm
  have : {a : ℕ → ℝ | ∀ i < j, W a i < W a j} = ⋂ i ∈ range j, {a | W a i < W a j} := by
    ext a; simp
  rw [this]
  refine Finset.measurableSet_biInter _ fun i hi => ?_
  exact measurableSet_lt (meas_W mm h (by have := Finset.mem_range.1 hi; omega)) (meas_W mm h hj)

lemma meas_L_eq (mm : MeasurableSpace (ℕ → ℝ)) {n : ℕ} (h : ∀ i < n, s i ≤ mm) (F : Finset ℕ)
    (hF : F ⊆ Icc 1 n) : MeasurableSet[mm] {a : ℕ → ℝ | L n a = F} := by
  letI := mm
  have : {a : ℕ → ℝ | L n a = F} = ⋂ j ∈ Icc 1 n,
      (if j ∈ F then {a : ℕ → ℝ | ∀ i < j, W a i < W a j} else {a | ∀ i < j, W a i < W a j}ᶜ) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro rfl j hj
      split_ifs with hjF
      · exact (Finset.mem_filter.mp hjF).2
      · exact fun hp => hjF (Finset.mem_filter.mpr ⟨hj, hp⟩)
    · intro H; ext j
      simp only [L, Finset.mem_filter]
      constructor
      · rintro ⟨hj, hp⟩
        have := H j hj; split_ifs at this with hjF
        · exact hjF
        · exact absurd hp this
      · intro hjF
        have hj := hF hjF
        have := H j hj; rw [if_pos hjF] at this
        exact ⟨hj, this⟩
  rw [this]
  refine Finset.measurableSet_biInter _ fun j hj => ?_
  have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
  split_ifs
  · exact meas_p mm h hjn
  · exact (meas_p mm h hjn).compl

lemma meas_Ev (mm : MeasurableSpace (ℕ → ℝ)) {n : ℕ} (h : ∀ i < n, s i ≤ mm) (k : ℕ) :
    MeasurableSet[mm] {a : ℕ → ℝ | Ev n k a} := by
  letI := mm
  have : {a : ℕ → ℝ | Ev n k a} = ⋃ F ∈ (Icc 1 n).powerset.filter (fun F => n ∈ F ∧ F.card = k),
      {a | L n a = F} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset, Ev]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨L n a, ⟨Finset.filter_subset _ _, h1, h2⟩, rfl⟩
    · rintro ⟨F, ⟨-, h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
  rw [this]
  refine Finset.measurableSet_biUnion _ fun F hF => ?_
  exact meas_L_eq mm h F (Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1)

lemma meas_Ev' (n k : ℕ) : MeasurableSet {a : ℕ → ℝ | Ev n k a} :=
  meas_Ev _ (fun i _ => s_le i) k

lemma measurable_shift (m : ℕ) : Measurable[⨆ i ∈ {i | m ≤ i}, s i] (shift m) := by
  letI := ⨆ i ∈ {i | m ≤ i}, s i
  refine measurable_pi_lambda _ fun j => ?_
  exact Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ {i | m ≤ i}) => s i) (m + j)
    (by simp))

lemma indep_shift (m : ℕ) {A B : Set (ℕ → ℝ)} (hA : MeasurableSet[⨆ i ∈ {i | i < m}, s i] A)
    (hB : MeasurableSet B) :
    PP ν (A ∩ shift m ⁻¹' B) = PP ν A * PP ν B := by
  have hind := indep_iSup_of_disjoint s_le (iIndep_s ν) (S := {i | i < m}) (T := {i | m ≤ i})
    (by rw [Set.disjoint_left]; intro i h1 h2; simp at h1 h2; omega)
  rw [Indep_iff] at hind
  rw [hind A _ hA (measurable_shift m hB)]
  congr 1
  have := map_inj ν (e := (m + ·)) (fun a b h => by simpa using h)
  have hm : Measurable (fun (a : ℕ → ℝ) (i : ℕ) => a (m + i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  calc PP ν (shift m ⁻¹' B) = (PP ν).map (fun (a : ℕ → ℝ) (i : ℕ) => a (m + i)) B :=
        (Measure.map_apply hm hB).symm
    _ = PP ν B := by rw [this]

end A3Sp
end Sp3

section Sp4
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace A3Sp

variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

noncomputable def u (k n : ℕ) : ℝ≥0∞ := PP ν {a | Ev n k a}
noncomputable def q (n : ℕ) : ℝ≥0∞ := PP ν {a | 0 < W a n}

/-! ### cyclic averaging -/

noncomputable def gE (n : ℕ) (a : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, Set.indicator {a | Ev n (k + 1) a} (fun _ => (1 : ℝ≥0∞) / ((k : ℝ≥0∞) + 1)) a

lemma gE_eq (n : ℕ) (a : ℕ → ℝ) : gE n a = ENNReal.ofReal (g n a) := by
  unfold gE g
  split_ifs with h
  · have hc : 1 ≤ (L n a).card := Finset.card_pos.mpr ⟨n, h⟩
    rw [tsum_eq_single ((L n a).card - 1)]
    · simp only [Set.indicator, Set.mem_setOf_eq]
      rw [if_pos (show Ev n ((L n a).card - 1 + 1) a from ⟨h, by omega⟩)]
      rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hc), ENNReal.ofReal_one,
        ENNReal.ofReal_natCast]
      congr 1; rw [← Nat.cast_one (R := ℝ≥0∞), ← Nat.cast_add]; congr 1; omega
    · intro k hk
      rw [Set.indicator_of_notMem]
      rintro ⟨-, h2⟩; omega
  · rw [ENNReal.ofReal_zero]
    exact ENNReal.tsum_eq_zero.mpr fun k => Set.indicator_of_notMem (fun h' => h h'.1) _

lemma measurable_gE (n : ℕ) : Measurable (gE n) :=
  Measurable.ennreal_tsum fun k => measurable_const.indicator (meas_Ev' n (k + 1))

lemma lintegral_gE (n : ℕ) : ∫⁻ a, gE n a ∂(PP ν) = ∑' k : ℕ, u ν (k + 1) n / ((k : ℝ≥0∞) + 1) := by
  unfold gE
  rw [lintegral_tsum fun k => (measurable_const.indicator (meas_Ev' n (k + 1))).aemeasurable]
  refine tsum_congr fun k => ?_
  rw [lintegral_indicator_const (meas_Ev' n (k + 1)), u]
  rw [div_eq_mul_inv, one_mul, div_eq_mul_inv, mul_comm]

lemma rot_inj (n r : ℕ) (hn : 0 < n) :
    Function.Injective (fun i => if i < n then (i + r) % n else i) := by
  intro i j h
  simp only at h
  have hm : ∀ x, (x + r) % n < n := fun x => Nat.mod_lt _ hn
  split_ifs at h with hi hj hj
  · have := Nat.ModEq.add_right_cancel' r h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · have := hm i; omega
  · have := hm j; omega
  · exact h

lemma rot_eq (n r : ℕ) (a : ℕ → ℝ) :
    rot n r a = fun i => a (if i < n then (i + r) % n else i) := by
  funext i; simp only [rot]; split_ifs <;> rfl

lemma cyclic_avg {n : ℕ} (hn : 0 < n) :
    (n : ℝ≥0∞) * ∑' k : ℕ, u ν (k + 1) n / ((k : ℝ≥0∞) + 1) = q ν n := by
  rw [← lintegral_gE]
  have hrot : ∀ r, ∫⁻ a, gE n (rot n r a) ∂(PP ν) = ∫⁻ a, gE n a ∂(PP ν) := by
    intro r
    simp_rw [rot_eq n r]
    exact (measurePreserving_inj ν (rot_inj n r hn)).lintegral_comp (measurable_gE n)
  have hsum : ∀ a, ∑ r ∈ range n, gE n (rot n r a) = Set.indicator {a | 0 < W a n} 1 a := by
    intro a
    simp_rw [gE_eq]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => by
      unfold g; split_ifs <;> positivity), cyclic n a hn]
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    split_ifs <;> simp
  calc (n : ℝ≥0∞) * ∫⁻ a, gE n a ∂(PP ν) = ∑ r ∈ range n, ∫⁻ a, gE n (rot n r a) ∂(PP ν) := by
        rw [Finset.sum_congr rfl fun r _ => hrot r, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ∫⁻ a, ∑ r ∈ range n, gE n (rot n r a) ∂(PP ν) := by
        rw [lintegral_finsetSum]
        intro r _
        simp_rw [rot_eq n r]
        exact (measurable_gE n).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)
    _ = q ν n := by
        simp_rw [hsum]
        rw [lintegral_indicator_one]
        · rfl
        · exact measurableSet_lt measurable_const (meas_W _ (n := n) (fun i _ => s_le i) le_rfl)

/-! ### renewal -/

lemma renewal (k n : ℕ) :
    u ν (k + 2) n = ∑ m ∈ range n, u ν (k + 1) m * u ν 1 (n - m) := by
  have hset : {a : ℕ → ℝ | Ev n (k + 1 + 1) a} =
      ⋃ m ∈ range n, ({a | Ev m (k + 1) a} ∩ shift m ⁻¹' {a | Ev (n - m) 1 a}) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Finset.mem_range, exists_prop]
    rw [renewal_iff (by omega)]
  unfold u
  rw [show k + 2 = k + 1 + 1 by ring, hset, measure_biUnion_finset]
  · refine Finset.sum_congr rfl fun m _ => ?_
    refine indep_shift ν m ?_ (meas_Ev' _ _)
    exact meas_Ev _ (fun i hi => le_iSup₂ (f := fun i (_ : i ∈ {i | i < m}) => s i) i hi) _
  · intro m hm m' hm' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro a ⟨h1, h2⟩ ⟨h3, h4⟩
    exact hne (renewal_unique (Finset.mem_range.mp hm) (Finset.mem_range.mp hm') ⟨h1, h2⟩ ⟨h3, h4⟩)
  · intro m _
    exact (meas_Ev' _ _).inter ((measurable_pi_lambda _ fun i => measurable_pi_apply _)
      (meas_Ev' _ _))

lemma u_zero_right (k : ℕ) : u ν k 0 = 0 := by
  unfold u; convert measure_empty (μ := PP ν); ext a; simpa using Ev_n_zero k a

lemma cauchy (x y : ℕ → ℝ≥0∞) (hy : y 0 = 0) :
    ∑' n, ∑ m ∈ range n, x m * y (n - m) = (∑' n, x n) * ∑' n, y n := by
  have h1 : ∀ n, ∑ m ∈ range n, x m * y (n - m) =
      ∑' m, if m < n then x m * y (n - m) else 0 := by
    intro n
    rw [tsum_eq_sum (s := range n)]
    · exact Finset.sum_congr rfl fun m hm => by rw [if_pos (Finset.mem_range.mp hm)]
    · intro m hm; rw [if_neg (fun h => hm (Finset.mem_range.mpr h))]
  simp_rw [h1]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun m => ?_
  have h2 : ∀ n, (if m < n then x m * y (n - m) else 0) = x m * (if m < n then y (n - m) else 0) :=
    fun n => by split_ifs <;> simp
  simp_rw [h2]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have e := (ENNReal.summable).sum_add_tsum_nat_add' (f := fun n => if m < n then y (n - m) else 0)
    (k := m + 1)
  rw [← e]
  rw [Finset.sum_eq_zero fun i hi => if_neg (by have := Finset.mem_range.mp hi; omega), zero_add]
  rw [tsum_eq_zero_add' (f := y) ENNReal.summable, hy, zero_add]
  refine tsum_congr fun j => ?_
  rw [if_pos (by omega)]; congr 1; omega

lemma tsum_u (k : ℕ) : ∑' n, u ν (k + 1) n = (∑' n, u ν 1 n) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← ih, ← cauchy _ _ (u_zero_right ν 1)]
    exact tsum_congr fun n => renewal ν k n

end A3Sp
end Sp4

section Sp5
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace A3Sp

variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

noncomputable def F : ℝ≥0∞ := ∑' n, u ν 1 n

lemma series_eq : ∑' n : ℕ, q ν (n + 1) / ((n : ℝ≥0∞) + 1) =
    ∑' k : ℕ, F ν ^ (k + 1) / ((k : ℝ≥0∞) + 1) := by
  have h1 : ∀ n : ℕ, q ν (n + 1) / ((n : ℝ≥0∞) + 1) =
      ∑' k : ℕ, u ν (k + 1) (n + 1) / ((k : ℝ≥0∞) + 1) := by
    intro n
    rw [← cyclic_avg ν (Nat.succ_pos n)]
    simp only [Nat.succ_eq_add_one]
    rw [Nat.cast_add, Nat.cast_one, mul_comm, ENNReal.mul_div_cancel_right]
    · exact (by positivity : ((n : ℝ≥0∞) + 1) ≠ 0)
    · exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  simp_rw [div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, F, ← tsum_u]
  congr 1
  rw [tsum_eq_zero_add' (f := u ν (k + 1)) ENNReal.summable, u_zero_right, zero_add]

lemma disj_first : Pairwise (Function.onFun Disjoint fun n => {a : ℕ → ℝ | Ev n 1 a}) := by
  have key : ∀ n n' (a : ℕ → ℝ), n < n' → Ev n 1 a → Ev n' 1 a → False := by
    intro n n' a h h1 h2
    rw [Ev, first_iff] at h1 h2
    have := h2.2.2 n h1.1 h; linarith [h1.2.1]
  intro n n' hne
  rw [Function.onFun, Set.disjoint_left]
  intro a h1 h2
  rcases lt_or_gt_of_ne hne with h | h
  · exact key n n' a h h1 h2
  · exact key n' n a h h2 h1

lemma union_first : (⋃ n, {a : ℕ → ℝ | Ev n 1 a}) = {a | ∀ n, 1 ≤ n → W a n ≤ 0}ᶜ := by
  ext a
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_le]
  constructor
  · rintro ⟨n, h⟩
    rw [Ev, first_iff] at h
    exact ⟨n, h.1, h.2.1⟩
  · rintro ⟨n, hn, hpos⟩
    have hex : ∃ n, 0 < W a n := ⟨n, hpos⟩
    refine ⟨Nat.find hex, ?_⟩
    rw [Ev, first_iff]
    have hs := Nat.find_spec hex
    refine ⟨?_, hs, fun j hj1 hj2 => not_lt.mp fun h => Nat.find_min hex hj2 h⟩
    by_contra h0
    have : Nat.find hex = 0 := by omega
    rw [this, W_zero] at hs; exact lt_irrefl _ hs

lemma prob_target : PP ν {a | ∀ n, 1 ≤ n → W a n ≤ 0} = 1 - F ν := by
  have hU : MeasurableSet (⋃ n, {a : ℕ → ℝ | Ev n 1 a}) := MeasurableSet.iUnion fun n => meas_Ev' n 1
  have hF : F ν = PP ν (⋃ n, {a : ℕ → ℝ | Ev n 1 a}) := by
    rw [measure_iUnion (disj_first) (fun n => meas_Ev' n 1)]; rfl
  have hT : MeasurableSet {a : ℕ → ℝ | ∀ n, 1 ≤ n → W a n ≤ 0} := by
    rw [← compl_compl {a : ℕ → ℝ | ∀ n, 1 ≤ n → W a n ≤ 0}, ← union_first]; exact hU.compl
  rw [hF, union_first, prob_compl_eq_one_sub hT,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]

lemma F_le_one : F ν ≤ 1 := by
  have : F ν = PP ν (⋃ n, {a : ℕ → ℝ | Ev n 1 a}) := by
    rw [measure_iUnion (disj_first) (fun n => meas_Ev' n 1)]; rfl
  rw [this]; exact prob_le_one

lemma harmonic_top : ∑' k : ℕ, (1 : ℝ≥0∞) / ((k : ℝ≥0∞) + 1) = ⊤ := by
  by_contra h
  have h' : ∑' k : ℕ, (((1 : NNReal) / ((k : NNReal) + 1) : NNReal) : ℝ≥0∞) ≠ ⊤ := by
    have e : (fun k : ℕ => (((1 : NNReal) / ((k : NNReal) + 1) : NNReal) : ℝ≥0∞)) =
        fun k : ℕ => (1 : ℝ≥0∞) / ((k : ℝ≥0∞) + 1) := by
      funext k; rw [ENNReal.coe_div (by positivity : (0 : NNReal) < (k : NNReal) + 1).ne']; simp
    rw [e]; exact h
  rw [ENNReal.tsum_coe_ne_top_iff_summable] at h'
  have h2 := NNReal.summable_coe.mpr h'
  have : Summable (fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ)) := by
    convert h2 using 2 with k; push_cast; ring
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp this)

theorem spitzer (hS : Summable fun n : ℕ => (q ν (n + 1)).toReal / ((n : ℝ) + 1)) :
    (PP ν {a | ∀ n, 1 ≤ n → W a n ≤ 0}).toReal =
      Real.exp (-∑' n : ℕ, (q ν (n + 1)).toReal / ((n : ℝ) + 1)) := by
  set S := ∑' n : ℕ, (q ν (n + 1)).toReal / ((n : ℝ) + 1) with hSdef
  have hqtop : ∀ n, q ν n ≠ ⊤ := fun n => measure_ne_top _ _
  have hE : ENNReal.ofReal S = ∑' n : ℕ, q ν (n + 1) / ((n : ℝ≥0∞) + 1) := by
    rw [hSdef, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hS]
    refine tsum_congr fun n => ?_
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_toReal (hqtop _)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [series_eq] at hE
  have hF1 : F ν < 1 := by
    refine lt_of_le_of_ne (F_le_one ν) fun h => ?_
    rw [h] at hE; simp only [one_pow] at hE
    rw [harmonic_top] at hE; exact ENNReal.ofReal_ne_top hE
  set x := (F ν).toReal with hx
  have hFtop : F ν ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hF1 le_top)
  have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
  have hx1 : x < 1 := by
    rw [hx]; exact (ENNReal.toReal_lt_toReal hFtop ENNReal.one_ne_top).mpr hF1 |>.trans_eq
      ENNReal.toReal_one
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rw [abs_of_nonneg hx0]; exact hx1)
  have hE2 : ∑' k : ℕ, F ν ^ (k + 1) / ((k : ℝ≥0∞) + 1) = ENNReal.ofReal (-Real.log (1 - x)) := by
    rw [← hlog.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hlog.summable]
    refine tsum_congr fun k => ?_
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow hx0, hx,
      ENNReal.ofReal_toReal hFtop]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [hE2] at hE
  have hlogpos : 0 ≤ -Real.log (1 - x) := by
    rw [neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hSnn : 0 ≤ S := tsum_nonneg fun n => by positivity
  rw [ENNReal.ofReal_eq_ofReal_iff hSnn hlogpos] at hE
  rw [hE, neg_neg, Real.exp_log (by linarith), prob_target,
    ENNReal.toReal_sub_of_le (F_le_one ν) ENNReal.one_ne_top, ENNReal.toReal_one]

end A3Sp
end Sp5

section Sp6
open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal NNReal
open GreedyRS.Greedy

namespace A3Sp

instance : IsProbabilityMeasure stdNormalSeq := by unfold stdNormalSeq; infer_instance

lemma indepZ : iIndepFun (fun j (z : ℕ → ℝ) => z j) stdNormalSeq :=
  iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)

lemma lawZ (j : ℕ) : stdNormalSeq.map (fun z => z j) = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval _ j

noncomputable def Ssum (n : ℕ) (z : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range n, z j

lemma meas_Ssum (n : ℕ) : Measurable (Ssum n) := by unfold Ssum; fun_prop

lemma law_Ssum (m : ℕ) : stdNormalSeq.map (Ssum m) = gaussianReal 0 m := by
  induction m with
  | zero =>
    have : Ssum 0 = fun _ => 0 := by funext z; simp [Ssum]
    rw [this, Nat.cast_zero, gaussianReal_zero_var, Measure.map_const]; simp
  | succ m ih =>
    have hsplit : Ssum (m + 1) = Ssum m + (fun z : ℕ → ℝ => z m) := by
      funext z; simp [Ssum, Finset.sum_range_succ]
    have hind : IndepFun (Ssum m) (fun z : ℕ → ℝ => z m) stdNormalSeq := by
      have : Ssum m = ∑ j ∈ Finset.range m, (fun z : ℕ → ℝ => z j) := by
        funext z; simp [Ssum]
      rw [this]
      exact indepZ.indepFun_finsetSum_of_notMem (fun _ => measurable_pi_apply _) (by simp)
    rw [hsplit, gaussianReal_add_gaussianReal_of_indepFun hind ih (lawZ _)]
    congr 1
    · simp
    · push_cast; ring

def phi (x : ℝ) (z : ℕ → ℝ) : ℕ → ℝ := fun j => x - z j

lemma measurable_phi (x : ℝ) : Measurable (phi x) :=
  measurable_pi_lambda _ fun j => measurable_const.sub (measurable_pi_apply j)

lemma map_phi (x : ℝ) : stdNormalSeq.map (phi x) = PP (gaussianReal x 1) := by
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply (measurable_phi x) (MeasurableSet.pi (Set.to_countable _) fun i _ => ht i)]
  have hpre : phi x ⁻¹' Set.pi (↑s) t = Set.pi (↑s) (fun i => (fun y => x - y) ⁻¹' t i) := by
    ext z; simp [phi]
  rw [hpre, stdNormalSeq, Measure.infinitePi_pi]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Measure.map_apply (by fun_prop) (ht i), gaussianReal_map_const_sub, sub_zero]
  · intro i _; exact (by fun_prop : Measurable fun y : ℝ => x - y) (ht i)

lemma W_phi (x : ℝ) (z : ℕ → ℝ) (n : ℕ) : W (phi x z) n = n * x - Ssum n z := by
  simp [W, phi, Ssum, Finset.sum_sub_distrib]

lemma gauss_scale (m : ℕ) :
    gaussianReal 0 ((m : ℝ≥0) + 1) = (gaussianReal 0 1).map (Real.sqrt ((m : ℝ) + 1) * ·) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext; simp [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]

lemma gauss_Iio_eq_Iic (c : ℝ) : gaussianReal 0 1 (Set.Iio c) = gaussianReal 0 1 (Set.Iic c) := by
  haveI := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  exact measure_congr Iio_ae_eq_Iic

lemma q_eq (x : ℝ) (m : ℕ) :
    (q (gaussianReal x 1) (m + 1)).toReal = Phi (Real.sqrt ((m : ℝ) + 1) * x) := by
  unfold q
  rw [← map_phi, Measure.map_apply (measurable_phi x)
    (measurableSet_lt measurable_const (meas_W _ (n := m + 1) (fun i _ => s_le i) le_rfl))]
  have h1 : phi x ⁻¹' {a | 0 < W a (m + 1)} = Ssum (m + 1) ⁻¹' Set.Iio (((m : ℝ) + 1) * x) := by
    ext z; simp only [Set.mem_preimage, Set.mem_setOf_eq, W_phi, Set.mem_Iio]; push_cast
    constructor <;> intro h <;> linarith
  rw [h1, ← Measure.map_apply (meas_Ssum _) measurableSet_Iio, law_Ssum]
  push_cast
  rw [gauss_scale, Measure.map_apply (by fun_prop) measurableSet_Iio]
  have hs : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hss := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)
  have h2 : (Real.sqrt ((m : ℝ) + 1) * ·) ⁻¹' Set.Iio (((m : ℝ) + 1) * x) =
      Set.Iio (Real.sqrt ((m : ℝ) + 1) * x) := by
    ext y; simp only [Set.mem_preimage, Set.mem_Iio]
    have e : ((m : ℝ) + 1) * x = Real.sqrt ((m : ℝ) + 1) * (Real.sqrt ((m : ℝ) + 1) * x) := by
      rw [← mul_assoc, hss]
    rw [e]
    constructor
    · intro h; exact lt_of_mul_lt_mul_left h hs.le
    · intro h; exact mul_lt_mul_of_pos_left h hs
  rw [h2, gauss_Iio_eq_Iic, Phi, cdf_eq_real, measureReal_def]

lemma Phi_nonneg (t : ℝ) : 0 ≤ Phi t := cdf_nonneg _ _

lemma Phi_neg (t : ℝ) : Phi (-t) = 1 - Phi t := by
  unfold Phi
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def]
  have hmap : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have h1 : gaussianReal 0 1 (Set.Iic (-t)) = gaussianReal 0 1 (Set.Iio t)ᶜ := by
    conv_lhs => rw [← hmap]
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    congr 1; ext y; simp [neg_le]
  rw [h1, prob_compl_eq_one_sub measurableSet_Iio, gauss_Iio_eq_Iic,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

lemma summable_q {x : ℝ} (hx : x < 0) :
    Summable fun n : ℕ => (q (gaussianReal x 1) (n + 1)).toReal / ((n : ℝ) + 1) := by
  set r := Real.exp (-x ^ 2 / 2)
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by have := sq_pos_of_neg hx; linarith)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_geometric_of_lt_one (Real.exp_pos _).le hr1)
  · rw [q_eq]; exact div_nonneg (Phi_nonneg _) (by positivity)
  · rw [q_eq]
    have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hpos : 0 < Real.sqrt ((n : ℝ) + 1) * -x := mul_pos hs (by linarith)
    have h1 : Phi (Real.sqrt ((n : ℝ) + 1) * x) = 1 - Phi (Real.sqrt ((n : ℝ) + 1) * -x) := by
      rw [← Phi_neg]; ring_nf
    have h2 := GreedyRS.Budget.ec2_4_normal_tail_bound _ hpos
    rw [mul_pow, Real.sq_sqrt (by positivity)] at h2
    have h3 : Real.exp (-(((n : ℝ) + 1) * (-x) ^ 2) / 2) ≤ r ^ n := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      nlinarith [sq_nonneg x]
    calc Phi (Real.sqrt ((n : ℝ) + 1) * x) / ((n : ℝ) + 1) ≤ Phi (Real.sqrt ((n : ℝ) + 1) * x) :=
          div_le_self (Phi_nonneg _) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      _ ≤ r ^ n := by rw [h1]; linarith

/-! ### from the ladder event to `AboveFrom` -/

lemma inf_gt {y : ℕ → ℝ} {x L : ℝ} (hy : ∀ n, x < y n) (hlim : Tendsto y atTop (𝓝 L))
    (hL : x < L) : BddBelow (Set.range y) ∧ x < ⨅ n, y n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).1 ((x + L) / 2) (by linarith))
  set m := min ((x + L) / 2) ((Finset.range (N + 1)).inf' ⟨0, by simp⟩ y) with hm
  have hxm : x < m := by
    rw [hm, lt_min_iff]
    exact ⟨by linarith, (Finset.lt_inf'_iff _).2 fun n _ => hy n⟩
  have hmy : ∀ n, m ≤ y n := by
    intro n
    by_cases hn : n < N + 1
    · exact (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 hn))
    · exact (min_le_left _ _).trans (hN n (by omega)).le
  exact ⟨⟨m, by rintro _ ⟨n, rfl⟩; exact hmy n⟩, lt_of_lt_of_le hxm (le_ciInf hmy)⟩

lemma slln0 : ∀ᵐ z ∂stdNormalSeq,
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, z i)) atTop (𝓝 0) := by
  have hint : Integrable (fun z : ℕ → ℝ => z 0) stdNormalSeq := by
    have h1 : Integrable (fun x : ℝ => x) (stdNormalSeq.map (fun z => z 0)) := by
      rw [lawZ]; exact (memLp_id_gaussianReal 1).integrable le_rfl
    exact (integrable_map_measure aestronglyMeasurable_id
      (measurable_pi_apply _).aemeasurable).1 h1
  have h := strong_law_ae (μ := stdNormalSeq) (fun i (z : ℕ → ℝ) => z i) hint
    (fun i j hij => indepZ.indepFun hij)
    (fun i => ⟨(measurable_pi_apply _).aemeasurable, (measurable_pi_apply _).aemeasurable,
      by rw [lawZ, lawZ]⟩)
  have h0 : ∫ z, z 0 ∂stdNormalSeq = 0 := by
    have := integral_map (μ := stdNormalSeq) (φ := fun z : ℕ → ℝ => z 0) (f := fun x : ℝ => x)
      (measurable_pi_apply 0).aemeasurable aestronglyMeasurable_id
    rw [← this, lawZ 0]
    exact integral_id_gaussianReal
  rw [h0] at h
  exact h

lemma ties_null (x : ℝ) (m : ℕ) : stdNormalSeq {z | Ssum (m + 1) z = ((m : ℝ) + 1) * x} = 0 := by
  have : {z : ℕ → ℝ | Ssum (m + 1) z = ((m : ℝ) + 1) * x} = Ssum (m + 1) ⁻¹' {((m : ℝ) + 1) * x} := by
    ext; simp
  rw [this, ← Measure.map_apply (meas_Ssum _) (measurableSet_singleton _), law_Ssum]
  haveI := nullSingletonClass_gaussianReal (μ := 0) (v := ((m + 1 : ℕ) : ℝ≥0)) (by simp)
  exact measure_singleton _

lemma event_eq (x : ℝ) (hx : x < 0) :
    stdNormalSeq {z | AboveFrom (zbar z) 1 x} =
      stdNormalSeq (phi x ⁻¹' {a | ∀ n, 1 ≤ n → W a n ≤ 0}) := by
  set A := {z : ℕ → ℝ | AboveFrom (zbar z) 1 x}
  set B := phi x ⁻¹' {a | ∀ n, 1 ≤ n → W a n ≤ 0}
  have hzbar : ∀ z n, 1 ≤ n → (x < zbar z n ↔ (n : ℝ) * x < Ssum n z) := by
    intro z n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    rw [zbar, lt_div_iff₀ this, mul_comm]; rfl
  have hAB : A ⊆ B := by
    intro z hz n hn
    obtain ⟨hb, hinf⟩ := hz
    have h1 : ⨅ k, zbar z (1 + k) ≤ zbar z (1 + (n - 1)) := ciInf_le hb _
    rw [show 1 + (n - 1) = n by omega] at h1
    have := (hzbar z n hn).1 (lt_of_lt_of_le hinf h1)
    rw [W_phi]; linarith
  set N := (⋃ m : ℕ, {z : ℕ → ℝ | Ssum (m + 1) z = ((m : ℝ) + 1) * x}) ∪
    {z | ¬ Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, z i)) atTop (𝓝 0)}
  have hN : stdNormalSeq N = 0 := by
    refine measure_union_null (measure_iUnion_null fun m => ties_null x m) ?_
    exact ae_iff.1 slln0
  have hBA : B ⊆ A ∪ N := by
    intro z hz
    by_cases hzN : z ∈ N
    · exact Or.inr hzN
    left
    simp only [N, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
      not_not] at hzN
    obtain ⟨hties, hlim⟩ := hzN
    have hy : ∀ n, x < zbar z (1 + n) := by
      intro n
      rw [hzbar z (1 + n) (by omega)]
      have h1 := hz (n + 1) (by omega)
      rw [W_phi] at h1
      have h2 := hties n
      rw [add_comm 1 n]; push_cast at h1 ⊢
      exact lt_of_le_of_ne (by linarith) (fun h => h2 h.symm)
    have hlim' : Tendsto (fun n => zbar z (1 + n)) atTop (𝓝 0) := by
      have e : (fun n => zbar z (1 + n)) =
          (fun n : ℕ => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, z i)) ∘ (fun n => n + 1) := by
        funext n; simp only [Function.comp, zbar, smul_eq_mul, add_comm 1 n]; rw [div_eq_inv_mul]
      rw [e]; exact hlim.comp (tendsto_add_atTop_nat 1)
    exact inf_gt hy hlim' hx
  exact le_antisymm (measure_mono hAB) ((measure_mono hBA).trans
    ((measure_union_le _ _).trans (by rw [hN, add_zero])))

lemma meas_target : MeasurableSet {a : ℕ → ℝ | ∀ n, 1 ≤ n → W a n ≤ 0} := by
  rw [← compl_compl {a : ℕ → ℝ | ∀ n, 1 ≤ n → W a n ≤ 0}, ← union_first]
  exact (MeasurableSet.iUnion fun n => meas_Ev' n 1).compl

theorem main (x : ℝ) (hx : x < 0) :
    stdNormalSeq {z | AboveFrom (zbar z) 1 x} =
      ENNReal.ofReal (Real.exp (-∑' n : ℕ,
        Phi (Real.sqrt ((n : ℝ) + 1) * x) / ((n : ℝ) + 1))) := by
  rw [event_eq x hx, ← Measure.map_apply (measurable_phi x) meas_target, map_phi]
  have h := spitzer (gaussianReal x 1) (summable_q hx)
  simp_rw [q_eq] at h
  rw [← h, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end A3Sp

end Sp6

open GreedyRS.Greedy in
theorem solution (x : ℝ) (hx : x < 0) :
    GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.zbar z) 1 x} =
      ENNReal.ofReal (Real.exp (-∑' n : ℕ,
        GreedyRS.Greedy.Phi (Real.sqrt ((n : ℝ) + 1) * x) / ((n : ℝ) + 1))) ∧
    GreedyRS.Greedy.stdNormalSeq {z | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.zbar z) 1 x} =
      ENNReal.ofReal (1 / GreedyRS.Greedy.Cfun (-x)) := by
  refine ⟨A3Sp.main x hx, ?_⟩
  rw [A3Sp.main x hx, GreedyRS.Greedy.Cfun, one_div, ← Real.exp_neg]
  have : ∀ n : ℕ, -(Real.sqrt ((n : ℝ) + 1)) * -x = Real.sqrt ((n : ℝ) + 1) * x :=
    fun n => by ring
  simp_rw [this]
