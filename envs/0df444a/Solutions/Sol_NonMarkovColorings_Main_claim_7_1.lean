-- Prove2me | solution 1 for NonMarkovColorings.Main.claim_7_1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T02:19:29.016457+00:00
-- url     : https://prove2.me/submissions/2a10ca39-b95a-4acc-a2a1-26009ff24d58

import Mathlib

namespace NonMarkovColorings.Main

def pre (X : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, X i

lemma pre_succ (X : ℕ → ℕ) (n : ℕ) : pre X (n + 1) = pre X n + X (n + 1) := by
  unfold pre
  exact Finset.sum_Icc_succ_top (by omega) _

lemma pre_mono (X : ℕ → ℕ) : Monotone (pre X) :=
  monotone_nat_of_le_succ fun n => by rw [pre_succ]; omega

lemma pre_lt (X : ℕ → ℕ) {j j' : ℕ} (h : j < j') (h1 : X j' = 1) : pre X j < pre X j' := by
  obtain ⟨n, rfl⟩ : ∃ n, j' = n + 1 := ⟨j' - 1, by omega⟩
  have := pre_mono X (show j ≤ n by omega)
  rw [pre_succ]; omega

def Tset (m : ℕ) (X Y : ℕ → ℕ) (E : ℕ) : Finset ℕ :=
  (Finset.Icc 1 m).filter fun j => X j = 1 ∧
    ((pre Y E < pre X j ∧ pre X j ≤ pre X E) ∨ (pre X E < pre X j ∧ pre X j ≤ pre Y E))

lemma Tset_card (m : ℕ) (X Y : ℕ → ℕ) (E : ℕ) (ε : ℝ)
    (hd : |(pre X E : ℝ) - (pre Y E : ℝ)| ≤ ε * m) : ((Tset m X Y E).card : ℝ) ≤ ε * m := by
  have hinj : Set.InjOn (pre X) ↑(Tset m X Y E) := by
    intro j hj j' hj' h
    simp only [Tset, Finset.coe_filter, Set.mem_setOf_eq] at hj hj'
    rcases lt_trichotomy j j' with h1 | h1 | h1
    · exact absurd h (pre_lt X h1 hj'.2.1).ne
    · exact h1
    · exact absurd h (pre_lt X h1 hj.2.1).ne'
  have hsub : (Tset m X Y E).image (pre X) ⊆
      Finset.Ioc (pre Y E) (pre X E) ∪ Finset.Ioc (pre X E) (pre Y E) := by
    intro r hr
    simp only [Finset.mem_image, Tset, Finset.mem_filter] at hr
    obtain ⟨j, ⟨_, _, h⟩, rfl⟩ := hr
    simp only [Finset.mem_union, Finset.mem_Ioc]
    exact h
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at h1
  have h2 := (Finset.card_union_le _ _).trans' h1
  simp only [Nat.card_Ioc] at h2
  have h3 : ((Tset m X Y E).card : ℝ) ≤ (((pre X E - pre Y E : ℕ) : ℝ) + ((pre Y E - pre X E : ℕ) : ℝ)) := by
    exact_mod_cast h2
  refine h3.trans (le_trans ?_ hd)
  rcases le_total (pre X E) (pre Y E) with h | h
  · rw [Nat.sub_eq_zero_of_le h, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast h)),
      Nat.cast_sub h]
    simp
  · rw [Nat.sub_eq_zero_of_le h, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast h)),
      Nat.cast_sub h]
    simp


noncomputable def Eth (m : ℕ) (p : ℕ → ℝ) (θ : ℝ) : ℕ := Nat.findGreatest (fun i => θ ≤ p i) m

lemma Eth_le (m : ℕ) (p : ℕ → ℝ) (θ : ℝ) : Eth m p θ ≤ m := Nat.findGreatest_le m

lemma Eth_ge {m : ℕ} {p : ℕ → ℝ} {θ : ℝ} {q : ℕ} (hq : q ≤ m) (h : θ ≤ p q) : q ≤ Eth m p θ :=
  Nat.le_findGreatest hq h

lemma Eth_spec {m : ℕ} {p : ℕ → ℝ} {θ : ℝ} (h : Eth m p θ ≠ 0) :
    1 ≤ Eth m p θ ∧ θ ≤ p (Eth m p θ) := by
  refine ⟨by omega, ?_⟩
  have h2 : ¬ ∀ k, 0 < k → k ≤ m → ¬ θ ≤ p k := fun hh => h ((Nat.findGreatest_eq_zero_iff).2 hh)
  push_neg at h2
  obtain ⟨k, hk0, hk, hpk⟩ := h2
  exact Nat.findGreatest_spec (P := fun i => θ ≤ p i) hk hpk

lemma Eth_lt {m : ℕ} {p : ℕ → ℝ} {θ : ℝ}
    (hmono : ∀ i ∈ Finset.Icc 1 m, ∀ j ∈ Finset.Icc 1 m, i ≤ j → p j ≤ p i)
    {q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ m) (h : p q < θ) : Eth m p θ < q := by
  by_contra hc
  have hc : q ≤ Eth m p θ := by omega
  have hE : Eth m p θ ≠ 0 := by omega
  obtain ⟨h1, h2⟩ := Eth_spec hE
  have := hmono q (by simp; omega) _ (by simp; exact ⟨h1, Eth_le m p θ⟩) hc
  linarith

lemma Eth_blockend {m : ℕ} {p : ℕ → ℝ} {θ : ℝ} (h : Eth m p θ ≠ 0) :
    Eth m p θ = m ∨ p (Eth m p θ + 1) < p (Eth m p θ) := by
  by_cases hm : Eth m p θ = m
  · exact Or.inl hm
  right
  have hlt : Eth m p θ < m := lt_of_le_of_ne (Eth_le m p θ) hm
  have := Nat.findGreatest_is_greatest (P := fun i => θ ≤ p i) (n := m) (Nat.lt_succ_self _) hlt
  obtain ⟨_, h2⟩ := Eth_spec h
  have h3 : p (Eth m p θ + 1) < θ := not_le.1 this
  linarith


lemma cover (m : ℕ) (ε : ℝ) (p : ℕ → ℝ) (X Y : ℕ → ℕ)
    (hp1 : ∀ i ∈ Finset.Icc 1 m, p i ≤ 1) (hp0 : ∀ i ∈ Finset.Icc 1 m, 0 ≤ p i)
    (hmono : ∀ i ∈ Finset.Icc 1 m, ∀ j ∈ Finset.Icc 1 m, i ≤ j → p j ≤ p i)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 m) (hXj : X j = 1)
    (hbad : let S := (Finset.Icc 1 m).filter fun j' => pre X j ≤ pre Y j'
            S = ∅ ∨ ∃ h : S.Nonempty, Real.sqrt ε < |p j - p (S.min' h)|) :
    j ∈ Tset m X Y m ∨ ∃ a b : ℝ, Real.sqrt ε < b - a ∧ 0 ≤ a ∧ b ≤ 1 ∧
      ∀ θ, a < θ → θ ≤ b → j ∈ Tset m X Y (Eth m p θ) := by
  have hj' := Finset.mem_Icc.1 hj
  have hAj : pre X j ≤ pre X m := pre_mono X hj'.2
  rcases hbad with hS | ⟨hne, hlt⟩
  · left
    have hm : m ∈ (Finset.Icc 1 m) := by simp; omega
    have : m ∉ (Finset.Icc 1 m).filter fun j' => pre X j ≤ pre Y j' := by rw [hS]; simp
    simp only [Finset.mem_filter, not_and, not_le] at this
    simp only [Tset, Finset.mem_filter]
    exact ⟨hj, hXj, Or.inl ⟨this hm, hAj⟩⟩
  · right
    set S := (Finset.Icc 1 m).filter fun j' => pre X j ≤ pre Y j' with hSdef
    set i := S.min' hne with hi
    have hiS : i ∈ S := Finset.min'_mem S hne
    simp only [hSdef, Finset.mem_filter, Finset.mem_Icc] at hiS
    obtain ⟨⟨hi1, hi2⟩, hAi⟩ := hiS
    have hmin : ∀ i', 1 ≤ i' → i' ≤ m → i' < i → pre Y i' < pre X j := by
      intro i' h1 h2 h3
      by_contra hc
      have : i' ∈ S := by simp [hSdef]; exact ⟨⟨h1, h2⟩, by omega⟩
      have := Finset.min'_le S i' this
      omega
    have hpj0 := hp0 j hj
    have hpj1 := hp1 j hj
    have hpi0 := hp0 i (by simp; omega)
    have hpi1 := hp1 i (by simp; omega)
    by_cases hle : p j ≤ p i
    · refine ⟨p j, p i, ?_, hpj0, hpi1, ?_⟩
      · have := abs_sub_comm (p j) (p i)
        rw [abs_of_nonpos (by linarith)] at hlt
        linarith
      · intro θ h1 h2
        have hiE : i ≤ Eth m p θ := Eth_ge hi2 h2
        have hjE : Eth m p θ < j := Eth_lt hmono hj'.1 hj'.2 h1
        have hBi : pre Y i ≤ pre Y (Eth m p θ) := pre_mono Y hiE
        have hlt' : pre X (Eth m p θ) < pre X j := by
          obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
          have := pre_mono X (show Eth m p θ ≤ n by omega)
          rw [pre_succ]; omega
        simp only [Tset, Finset.mem_filter]
        exact ⟨hj, hXj, Or.inr ⟨hlt', by omega⟩⟩
    · push_neg at hle
      refine ⟨p i, p j, ?_, hpi0, hpj1, ?_⟩
      · rw [abs_of_pos (by linarith)] at hlt
        linarith
      · intro θ h1 h2
        have hjE : j ≤ Eth m p θ := Eth_ge hj'.2 h2
        have hiE : Eth m p θ < i := Eth_lt hmono hi1 hi2 h1
        have := hmin (Eth m p θ) (by omega) (Eth_le m p θ) hiE
        simp only [Tset, Finset.mem_filter]
        exact ⟨hj, hXj, Or.inl ⟨this, pre_mono X hjE⟩⟩


lemma union_card_le (m : ℕ) (X Y : ℕ → ℕ) (ε : ℝ) (I : Finset ℕ) (f : ℕ → ℕ) (B : Finset ℕ)
    (h0 : ((Tset m X Y m).card : ℝ) ≤ ε * m)
    (hf : ∀ k ∈ I, ((Tset m X Y (f k)).card : ℝ) ≤ ε * m)
    (hB : B ⊆ Tset m X Y m ∪ I.biUnion fun k => Tset m X Y (f k)) :
    (B.card : ℝ) ≤ ε * m * (1 + I.card) := by
  have h1 := Finset.card_le_card hB
  have h2 := Finset.card_union_le (Tset m X Y m) (I.biUnion fun k => Tset m X Y (f k))
  have h3 := Finset.card_biUnion_le (s := I) (t := fun k => Tset m X Y (f k))
  have h4 : ((∑ k ∈ I, (Tset m X Y (f k)).card : ℕ) : ℝ) ≤ I.card * (ε * m) := by
    push_cast
    calc _ ≤ ∑ k ∈ I, ε * m := Finset.sum_le_sum hf
      _ = _ := by simp
  have h5 : (B.card : ℝ) ≤ (Tset m X Y m).card + ∑ k ∈ I, (Tset m X Y (f k)).card := by
    exact_mod_cast h1.trans (h2.trans (Nat.add_le_add_left h3 _))
  push_cast at h4 h5
  have : (I.card : ℝ) * (ε * m) = ε * m * I.card := by ring
  linarith

end NonMarkovColorings.Main

open NonMarkovColorings.Main

theorem solution (m : ℕ) (ε : ℝ) (p : ℕ → ℝ) (X Y : ℕ → ℕ)
    (hp1 : ∀ i ∈ Finset.Icc 1 m, p i ≤ 1) (hp0 : ∀ i ∈ Finset.Icc 1 m, 0 ≤ p i)
    (hmono : ∀ i ∈ Finset.Icc 1 m, ∀ j ∈ Finset.Icc 1 m, i ≤ j → p j ≤ p i)
    (hX : ∀ i ∈ Finset.Icc 1 m, X i = 0 ∨ X i = 1)
    (hY : ∀ i ∈ Finset.Icc 1 m, Y i = 0 ∨ Y i = 1)
    (hsum : ∀ j ∈ Finset.Icc 1 m, (j = m ∨ p (j + 1) < p j) →
      |∑ i ∈ Finset.Icc 1 j, ((X i : ℝ) - (Y i : ℝ))| ≤ ε * m) :
    (((Finset.Icc 1 m).filter fun j => X j = 1 ∧
        let S := (Finset.Icc 1 m).filter fun j' =>
          ∑ i ∈ Finset.Icc 1 j, X i ≤ ∑ i ∈ Finset.Icc 1 j', Y i
        S = ∅ ∨ ∃ h : S.Nonempty, Real.sqrt ε < |p j - p (S.min' h)|).card : ℝ) ≤
      (ε + Real.sqrt ε) * m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hcast : ∀ E, (∑ i ∈ Finset.Icc 1 E, ((X i : ℝ) - (Y i : ℝ))) = (pre X E : ℝ) - (pre Y E : ℝ) := by
    intro E
    simp [pre, Finset.sum_sub_distrib]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hεm : (0 : ℝ) ≤ ε * m := by
    have := hsum m (by simp; omega) (Or.inl rfl)
    exact (abs_nonneg _).trans this
  have hε : 0 ≤ ε := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hT0 : ((Tset m X Y m).card : ℝ) ≤ ε * m :=
    Tset_card m X Y m ε (by rw [← hcast]; exact hsum m (by simp; omega) (Or.inl rfl))
  have hTE : ∀ θ, ((Tset m X Y (Eth m p θ)).card : ℝ) ≤ ε * m := by
    intro θ
    refine Tset_card m X Y _ ε ?_
    by_cases h0 : Eth m p θ = 0
    · rw [h0]; simpa [pre] using hεm
    · obtain ⟨h1, _⟩ := Eth_spec h0
      rw [← hcast]
      exact hsum _ (by simp; exact ⟨h1, Eth_le m p θ⟩) (Eth_blockend h0)
  set Bd := (Finset.Icc 1 m).filter fun j => X j = 1 ∧
        let S := (Finset.Icc 1 m).filter fun j' =>
          ∑ i ∈ Finset.Icc 1 j, X i ≤ ∑ i ∈ Finset.Icc 1 j', Y i
        S = ∅ ∨ ∃ h : S.Nonempty, Real.sqrt ε < |p j - p (S.min' h)| with hBd
  have hcov : ∀ j ∈ Bd, j ∈ Tset m X Y m ∨ ∃ a b : ℝ, Real.sqrt ε < b - a ∧ 0 ≤ a ∧ b ≤ 1 ∧
      ∀ θ, a < θ → θ ≤ b → j ∈ Tset m X Y (Eth m p θ) := by
    intro j hj
    simp only [hBd, Finset.mem_filter] at hj
    exact cover m ε p X Y hp1 hp0 hmono j hj.1 hj.2.1 hj.2.2
  have hw0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  rcases hε.eq_or_lt with h0 | hpos
  · subst h0
    have hemp : ∀ T : Finset ℕ, (T.card : ℝ) ≤ 0 * m → ∀ j, j ∉ T := by
      intro T hT j hj
      have : T.card = 0 := by
        have : (T.card : ℝ) ≤ 0 := by simpa using hT
        exact_mod_cast le_antisymm (by exact_mod_cast this) (Nat.zero_le _)
      rw [Finset.card_eq_zero] at this
      simp [this] at hj
    have hB : Bd = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      rcases hcov j hj with h | ⟨a, b, hab, ha, hb, hθ⟩
      · exact hemp _ hT0 j h
      · rw [Real.sqrt_zero] at hab
        exact hemp _ (hTE b) j (hθ b (by linarith) le_rfl)
    rw [hB]; simp
  · have hw : 0 < Real.sqrt ε := Real.sqrt_pos.2 hpos
    have hww : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε
    set w := Real.sqrt ε with hwdef
    set K := ⌊1 / w⌋₊ with hK
    have hsub : Bd ⊆ Tset m X Y m ∪ (Finset.Icc 1 K).biUnion
        fun k => Tset m X Y (Eth m p ((k : ℝ) * w)) := by
      intro j hj
      rcases hcov j hj with h | ⟨a, b, hab, ha, hb, hθ⟩
      · exact Finset.mem_union_left _ h
      · apply Finset.mem_union_right
        have hb0 : 0 ≤ b := by linarith
        have h1 : ((⌊b / w⌋₊ : ℕ) : ℝ) ≤ b / w := Nat.floor_le (by positivity)
        have h2 : b / w < ((⌊b / w⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
        have h1' : ((⌊b / w⌋₊ : ℕ) : ℝ) * w ≤ b := by
          rwa [le_div_iff₀ hw] at h1
        have h2' : b < (((⌊b / w⌋₊ : ℕ) : ℝ) + 1) * w := by
          rwa [div_lt_iff₀ hw] at h2
        have h3 : a < ((⌊b / w⌋₊ : ℕ) : ℝ) * w := by nlinarith
        have hk0 : 1 ≤ ⌊b / w⌋₊ := by
          by_contra hc
          have : ⌊b / w⌋₊ = 0 := by omega
          rw [this] at h3
          simp at h3
          linarith
        have hkK : ⌊b / w⌋₊ ≤ K := by
          apply Nat.le_floor
          rw [le_div_iff₀ hw]
          linarith
        rw [Finset.mem_biUnion]
        exact ⟨⌊b / w⌋₊, Finset.mem_Icc.2 ⟨hk0, hkK⟩, hθ _ h3 h1'⟩
    have hcard := union_card_le m X Y ε (Finset.Icc 1 K) (fun k => Eth m p ((k : ℝ) * w)) Bd hT0
      (fun k _ => hTE _) hsub
    have hK1 : (K : ℝ) * w ≤ 1 := by
      have : (K : ℝ) ≤ 1 / w := Nat.floor_le (by positivity)
      rwa [le_div_iff₀ hw] at this
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    have e : ε * m * (1 + K) = ε * m + w * (w * K) * m := by rw [← hww]; ring
    have hlast : w * (w * K) * m ≤ w * m := by
      have : w * (K * w) ≤ w * 1 := mul_le_mul_of_nonneg_left hK1 hw.le
      nlinarith
    calc (Bd.card : ℝ) ≤ ε * m * (1 + K) := by simpa using hcard
      _ ≤ _ := by nlinarith
