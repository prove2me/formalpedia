-- Prove2me | solution 1 for LonelyRunnerConjecture.lacunary_speeds
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:32:31.090795+00:00
-- url     : https://prove2.me/submissions/7d4151a0-734d-4df6-966b-d9409aa95517

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

set_option autoImplicit false

open LonelyRunnerConjecture

private lemma good_of (δ y : ℝ) (n : ℤ) (hδ : 0 < δ) (h1 : (n : ℝ) + δ ≤ y)
    (h2 : y ≤ n + 1 - δ) : δ ≤ distToNearestInt y := by
  have hfl : ⌊y⌋ = n := by
    rw [Int.floor_eq_iff]; constructor <;> linarith
  have hfr : Int.fract y = y - n := by unfold Int.fract; rw [hfl]
  unfold distToNearestInt
  rw [hfr]
  apply le_min <;> linarith

private lemma step (δ c a : ℝ) (hδ : 0 < δ) (hc1 : δ ≤ c) (hc2 : c ≤ 1 - δ) :
    ∃ x : ℝ, a ≤ x ∧ x + (c - δ) ≤ a + 2 * c ∧
      ∃ m : ℤ, (m : ℝ) + δ ≤ x ∧ x + (c - δ) ≤ m + 1 - δ := by
  have h0 : ((⌊a⌋ : ℤ) : ℝ) ≤ a := Int.floor_le a
  have h1 : a < ((⌊a⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one a
  by_cases hA : a < (⌊a⌋ : ℝ) + δ
  · exact ⟨(⌊a⌋ : ℝ) + δ, by linarith, by linarith, ⌊a⌋, le_rfl, by linarith⟩
  by_cases hB : a + c ≤ (⌊a⌋ : ℝ) + 1
  · exact ⟨a, le_rfl, by linarith, ⌊a⌋, by linarith, by linarith⟩
  · refine ⟨(⌊a⌋ : ℝ) + 1 + δ, by linarith, by linarith, ⌊a⌋ + 1, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith

private lemma main (δ : ℝ) (hδ : 0 < δ) (s : Finset ℕ) :
    (∀ v ∈ s, 0 < v) → (∀ a ∈ s, ∀ b ∈ s, a < b → 2 * a ≤ b) →
    ((s.card : ℝ) + 1) * δ ≤ 1 → ∀ M ∈ s, (∀ v ∈ s, v ≤ M) →
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → t ≤ T + (1 - ((s.card : ℝ) + 1) * δ) / M →
      ∀ v ∈ s, δ ≤ distToNearestInt (t * v) := by
  induction s using Finset.induction_on_max with
  | empty => intro _ _ _ M hM; simp at hM
  | insert a s hlt ih =>
    intro hpos hdoub hcard M hM hMax
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hMa : M = a := by
      rcases Finset.mem_insert.1 hM with h | h
      · exact h
      · exact absurd (hMax a (Finset.mem_insert_self a s)) (not_le.2 (hlt M h))
    subst hMa
    rw [Finset.card_insert_of_notMem has] at hcard ⊢
    push_cast at hcard ⊢
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hpos M (Finset.mem_insert_self _ _)
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      simp only [Finset.card_empty, Nat.cast_zero] at hcard ⊢
      refine ⟨δ / M, fun t ht1 ht2 v hv => ?_⟩
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hv
      subst hv
      have e1 : δ ≤ t * v := by rwa [div_le_iff₀ hMpos] at ht1
      have e2 : t * v ≤ 1 - δ := by
        rw [← add_div, le_div_iff₀ hMpos] at ht2; linarith
      exact good_of δ _ 0 hδ (by simpa using e1) (by simpa using e2)
    · have hM's : s.max' hs ∈ s := s.max'_mem hs
      have hM'le : ∀ v ∈ s, v ≤ s.max' hs := fun v hv => s.le_max' v hv
      have hcn : 0 ≤ (s.card : ℝ) * δ := by positivity
      obtain ⟨T', hT'⟩ := ih (fun v hv => hpos v (Finset.mem_insert_of_mem hv))
        (fun a ha b hb => hdoub a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb))
        (by linarith) (s.max' hs) hM's hM'le
      have h2 : 2 * s.max' hs ≤ M := hdoub _ (Finset.mem_insert_of_mem hM's) M
        (Finset.mem_insert_self _ _) (hlt _ hM's)
      have h2r : (2 : ℝ) * (s.max' hs : ℝ) ≤ M := by exact_mod_cast h2
      have hM'pos : (0 : ℝ) < (s.max' hs : ℝ) := by
        exact_mod_cast hpos _ (Finset.mem_insert_of_mem hM's)
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 - ((s.card : ℝ) + 1) * δ := ⟨_, rfl⟩
      rw [← hc] at hT'
      have hc1 : δ ≤ c := by rw [hc]; linarith
      have hc2 : c ≤ 1 - δ := by rw [hc]; linarith
      have hc0 : 0 ≤ c := by linarith
      obtain ⟨x, hx1, hx2, m, hm1, hm2⟩ := step δ c (T' * M) hδ hc1 hc2
      refine ⟨x / M, fun t ht1 ht2 v hv => ?_⟩
      have htM1 : x ≤ t * M := by rwa [div_le_iff₀ hMpos] at ht1
      have htM2 : t * M ≤ x + (c - δ) := by
        have e : (1 - ((s.card : ℝ) + 1 + 1) * δ) = c - δ := by rw [hc]; ring
        rw [e, ← add_div, le_div_iff₀ hMpos] at ht2; exact ht2
      rcases Finset.mem_insert.1 hv with rfl | hv
      · exact good_of δ _ m hδ (by linarith) (by linarith)
      · apply hT' t _ _ v hv
        · by_contra hcon
          rw [not_le] at hcon
          have : t * M < T' * M := mul_lt_mul_of_pos_right hcon hMpos
          linarith
        · have hq : 2 * c / M ≤ c / (s.max' hs : ℝ) := by
            rw [div_le_div_iff₀ hMpos hM'pos]; nlinarith
          have ht3 : t ≤ T' + 2 * c / M := by
            have e : T' + 2 * c / M = (T' * M + 2 * c) / M := by field_simp
            rw [e, le_div_iff₀ hMpos]; linarith
          linarith

theorem solution (k : ℕ) (hk : 2 ≤ k) (S : Finset ℕ) (hS : S.card = k)
    (hpos : ∀ v ∈ S, 0 < v)
    (hdoub : ∀ a ∈ S, ∀ b ∈ S, a < b → 2 * a ≤ b) :
    ∃ t : ℝ, ∀ v ∈ S, (1 : ℝ) / (k + 1 : ℝ) ≤ distToNearestInt (t * (v : ℝ)) := by
  have hne : S.Nonempty := by rw [← Finset.card_pos, hS]; omega
  have hδ : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
  have hk1 : ((S.card : ℝ) + 1) * (1 / (k + 1 : ℝ)) = 1 := by
    rw [hS]; field_simp
  obtain ⟨T, hT⟩ := main (1 / (k + 1 : ℝ)) hδ S hpos hdoub hk1.le (S.max' hne)
    (S.max'_mem hne) (fun v hv => S.le_max' v hv)
  refine ⟨T, fun v hv => hT T le_rfl ?_ v hv⟩
  rw [hk1]; simp
