-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.clbi_covering
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:45:49.46802+00:00
-- url     : https://prove2.me/submissions/7237dd1a-3b31-450a-af73-453a2c7c0ba3

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

set_option autoImplicit false

open Filter Topology in
lemma clbiCov_affRight {g : ℝ → ℝ} {a b t m : ℝ} (hm : m ≤ t) (ht : t < m + 1)
    (h : ∀ s ∈ Set.Icc m (m + 1), g s = a + b * s) :
    HasDerivWithinAt g b (Set.Ici t) t := by
  have h1 : HasDerivWithinAt (fun s => a + b * s) b (Set.Ici t) t := by
    have := (((hasDerivAt_id t).const_mul b).const_add a).hasDerivWithinAt (s := Set.Ici t)
    simpa using this
  apply h1.congr_of_eventuallyEq
  · have hmem : Set.Icc m (m + 1) ∈ 𝓝[≥] t :=
      Filter.mem_of_superset (Ico_mem_nhdsGE ht) (fun s hs => ⟨le_trans hm hs.1, hs.2.le⟩)
    filter_upwards [hmem] with s hs
    exact h s hs
  · exact h t ⟨hm, ht.le⟩

open Filter Topology in
lemma clbiCov_affLeft {g : ℝ → ℝ} {a b t m : ℝ} (hm : m < t) (ht : t ≤ m + 1)
    (h : ∀ s ∈ Set.Icc m (m + 1), g s = a + b * s) :
    HasDerivWithinAt g b (Set.Iic t) t := by
  have h1 : HasDerivWithinAt (fun s => a + b * s) b (Set.Iic t) t := by
    have := (((hasDerivAt_id t).const_mul b).const_add a).hasDerivWithinAt (s := Set.Iic t)
    simpa using this
  apply h1.congr_of_eventuallyEq
  · have hmem : Set.Icc m (m + 1) ∈ 𝓝[≤] t :=
      Filter.mem_of_superset (Ioc_mem_nhdsLE hm) (fun s hs => ⟨hs.1.le, le_trans hs.2 ht⟩)
    filter_upwards [hmem] with s hs
    exact h s hs
  · exact h t ⟨hm.le, ht⟩

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy in
theorem solution (g : ℝ → ℝ) (hg : IsCLBI g) (s₁ s₂ c : ℝ) (h0 : 0 ≤ s₁) (h12 : s₁ < s₂)
    (hr : ∃ r, HasDerivWithinAt g r (Set.Ici s₂) s₂ ∧ r < c)
    (hl : s₁ = 0 ∨ ∃ l, HasDerivWithinAt g l (Set.Iic s₁) s₁ ∧ c < l) :
    ∃ n : ℕ, s₁ ≤ n ∧ (n : ℝ) ≤ s₂ ∧ InSubdiff g n c := by
  choose a b hab using hg.2
  have hs2 : 0 ≤ s₂ := by linarith
  -- slope at s₂
  obtain ⟨r, hrd, hrc⟩ := hr
  have hbr : b ⌊s₂⌋₊ < c := by
    have hd := clbiCov_affRight (Nat.floor_le hs2) (Nat.lt_floor_add_one s₂) (hab ⌊s₂⌋₊)
    have := (uniqueDiffWithinAt_Ici s₂).eq_deriv _ hd hrd
    rw [this]; exact hrc
  -- slope left of s₁
  have hleft : ∀ k : ℕ, ⌈s₁⌉₊ = k + 1 → c < b k := by
    intro k hk
    have hpos : s₁ ≠ 0 := by
      intro h; rw [h] at hk; simp at hk
    rcases hl with h | ⟨l, hld, hlc⟩
    · exact absurd h hpos
    have hk1 : (k : ℝ) < s₁ := by
      have : k < ⌈s₁⌉₊ := by omega
      exact Nat.lt_ceil.mp this
    have hk2 : s₁ ≤ (k : ℝ) + 1 := by
      have : ⌈s₁⌉₊ ≤ k + 1 := by omega
      have := Nat.ceil_le.mp this
      exact_mod_cast this
    have hd := clbiCov_affLeft hk1 hk2 (hab k)
    have := (uniqueDiffWithinAt_Iic s₁).eq_deriv _ hd hld
    rw [this]; exact hlc
  have hcf : ⌈s₁⌉₊ ≤ ⌊s₂⌋₊ := by
    by_contra hlt
    rw [not_le] at hlt
    have hk : ⌈s₁⌉₊ = ⌊s₂⌋₊ + 1 := by
      have : ⌈s₁⌉₊ ≤ ⌊s₂⌋₊ + 1 := by
        apply Nat.ceil_le.mpr
        have := Nat.lt_floor_add_one s₂
        push_cast
        linarith
      omega
    have := hleft _ hk
    linarith
  have hex : ∃ n : ℕ, ⌈s₁⌉₊ ≤ n ∧ b n ≤ c := ⟨⌊s₂⌋₊, hcf, hbr.le⟩
  classical
  let n := Nat.find hex
  have hn : ⌈s₁⌉₊ ≤ n ∧ b n ≤ c := Nat.find_spec hex
  have hnle : n ≤ ⌊s₂⌋₊ := Nat.find_min' hex ⟨hcf, hbr.le⟩
  refine ⟨n, ?_, ?_, ?_⟩
  · exact le_trans (Nat.le_ceil s₁) (by exact_mod_cast hn.1)
  · exact le_trans (by exact_mod_cast hnle) (Nat.floor_le hs2)
  · refine ⟨⟨b n, ?_, hn.2⟩, ?_⟩
    · exact clbiCov_affRight (le_refl _) (by linarith) (hab n)
    · rcases Nat.eq_zero_or_eq_succ_pred n with h | h
      · left; rw [h]; simp
      · right
        set k := n.pred with hkdef
        refine ⟨b k, ?_, ?_⟩
        · have hn' : (n : ℝ) = (k : ℝ) + 1 := by rw [h]; push_cast; ring
          rw [hn']
          exact clbiCov_affLeft (by linarith) (le_refl _) (hab k)
        · by_cases hck : ⌈s₁⌉₊ ≤ k
          · have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
            exact (lt_of_not_ge (fun hb => hmin ⟨hck, hb⟩)).le
          · have : ⌈s₁⌉₊ = k + 1 := by omega
            exact (hleft k this).le
