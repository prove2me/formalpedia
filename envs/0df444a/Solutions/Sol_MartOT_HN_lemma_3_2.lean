-- Prove2me | solution 1 for MartOT.HN.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:46:26.046452+00:00
-- url     : https://prove2.me/submissions/7e706e71-0598-4552-b817-9a33916b1f64

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory

/-- A set with at least `k` elements contains a strictly increasing `k`-tuple. -/
lemma hn32_tuple (k : ℕ) (s : Set ℝ) (hs : (k : ℕ∞) ≤ s.encard) :
    ∃ b : Fin k → ℝ, StrictMono b ∧ ∀ i, b i ∈ s := by
  obtain ⟨t, hts, htk⟩ := Set.exists_subset_encard_eq hs
  have hfin : t.Finite := Set.finite_of_encard_eq_coe htk
  have hcard : hfin.toFinset.card = k := by
    have h1 := hfin.cast_ncard_eq
    rw [htk, Set.ncard_eq_toFinset_card t hfin] at h1
    exact_mod_cast h1
  refine ⟨fun i => hfin.toFinset.orderEmbOfFin hcard i,
    (hfin.toFinset.orderEmbOfFin hcard).strictMono, fun i => hts ?_⟩
  exact (Set.Finite.mem_toFinset hfin).mp (hfin.toFinset.orderEmbOfFin_mem hcard i)

/-- Points of `A` that are not approximated from one side (given by `side`) are countably
many. -/
lemma hn32_countable (k : ℕ) (A : Set ℝ) (F : ℝ → ℝ × (Fin k → ℝ))
    (side : ℝ → ℝ → Prop) (hside : ∀ a a', a ≠ a' → side a a' ∨ side a' a) :
    {a ∈ A | ∃ ε > 0, ∀ a' ∈ A, side a a' → ¬ dist (F a') (F a) < ε}.Countable := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis (ℝ × (Fin k → ℝ))
  set R := {a ∈ A | ∃ ε > 0, ∀ a' ∈ A, side a a' → ¬ dist (F a') (F a) < ε} with hR
  have hex : ∀ a ∈ R, ∃ U ∈ B, F a ∈ U ∧ ∀ a' ∈ A, side a a' → F a' ∉ U := by
    rintro a ⟨-, ε, hε, hno⟩
    obtain ⟨U, hUB, haU, hUsub⟩ :=
      hB.exists_subset_of_mem_open (Metric.mem_ball_self hε) Metric.isOpen_ball
    exact ⟨U, hUB, haU, fun a' ha' hs hU => hno a' ha' hs (hUsub hU)⟩
  choose! g hgB hgmem hgno using hex
  refine Set.MapsTo.countable_of_injOn (f := g) (t := B) (fun a ha => hgB a ha) ?_ hBc
  intro a1 h1 a2 h2 heq
  by_contra hne
  rcases hside a1 a2 hne with hs | hs
  · exact hgno a1 h1 a2 h2.1 hs (heq ▸ hgmem a2 h2)
  · exact hgno a2 h2 a1 h1.1 hs (heq.symm ▸ hgmem a1 h1)

theorem solution (k : ℕ) (hk : 0 < k) (Γ : Set (ℝ × ℝ))
    (hunc : ¬ {a : ℝ | (k : ℕ∞) ≤ {y : ℝ | (a, y) ∈ Γ}.encard}.Countable) :
    ∃ (a : ℝ) (b : Fin k → ℝ), StrictMono b ∧ (∀ i, (a, b i) ∈ Γ) ∧
      ∀ ε : ℝ, 0 < ε →
        (∃ a' : ℝ, a < a' ∧ ∃ b' : Fin k → ℝ, StrictMono b' ∧ (∀ i, (a', b' i) ∈ Γ) ∧
          |a - a'| < ε ∧ ∀ i, |b i - b' i| < ε) ∧
        (∃ a'' : ℝ, a'' < a ∧ ∃ b'' : Fin k → ℝ, StrictMono b'' ∧ (∀ i, (a'', b'' i) ∈ Γ) ∧
          |a - a''| < ε ∧ ∀ i, |b i - b'' i| < ε) := by
  set A := {a : ℝ | (k : ℕ∞) ≤ {y : ℝ | (a, y) ∈ Γ}.encard} with hA
  have hex : ∀ a ∈ A, ∃ b : Fin k → ℝ, StrictMono b ∧ ∀ i, (a, b i) ∈ Γ := by
    intro a ha
    obtain ⟨b, hb, hbs⟩ := hn32_tuple k _ ha
    exact ⟨b, hb, hbs⟩
  choose! b hbmono hbmem using hex
  set F : ℝ → ℝ × (Fin k → ℝ) := fun a => (a, b a) with hF
  have hR := hn32_countable k A F (fun a a' => a < a') (fun a a' h => lt_or_gt_of_ne h)
  have hL := hn32_countable k A F (fun a a' => a' < a) (fun a a' h => (lt_or_gt_of_ne h).symm)
  have hnot : ¬ A ⊆ {a ∈ A | ∃ ε > 0, ∀ a' ∈ A, a < a' → ¬ dist (F a') (F a) < ε} ∪
      {a ∈ A | ∃ ε > 0, ∀ a' ∈ A, a' < a → ¬ dist (F a') (F a) < ε} :=
    fun hsub => hunc ((hR.union hL).mono hsub)
  rw [Set.not_subset] at hnot
  obtain ⟨a, haA, hnot⟩ := hnot
  simp only [Set.mem_union, Set.mem_sep_iff, not_or, not_and, not_exists, not_forall,
    not_not] at hnot
  obtain ⟨hnR, hnL⟩ := hnot
  have key : ∀ a' ε, dist (F a') (F a) < ε → |a - a'| < ε ∧ ∀ i, |b a i - b a' i| < ε := by
    intro a' ε hd
    have hε : 0 < ε := lt_of_le_of_lt dist_nonneg hd
    rw [Prod.dist_eq, max_lt_iff] at hd
    obtain ⟨h1, h2⟩ := hd
    rw [dist_pi_lt_iff hε] at h2
    refine ⟨by rw [abs_sub_comm]; exact h1, fun i => ?_⟩
    have := h2 i
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this
  refine ⟨a, b a, hbmono a haA, hbmem a haA, fun ε hε => ⟨?_, ?_⟩⟩
  · obtain ⟨a', ha'A, hlt, hd⟩ := hnR haA ε hε
    exact ⟨a', hlt, b a', hbmono a' ha'A, hbmem a' ha'A, key a' ε hd⟩
  · obtain ⟨a', ha'A, hlt, hd⟩ := hnL haA ε hε
    exact ⟨a', hlt, b a', hbmono a' ha'A, hbmem a' ha'A, key a' ε hd⟩
