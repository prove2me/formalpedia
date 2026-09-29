-- Prove2me | solution 1 for HomeoLine.exists_zpow_apply_gt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-10T15:46:41.484414+00:00
-- url     : https://prove2.me/submissions/e38c32ef-0fdd-4a3c-a86b-f4c596ba2dda

import Mathlib


open Filter Topology

/-- The increasing half of Brin–Squier (3.4): if `f` moves every point of `[c, d]` and moves `c`
to the right, then a positive power of `f` carries `c` beyond `d`. -/
private lemma aux_of_lt (f : ℝ ≃o ℝ) {c d : ℝ}
    (h : ∀ t ∈ Set.Icc c d, f t ≠ t) (hc : c < f c) :
    ∃ n : ℕ, d < (f ^ n) c := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  set a : ℕ → ℝ := fun n => (f ^ n) c with ha
  have ha0 : a 0 = c := by simp [ha]
  have hstep : ∀ n, a (n + 1) = f (a n) := by
    intro n
    simp [ha, pow_succ']
  -- the orbit is strictly increasing
  have hlt : ∀ n, a n < a (n + 1) := by
    intro n
    induction n with
    | zero => rw [ha0, hstep, ha0]; exact hc
    | succ k ih =>
        have h2 := f.strictMono ih
        rwa [← hstep k, ← hstep (k + 1)] at h2
  have hmono : StrictMono a := strictMono_nat_of_lt_succ hlt
  -- it is bounded above by `d`
  have hbdd : BddAbove (Set.range a) := ⟨d, by rintro x ⟨n, rfl⟩; exact hcon n⟩
  set L : ℝ := ⨆ n, a n with hL
  have htend : Tendsto a atTop (𝓝 L) := tendsto_atTop_ciSup hmono.monotone hbdd
  -- the limit is a fixed point of `f`
  have h1 : Tendsto (fun n => f (a n)) atTop (𝓝 (f L)) :=
    (f.continuous.tendsto L).comp htend
  have h2 : Tendsto (fun n => f (a n)) atTop (𝓝 L) := by
    have : Tendsto (fun n => a (n + 1)) atTop (𝓝 L) :=
      htend.comp (tendsto_add_atTop_nat 1)
    simpa only [hstep] using this
  have hfix : f L = L := tendsto_nhds_unique h1 h2
  -- and it lies in `[c, d]`, contradicting the hypothesis
  have hcL : c ≤ L := ha0 ▸ le_ciSup hbdd 0
  have hLd : L ≤ d := ciSup_le hcon
  exact h L ⟨hcL, hLd⟩ hfix

/-- **Brin–Squier (3.4).**  If an orientation-preserving homeomorphism `f` of `ℝ` moves every
point of a closed interval `[c, d]`, then some integer power of `f` carries `c` beyond `d`. -/
theorem solution (f : ℝ ≃o ℝ) {c d : ℝ} (h : ∀ t ∈ Set.Icc c d, f t ≠ t) :
    ∃ n : ℤ, d < (f ^ n) c := by
  rcases lt_or_ge d c with hdc | hcd
  · exact ⟨0, by simpa using hdc⟩
  have hcmem : c ∈ Set.Icc c d := ⟨le_rfl, hcd⟩
  have hne : f c ≠ c := h c hcmem
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- `f c < c`: run the increasing argument on `f⁻¹`
    have h' : ∀ t ∈ Set.Icc c d, f⁻¹ t ≠ t := by
      intro t ht hft
      refine h t ht ?_
      calc f t = f (f⁻¹ t) := by rw [hft]
        _ = t := RelIso.apply_inv_self f t
    have hc' : c < f⁻¹ c := by
      have := (f⁻¹ : ℝ ≃o ℝ).strictMono hlt
      rwa [RelIso.inv_apply_self] at this
    obtain ⟨n, hn⟩ := aux_of_lt f⁻¹ h' hc'
    refine ⟨-(n : ℤ), ?_⟩
    rwa [zpow_neg, zpow_natCast, ← inv_pow]
  · obtain ⟨n, hn⟩ := aux_of_lt f h hlt
    exact ⟨(n : ℤ), by rwa [zpow_natCast]⟩

