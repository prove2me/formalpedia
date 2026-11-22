-- Prove2me | solution 1 for MasulloGRH.heckeLFunction_classical_zero_free_region
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T15:10:51.606374+00:00
-- url     : https://prove2.me/submissions/496b73f2-a191-4cff-a1dc-0a8fcb950d5b

import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Theorems.Thm_MasulloGRH_heckeLFunction_zero_free_region_large_height
import Theorems.Thm_MasulloGRH_heckeLFunction_no_zero_re_ge_one

set_option autoImplicit false

open MasulloGRH Filter Topology

namespace MasulloGRH.PropB611

/-- `L_f(s, χ)` is meromorphic in normal form on `ℂ`. -/
lemma meromorphicNFOn_heckeLFunction {F : Type*} [Field F] [NumberField F]
    (χ : HeckeCharacter F) : MeromorphicNFOn (heckeLFunction χ) Set.univ := by
  have h := heckeLFunction_exists_meromorphic_continuation F χ
  unfold heckeLFunction
  rw [dif_pos h]
  exact h.choose_spec.1

/-- At a point where `f` is analytic and nonzero, the meromorphic order is `0`. -/
lemma meromorphicOrderAt_nonpos_of_analyticAt_of_ne_zero {f : ℂ → ℂ} {s : ℂ}
    (hA : AnalyticAt ℂ f s) (h0 : f s ≠ 0) : meromorphicOrderAt f s ≤ 0 := by
  rw [hA.meromorphicOrderAt_eq, (hA.analyticOrderAt_eq_zero).2 h0]
  simp

/-- If the order of a meromorphic function at `z` is at most `0`, then it is at most `0` at
every point near `z`: zeros of a meromorphic function do not accumulate at a non-zero. -/
lemma eventually_meromorphicOrderAt_nonpos {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z)
    (hz : meromorphicOrderAt f z ≤ 0) : ∀ᶠ w in 𝓝 z, meromorphicOrderAt f w ≤ 0 := by
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exfalso
    have htop : meromorphicOrderAt f z = ⊤ := meromorphicOrderAt_eq_top_iff.2 h0
    rw [htop] at hz
    exact absurd hz (by simp)
  · have hev : ∀ᶠ w in 𝓝[≠] z, meromorphicOrderAt f w ≤ 0 :=
      (hne.and hf.eventually_analyticAt).mono fun w hw =>
        meromorphicOrderAt_nonpos_of_analyticAt_of_ne_zero hw.2 hw.1
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with w hw
    by_cases hwz : w = z
    · rw [hwz]; exact hz
    · exact hw hwz

lemma one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

end MasulloGRH.PropB611

open MasulloGRH.PropB611 in
theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) < s.re →
      meromorphicOrderAt (heckeLFunction χ) s ≤ 0 := by
  obtain ⟨cA, hcA, T, hA⟩ := heckeLFunction_zero_free_region_large_height F χ
  have hB := heckeLFunction_no_zero_re_ge_one F χ
  have hNF := meromorphicNFOn_heckeLFunction χ
  set T₁ : ℝ := max T 3 with hT₁
  -- the compact segment `{1 + i t : |t| ≤ T₁}` of the line `Re s = 1`
  set I : Set ℂ := (fun t : ℝ => (1 : ℂ) + t * Complex.I) '' Set.Icc (-T₁) T₁ with hIdef
  have hIc : IsCompact I := isCompact_Icc.image (by fun_prop)
  set G : Set ℂ := {z | ∀ᶠ w in 𝓝 z, meromorphicOrderAt (heckeLFunction χ) w ≤ 0} with hGdef
  have hGo : IsOpen G := isOpen_setOfPred_eventually_nhds
  have hIG : I ⊆ G := by
    rintro _ ⟨t, -, rfl⟩
    exact eventually_meromorphicOrderAt_nonpos (hNF.meromorphicOn _ (Set.mem_univ _))
      (hB _ (by simp))
  obtain ⟨δ, hδ, hthick⟩ := hIc.exists_thickening_subset_open hGo hIG
  refine ⟨min cA δ, lt_min hcA hδ, fun s hs => ?_⟩
  rcases le_or_gt 1 s.re with h1 | h1
  · exact hB s h1
  have hlog3 : 1 ≤ Real.log (|s.im| + 3) :=
    one_le_log_of_three_le (by linarith [abs_nonneg s.im])
  rcases le_or_gt T₁ |s.im| with hT | hT
  · -- large height: the classical region of child (A)
    have h3 : (3 : ℝ) ≤ |s.im| := le_trans (le_max_right _ _) hT
    have hl : 1 ≤ Real.log |s.im| := one_le_log_of_three_le h3
    have hll : Real.log |s.im| ≤ Real.log (|s.im| + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    apply hA s (le_trans (le_max_left _ _) hT)
    have h1' : min cA δ / Real.log (|s.im| + 3) ≤ min cA δ / Real.log |s.im| :=
      div_le_div_of_nonneg_left (le_of_lt (lt_min hcA hδ)) (by linarith) hll
    have h2' : min cA δ / Real.log |s.im| ≤ cA / Real.log |s.im| :=
      div_le_div_of_nonneg_right (min_le_left _ _) (by linarith)
    linarith
  · -- bounded height: the thickening of the compact segment
    have hc' : min cA δ / Real.log (|s.im| + 3) ≤ δ :=
      le_trans (div_le_self (le_of_lt (lt_min hcA hδ)) hlog3) (min_le_right _ _)
    have hmem : s ∈ Metric.thickening δ I := by
      rw [Metric.mem_thickening_iff]
      refine ⟨(1 : ℂ) + (s.im : ℂ) * Complex.I, ⟨s.im, ?_, rfl⟩, ?_⟩
      · rw [Set.mem_Icc]
        exact ⟨by linarith [neg_abs_le s.im], le_trans (le_abs_self _) hT.le⟩
      · have heq : s - ((1 : ℂ) + (s.im : ℂ) * Complex.I) = ((s.re - 1 : ℝ) : ℂ) := by
          apply Complex.ext <;> simp
        rw [dist_eq_norm, heq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
        linarith
    exact (hthick hmem).self_of_nhds
