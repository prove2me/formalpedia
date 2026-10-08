-- Prove2me | solution 1 for LocalRademacher.StarHull.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:07:35.903192+00:00
-- url     : https://prove2.me/submissions/0600de84-d1f3-4d1d-92d2-3f36e4512da5

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_LocalRademacher_StarHull_Classes

set_option autoImplicit false

theorem e92_sr_le {ψ : ℝ → ℝ} (hanti : AntitoneOn (fun r => ψ r / Real.sqrt r) (Set.Ioi 0))
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : ψ t * Real.sqrt s ≤ ψ s * Real.sqrt t := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have key := hanti (Set.mem_Ioi.mpr hs) (Set.mem_Ioi.mpr ht) hst
  simp only at key
  rwa [div_le_div_iff₀ (Real.sqrt_pos.mpr ht) (Real.sqrt_pos.mpr hs)] at key

theorem e92_sr_strict {ψ : ℝ → ℝ} (hanti : AntitoneOn (fun r => ψ r / Real.sqrt r) (Set.Ioi 0))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (hps : 0 < ψ s) : ψ t * s < ψ s * t := by
  have h := e92_sr_le hanti hs hst.le
  have ht : 0 < t := lt_trans hs hst
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hlt : Real.sqrt s < Real.sqrt t := Real.sqrt_lt_sqrt hs.le hst
  have hs0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have h1 : ψ t * Real.sqrt s * Real.sqrt s ≤ ψ s * Real.sqrt t * Real.sqrt s :=
    mul_le_mul_of_nonneg_right h hs0
  have h2 : 0 < ψ s * Real.sqrt t * (Real.sqrt t - Real.sqrt s) := by
    have : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have : 0 < Real.sqrt t - Real.sqrt s := by linarith
    positivity
  calc ψ t * s = ψ t * Real.sqrt s * Real.sqrt s := by rw [mul_assoc, hss]
    _ ≤ ψ s * Real.sqrt t * Real.sqrt s := h1
    _ < ψ s * Real.sqrt t * Real.sqrt t := by nlinarith
    _ = ψ s * t := by rw [mul_assoc, htt]

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized in
theorem solution (ψ : ℝ → ℝ) (hψ : IsSubRoot ψ) (hnt : ∃ r, 0 ≤ r ∧ ψ r ≠ 0) :
    ContinuousOn ψ (Set.Ioi 0) ∧ (∃! rstar : ℝ, 0 < rstar ∧ ψ rstar = rstar) ∧
      ∀ rstar : ℝ, 0 < rstar → ψ rstar = rstar → ∀ r : ℝ, 0 < r → (ψ r ≤ r ↔ rstar ≤ r) := by
  obtain ⟨hnn, hmono, hanti⟩ := hψ
  -- positivity on (0, ∞)
  have hpos : ∀ r, 0 < r → 0 < ψ r := by
    obtain ⟨r0, hr0, hne⟩ := hnt
    have h0 : 0 < ψ r0 := lt_of_le_of_ne (hnn r0 hr0) (Ne.symm hne)
    intro r hr
    rcases le_or_gt r0 r with h | h
    · exact lt_of_lt_of_le h0 (hmono (Set.mem_Ici.mpr hr0) (Set.mem_Ici.mpr hr.le) h)
    · have h' := e92_sr_le hanti hr h.le
      rcases (hnn r hr.le).eq_or_lt with he | he
      · rw [← he] at h'
        have : 0 < ψ r0 * Real.sqrt r := mul_pos h0 (Real.sqrt_pos.mpr hr)
        linarith
      · exact he
  -- continuity
  have hcont : ContinuousOn ψ (Set.Ioi 0) := by
    intro y hy
    have hy : 0 < y := hy
    apply ContinuousAt.continuousWithinAt
    have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have hψy : 0 ≤ ψ y := hnn y hy.le
    set L : ℝ → ℝ := fun x => ψ y * min 1 (Real.sqrt x / Real.sqrt y) with hL
    set U : ℝ → ℝ := fun x => ψ y * max 1 (Real.sqrt x / Real.sqrt y) with hU
    have hLc : Filter.Tendsto L (nhds y) (nhds (ψ y)) := by
      have hc : Continuous L :=
        continuous_const.mul (continuous_const.min (Real.continuous_sqrt.div_const _))
      have := hc.tendsto y
      simpa [hL, div_self hsy.ne'] using this
    have hUc : Filter.Tendsto U (nhds y) (nhds (ψ y)) := by
      have hc : Continuous U :=
        continuous_const.mul (continuous_const.max (Real.continuous_sqrt.div_const _))
      have := hc.tendsto y
      simpa [hU, div_self hsy.ne'] using this
    have hev : ∀ᶠ x in nhds y, 0 < x := Ioi_mem_nhds hy
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLc hUc ?_ ?_
    · filter_upwards [hev] with x hx
      simp only [hL]
      rcases le_total x y with hxy | hxy
      · -- ψ y * √x ≤ ψ x * √y
        have h := e92_sr_le hanti hx hxy
        have : ψ y * (Real.sqrt x / Real.sqrt y) ≤ ψ x := by
          rw [mul_div_assoc', div_le_iff₀ hsy]; exact h
        exact le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hψy) this
      · have : ψ y ≤ ψ x := hmono (Set.mem_Ici.mpr hy.le) (Set.mem_Ici.mpr hx.le) hxy
        have h2 : ψ y * min 1 (Real.sqrt x / Real.sqrt y) ≤ ψ y * 1 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hψy
        linarith
    · filter_upwards [hev] with x hx
      simp only [hU]
      rcases le_total x y with hxy | hxy
      · have : ψ x ≤ ψ y := hmono (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr hy.le) hxy
        have h2 : ψ y * 1 ≤ ψ y * max 1 (Real.sqrt x / Real.sqrt y) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hψy
        linarith
      · have h := e92_sr_le hanti hy hxy
        have : ψ x ≤ ψ y * (Real.sqrt x / Real.sqrt y) := by
          rw [mul_div_assoc', le_div_iff₀ hsy]; exact h
        exact le_trans this (mul_le_mul_of_nonneg_left (le_max_right _ _) hψy)
  -- strict decrease of ψ r / r
  have hstrict : ∀ s t, 0 < s → s < t → ψ t * s < ψ s * t :=
    fun s t hs hst => e92_sr_strict hanti hs hst (hpos s hs)
  have hiff : ∀ rstar : ℝ, 0 < rstar → ψ rstar = rstar → ∀ r : ℝ, 0 < r →
      (ψ r ≤ r ↔ rstar ≤ r) := by
    intro rs hrs hfix r hr
    constructor
    · intro hle
      by_contra hlt
      rw [not_le] at hlt
      have := hstrict r rs hr hlt
      rw [hfix] at this
      nlinarith
    · intro hle
      rcases hle.eq_or_lt with he | hlt
      · rw [← he, hfix]
      · have := hstrict rs r hrs hlt
        rw [hfix] at this
        by_contra hc
        rw [not_le] at hc
        nlinarith
  -- existence
  set c := ψ 1 with hcdef
  have hc : 0 < c := hpos 1 one_pos
  have hexist : ∃ rs, 0 < rs ∧ ψ rs = rs := by
    set m := min c 1 with hm
    have hm0 : 0 < m := lt_min hc one_pos
    have hmc : m ≤ c := min_le_left _ _
    have hm1 : m ≤ 1 := min_le_right _ _
    set a := (m / 2) ^ 2 with ha
    set b := (c + 1) ^ 2 with hb
    have ha0 : 0 < a := by positivity
    have hsa : Real.sqrt a = m / 2 := by
      rw [ha, Real.sqrt_sq (by positivity)]
    have hsb : Real.sqrt b = c + 1 := by
      rw [hb, Real.sqrt_sq (by positivity)]
    have ha1 : a ≤ 1 := by
      rw [ha]; nlinarith
    have hb1 : 1 ≤ b := by
      rw [hb]; nlinarith
    have hab : a ≤ b := le_trans ha1 hb1
    -- ψ a > a
    have hFa : 0 < ψ a - a := by
      have h := e92_sr_le hanti ha0 ha1
      rw [Real.sqrt_one, hsa, mul_one] at h
      -- c * (m/2) ≤ ψ a, a = (m/2)^2 < c*(m/2)
      have : (m / 2) ^ 2 < c * (m / 2) := by nlinarith
      nlinarith
    have hFb : ψ b - b < 0 := by
      have h := e92_sr_le hanti one_pos hb1
      rw [Real.sqrt_one, hsb, mul_one] at h
      have : c * (c + 1) < (c + 1) ^ 2 := by nlinarith
      nlinarith
    have hcF : ContinuousOn (fun r => ψ r - r) (Set.Icc a b) := by
      apply ContinuousOn.sub _ continuousOn_id
      exact hcont.mono (fun x hx => lt_of_lt_of_le ha0 hx.1)
    have hmem : (0 : ℝ) ∈ Set.Icc (ψ b - b) (ψ a - a) := ⟨hFb.le, hFa.le⟩
    obtain ⟨rs, hrs, hrs0⟩ := intermediate_value_Icc' hab hcF hmem
    refine ⟨rs, lt_of_lt_of_le ha0 hrs.1, ?_⟩
    simp only at hrs0
    linarith
  refine ⟨hcont, ?_, hiff⟩
  obtain ⟨rs, hrs, hfix⟩ := hexist
  refine ⟨rs, ⟨hrs, hfix⟩, ?_⟩
  rintro t ⟨ht, htfix⟩
  have h1 := (hiff rs hrs hfix t ht).mp (le_of_eq htfix)
  have h2 := (hiff t ht htfix rs hrs).mp (le_of_eq hfix)
  linarith
