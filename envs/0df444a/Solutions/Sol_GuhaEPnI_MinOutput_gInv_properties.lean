-- Prove2me | solution 1 for GuhaEPnI.MinOutput.gInv_properties
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:47:12.235519+00:00
-- url     : https://prove2.me/submissions/383c2b7c-43d7-4eb8-8df9-3c6dba526c16

import Mathlib
import Definitions.Def_EntropyPhotonNumber

namespace Aux_Guha_gi

open OAI.EntropyPhotonNumber

lemma hasDeriv_g {t : ℝ} (ht : 0 < t) :
    HasDerivAt g (Real.log (t + 1) - Real.log t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s + 1) * Real.log (s + 1)) (Real.log (t + 1) + 1) t := by
    have := (Real.hasDerivAt_mul_log (show t + 1 ≠ 0 by linarith)).comp t
      ((hasDerivAt_id t).add_const 1)
    exact this.congr_deriv (by simp)
  have h2 := Real.hasDerivAt_mul_log ht.ne'
  unfold g
  exact (h1.sub h2).congr_deriv (by ring)

lemma deriv_g_eq : Set.EqOn (deriv g) (fun s => Real.log (s + 1) - Real.log s) (Set.Ioi 0) :=
  fun t ht => (hasDeriv_g ht).deriv

lemma g_cont : Continuous g := by
  unfold g
  exact (Real.continuous_mul_log.comp (continuous_id.add continuous_const)).sub
    Real.continuous_mul_log

end Aux_Guha_gi

namespace Aux_Guha_gi
open OAI.EntropyPhotonNumber
theorem gprops :
    (∀ t : ℝ, 0 ≤ t → 0 ≤ g t) ∧
    MonotoneOn g (Set.Ici 0) ∧
    ConcaveOn ℝ (Set.Ici 0) g := by
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) g_cont.continuousOn
    · rw [interior_Ici]
      intro t ht
      exact (hasDeriv_g ht).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      rw [(hasDeriv_g ht).deriv]
      have := Real.log_le_log ht (by linarith : t ≤ t + 1)
      linarith
  have hg0 : g 0 = 0 := by unfold g; simp
  refine ⟨fun t ht => ?_, hmono, ?_⟩
  · have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    rw [hg0] at this
    exact this
  · apply concaveOn_of_deriv2_nonpos (convex_Ici 0) g_cont.continuousOn
    · rw [interior_Ici]
      intro t ht
      exact (hasDeriv_g ht).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      have hd : HasDerivAt (fun s => Real.log (s + 1) - Real.log s) (1 / (t + 1) - 1 / t) t := by
        have hpos : (0 : ℝ) < id t + 1 := by simp only [id]; linarith [show (0:ℝ) < t from ht]
        have h1 := ((hasDerivAt_id t).add_const 1).log hpos.ne'
        have h2 := Real.hasDerivAt_log (show (0:ℝ) < t from ht).ne'
        exact (h1.sub h2).congr_deriv (by simp only [id]; ring)
      have heq : deriv g =ᶠ[nhds t] fun s => Real.log (s + 1) - Real.log s :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) deriv_g_eq
      exact (hd.congr_of_eventuallyEq heq).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      have hd : HasDerivAt (fun s => Real.log (s + 1) - Real.log s) (1 / (t + 1) - 1 / t) t := by
        have hpos : (0 : ℝ) < id t + 1 := by simp only [id]; linarith
        have h1 := ((hasDerivAt_id t).add_const 1).log hpos.ne'
        have h2 := Real.hasDerivAt_log ht'.ne'
        exact (h1.sub h2).congr_deriv (by simp only [id]; ring)
      have heq : deriv g =ᶠ[nhds t] fun s => Real.log (s + 1) - Real.log s :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht') deriv_g_eq
      rw [Function.iterate_succ_apply, Function.iterate_one, (hd.congr_of_eventuallyEq heq).deriv]
      have : 1 / (t + 1) ≤ 1 / t := one_div_le_one_div_of_le ht' (by linarith)
      linarith

end Aux_Guha_gi

open OAI.EntropyPhotonNumber Aux_Guha_gi in
theorem solution :
    (∀ t : ℝ, 0 ≤ t → gInv (g t) = t) ∧
    (∀ s : ℝ, 0 ≤ s → g (gInv s) = s) ∧
    (∀ s : ℝ, 0 ≤ s → 0 ≤ gInv s) ∧
    MonotoneOn gInv (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) gInv := by
  obtain ⟨hnn, hmono, hconc⟩ := gprops
  have hsm : StrictMonoOn g (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) g_cont.continuousOn
    rw [interior_Ici]
    intro t ht
    rw [(hasDeriv_g ht).deriv]
    have := Real.log_lt_log ht (by linarith : t < t + 1)
    linarith
  have hinv1 : ∀ t : ℝ, 0 ≤ t → gInv (g t) = t := by
    intro t ht
    unfold gInv
    apply IsLeast.csInf_eq
    refine ⟨⟨ht, le_rfl⟩, ?_⟩
    rintro u ⟨hu0, hu⟩
    by_contra hlt
    push_neg at hlt
    have := hsm (Set.mem_Ici.mpr hu0) (Set.mem_Ici.mpr ht) hlt
    linarith
  have hlogle : ∀ t : ℝ, 0 ≤ t → Real.log (t + 1) ≤ g t := by
    intro t ht
    unfold g
    rcases ht.lt_or_eq with ht' | ht'
    · have := Real.log_le_log ht' (by linarith : t ≤ t + 1)
      nlinarith
    · rw [← ht']; simp
  have hsurj : ∀ s : ℝ, 0 ≤ s → ∃ t, 0 ≤ t ∧ g t = s := by
    intro s hs
    set T := Real.exp s - 1 with hT
    have hT0 : 0 ≤ T := by rw [hT]; linarith [Real.add_one_le_exp s]
    have hgT : s ≤ g T := by
      have := hlogle T hT0
      rw [hT, sub_add_cancel, Real.log_exp] at this
      exact this
    have hg0 : g 0 = 0 := by unfold g; simp
    have := intermediate_value_Icc hT0 g_cont.continuousOn
      (show s ∈ Set.Icc (g 0) (g T) from ⟨by rw [hg0]; exact hs, hgT⟩)
    obtain ⟨t, ht, hgt⟩ := this
    exact ⟨t, ht.1, hgt⟩
  have hinv2 : ∀ s : ℝ, 0 ≤ s → g (gInv s) = s := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hsurj s hs
    rw [hinv1 t ht]
  have hinv3 : ∀ s : ℝ, 0 ≤ s → 0 ≤ gInv s := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hsurj s hs
    rw [hinv1 t ht]; exact ht
  -- key: gInv s ≤ u whenever s ≤ g u
  have hle : ∀ s u : ℝ, 0 ≤ s → 0 ≤ u → s ≤ g u → gInv s ≤ u := by
    intro s u hs hu hsu
    by_contra hlt
    push_neg at hlt
    have := hsm (Set.mem_Ici.mpr hu) (Set.mem_Ici.mpr (hinv3 s hs)) hlt
    rw [hinv2 s hs] at this
    linarith
  refine ⟨hinv1, hinv2, hinv3, ?_, ?_⟩
  · intro s1 hs1 s2 hs2 h12
    apply hle s1 _ hs1 (hinv3 s2 hs2)
    rw [hinv2 s2 hs2]; exact h12
  · refine ⟨convex_Ici 0, ?_⟩
    intro s1 hs1 s2 hs2 a b ha hb hab
    have hs1' : (0 : ℝ) ≤ s1 := hs1
    have hs2' : (0 : ℝ) ≤ s2 := hs2
    have ht1 := hinv3 s1 hs1'
    have ht2 := hinv3 s2 hs2'
    have hc := hconc.2 (Set.mem_Ici.mpr ht1) (Set.mem_Ici.mpr ht2) ha hb hab
    rw [hinv2 s1 hs1', hinv2 s2 hs2'] at hc
    simp only [smul_eq_mul] at hc ⊢
    apply hle _ _ (by positivity) (by positivity)
    exact hc
