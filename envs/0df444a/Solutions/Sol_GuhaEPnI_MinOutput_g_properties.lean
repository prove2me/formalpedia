-- Prove2me | solution 1 for GuhaEPnI.MinOutput.g_properties
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:44:35.906996+00:00
-- url     : https://prove2.me/submissions/40c3bb1b-b6f0-4d56-ac72-2c92fe927c11

import Mathlib
import Definitions.Def_EntropyPhotonNumber

namespace Aux_Guha_g

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

end Aux_Guha_g

open OAI.EntropyPhotonNumber Aux_Guha_g in
theorem solution :
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
