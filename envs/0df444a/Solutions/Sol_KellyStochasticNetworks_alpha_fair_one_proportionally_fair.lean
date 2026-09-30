-- Prove2me | solution 1 for KellyStochasticNetworks.alpha_fair_one_proportionally_fair
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:13:21.197017+00:00
-- url     : https://prove2.me/submissions/1265a55e-c5cd-40bb-bdac-a018e28a8a97

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem pf_iff {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (c : Fin R → ℝ) (hc : ∀ r, 0 < c r)
    (X : Fin R → ℝ) (hXpos : ∀ r, 0 < X r) (hXfeas : X ∈ networkFeasible A C) :
    IsMaxOn (fun Y : Fin R → ℝ => ∑ r, c r * Real.log (Y r))
        (networkFeasible A C ∩ {Y | ∀ r, 0 < Y r}) X
      ↔ ∀ Y ∈ networkFeasible A C, (∑ r, c r * ((Y r - X r) / X r)) ≤ 0 := by
  constructor
  · intro hmax Y hY
    obtain ⟨hY0, hYC⟩ := hY
    obtain ⟨hX0, hXC⟩ := hXfeas
    set g : ℝ → ℝ := fun t => ∑ r, c r * Real.log (X r + t * (Y r - X r)) with hg
    have hderiv : HasDerivAt g (∑ r, c r * ((Y r - X r) / X r)) 0 := by
      have hd : ∀ r ∈ Finset.univ, HasDerivAt
          (fun t => c r * Real.log (X r + t * (Y r - X r))) (c r * ((Y r - X r) / X r)) 0 := by
        intro r _
        have h1 : HasDerivAt (fun t : ℝ => X r + t * (Y r - X r)) (Y r - X r) 0 := by
          simpa using ((hasDerivAt_id (0:ℝ)).mul_const (Y r - X r)).const_add (X r)
        have h2 := h1.log (by simp only [zero_mul, add_zero]; exact (hXpos r).ne')
        simp only [zero_mul, add_zero] at h2
        exact h2.const_mul (c r)
      exact HasDerivAt.fun_sum hd
    have hslope := hderiv.tendsto_slope_zero_right
    have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t⁻¹ • (g (0 + t) - g 0) ≤ 0 := by
      have h1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t < 1 :=
        nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
      filter_upwards [h1, self_mem_nhdsWithin] with t ht1 ht0
      have ht0' : 0 < t := ht0
      have hmem : (fun r => X r + t * (Y r - X r)) ∈
          networkFeasible A C ∩ {Y | ∀ r, 0 < Y r} := by
        refine ⟨⟨fun r => ?_, fun j => ?_⟩, fun r => ?_⟩
        · have := hX0 r; have := hY0 r; nlinarith
        · have e : linkFlow A (fun r => X r + t * (Y r - X r)) j =
              (1 - t) * linkFlow A X j + t * linkFlow A Y j := by
            simp only [linkFlow, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun r _ => by ring
          rw [e]
          have m1 := mul_le_mul_of_nonneg_left (hXC j) (by linarith : (0:ℝ) ≤ 1 - t)
          have m2 := mul_le_mul_of_nonneg_left (hYC j) ht0'.le
          nlinarith
        · have := hXpos r; have := hY0 r
          have : 0 < (1 - t) * X r := mul_pos (by linarith) (hXpos r)
          nlinarith
      have hle := hmax hmem
      simp only [Set.mem_ofPred_eq] at hle
      have hg0 : g 0 = ∑ r, c r * Real.log (X r) := by simp [hg]
      rw [zero_add, hg0, smul_eq_mul]
      apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0'.le)
      simp only [hg]
      linarith
    exact le_of_tendsto hslope hev
  · intro h Y hY
    obtain ⟨hYf, hYpos⟩ := hY
    have hsum := h Y hYf
    show ∑ r, c r * Real.log (Y r) ≤ ∑ r, c r * Real.log (X r)
    have hpt : ∀ r, c r * Real.log (Y r) ≤ c r * Real.log (X r) + c r * ((Y r - X r) / X r) := by
      intro r
      have hq : 0 < Y r / X r := div_pos (hYpos r) (hXpos r)
      have hl := Real.log_le_sub_one_of_pos hq
      rw [Real.log_div (hYpos r).ne' (hXpos r).ne'] at hl
      have e : Y r / X r - 1 = (Y r - X r) / X r := by field_simp [(hXpos r).ne']
      rw [e] at hl
      have := mul_le_mul_of_nonneg_left hl (hc r).le
      nlinarith
    have := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hpt r
    rw [Finset.sum_add_distrib] at this
    linarith

theorem af_one_pf {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w n : Fin R → ℝ) (hA : ∀ j r, 0 ≤ A j r) (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r)
    (X : Fin R → ℝ) (hXpos : ∀ r, 0 < X r) (hXfeas : X ∈ networkFeasible A C) :
    IsMaxOn (alphaFairObjective w n 1) (networkFeasible A C ∩ {Y | ∀ r, 0 < Y r}) X
      ↔ ∀ Y ∈ networkFeasible A C, (∑ r, w r * n r * ((Y r - X r) / X r)) ≤ 0 := by
  have hfun : alphaFairObjective w n 1 = fun Y : Fin R → ℝ => ∑ r, (w r * n r) * Real.log (Y r) := by
    funext Y; simp [alphaFairObjective]
  rw [hfun]
  exact pf_iff A C (fun r => w r * n r) (fun r => mul_pos (hw r) (hn r)) X hXpos hXfeas

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w n : Fin R → ℝ) (hA : ∀ j r, 0 ≤ A j r) (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r)
    (X : Fin R → ℝ) (hXpos : ∀ r, 0 < X r) (hXfeas : X ∈ networkFeasible A C) :
    IsMaxOn (alphaFairObjective w n 1) (networkFeasible A C ∩ {Y | ∀ r, 0 < Y r}) X
      ↔ ∀ Y ∈ networkFeasible A C, (∑ r, w r * n r * ((Y r - X r) / X r)) ≤ 0 := by
  exact af_one_pf A C w n hA hw hn X hXpos hXfeas
