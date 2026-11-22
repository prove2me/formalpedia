-- Prove2me | solution 1 for MasulloRH.translated_negative_gram_distance_to_geometric_approximants
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T07:12:16.583208+00:00
-- url     : https://prove2.me/submissions/ee0c3764-4cc3-4cc6-a40b-0d830a5e1502

import Theorems.Thm_MasulloRH_critical_width_translated_global_gram_density
import Mathlib
open MeasureTheory Filter Topology
theorem solution (f : ℝ → ℂ) (S : Set (ℝ → ℂ))
    (hf : AEStronglyMeasurable f volume)
    (hs : ∀ u ∈ S, AEStronglyMeasurable u volume)
    (hint : ∀ u ∈ S, Integrable (fun x : ℝ =>
      (Real.exp |x| * (1+x^2)^2) * ‖f x - u x‖^2))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ u ∈ S,
        (∫ x : ℝ, Real.exp (-x) * ‖f x-u x‖^2) < ε) :
    Tendsto (fun L : ℝ => sInf ((fun u : ℝ → ℂ =>
      ∫ x : ℝ, ((Real.exp |x-L| * (1+(x-L)^2)^2) / (Real.exp L * L^4)) *
        ‖f x-u x‖^2) '' S)) atTop (𝓝 0) := by
  let W := fun x : ℝ => Real.exp |x| * (1+x^2)^2
  have hwe (x : ℝ) : W (-x) = W x := by simp [W]
  have href (x L : ℝ) : W (x-L) = W (-x+L) := by
    convert hwe (-x+L) using 2 <;> ring
  obtain ⟨hp,hb⟩ := MasulloRH.critical_width_translated_global_gram_density
  let I := fun (L : ℝ) (u : ℝ → ℂ) =>
    ∫ x : ℝ, W (x-L)/(Real.exp L*L^4)*‖f x-u x‖^2
  have hi (u) (hu : u ∈ S) : Tendsto (fun L => I L u) atTop
      (𝓝 (∫ x : ℝ, Real.exp (-x)*‖f x-u x‖^2)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ => 9*(W x * ‖f x-u x‖^2))
    · apply Eventually.of_forall
      intro L
      have hc : Continuous (fun x : ℝ => W (x-L)/(Real.exp L*L^4)) := by
        dsimp [W]; fun_prop
      exact hc.aestronglyMeasurable.mul ((hf.sub (hs u hu)).norm.pow 2)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
      apply Eventually.of_forall
      intro x
      have hn : 0 ≤ W (x-L)/(Real.exp L*L^4)*‖f x-u x‖^2 := by dsimp [W]; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hn, ← mul_assoc, href x L, ← hwe x]
      exact mul_le_mul_of_nonneg_right (hb (-x) L hL) (sq_nonneg _)
    · exact (hint u hu).const_mul 9
    · apply Eventually.of_forall
      intro x
      simp_rw [href x]
      exact (hp (-x)).mul_const _
  have hnn (L : ℝ) (u : ℝ → ℂ) : 0 ≤ I L u := by
    exact integral_nonneg (fun x => by dsimp [W]; positivity)
  obtain ⟨u₀,hu₀,_⟩ := happrox 1 zero_lt_one
  change Tendsto (fun L => sInf (I L '' S)) atTop (𝓝 0)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun L => ha.trans_le (le_csInf
      ⟨I L u₀,⟨u₀,hu₀,rfl⟩⟩ (by rintro _ ⟨u,_,rfl⟩; exact hnn L u)))
  · intro b hb'
    obtain ⟨u,hu,hlt⟩ := happrox b hb'
    filter_upwards [(hi u hu).eventually_lt_const hlt] with L hL
    apply lt_of_le_of_lt _ hL
    have hedge : I L u ∈ (I L '' S) := ⟨u,hu,rfl⟩
    exact csInf_le (show BddBelow (I L '' S) from
      ⟨0, by rintro _ ⟨v,_,rfl⟩; exact hnn L v⟩) hedge
