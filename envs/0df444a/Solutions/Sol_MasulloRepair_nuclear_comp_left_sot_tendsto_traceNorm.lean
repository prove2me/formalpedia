-- Prove2me | solution 1 for MasulloRepair.nuclear_comp_left_sot_tendsto_traceNorm
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:17:29.863252+00:00
-- url     : https://prove2.me/submissions/7800bbcd-6dc2-499a-a9d3-60d318dfba30

import Definitions.Def_MasulloGRH_HilbertNuclear
import Theorems.Thm_MasulloGRH_traceNorm_le_nuclear_series
import Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series

set_option autoImplicit false

open Filter Topology MasulloGRH

namespace A3LeftAux

open scoped ComplexOrder in
/-- The trace norm `Re ∑ ⟨φ, |A| φ⟩` is nonnegative, because `|A|` is a positive operator. -/
lemma traceNorm_nonneg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →L[ℂ] H) : 0 ≤ traceNorm A := by
  unfold traceNorm operatorTrace
  have hpos : (operatorAbs A).IsPositive := by
    rw [← ContinuousLinearMap.nonneg_iff_isPositive]
    exact CFC.sqrt_nonneg _
  have h : (0 : ℂ) ≤ ∑' i, inner ℂ (chosenHilbertBasis H i)
      (operatorAbs A (chosenHilbertBasis H i)) :=
    tsum_nonneg fun i => hpos.inner_nonneg_right _
  exact (Complex.nonneg_iff.mp h).1

end A3LeftAux

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T)
    {ι : Type*} (l : Filter ι) (Q : ι → H →L[ℂ] H) (Q₀ : H →L[ℂ] H) (C : ℝ)
    (hbd : ∀ᶠ i in l, ‖Q i‖ ≤ C)
    (hQ : ∀ u : H, Tendsto (fun i => Q i u) l (𝓝 (Q₀ u))) :
    (∀ i, IsNuclearOperator (Q i ∘L T)) ∧ IsNuclearOperator (Q₀ ∘L T) ∧
    Tendsto (fun i => traceNorm (Q i ∘L T - Q₀ ∘L T)) l (𝓝 0) ∧
    Tendsto (fun i => operatorTrace (Q i ∘L T)) l (𝓝 (operatorTrace (Q₀ ∘L T))) := by
  obtain ⟨x, y, hs, hxy⟩ := hT
  -- expansion of `A ∘ T` for every bounded `A`
  have hcomp : ∀ A : H →L[ℂ] H, ∀ u,
      HasSum (fun m => inner ℂ (x m) u • A (y m)) ((A ∘L T) u) := by
    intro A u
    have h := A.hasSum (hxy u)
    simpa [map_smul] using h
  have hsumA : ∀ A : H →L[ℂ] H, Summable (fun m => ‖x m‖ * ‖A (y m)‖) := by
    intro A
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (hs.mul_left ‖A‖)
    calc ‖x m‖ * ‖A (y m)‖ ≤ ‖x m‖ * (‖A‖ * ‖y m‖) := by
          gcongr; exact A.le_opNorm _
      _ = ‖A‖ * (‖x m‖ * ‖y m‖) := by ring
  refine ⟨fun i => ⟨x, fun m => Q i (y m), hsumA _, hcomp _⟩,
    ⟨x, fun m => Q₀ (y m), hsumA _, hcomp _⟩, ?_, ?_⟩
  · -- trace norm
    have hle : ∀ i, traceNorm (Q i ∘L T - Q₀ ∘L T) ≤ ∑' m, ‖x m‖ * ‖(Q i - Q₀) (y m)‖ := by
      intro i
      have h : Q i ∘L T - Q₀ ∘L T = (Q i - Q₀) ∘L T := by ext u; simp
      rw [h]
      exact traceNorm_le_nuclear_series _ x (fun m => (Q i - Q₀) (y m)) (hsumA _) (hcomp _)
    have hlim : Tendsto (fun i => ∑' m, ‖x m‖ * ‖(Q i - Q₀) (y m)‖) l
        (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
      refine tendsto_tsum_of_dominated_convergence
        (bound := fun m => (C + ‖Q₀‖) * (‖x m‖ * ‖y m‖)) (hs.mul_left _) ?_ ?_
      · intro m
        have h1 : Tendsto (fun i => (Q i - Q₀) (y m)) l (𝓝 0) := by
          have := (hQ (y m)).sub_const (Q₀ (y m))
          simpa using this
        have h2 := (h1.norm).const_mul ‖x m‖
        simpa using h2
      · filter_upwards [hbd] with i hi m
        rw [Real.norm_of_nonneg (by positivity)]
        have h3 : ‖(Q i - Q₀) (y m)‖ ≤ (C + ‖Q₀‖) * ‖y m‖ := by
          calc ‖(Q i - Q₀) (y m)‖ ≤ ‖Q i - Q₀‖ * ‖y m‖ := (Q i - Q₀).le_opNorm _
            _ ≤ (‖Q i‖ + ‖Q₀‖) * ‖y m‖ := by gcongr; exact norm_sub_le _ _
            _ ≤ (C + ‖Q₀‖) * ‖y m‖ := by gcongr
        calc ‖x m‖ * ‖(Q i - Q₀) (y m)‖ ≤ ‖x m‖ * ((C + ‖Q₀‖) * ‖y m‖) := by gcongr
          _ = (C + ‖Q₀‖) * (‖x m‖ * ‖y m‖) := by ring
    rw [tsum_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun i => A3LeftAux.traceNorm_nonneg _) hle
  · -- trace
    have htr : ∀ A : H →L[ℂ] H, operatorTrace (A ∘L T) = ∑' m, inner ℂ (x m) (A (y m)) :=
      fun A => operatorTrace_of_nuclear_series _ x (fun m => A (y m)) (hsumA A) (hcomp A)
    simp only [htr]
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun m => C * (‖x m‖ * ‖y m‖)) (hs.mul_left _) ?_ ?_
    · intro m
      exact tendsto_const_nhds.inner (hQ (y m))
    · filter_upwards [hbd] with i hi m
      calc ‖inner ℂ (x m) (Q i (y m))‖ ≤ ‖x m‖ * ‖Q i (y m)‖ := norm_inner_le_norm _ _
        _ ≤ ‖x m‖ * (C * ‖y m‖) := by
          gcongr
          exact (Q i).le_of_opNorm_le hi _
        _ = C * (‖x m‖ * ‖y m‖) := by ring
