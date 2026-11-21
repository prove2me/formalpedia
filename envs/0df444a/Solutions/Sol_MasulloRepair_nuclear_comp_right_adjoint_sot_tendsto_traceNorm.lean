-- Prove2me | solution 1 for MasulloRepair.nuclear_comp_right_adjoint_sot_tendsto_traceNorm
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:17:30.76198+00:00
-- url     : https://prove2.me/submissions/f56656ff-bedd-429f-b8f8-b58ea1b30508

import Definitions.Def_MasulloGRH_HilbertNuclear
import Theorems.Thm_MasulloGRH_traceNorm_le_nuclear_series
import Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series

set_option autoImplicit false

open Filter Topology MasulloGRH

namespace A3RightAux

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

end A3RightAux

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsNuclearOperator T)
    {ι : Type*} (l : Filter ι) (Q : ι → H →L[ℂ] H) (Q₀ : H →L[ℂ] H) (C : ℝ)
    (hbd : ∀ᶠ i in l, ‖Q i‖ ≤ C)
    (hQ : ∀ u : H, Tendsto (fun i => ContinuousLinearMap.adjoint (Q i) u) l
      (𝓝 (ContinuousLinearMap.adjoint Q₀ u))) :
    (∀ i, IsNuclearOperator (T ∘L Q i)) ∧ IsNuclearOperator (T ∘L Q₀) ∧
    Tendsto (fun i => traceNorm (T ∘L Q i - T ∘L Q₀)) l (𝓝 0) ∧
    Tendsto (fun i => operatorTrace (T ∘L Q i)) l (𝓝 (operatorTrace (T ∘L Q₀))) := by
  obtain ⟨x, y, hs, hxy⟩ := hT
  -- expansion of `T ∘ A` for every bounded `A`
  have hcomp : ∀ A : H →L[ℂ] H, ∀ u,
      HasSum (fun m => inner ℂ (ContinuousLinearMap.adjoint A (x m)) u • y m) ((T ∘L A) u) := by
    intro A u
    have h := hxy (A u)
    simpa [ContinuousLinearMap.adjoint_inner_left] using h
  have hadj : ∀ A : H →L[ℂ] H, ∀ v, ‖ContinuousLinearMap.adjoint A v‖ ≤ ‖A‖ * ‖v‖ := by
    intro A v
    have h := (ContinuousLinearMap.adjoint A).le_opNorm v
    rwa [LinearIsometryEquiv.norm_map] at h
  have hsumA : ∀ A : H →L[ℂ] H,
      Summable (fun m => ‖ContinuousLinearMap.adjoint A (x m)‖ * ‖y m‖) := by
    intro A
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (hs.mul_left ‖A‖)
    calc ‖ContinuousLinearMap.adjoint A (x m)‖ * ‖y m‖ ≤ (‖A‖ * ‖x m‖) * ‖y m‖ := by
          gcongr; exact hadj A _
      _ = ‖A‖ * (‖x m‖ * ‖y m‖) := by ring
  refine ⟨fun i => ⟨fun m => ContinuousLinearMap.adjoint (Q i) (x m), y, hsumA _, hcomp _⟩,
    ⟨fun m => ContinuousLinearMap.adjoint Q₀ (x m), y, hsumA _, hcomp _⟩, ?_, ?_⟩
  · -- trace norm
    have hle : ∀ i, traceNorm (T ∘L Q i - T ∘L Q₀) ≤
        ∑' m, ‖ContinuousLinearMap.adjoint (Q i - Q₀) (x m)‖ * ‖y m‖ := by
      intro i
      have h : T ∘L Q i - T ∘L Q₀ = T ∘L (Q i - Q₀) := by ext u; simp
      rw [h]
      exact traceNorm_le_nuclear_series _ (fun m => ContinuousLinearMap.adjoint (Q i - Q₀) (x m)) y
        (hsumA _) (hcomp _)
    have hlim : Tendsto (fun i => ∑' m, ‖ContinuousLinearMap.adjoint (Q i - Q₀) (x m)‖ * ‖y m‖) l
        (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
      refine tendsto_tsum_of_dominated_convergence
        (bound := fun m => (C + ‖Q₀‖) * (‖x m‖ * ‖y m‖)) (hs.mul_left _) ?_ ?_
      · intro m
        have h1 : Tendsto (fun i => ContinuousLinearMap.adjoint (Q i - Q₀) (x m)) l (𝓝 0) := by
          have := (hQ (x m)).sub_const (ContinuousLinearMap.adjoint Q₀ (x m))
          simpa using this
        have h2 := (h1.norm).mul_const ‖y m‖
        simpa using h2
      · filter_upwards [hbd] with i hi m
        rw [Real.norm_of_nonneg (by positivity)]
        have h3 : ‖ContinuousLinearMap.adjoint (Q i - Q₀) (x m)‖ ≤ (C + ‖Q₀‖) * ‖x m‖ := by
          calc ‖ContinuousLinearMap.adjoint (Q i - Q₀) (x m)‖
              ≤ ‖Q i - Q₀‖ * ‖x m‖ := hadj _ _
            _ ≤ (‖Q i‖ + ‖Q₀‖) * ‖x m‖ := by gcongr; exact norm_sub_le _ _
            _ ≤ (C + ‖Q₀‖) * ‖x m‖ := by gcongr
        calc ‖ContinuousLinearMap.adjoint (Q i - Q₀) (x m)‖ * ‖y m‖
            ≤ ((C + ‖Q₀‖) * ‖x m‖) * ‖y m‖ := by gcongr
          _ = (C + ‖Q₀‖) * (‖x m‖ * ‖y m‖) := by ring
    rw [tsum_zero] at hlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun i => A3RightAux.traceNorm_nonneg _) hle
  · -- trace
    have htr : ∀ A : H →L[ℂ] H, operatorTrace (T ∘L A) =
        ∑' m, inner ℂ (ContinuousLinearMap.adjoint A (x m)) (y m) :=
      fun A => operatorTrace_of_nuclear_series _
        (fun m => ContinuousLinearMap.adjoint A (x m)) y (hsumA A) (hcomp A)
    simp only [htr]
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun m => C * (‖x m‖ * ‖y m‖)) (hs.mul_left _) ?_ ?_
    · intro m
      exact (hQ (x m)).inner tendsto_const_nhds
    · filter_upwards [hbd] with i hi m
      calc ‖inner ℂ (ContinuousLinearMap.adjoint (Q i) (x m)) (y m)‖
          ≤ ‖ContinuousLinearMap.adjoint (Q i) (x m)‖ * ‖y m‖ := norm_inner_le_norm _ _
        _ ≤ (C * ‖x m‖) * ‖y m‖ := by
          gcongr
          exact (hadj _ _).trans (by gcongr)
        _ = C * (‖x m‖ * ‖y m‖) := by ring
