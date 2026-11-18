-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_ae_finite_occupied_pieces
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T13:32:20.695018+00:00
-- url     : https://prove2.me/submissions/28be70d0-9652-43da-9eac-4c912709a8a4

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_lintegral_poissonRandomMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- A finite-intensity region occupies only finitely many Poisson partition pieces a.s. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (S : Set E) (hS : MeasurableSet S) (hfin : m S < ⊤) :
    ∀ᵐ ω ∂P,
      Set.Finite {k : ℕ | ∃ n ∈ Finset.range (K k ω), Y k n ω ∈ S} := by
  have hg1 : Measurable (S.indicator (fun _ : E => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hS
  filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hS hfin] with ω hω
  have hcount : ∑' k, ∑ n ∈ Finset.range (K k ω),
        S.indicator (fun _ : E => (1 : ℝ≥0∞)) (Y k n ω) =
        poissonRandomMeasure K Y ω S := by
    rw [← lintegral_poissonRandomMeasure hg1 ω,
      lintegral_indicator hS, setLIntegral_one]
  have hfinite : Set.Finite {k | (1 : ℝ≥0∞) ≤
      ∑ n ∈ Finset.range (K k ω),
        S.indicator (fun _ : E => (1 : ℝ≥0∞)) (Y k n ω)} :=
    ENNReal.finite_const_le_of_tsum_ne_top (by rw [hcount]; exact hω.ne) one_ne_zero
  refine hfinite.subset fun k hk => ?_
  obtain ⟨n, hn, hmem⟩ := hk
  calc
    (1 : ℝ≥0∞) = S.indicator (fun _ : E => (1 : ℝ≥0∞)) (Y k n ω) := by
      rw [Set.indicator_of_mem hmem]
    _ ≤ _ := Finset.single_le_sum
      (f := fun j => S.indicator (fun _ : E => (1 : ℝ≥0∞)) (Y k j ω))
      (fun _ _ => zero_le) hn
