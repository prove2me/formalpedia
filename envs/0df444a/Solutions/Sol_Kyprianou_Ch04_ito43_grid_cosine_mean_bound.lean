-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_grid_cosine_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:32:28.856823+00:00
-- url     : https://prove2.me/submissions/b268c17e-1d6a-4612-8f83-19dbb1b776ce

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_cosine_increment_bound
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Uniform first moment of the total cosine deficit on a fine deterministic grid. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (tr : LevyKhintchineTriple)
    (hc : ∀ (t : NNReal) (ξ : ℝ), charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ))
    (T : NNReal) (ξ : ℝ) (n : ℕ) (hn : 0 < n)
    (hh : (T : ℝ)/(n : ℝ) * ‖Kyprianou.Ch01.levyTripleExponent tr ξ‖ ≤ 1) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let F : Ω → ℝ := fun w => ∑ k ∈ Finset.range n,
      (1 - Real.cos (ξ * (X (u (k+1)) w - X (u k) w)))
    Integrable F P ∧ (∀ w, 0 ≤ F w) ∧
      (∫ w, F w ∂P) ≤ 2 * (T : ℝ) * ‖Kyprianou.Ch01.levyTripleExponent tr ξ‖ := by
  intro u F
  let h := T/(n : NNReal)
  have hu (k : ℕ) : u (k+1) = u k + h := by
    dsimp [u,h]
    push_cast
    ring
  let G : ℕ → Ω → ℝ := fun k w => 1 - Real.cos (ξ * (X (u (k+1)) w - X (u k) w))
  have hG (k : ℕ) : Integrable (G k) P ∧ (∀ w, 0 ≤ G k w) ∧
      (∫ w, G k w ∂P) ≤ 2 * (h : ℝ) * ‖Kyprianou.Ch01.levyTripleExponent tr ξ‖ := by
    have H := Kyprianou.Ch04.ito43_levy_cosine_increment_bound P X hX tr hc (u k) h ξ (by exact_mod_cast hh)
    simpa only [← hu k,G] using H
  refine ⟨integrable_finset_sum _ (fun k _ => (hG k).1), ?_, ?_⟩
  · exact fun w => Finset.sum_nonneg fun k _ => (hG k).2.1 w
  · change (∫ w, ∑ k ∈ Finset.range n, G k w ∂P) ≤ _
    rw [integral_finset_sum _ (fun k _ => (hG k).1)]
    calc
      _ ≤ ∑ k ∈ Finset.range n, (2 * (h : ℝ) * ‖Kyprianou.Ch01.levyTripleExponent tr ξ‖) :=
        Finset.sum_le_sum fun k _ => (hG k).2.2
      _ = _ := by
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        simp [h,NNReal.coe_div,NNReal.coe_natCast]
        field_simp
