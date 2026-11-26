-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_levy_jump_energy_localisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:24:25.878342+00:00
-- url     : https://prove2.me/submissions/b27afb3d-a446-457e-bf84-c03085b23845

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_energy_tightness
import Theorems.Thm_Kyprianou_Ch04_ito43_full_grid_energy_tail
import Theorems.Thm_Kyprianou_Ch04_ito43_tightness_ae_frequent_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_frequent_grid_bound_tail
import Theorems.Thm_Kyprianou_Ch04_ito43_finite_jump_energy_summable
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Square-summability and outer probability localisation of the actual jump energy. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X L : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (tr : LevyKhintchineTriple)
    (hc : ∀ (t : NNReal) (ξ : ℝ), charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ))
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (T : NNReal) (hT : 0 < T) :
    let J : Ω → (Ioc (0 : NNReal) T → ℝ) := fun w t => (X t w-L t w)^2
    (∀ᵐ w ∂P, Summable (J w)) ∧
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
        (P {w | ¬ Summable (J w) ∨ C < ∑' t, J w t}).toReal ≤ η := by
  intro J
  let Q : ℕ → Ω → ℝ := fun n w => ∑ k ∈ Finset.range (n+1),
    (X (T*((k+1 : ℕ) : NNReal)/((n+1 : ℕ) : NNReal)) w -
     X (T*(k : NNReal)/((n+1 : ℕ) : NNReal)) w)^2
  have htight (η : ℝ) (hη : 0 < η) :
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (P {w | C ≤ Q n w}).toReal ≤ η := by
    obtain ⟨C,hC,h⟩ := Kyprianou.Ch04.ito43_grid_energy_tightness P X hX tr hc T η hη
    exact ⟨C,hC,Kyprianou.Ch04.ito43_full_grid_energy_tail P X T C η h⟩
  have hpath : ∀ᵐ w ∂P, ∀ C : ℝ, (∃ᶠ n in atTop, Q n w < C) →
      Summable (J w) ∧ (∑' t, J w t) ≤ C := by
    filter_upwards [hX.cadlag_ae,hL] with w hw hl
    intro C hC
    exact Kyprianou.Ch04.ito43_finite_jump_energy_summable
      (fun t => X t w) (fun t => L t w) T hT (fun t => (hw t).1) hl C hC
  constructor
  · filter_upwards [hpath,Kyprianou.Ch04.ito43_tightness_ae_frequent_bound P Q htight]
      with w hw hQ
    obtain ⟨C,hC⟩ := hQ
    exact (hw C hC).1
  · intro η hη
    obtain ⟨C,hC,hQ⟩ := htight η hη
    refine ⟨C,hC,?_⟩
    have hsub : ∀ᵐ w ∂P, w ∈ {w | ¬ Summable (J w) ∨ C < ∑' t, J w t} →
        w ∈ {w | ¬ ∃ᶠ n in atTop, Q n w < C} := by
      filter_upwards [hpath] with w hw hb
      intro h
      obtain ⟨hs,hbnd⟩ := hw C h
      exact hb.elim (fun hn => hn hs) (fun hn => (not_lt_of_ge hbnd) hn)
    exact (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)).trans
      (Kyprianou.Ch04.ito43_frequent_grid_bound_tail P Q C η hη.le hQ)
