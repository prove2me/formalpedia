-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_geometric_descending_potential
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T01:11:56.145772+00:00
-- url     : https://prove2.me/submissions/aa869cd2-b0fb-4ce1-9711-0f006bb89628
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_laplace_gap
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_geometric_renewal_from_gap
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_potential_atom_agreement
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_bound_and_vanishing
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (hdraw : ∀ d : ℝ, 0 < d → ∃ ρ : Measure ℝ,
      IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
          f d * (1 - s / d)) :
    ∃ ν : Measure ℝ, ν (Iio (0 : ℝ)) = 0 ∧
      (∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤) ∧
      (∀ x : ℝ, 0 < x → ν {x} = 0) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) =
          ENNReal.ofReal (s / f s)) := by
  classical
  have hex : ∀ d : ℝ, ∃ ρ : Measure ℝ, 0 < d →
      (IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
        ∀ s : ℝ, 0 < s →
          (f d - f s) * (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
            f d * (1 - s / d)) := by
    intro d; by_cases hd : 0 < d
    · obtain ⟨ρ, hρ⟩ := hdraw d hd; exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨Measure.dirac 0, fun h => absurd h hd⟩
  choose ρd hρd using hex
  have hρd' : ∀ d : ℝ, 0 < d →
      IsProbabilityMeasure (ρd d) ∧ (ρd d) (Iio (0 : ℝ)) = 0 ∧
        ∀ s : ℝ, 0 < s →
          (f d - f s) * (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂(ρd d)).toReal =
            f d * (1 - s / d) := fun d hd => hρd d hd
  have hνex : ∀ d : ℝ, ∃ ν : Measure ℝ, 0 < d →
      (ν (Iio (0 : ℝ)) = 0 ∧ (∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤) ∧
        (∀ s : ℝ, 0 < s →
          (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) = ENNReal.ofReal (s / f s)) ∧
        (∀ x : ℝ, 0 < x → ν {x} = ENNReal.ofReal (d / f d) * (ρd d) {x})) := by
    intro d; by_cases hd : 0 < d
    · obtain ⟨hprob, hsupp, heq⟩ := hρd' d hd
      obtain ⟨κ, hSFin, hκsupp, hκatom, hκgen, hκform, s0, hs0, hr0⟩ :=
        Kyprianou.Ch08.StageB.p2m81_tail_kernel_laplace_gap f hpos d hd (ρd d) hprob hsupp heq
      haveI := hSFin
      obtain ⟨ν, hν⟩ :=
        Kyprianou.Ch08.StageB.p2m81_geometric_renewal_from_gap f hpos d hd (ρd d) hprob hsupp heq
          κ hκsupp hκatom hκgen hκform
          (fun s => (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂κ))
          (fun _ _ => rfl) s0 hs0 hr0
      exact ⟨ν, fun _ => hν⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose νd hνd using hνex
  have hνd' : ∀ d : ℝ, 0 < d →
      ((νd d) (Iio (0 : ℝ)) = 0 ∧ (∀ x : ℝ, 0 ≤ x → (νd d) (Iic x) < ⊤) ∧
        (∀ s : ℝ, 0 < s →
          (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂(νd d)) = ENNReal.ofReal (s / f s)) ∧
        (∀ x : ℝ, 0 < x →
          (νd d) {x} = ENNReal.ofReal (d / f d) * (ρd d) {x})) := fun d hd => hνd d hd
  obtain ⟨hbound, hlim⟩ :=
    Kyprianou.Ch08.StageB.p2m81_drawdown_bound_and_vanishing f hpos hdraw ρd hρd'
  obtain ⟨h1supp, h1loc, h1lap, -⟩ := hνd' 1 one_pos
  refine ⟨νd 1, h1supp, h1loc, ?_, h1lap⟩
  intro x hx
  let c : ℝ≥0∞ := ENNReal.ofReal (1 / f 1)
  have hscaled : Tendsto (fun d : ℝ => c * (ρd d) {x}) atTop (nhds 0) := by
    simpa [c] using ENNReal.Tendsto.const_mul (hlim x hx) (Or.inr ENNReal.ofReal_ne_top)
  have hbound_ev : ∀ᶠ d : ℝ in atTop, (νd 1) {x} ≤ c * (ρd d) {x} := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with d hd1
    have hd : 0 < d := lt_of_lt_of_le one_pos hd1
    obtain ⟨hdsupp, -, hdlap, hdatom⟩ := hνd' d hd
    have hagree : (νd 1) {x} = (νd d) {x} :=
      Kyprianou.Ch08.StageB.p2m81_potential_atom_agreement f hpos (νd 1) (νd d)
        h1supp hdsupp h1lap hdlap x hx
    have hcoef : ENNReal.ofReal (d / f d) ≤ c :=
      ENNReal.ofReal_le_ofReal (hbound d hd1)
    rw [hagree, hdatom x hx]
    exact mul_le_mul_of_nonneg_right hcoef bot_le
  exact bot_unique (le_of_tendsto_of_tendsto tendsto_const_nhds hscaled hbound_ev)
