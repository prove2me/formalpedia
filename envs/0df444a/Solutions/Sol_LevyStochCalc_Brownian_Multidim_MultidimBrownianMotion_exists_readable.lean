-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:26:56.500543+00:00
-- url     : https://prove2.me/submissions/79770d59-577d-43d6-8708-e61a70088d20

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Multidim
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_exists_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/Multidim.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section Existence
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Existence of d-dimensional Brownian motion.** For any `d ≥ 0`, there
exists a probability space carrying a `d`-dimensional Brownian motion.

Proof: take `d` independent copies of the construction from
`LevyStochCalc.Brownian.BrownianMotion.exists`, joined via the product
probability space. -/
theorem solution (d : ℕ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d) := by
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, ⟨W₀⟩⟩ :=
    LevyStochCalc.Brownian.BrownianMotion.exists_readable
  refine ⟨Fin d → Ω₀, MeasurableSpace.pi,
    MeasureTheory.Measure.pi (fun _ => P₀), inferInstance, ?_⟩
  refine ⟨{
    W := fun i => LevyStochCalc.Brownian.Multidim.project_BM W₀ d i
    components_independent := ?_
    joint_continuous_paths := ?_
  }⟩
  pick_goal 2
  · -- joint continuity from per-component continuity (a.s. over the product
    -- measure) via `continuous_pi_iff`: a `Fin d → ℝ`-valued function of `t`
    -- is continuous iff each projection `(fun t => f t i)` is.  Each
    -- `(project_BM W₀ d i).continuous_paths` is already an a.s. statement, and
    -- the conjunction over the finite set `Fin d` remains a.s.
    have h_each : ∀ i : Fin d, ∀ᵐ ω ∂(MeasureTheory.Measure.pi (fun _ : Fin d => P₀)),
        Continuous (fun (t : ℝ) => (LevyStochCalc.Brownian.Multidim.project_BM W₀ d i).W t ω) :=
      fun i => (LevyStochCalc.Brownian.Multidim.project_BM W₀ d i).continuous_paths
    have h_all : ∀ᵐ ω ∂(MeasureTheory.Measure.pi (fun _ : Fin d => P₀)),
        ∀ i : Fin d, Continuous (fun (t : ℝ) => (LevyStochCalc.Brownian.Multidim.project_BM W₀ d i).W t ω) :=
      MeasureTheory.ae_all_iff.mpr h_each
    filter_upwards [h_all] with ω hω
    exact continuous_pi (fun i => hω i)
  -- Components are independent: use ProbabilityTheory.iIndepFun_pi
  -- with X_i = (fun ω : Ω₀ => fun t => W₀.W t ω) for each i.
  have h_meas_W₀ : ∀ _ : Fin d,
      AEMeasurable (fun ω₀ : Ω₀ => fun t : ℝ => W₀.W t ω₀) P₀ := by
    intro _
    -- Function into ℝ → ℝ is measurable iff each evaluation is measurable.
    refine (measurable_pi_iff.mpr ?_).aemeasurable
    intro t
    exact W₀.measurable_eval t
  have := ProbabilityTheory.iIndepFun_pi
    (X := fun _ : Fin d => fun ω₀ : Ω₀ => fun t : ℝ => W₀.W t ω₀)
    (μ := fun _ : Fin d => P₀) h_meas_W₀
  convert this using 1
  rfl
