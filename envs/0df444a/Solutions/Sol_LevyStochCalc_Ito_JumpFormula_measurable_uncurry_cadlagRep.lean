-- Prove2me | solution 1 for LevyStochCalc.Ito.JumpFormula.measurable_uncurry_cadlagRep
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:41:57.912801+00:00
-- url     : https://prove2.me/submissions/2e30ff55-c0a5-462c-b635-6ec779ebcc11

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The càdlàg representative of a solution path

The Itô–Lévy formula at bounded derivatives asks for left limits of the solution at every sample
point and every time, while the well-posedness theorem produces paths that are càdlàg only on a
measurable set `G` of full measure. `cadlagRep G X` is the path map that agrees with `X` on `G` at
nonnegative times, is the constant zero path off `G`, and is frozen at the zero state before time
zero. It is càdlàg at every sample point and every time, adapted whenever `G` belongs to the
initial σ-algebra, progressively measurable because it is right-continuous everywhere, and solves
the equation on every window, because both stochastic integrals depend only on the class of their
integrand.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section CadlagRep

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

variable {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}



theorem _root_.solution (hGm : MeasurableSet G)
    (hX : Measurable (Function.uncurry X)) :
    Measurable (Function.uncurry (cadlagRep G X)) := by
  have hR : Measurable (Function.uncurry (repairOn G X)) := by
    first
    | exact measurable_uncurry_repairOn hGm hX
    | exact?
  have ht : MeasurableSet (Prod.fst ⁻¹' Set.Ici (0 : ℝ) : Set (ℝ × Ω)) :=
    measurable_fst measurableSet_Ici
  convert hR.indicator ht using 1
  funext p
  by_cases hp : 0 ≤ p.1 <;> simp [Function.uncurry, cadlagRep, Set.indicator_apply, hp]
