-- Prove2me | solution 1 for MarkovProcess.Kernel.eq_of_map_finiteRestriction_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:18:04.091094+00:00
-- url     : https://prove2.me/submissions/fe03eea5-4520-47c6-91de-80a00b730739

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Probability.Kernel.Composition.MapComap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
variable {index alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]

theorem solution
    (kappa eta : Kernel beta (index → alpha)) [IsFiniteKernel kappa]
    (h : ∀ I : Finset index,
      kappa.map I.restrict = eta.map I.restrict) :
    kappa = eta := by
  ext x : 1
  let family : (I : Finset index) → Measure (I → alpha) :=
    fun I ↦ (kappa x).map I.restrict
  have hkappa : IsProjectiveLimit (kappa x) family := by
    intro I
    rfl
  have heta : IsProjectiveLimit (eta x) family := by
    intro I
    have hx := congrArg (fun z : Kernel beta (I → alpha) ↦ z x) (h I)
    simpa only [Kernel.map_apply _ (Finset.measurable_restrict I) x] using hx.symm
  let (I : Finset index) : IsFiniteMeasure (family I) := by
    dsimp only [family]
    infer_instance
  exact hkappa.unique heta
