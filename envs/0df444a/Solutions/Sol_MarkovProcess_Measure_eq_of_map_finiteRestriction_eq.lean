-- Prove2me | solution 1 for MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:17:58.497845+00:00
-- url     : https://prove2.me/submissions/c7ed5a51-6d48-4caa-b47b-a9981b84c680

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Constructions.Projective
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
variable {index alpha : Type*} [MeasurableSpace alpha]

theorem solution
    (mu nu : Measure (index → alpha)) [IsFiniteMeasure mu]
    (h : ∀ I : Finset index, mu.map I.restrict = nu.map I.restrict) :
    mu = nu := by
  let family : (I : Finset index) → Measure (I → alpha) :=
    fun I ↦ mu.map I.restrict
  have hmu : IsProjectiveLimit mu family := by
    intro I
    rfl
  have hnu : IsProjectiveLimit nu family := by
    intro I
    exact (h I).symm
  let (I : Finset index) : IsFiniteMeasure (family I) := by
    dsimp only [family]
    infer_instance
  exact hmu.unique hnu
