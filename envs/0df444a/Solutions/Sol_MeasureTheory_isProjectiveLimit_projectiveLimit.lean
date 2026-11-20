-- Prove2me | solution 1 for MeasureTheory.isProjectiveLimit_projectiveLimit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:34:30.09219+00:00
-- url     : https://prove2.me/submissions/2b146645-917b-47bc-9dbc-61b40ac1ca28

import Definitions.Def_KolmogorovExtension4_KolmogorovExtension_F000

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/

@[expose] public section

open Set

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  {P : ∀ J : Finset ι, Measure (Π j : J, α j)}

section InnerRegular

variable [∀ i, TopologicalSpace (α i)] [∀ i, OpensMeasurableSpace (α i)]
  [∀ i, SecondCountableTopology (α i)] [∀ I, IsFiniteMeasure (P I)]

local notation "Js" => measurableCylinders.finset

local notation "As" => measurableCylinders.set

end InnerRegular

section Polish

variable [∀ i, TopologicalSpace (α i)] [∀ i, BorelSpace (α i)]
  [∀ i, PolishSpace (α i)] [∀ I, IsFiniteMeasure (P I)]


theorem _root_.solution (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveLimit (projectiveLimit P hP) P := by
  intro J
  ext s hs
  rw [Measure.map_apply (Finset.measurable_restrict J) hs, ← cylinder]
  exact (AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _
    (cylinder_mem_measurableCylinders J s hs)).trans (projectiveFamilyContent_cylinder hP hs)

end Polish

end MeasureTheory
