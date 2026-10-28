-- Prove2me | solution 1 for LevyStochCalc.Brownian.iIndep_of_indep_biSup_lt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:42.17522+00:00
-- url     : https://prove2.me/submissions/b5563275-aefe-4ab6-930c-ab5947929f50

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/MathlibBridge.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
/-- A family of σ-algebras indexed by a linear order is mutually independent as soon as each
member is independent of the supremum of the members of strictly smaller index. -/
theorem solution {ι : Type*} [LinearOrder ι] {m : ι → MeasurableSpace Ω}
    (h : ∀ i, Indep (⨆ j < i, m j) (m i) P) : iIndep m P := by
  classical
  have key : ∀ (S : Finset ι) (f : ι → Set Ω), (∀ i ∈ S, MeasurableSet[m i] (f i)) →
      P (⋂ i ∈ S, f i) = ∏ i ∈ S, P (f i) := by
    intro S
    induction S using Finset.induction_on_max with
    | empty => intro f _; simp
    | insert a s hlt ih =>
      intro f hf
      have hane : a ∉ s := fun ha ↦ lt_irrefl a (hlt a ha)
      have hfs : ∀ i ∈ s, MeasurableSet[m i] (f i) := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hmeas : MeasurableSet[⨆ j < a, m j] (⋂ i ∈ s, f i) :=
        Finset.measurableSet_biInter (α := Ω) (m := ⨆ j < a, m j) s fun i hi ↦
          le_iSup₂ (f := fun j (_ : j < a) ↦ m j) i (hlt i hi) _ (hfs i hi)
      rw [Finset.set_biInter_insert, Finset.prod_insert hane,
        (Indep_iff _ _ _).1 (h a).symm _ _ (hf a (Finset.mem_insert_self a s)) hmeas,
        ih f hfs]
  rw [iIndep_iff]
  intro S f hf
  exact key S f hf
