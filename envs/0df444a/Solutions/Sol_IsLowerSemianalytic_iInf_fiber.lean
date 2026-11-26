-- Prove2me | solution 1 for IsLowerSemianalytic.iInf_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:00:03.393388+00:00
-- url     : https://prove2.me/submissions/387b8001-ff51-47f5-8246-9afdbeaa0eb1

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic

set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X]
namespace IsLowerSemianalytic
theorem _root_.solution
    {Y : Type*} [TopologicalSpace Y] [PolishSpace X] [PolishSpace Y]
    [T2Space X]
    {D : Set (X × Y)} (hD : AnalyticSet D)
    {f : X × Y → ENNReal} (hf : IsLowerSemianalytic (X := X × Y) f) :
    IsLowerSemianalytic (fun x => ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y)) := by
  intro c
  have h_sub : {x | ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y) < c} =
      Prod.fst '' (D ∩ {p | f p < c}) := by
    ext x; simp only [mem_ofPred_eq, mem_image, Prod.exists]
    constructor
    · intro hlt
      rw [iInf_lt_iff] at hlt
      obtain ⟨y, hy⟩ := hlt
      rw [iInf_lt_iff] at hy
      obtain ⟨hm, hfc⟩ := hy
      exact ⟨x, y, ⟨hm, hfc⟩, rfl⟩
    · rintro ⟨x', y, ⟨hm, hfc⟩, rfl⟩
      exact lt_of_le_of_lt (iInf₂_le y hm) hfc
  rw [h_sub]
  have h_inter : AnalyticSet (D ∩ {p | f p < c}) := by
    have h1 := hD
    have h2 := hf c
    rw [show D ∩ {p | f p < c} = ⋂ (i : Fin 2),
        (![D, {p | f p < c}]) i from by ext x; simp [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]]
    exact AnalyticSet.iInter (fun i => by fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> assumption)
  exact h_inter.image_of_continuous continuous_fst
end IsLowerSemianalytic
