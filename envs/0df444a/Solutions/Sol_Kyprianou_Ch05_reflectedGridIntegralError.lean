-- Prove2me | solution 1 for Kyprianou.Ch05.reflectedGridIntegralError
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:52:37.424191+00:00
-- url     : https://prove2.me/submissions/0e407be0-5e75-45d3-ae45-2c8c34a1a3c5

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_Kyprianou_Ch05_reflectedGridPartitionData
import Theorems.Thm_Kyprianou_Ch05_finitePartitionIntegralError
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Apply the finite-partition integral estimate to the reflected clipped grid. -/
theorem solution
    (V : Measure Real) (hfinite : ∀ x : Real, V (Set.Icc 0 x) ≠ ⊤)
    (h : Real → Real) (hm : Measurable h)
    (hloc : ∀ a b : Real, a < b →
      BddAbove (h '' Set.Icc a b) ∧ BddBelow (h '' Set.Icc a b))
    (d : Real) (hd : 0 < d) (c e : Nat → Real)
    (ha : ∀ (k : Nat) (y : Real), y ∈ Set.Ico ((k : Real)*d) (((k : Real)+1)*d) →
      |h y-c k| ≤ e k)
    (x : Real) (hx : 0 ≤ x) :
    |(∫ z in Set.Icc 0 x, h (x-z) ∂V) -
      (∑' k : Nat, c k * (V (Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d))).toReal)| ≤
      ∑' k : Nat, e k * (V (Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d))).toReal := by
  let S := fun k : Nat => Icc 0 x ∩ Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d)
  obtain ⟨hU,hD,hM,hN⟩ := reflectedGridPartitionData x d hx hd
  obtain ⟨⟨u,hu⟩,⟨l,hl⟩⟩ := hloc 0 (x+1) (by linarith)
  have hf : IntegrableOn (fun z => h (x-z)) (Icc 0 x) V := by
    apply Measure.integrableOn_of_bounded (hfinite x) (M := |u|+|l|)
      (hm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    refine (ae_restrict_mem measurableSet_Icc).mono ?_
    intro z hz
    have hmem : h (x-z) ∈ h '' Icc 0 (x+1) :=
      ⟨x-z,⟨by linarith [hz.2],by linarith [hz.1]⟩,rfl⟩
    change ‖h (x-z)‖ ≤ |u|+|l|
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hl hmem, abs_nonneg u, neg_abs_le l],
      by linarith [hu hmem, le_abs_self u, abs_nonneg l]⟩
  apply finitePartitionIntegralError V (Icc 0 x) S (hfinite x) hU hD hM hN _ hf c e
  intro k z hz
  exact ha k (x-z) ⟨by linarith [hz.2.2],by linarith [hz.2.1]⟩
