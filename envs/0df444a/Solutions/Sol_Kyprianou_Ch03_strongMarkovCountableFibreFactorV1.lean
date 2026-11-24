-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovCountableFibreFactorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:07:12.676517+00:00
-- url     : https://prove2.me/submissions/1ec2ae95-b6c4-473b-8000-8c3dd4abe241

import Mathlib.MeasureTheory.Measure.AEMeasurable
open MeasureTheory Set Filter
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Omega I E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (D : Set Omega) (hD : MeasurableSet D)
    (T : Omega → I) (hCount : Countable (Set.range T))
    (Y : I → Omega → E) (Z : Omega → E) (nu : Measure E)
    (hZ : Measurable Z)
    (hEq : ∀ w, Z w = Y (T w) w)
    (hFib : ∀ i : I, MeasurableSet (D ∩ {w | T w = i}))
    (hLaw : ∀ i : I, Measure.map (Y i) (P.restrict (D ∩ {w | T w = i})) =
      P (D ∩ {w | T w = i}) • nu) :
    Measure.map Z (P.restrict D) = P D • nu := by
  classical
  letI : Countable (Set.range T) := hCount
  let B : Set.range T → Set Omega := fun i => D ∩ {w | T w = (i : I)}
  have hb : ∀ i, MeasurableSet (B i) := fun i => hFib i
  have hd : Pairwise (Function.onFun Disjoint B) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro w ⟨_, hi⟩ ⟨_, hj⟩
    exact hij (Subtype.ext (hi.symm.trans hj))
  have hu : (⋃ i, B i) = D := by
    ext w
    simp only [B, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hw, _⟩
      exact hw
    · intro hw
      exact ⟨⟨T w, ⟨w, rfl⟩⟩, hw, rfl⟩
  have hsum : P.restrict D = Measure.sum (fun i => P.restrict (B i)) := by
    rw [← hu]
    exact Measure.restrict_iUnion hd hb
  have hm : ∀ i, Measure.map Z (P.restrict (B i)) = P (B i) • nu := by
    intro i
    rw [← hLaw (i : I)]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem (hb i)] with w hw
    rw [hEq w, hw.2]
  calc
    Measure.map Z (P.restrict D) = Measure.sum (fun i => Measure.map Z (P.restrict (B i))) := by
      rw [hsum, Measure.map_sum hZ.aemeasurable]
    _ = Measure.sum (fun i => P (B i) • nu) := by simp only [hm]
    _ = P D • nu := by
      ext S hS
      rw [Measure.sum_apply _ hS, Measure.smul_apply, ← hu, measure_iUnion hd hb]
      simp only [Measure.smul_apply, smul_eq_mul, ENNReal.tsum_mul_right]
