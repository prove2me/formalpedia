-- Prove2me | solution 1 for Kyprianou.Ch05.karamataExpTiltRecoverMass
-- status  : ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-27T01:06:38.127839+00:00
-- url     : https://prove2.me/submissions/ae4d247b-4e9c-47f1-acd4-99962444c5dc

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exp-tilt mass recovery: the exp-tilted, exp-mapped measure, re-weighted
by `(max z c)⁻¹` with `c = exp (-1)`, has mass `M (Icc 0 1)` above `c`,
and no atom at `c` when `M` has no atom at `1`. Pointwise, for `z ≤ 1`
the re-weighting exactly cancels the tilt density, so the integral over
`z ≤ 1` is the mass of `[0, 1]`. -/
theorem solution
    (M : Measure Real) (hs : M (Iio 0) = 0) :
    let N := ((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
      (fun z : Real => Real.exp (-z)))
    let c := Real.exp (-1)
    (N.withDensity (fun z : Real => ENNReal.ofReal ((max z c)⁻¹))) (Ici c) =
      M (Icc 0 1) ∧ (M {1} = 0 → N {c} = 0) := by
  have hfmeas : Measurable (fun z : Real => ENNReal.ofReal ((max z (Real.exp (-1)))⁻¹)) :=
    ((measurable_id.max measurable_const).inv).ennreal_ofReal
  have hφmeas : Measurable (fun z : Real => Real.exp (-z)) :=
    Real.measurable_exp.comp measurable_id.neg
  have hgmeas : Measurable (fun z : Real => ENNReal.ofReal (Real.exp (-z))) :=
    hφmeas.ennreal_ofReal
  have hcomp : Measurable (fun z : Real =>
      ENNReal.ofReal ((max (Real.exp (-z)) (Real.exp (-1)))⁻¹)) :=
    hfmeas.comp hφmeas
  have hIic : M (Set.Iic (1 : Real)) = M (Set.Icc 0 1) := by
    have hdisj : Disjoint (Set.Icc (0 : Real) 1) (Set.Iio 0) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      simp only [Set.mem_Icc, Set.mem_Iio] at hx1 hx2
      linarith
    have hunion : Set.Icc (0 : Real) 1 ∪ Set.Iio 0 = Set.Iic 1 := by
      ext x
      simp only [Set.mem_union, Set.mem_Icc, Set.mem_Iio, Set.mem_Iic]
      constructor
      · rintro (⟨h0, h1⟩ | h)
        · exact h1
        · linarith
      · intro h
        by_cases h0 : 0 ≤ x
        · exact Or.inl ⟨h0, h⟩
        · exact Or.inr (by linarith)
    calc M (Set.Iic (1 : Real)) = M (Set.Icc (0 : Real) 1 ∪ Set.Iio 0) := by rw [hunion]
      _ = M (Set.Icc (0 : Real) 1) + M (Set.Iio 0) :=
          measure_union hdisj measurableSet_Iio
      _ = M (Set.Icc (0 : Real) 1) := by rw [hs, add_zero]
  have hind : ∀ z : Real,
      (Set.Ici (Real.exp (-1))).indicator
          (fun z : Real => ENNReal.ofReal ((max z (Real.exp (-1)))⁻¹))
          (Real.exp (-z)) =
        (Set.Iic (1 : Real)).indicator
          (fun z : Real => ENNReal.ofReal ((max (Real.exp (-z)) (Real.exp (-1)))⁻¹)) z := by
    intro z
    by_cases hz : z ≤ 1
    · rw [Set.indicator_of_mem, Set.indicator_of_mem]
      · exact hz
      · show Real.exp (-1) ≤ Real.exp (-z)
        exact Real.exp_le_exp.mpr (by linarith)
    · push_neg at hz
      rw [Set.indicator_of_notMem, Set.indicator_of_notMem]
      · exact not_le.mpr hz
      · show ¬ Real.exp (-1) ≤ Real.exp (-z)
        rw [Real.exp_le_exp]
        push_neg
        linarith
  have hmul' : ∀ z : Real,
      (Set.Iic (1 : Real)).indicator
          (fun z : Real => ENNReal.ofReal ((max (Real.exp (-z)) (Real.exp (-1)))⁻¹)) z *
        ENNReal.ofReal (Real.exp (-z)) =
        (Set.Iic (1 : Real)).indicator
          (fun z : Real => ENNReal.ofReal ((max (Real.exp (-z)) (Real.exp (-1)))⁻¹) *
            ENNReal.ofReal (Real.exp (-z))) z := by
    intro z
    by_cases hz : z ∈ Set.Iic (1 : Real)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
  have hmul : ∀ z : Real,
      ENNReal.ofReal (Real.exp (-z)) *
        (Set.Iic (1 : Real)).indicator
          (fun z : Real => ENNReal.ofReal ((max (Real.exp (-z)) (Real.exp (-1)))⁻¹)) z =
        (Set.Iic (1 : Real)).indicator
          (fun z : Real => ENNReal.ofReal ((max (Real.exp (-z)) (Real.exp (-1)))⁻¹) *
            ENNReal.ofReal (Real.exp (-z))) z := by
    intro z
    by_cases hz : z ∈ Set.Iic (1 : Real)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, mul_comm]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
  have hEqOn : Set.EqOn
      (fun z : Real => ENNReal.ofReal ((max (Real.exp (-z)) (Real.exp (-1)))⁻¹) *
        ENNReal.ofReal (Real.exp (-z)))
      (fun _ => (1 : ℝ≥0∞)) (Set.Iic (1 : Real)) := by
    intro z hz
    have hz1 : z ≤ 1 := hz
    show ENNReal.ofReal ((max (Real.exp (-z)) (Real.exp (-1)))⁻¹) *
        ENNReal.ofReal (Real.exp (-z)) = 1
    have hmax : max (Real.exp (-z)) (Real.exp (-1)) = Real.exp (-z) :=
      max_eq_left (Real.exp_le_exp.mpr (by linarith : (-1 : Real) ≤ -z))
    rw [hmax]
    have e1 : (Real.exp (-z))⁻¹ = Real.exp z := by rw [Real.exp_neg, inv_inv]
    rw [e1, ← ENNReal.ofReal_mul (Real.exp_pos z).le, ← Real.exp_add]
    simp
  have hInd : (Set.Iic (1 : Real)).indicator
        (fun z : Real => ENNReal.ofReal ((max (Real.exp (-z)) (Real.exp (-1)))⁻¹) *
          ENNReal.ofReal (Real.exp (-z))) =
        (Set.Iic (1 : Real)).indicator (fun _ : Real => (1 : ℝ≥0∞)) := by
    funext a
    by_cases ha : a ∈ Set.Iic (1 : Real)
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
      exact hEqOn ha
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]
  have key :
      ((((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
          (fun z : Real => Real.exp (-z))).withDensity
          (fun z : Real => ENNReal.ofReal ((max z (Real.exp (-1)))⁻¹)))
        (Set.Ici (Real.exp (-1)))) = M (Set.Icc 0 1) ∧
      (M {1} = 0 →
        ((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
          (fun z : Real => Real.exp (-z))) {Real.exp (-1)} = 0) := by
    constructor
    · have hA : ((((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
              (fun z : Real => Real.exp (-z))).withDensity
              (fun z : Real => ENNReal.ofReal ((max z (Real.exp (-1)))⁻¹)))
            (Set.Ici (Real.exp (-1)))) =
            ∫⁻ a in Set.Ici (Real.exp (-1)),
              (fun z : Real => ENNReal.ofReal ((max z (Real.exp (-1)))⁻¹)) a ∂
              (((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
                (fun z : Real => Real.exp (-z)))) :=
          withDensity_apply _ measurableSet_Ici
      rw [hA,
        ← lintegral_indicator measurableSet_Ici,
        lintegral_map (hfmeas.indicator measurableSet_Ici)
          hφmeas]
      simp only [hind]
      rw [lintegral_indicator measurableSet_Iic,
        ← lintegral_indicator measurableSet_Iic,
        lintegral_withDensity_eq_lintegral_mul M hgmeas
          (hcomp.indicator measurableSet_Iic)]
      simp only [Pi.mul_apply, hmul, hmul']
      rw [hInd, lintegral_indicator_const measurableSet_Iic, one_mul, hIic]
    · intro h1
      rw [Measure.map_apply hφmeas (measurableSet_singleton _)]
      have hpre : (fun z : Real => Real.exp (-z)) ⁻¹' {Real.exp (-1)} = {1} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro h
          exact neg_inj.mp (Real.exp_injective h)
        · intro h
          rw [h]
      rw [hpre]
      exact MeasureTheory.withDensity_absolutelyContinuous M _ h1
  exact key
