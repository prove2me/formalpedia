-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FirstMarkedCountPathV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:25:49.939097+00:00
-- url     : https://prove2.me/submissions/2631f9f7-24db-4fd4-a9a0-be7003375b2c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (w : Omega) (a T : NNReal) (ha : 0 < a)
    (hJ : L.X a w - Function.leftLim (fun u : NNReal => L.X u w) a ≠ 0)
    (hBefore : ∀ t : NNReal, 0 < t → t < a →
      L.X t w = Function.leftLim (fun u : NNReal => L.X u w) t)
    (B : Set Real) (hB : MeasurableSet B) :
    let NX := ((Measure.count.restrict {u : NNReal | 0 < u ∧
      L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
      (fun u : NNReal => (u,L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
    NX (Ioc 0 (min a T) ×ˢ B) =
      @ite ENNReal (a ≤ T ∧ L.X a w - Function.leftLim (fun u : NNReal => L.X u w) a ∈ B)
        (Classical.propDecidable _) 1 0 := by
  classical
  dsimp only
  let j : NNReal → Real := fun t => L.X t w - Function.leftLim (fun u : NNReal => L.X u w) t
  have hm : Measurable (fun t : NNReal => (t,j t)) :=
    measurable_id.prodMk ((avram_wave4_04a_actual_levy_jumpmark_joint_measurable L).comp
      (measurable_id.prodMk measurable_const))
  have hs : MeasurableSet (Ioc (0 : NNReal) (min a T) ×ˢ B) :=
    measurableSet_Ioc.prod hB
  change (Measure.map (fun t => (t,j t))
    (Measure.count.restrict {t | 0 < t ∧ j t ≠ 0})) (Ioc 0 (min a T) ×ˢ B) = _
  rw [Measure.map_apply hm hs, Measure.restrict_apply (hs.preimage hm)]
  have he : ((fun t : NNReal => (t,j t)) ⁻¹' (Ioc 0 (min a T) ×ˢ B)) ∩
      {t : NNReal | 0 < t ∧ j t ≠ 0} =
      if a ≤ T ∧ j a ∈ B then {a} else ∅ := by
    ext t
    by_cases h : a ≤ T ∧ j a ∈ B
    · simp only [h, if_pos, mem_singleton_iff]
      constructor
      · intro ht
        have hle : t ≤ a := (mem_Ioc.mp ht.1.1).2.trans (min_le_left _ _)
        by_contra hne
        exact ht.2.2 (sub_eq_zero.mpr (hBefore t ht.2.1 (lt_of_le_of_ne hle hne)))
      · rintro rfl
        exact ⟨⟨⟨ha,le_min le_rfl h.1⟩,h.2⟩,ha,hJ⟩
    · rw [if_neg h]
      constructor
      · intro ht
        have hle : t ≤ a := (mem_Ioc.mp ht.1.1).2.trans (min_le_left _ _)
        have htEq : t = a := le_antisymm hle (le_of_not_gt fun hlt =>
          ht.2.2 (sub_eq_zero.mpr (hBefore t ht.2.1 hlt)))
        subst t
        exact (h ⟨(mem_Ioc.mp ht.1.1).2.trans (min_le_right _ _),ht.1.2⟩).elim
      · intro ht
        exact ht.elim
  rw [he]
  by_cases h : a ≤ T ∧ j a ∈ B <;> simp [h,j]
