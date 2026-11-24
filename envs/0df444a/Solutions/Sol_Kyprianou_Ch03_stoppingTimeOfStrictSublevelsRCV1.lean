-- Prove2me | solution 1 for Kyprianou.Ch03.stoppingTimeOfStrictSublevelsRCV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:02:33.304832+00:00
-- url     : https://prove2.me/submissions/7feef553-a558-4890-8595-4ef79d237a0b

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem le_iff_forall_lt (τ : WithTop NNReal) (t : NNReal) (n0 : ℕ) :
    τ ≤ (t : WithTop NNReal) ↔
      ∀ n : ℕ, τ < ((t + 1 / ((n + n0 : ℕ) + 1 : NNReal) : NNReal) : WithTop NNReal) := by
  constructor
  · intro h n
    refine lt_of_le_of_lt h ?_
    rw [WithTop.coe_lt_coe]
    exact lt_add_of_pos_right _ (by positivity)
  · intro h
    by_contra hlt
    push_neg at hlt
    induction τ using WithTop.recTopCoe with
    | top => exact absurd (h 0) (not_lt.mpr le_top)
    | coe c =>
      have hct : t < c := WithTop.coe_lt_coe.mp hlt
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hct)
      have h1 : 1 / (((k + n0 : ℕ) : NNReal) + 1) ≤ 1 / ((k : NNReal) + 1) := by
        gcongr
        exact_mod_cast Nat.le_add_right k n0
      have h2 : t + 1 / (((k + n0 : ℕ) : NNReal) + 1) < c := by
        have := (lt_tsub_iff_left).mp (h1.trans_lt hk)
        exact this
      exact absurd (WithTop.coe_lt_coe.mp (h k)) (not_lt.mpr h2.le)


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hRC : F.IsRightContinuous) (T : Omega → WithTop NNReal)
    (hLt : ∀ s : NNReal, MeasurableSet[F s] {w | T w < (s : WithTop NNReal)}) :
    IsStoppingTime F T := by
  intro t
  have hplus : MeasurableSet[Filtration.rightCont F t] {omega | T omega ≤ (t : WithTop NNReal)} := by
    rw [Filtration.rightCont_eq_of_neBot_nhdsGT]
    refine MeasurableSpace.measurableSet_iInf.mpr fun j => ?_
    refine MeasurableSpace.measurableSet_iInf.mpr fun htj => ?_
    obtain ⟨n0, hn0⟩ := exists_nat_one_div_lt (tsub_pos_of_lt htj)
    have hset : {omega | T omega ≤ (t : WithTop NNReal)} =
        ⋂ n : ℕ, {omega | T omega <
          ((t + 1 / ((n + n0 : ℕ) + 1 : NNReal) : NNReal) : WithTop NNReal)} := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact le_iff_forall_lt (T omega) t n0
    rw [hset]
    refine MeasurableSet.iInter fun n => ?_
    have hle : t + 1 / (((n + n0 : ℕ) : NNReal) + 1) ≤ j := by
      have h1 : 1 / (((n + n0 : ℕ) : NNReal) + 1) ≤ 1 / ((n0 : NNReal) + 1) := by
        gcongr
        exact_mod_cast Nat.le_add_left n0 n
      have h2 := ((lt_tsub_iff_left).mp (h1.trans_lt hn0)).le
      exact h2
    exact F.mono hle _ (hLt _)
  exact hRC.RC t _ hplus
