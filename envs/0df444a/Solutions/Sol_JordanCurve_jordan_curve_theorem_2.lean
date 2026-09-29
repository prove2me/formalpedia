-- Prove2me | solution 2 for JordanCurve.jordan_curve_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T13:13:29.394153+00:00
-- url     : https://prove2.me/submissions/c43244cf-cd2d-4547-aa74-8ecd640c4b5f

import Definitions.Def_Schoenflies_Jordan
import Definitions.Def_Schoenflies_SquareCycle
import Theorems.Thm_JordanCurve_circle_embedding_is_schoenflies_jordan

theorem solution
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ) :
    ∃ inside outside : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen inside ∧ IsOpen outside ∧
      IsConnected inside ∧ IsConnected outside ∧
      Bornology.IsBounded inside ∧ ¬ Bornology.IsBounded outside ∧
      Disjoint inside outside ∧
      inside ∪ outside = (Set.range γ)ᶜ ∧
      frontier inside = Set.range γ ∧
      frontier outside = Set.range γ := by
  let C : Set (EuclideanSpace ℝ (Fin 2)) := Set.range γ
  have hCurve : Schoenflies.IsJordanCurve C :=
    JordanCurve.circle_embedding_is_schoenflies_jordan γ hγ hinj
  have hSep : Schoenflies.IsSeparating C :=
    Schoenflies.IsJordanCurve.isSeparating
      (fun A hA => Schoenflies.isConnected_compl_arc hA Schoenflies.squaresTwoConnected)
      hCurve
  refine ⟨Schoenflies.inside C, Schoenflies.outside C,
    hSep.isOpen_inside, hSep.isOpen_outside,
    hSep.isConnected_inside, hSep.isConnected_outside,
    hSep.isBounded_inside, hSep.not_isBounded_outside, ?_,
    Schoenflies.inside_union_outside C, hSep.frontier_inside,
    hSep.frontier_outside⟩
  exact Set.disjoint_left.mpr (fun x hi ho => ho.2 hi.2)
