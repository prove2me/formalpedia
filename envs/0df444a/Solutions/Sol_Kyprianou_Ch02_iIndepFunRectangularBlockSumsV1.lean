-- Prove2me | solution 1 for Kyprianou.Ch02.iIndepFunRectangularBlockSumsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:51:40.160902+00:00
-- url     : https://prove2.me/submissions/1bbd42df-a17b-46f7-b510-08210ac808fb

import Theorems.Thm_levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (m n : ℕ) (D : Fin m × Fin n → Ω → ℝ)
    (hm : ∀ p, AEMeasurable (D p) P) (hi : iIndepFun D P) :
    iIndepFun (fun (i : Fin m) ω =>
      (∑ j : Fin n, max (D (i,j) ω) 0, ∑ j : Fin n, max (-D (i,j) ω) 0)) P := by
  let F (p : Fin m × Fin n) := (hm p).mk (D p)
  have hF (p : Fin m × Fin n) : Measurable (F p) := (hm p).measurable_mk
  have he (p : Fin m × Fin n) : D p =ᵐ[P] F p := (hm p).ae_eq_mk
  have hIF : iIndepFun F P := hi.congr he
  let S (i : Fin m) : Set (Fin m × Fin n) := {p | p.1=i}
  have hS : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro p hp hq
    exact hij (hp.symm.trans hq)
  have hb := levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint hF hIF hS
  let g (i : Fin m) (z : S i → ℝ) : ℝ × ℝ :=
    (∑ j : Fin n, max (z ⟨(i,j),rfl⟩) 0, ∑ j : Fin n, max (-z ⟨(i,j),rfl⟩) 0)
  have hg (i : Fin m) : Measurable (g i) := by fun_prop
  apply (hb.comp g hg).congr
  intro i
  filter_upwards [ae_all_iff.2 he] with ω hω
  simp [g, Function.comp_def, Set.restrict, hω]
