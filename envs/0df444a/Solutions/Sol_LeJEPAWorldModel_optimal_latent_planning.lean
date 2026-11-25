-- Prove2me | solution 1 for LeJEPAWorldModel.optimal_latent_planning
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T17:49:54.727973+00:00
-- url     : https://prove2.me/submissions/67e81b4e-a54f-4dec-9f4f-54b8dbe868dc

import Mathlib
import Definitions.Def_LeJEPAWorldModel_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeJEPAWorldModel

lemma lp_key {N : ℕ} {A : Type*} (Q : Matrix (Fin N) (Fin N) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin N) ℝ)
    (P : (Fin N → ℝ) → A → Measure (Fin N → ℝ))
    (c : (Fin N → ℝ) → A → ℝ) (cT : (Fin N → ℝ) → ℝ)
    (hinv : ∀ R ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∀ z a, c (R.mulVec z) a = c z a)
    (hinvT : ∀ R ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∀ z, cT (R.mulVec z) = cT z) :
    ∀ (as : List A) (z : Fin N → ℝ),
      planCost (pushDynamics Q P) c cT as (Q.mulVec z) = planCost P c cT as z := by
  have h1 : Q.transpose * Q = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp hQ
  have h2 : Q * Q.transpose = 1 := (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp hQ
  have hl : Function.LeftInverse (fun z => Q.transpose.mulVec z) (fun z => Q.mulVec z) := fun z => by
    simp [Matrix.mulVec_mulVec, h1]
  have hr : Function.RightInverse (fun z => Q.transpose.mulVec z) (fun z => Q.mulVec z) := fun z => by
    simp [Matrix.mulVec_mulVec, h2]
  have hme : MeasurableEmbedding (fun z : Fin N → ℝ => Q.mulVec z) :=
    MeasurableEmbedding.of_measurable_inverse (Q.mulVecLin.continuous_of_finiteDimensional.measurable)
      (by rw [hr.surjective.range_eq]; exact MeasurableSet.univ)
      (Q.transpose.mulVecLin.continuous_of_finiteDimensional.measurable) hl
  intro as
  induction as with
  | nil => intro z; simp [planCost, hinvT Q hQ]
  | cons a as ih =>
    intro z
    simp only [planCost, pushDynamics]
    rw [hinv Q hQ, hme.integral_map, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    simp only [ih]

end LeJEPAWorldModel

open LeJEPAWorldModel in
theorem solution {N : ℕ} {A : Type*} (Q : Matrix (Fin N) (Fin N) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin N) ℝ)
    (P : (Fin N → ℝ) → A → Measure (Fin N → ℝ)) (hP : ∀ z a, IsProbabilityMeasure (P z a))
    (hPmeas : ∀ a s, MeasurableSet s → Measurable fun z => P z a s)
    (c : (Fin N → ℝ) → A → ℝ) (cT : (Fin N → ℝ) → ℝ)
    (hc : ∀ a, Measurable fun z => c z a) (hcT : Measurable cT)
    (hinv : ∀ R ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∀ z a, c (R.mulVec z) a = c z a)
    (hinvT : ∀ R ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∀ z, cT (R.mulVec z) = cT z)
    (T : ℕ) (z0 : Fin N → ℝ) :
    optimalValue (pushDynamics Q P) c cT T (Q.mulVec z0) = optimalValue P c cT T z0 ∧
    ∀ as : List A, IsOptimalPlan (pushDynamics Q P) c cT T (Q.mulVec z0) as ↔
      IsOptimalPlan P c cT T z0 as := by
  have key := lp_key Q hQ P c cT hinv hinvT
  refine ⟨?_, fun as => ?_⟩
  · simp only [optimalValue, key]
  · simp only [IsOptimalPlan, key]
