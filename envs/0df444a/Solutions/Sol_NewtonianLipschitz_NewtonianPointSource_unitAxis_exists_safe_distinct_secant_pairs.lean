-- Prove2me | solution 1 for NewtonianLipschitz.NewtonianPointSource.unitAxis_exists_safe_distinct_secant_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:18:05.164654+00:00
-- url     : https://prove2.me/submissions/8409ae1e-5c9f-46af-b2f3-08daa8e83d39

module
public import Definitions.Def_NewtonianLipschitz_AdmissibleCriticalDirection
public import Definitions.Def_NewtonianLipschitz_AdmissibleSecantPairs
public import Theorems.Thm_NewtonianLipschitz_candidateMaximum_pos
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_exists_safe_sharp_outward_ray
public import Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_unitAxis_fderiv_opNorm_eq_candidateMaximum


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
namespace NewtonianPointSource
theorem _root_.solution :
    ∃ h : Vec3, ‖h‖ = 1 ∧
      ‖(fderiv ℝ NewtonianPointSource.unitAxis.accelerationField
        (normalizedVector candidateCriticalPoint candidateCriticalPoint)) h‖ =
          candidateMaximum ∧
      ∀ s : ℝ, 0 < s →
        (1 : ℝ) ≤
          ‖normalizedVector candidateCriticalPoint candidateCriticalPoint +
            s • h‖ ∧
        ‖(normalizedVector candidateCriticalPoint candidateCriticalPoint +
            s • h) -
          normalizedVector candidateCriticalPoint candidateCriticalPoint‖ =
            s ∧
        normalizedVector candidateCriticalPoint candidateCriticalPoint +
          s • h ≠
            normalizedVector candidateCriticalPoint candidateCriticalPoint := by
  let x : Vec3 :=
    normalizedVector candidateCriticalPoint candidateCriticalPoint
  let c := NewtonianPointSource.unitAxis
  obtain ⟨h, hh, haction, hsafe⟩ :=
    NewtonianPointSource.unitAxis_exists_safe_sharp_outward_ray
  have hoper :
      ‖fderiv ℝ c.accelerationField x‖ = candidateMaximum :=
    NewtonianPointSource.unitAxis_fderiv_opNorm_eq_candidateMaximum
  have hmult :
      candidateMaximum ≤ candidateMaximum * ‖h‖ := by
    calc
      candidateMaximum =
          ‖(fderiv ℝ c.accelerationField x) h‖ := haction.symm
      _ ≤ ‖fderiv ℝ c.accelerationField x‖ * ‖h‖ :=
        (fderiv ℝ c.accelerationField x).le_opNorm h
      _ = candidateMaximum * ‖h‖ := by rw [hoper]
  have hnorm : ‖h‖ = (1 : ℝ) := by
    rcases lt_or_eq_of_le hh with hlt | heq
    · have hmul :=
        mul_lt_mul_of_pos_left hlt candidateMaximum_pos
      linarith
    · exact heq
  refine ⟨h, hnorm, haction, ?_⟩
  intro s hs
  have hdist : ‖(x + s • h) - x‖ = s := by
    rw [add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hs.le, hnorm, mul_one]
  have hdistinct : x + s • h ≠ x := by
    intro heq
    rw [heq, sub_self, norm_zero] at hdist
    linarith
  exact ⟨hsafe s hs.le, hdist, hdistinct⟩
end NewtonianPointSource
end NewtonianLipschitz
