-- Prove2me | solution 1 for OAI.Cotype.complexProjectionPolynomial_spectral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:33:38.828865+00:00
-- url     : https://prove2.me/submissions/17a42168-8b99-432c-9f1e-ffe2eb9814bf

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum

open OAI OAI.Cotype
open scoped BigOperators
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
theorem h50c_deg_cons {m : ℕ} (b : Bool) (η : Cube m) :
    projectionDegree (Fin.cons b η : Cube (m+1)) = (if b then 1 else 0) + projectionDegree η := by
  classical
  simp only [projectionDegree, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem h50c_pat_cons {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {m : ℕ}
    (P : Fin (m+1) → Y →L[ℝ] Y) (b : Bool) (η : Cube m) :
    projectionPattern P (Fin.cons b η : Cube (m+1)) =
      (if b then 1 - P 0 else P 0) * projectionPattern (fun i => P i.succ) η := by
  simp only [projectionPattern, projectionProduct, Fin.cons_zero, Fin.cons_succ]

theorem h50c_spec {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (z : ℂ) : ∀ (m : ℕ) (P : Fin m → Y →L[ℝ] Y),
    complexProjectionProduct (fun i => complexDualLift (P i) + z • (1 - complexDualLift (P i))) =
      ∑ ε : Cube m, (z^(projectionDegree ε)) • complexDualLift (projectionPattern P ε) := by
  intro m
  induction m with
  | zero =>
    intro P
    simp [complexProjectionProduct, projectionDegree, projectionPattern, projectionProduct]
  | succ m ih =>
    intro P
    rw [complexProjectionProduct, ih (fun i => P i.succ)]
    rw [← (projectionChoiceCons Bool m).sum_comp]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, projectionChoiceCons, Equiv.coe_fn_mk,
      h50c_deg_cons, h50c_pat_cons]
    simp only [if_true, if_false, Bool.false_eq_true, zero_add, complexDualLift_mul, complexDualLift_sub,
      complexDualLift_one, add_mul, Finset.mul_sum, mul_smul_comm, smul_mul_assoc, pow_add, pow_one,
      mul_comm z, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    simp only [smul_add, Finset.sum_add_distrib]; exact add_comm _ _

theorem solution {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (z : ℂ) :
    complexProjectionPolynomial P z = complexSpectralEval P (fun ε => z^(projectionDegree ε)) := by
  exact h50c_spec z m P

