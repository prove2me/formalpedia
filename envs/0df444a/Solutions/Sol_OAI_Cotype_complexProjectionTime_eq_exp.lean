-- Prove2me | solution 1 for OAI.Cotype.complexProjectionTime_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:38:03.476479+00:00
-- url     : https://prove2.me/submissions/69e86074-9e9f-4889-aae8-77bfbab05a89

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
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator

open OAI OAI.Cotype
open scoped BigOperators
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

theorem solution {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j)) (t : ℂ) :
    complexProjectionTime P t = NormedSpace.exp ((-t) • projectionGenerator P) := by
  let Φ := complexProjectionSpectralHom P hp hc
  have hΦc : Continuous Φ := (Φ.toLinearMap).continuous_of_finiteDimensional
  have hG : (-t) • projectionGenerator P = Φ ((-t) • fun ε : Cube m => (projectionDegree ε : ℂ)) := by
    rw [map_smul]; rfl
  rw [hG, ← NormedSpace.map_exp Φ hΦc]
  show complexProjectionPolynomial P (Complex.exp (-t)) = complexSpectralEval P _
  rw [complexProjectionPolynomial, h50c_spec, complexSpectralEval]
  refine Finset.sum_congr rfl fun ε _ => ?_
  congr 1
  rw [Pi.exp_def]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Complex.exp_eq_exp_ℂ, ← Complex.exp_nat_mul]
  ring_nf

