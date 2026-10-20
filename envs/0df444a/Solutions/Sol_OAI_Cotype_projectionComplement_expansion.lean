-- Prove2me | solution 1 for OAI.Cotype.projectionComplement_expansion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:41:46.747732+00:00
-- url     : https://prove2.me/submissions/9ac98d7e-e04e-4126-9767-cae23c896f37

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

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem t_expand {n : ℕ} (P : Fin n → X →L[ℝ] X) :
    projectionProduct (fun i => 1 - P i) =
      ∑ ε : Cube n, (∏ i, sign (ε i)) • projectionSubset P ε := by
  induction n with
  | zero => simp [projectionProduct, projectionSubset]
  | succ n ih =>
    rw [← (cubeCons n).sum_comp]
    simp only [Fintype.sum_prod_type, cubeCons, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, projectionSubset, projectionProduct, Fintype.sum_bool]
    rw [ih (fun i => P i.succ)]
    simp only [projectionSubset, sign_true, sign_false, if_true, Bool.false_eq_true, if_false,
      one_mul, neg_one_mul, sub_mul, Finset.mul_sum, mul_smul_comm, neg_smul, Finset.sum_neg_distrib]
    rw [neg_add_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_sub]

theorem solution {n : ℕ} (P : Fin n → X →L[ℝ] X) :
    projectionProduct (fun i => 1 - P i) =
      ∑ ε : Cube n, (∏ i, sign (ε i)) • projectionSubset P ε := by
  exact t_expand P

