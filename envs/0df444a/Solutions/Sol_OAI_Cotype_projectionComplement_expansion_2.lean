-- Prove2me | solution 2 for OAI.Cotype.projectionComplement_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:44:55.428169+00:00
-- url     : https://prove2.me/submissions/1065cff9-428e-4e92-b736-7b389eff58c2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionProducts.lean:L91-L107
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.projectionComplement_expansion. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.Cotype.ProjectionProducts ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem projectionComplement_expansion {n : ℕ} (P : Fin n → X →L[ℝ] X) :
    projectionProduct (fun i => 1 - P i) =
      ∑ ε : Cube n, (∏ i, sign (ε i)) • projectionSubset P ε := by
  induction n with
  | zero => simp [projectionProduct, projectionSubset]
  | succ n ih =>
    rw [← (cubeCons n).sum_comp]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    change (1-P 0) * projectionProduct (fun i => 1-P i.succ) = _
    rw [ih]
    simp only [cubeCons, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      sign_false, sign_true, projectionSubset, projectionProduct, Bool.false_eq_true, ite_false, ite_true,
      one_mul, neg_one_mul, neg_smul]
    simp only [sub_mul, one_mul, Finset.mul_sum, mul_smul_comm]
    simp only [sub_eq_add_neg, smul_add, smul_neg,
      Finset.sum_add_distrib, Finset.sum_neg_distrib]
    abel

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.projectionComplement_expansion := @_root_.OAI.Cotype.projectionComplement_expansion
