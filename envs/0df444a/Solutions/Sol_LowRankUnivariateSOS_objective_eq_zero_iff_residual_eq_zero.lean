-- Prove2me | solution 1 for LowRankUnivariateSOS.objective_eq_zero_iff_residual_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:22.163136+00:00
-- url     : https://prove2.me/submissions/52ec2769-9f5e-49ef-8601-162d654b6b4d

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_left
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_right
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_left
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_right
import Theorems.Thm_LowRankUnivariateSOS_A_self_eq_sigma2
attribute [local simp] LowRankUnivariateSOS.dot_add_left
attribute [local simp] LowRankUnivariateSOS.dot_add_right
attribute [local simp] LowRankUnivariateSOS.dot_smul_left
attribute [local simp] LowRankUnivariateSOS.dot_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_zero_left
attribute [local simp] LowRankUnivariateSOS.dot_zero_right
attribute [local simp] LowRankUnivariateSOS.dot_neg_left
attribute [local simp] LowRankUnivariateSOS.dot_neg_right
attribute [local simp] LowRankUnivariateSOS.A_self_eq_sigma2

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]
namespace LowRankUnivariateSOS
theorem _root_.solution {p : Poly} {u : UPair} :
    objective B p u = 0 ↔ residual p u = 0 := by
  have hani : B.toQuadraticMap.Anisotropic :=
    (Fact.out : B.toQuadraticMap.PosDef).anisotropic
  constructor
  · intro h
    exact (QuadraticMap.Anisotropic.eq_zero_iff hani).mp (by
      simpa [objective, LinearMap.BilinMap.toQuadraticMap_apply] using h)
  · intro h
    simp [objective, h]
end LowRankUnivariateSOS
