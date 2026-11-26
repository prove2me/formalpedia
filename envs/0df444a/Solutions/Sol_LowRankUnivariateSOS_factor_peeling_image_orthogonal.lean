-- Prove2me | solution 1 for LowRankUnivariateSOS.factor_peeling_image_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:45.258801+00:00
-- url     : https://prove2.me/submissions/4686dcab-c7f4-49b6-8b55-2ae3e42015a2

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.List.Prime
import Mathlib.Data.Multiset.Filter
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
import Theorems.Thm_LowRankUnivariateSOS_zero_fst
import Theorems.Thm_LowRankUnivariateSOS_zero_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_zero
import Theorems.Thm_LowRankUnivariateSOS_sigma2_zero
import Theorems.Thm_LowRankUnivariateSOS_A_zero_left
import Theorems.Thm_LowRankUnivariateSOS_A_zero_right
import Theorems.Thm_LowRankUnivariateSOS_factor_peeling_path
import Theorems.Thm_LowRankUnivariateSOS_A_scalePair_left
import Theorems.Thm_LowRankUnivariateSOS_A_self_eq_sigma2
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_left
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_right
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_left
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_right
import Theorems.Thm_LowRankUnivariateSOS_image_orthogonal_of_peeling_path
import Theorems.Thm_LowRankUnivariateSOS_image_orthogonal_self_of_focp
import Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
import Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
import Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
import Theorems.Thm_LowRankUnivariateSOS_sigma2_perpPair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_scalePair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_smul
import Theorems.Thm_LowRankUnivariateSOS_smul_fst
import Theorems.Thm_LowRankUnivariateSOS_smul_snd
attribute [local simp] LowRankUnivariateSOS.A_scalePair_left
attribute [local simp] LowRankUnivariateSOS.A_self_eq_sigma2
attribute [local simp] LowRankUnivariateSOS.A_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_add_left
attribute [local simp] LowRankUnivariateSOS.dot_add_right
attribute [local simp] LowRankUnivariateSOS.dot_neg_left
attribute [local simp] LowRankUnivariateSOS.dot_neg_right
attribute [local simp] LowRankUnivariateSOS.dot_smul_left
attribute [local simp] LowRankUnivariateSOS.dot_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_zero_left
attribute [local simp] LowRankUnivariateSOS.dot_zero_right
attribute [local simp] LowRankUnivariateSOS.perpPair_fst
attribute [local simp] LowRankUnivariateSOS.perpPair_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_fst
attribute [local simp] LowRankUnivariateSOS.scalePair_snd
attribute [local simp] LowRankUnivariateSOS.sigma2_perpPair
attribute [local simp] LowRankUnivariateSOS.sigma2_scalePair
attribute [local simp] LowRankUnivariateSOS.sigma2_smul
attribute [local simp] LowRankUnivariateSOS.smul_fst
attribute [local simp] LowRankUnivariateSOS.smul_snd


attribute [local simp] LowRankUnivariateSOS.zero_fst
attribute [local simp] LowRankUnivariateSOS.zero_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_zero
attribute [local simp] LowRankUnivariateSOS.sigma2_zero
attribute [local simp] LowRankUnivariateSOS.A_zero_left
attribute [local simp] LowRankUnivariateSOS.A_zero_right

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}
namespace LowRankUnivariateSOS
theorem _root_.solution
    (p : Poly) (u : UPair)
    (hsocp : IsSOCP B p u)
    (data : ReducedFactorization u) (ha : data.a ≠ 0) :
    ∃ g : Poly, g ≠ 0 ∧ IsCoprime g (sigma2 data.u0) ∧
      ImageOrthogonalResidual B p (scalePair data.a data.u0) (scalePair g data.u0) := by
  have hstart : ImageOrthogonalResidual B p u u :=
    image_orthogonal_self_of_focp (B := B) hsocp.1
  rcases factor_peeling_path u data ha with ⟨g, hg, hcopg, hpath⟩
  have himg : ImageOrthogonalResidual B p u (scalePair g data.u0) :=
    image_orthogonal_of_peeling_path (B := B) hsocp hstart hpath
  refine ⟨g, hg, hcopg, ?_⟩
  simpa [data.eq_scale] using himg
end LowRankUnivariateSOS
