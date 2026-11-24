-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.expand_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:18:44.236638+00:00
-- url     : https://prove2.me/submissions/d5f3f499-3156-43a1-ad20-746306f10af1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open Module NumberField
open GlobalTheory.CompanionTheory.Ar.HT.LatBasic
open TensorProduct
variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CompanionTheory.Ar.HT.LatBasic
theorem _root_.solution (x : E) :
    x = ∑ k, Algebra.trace ℚ E (x * integralBasis E k) • dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr x
  simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at h
  exact h.symm
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
