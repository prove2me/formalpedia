-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.repr_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:18:45.63469+00:00
-- url     : https://prove2.me/submissions/7848e5e9-13f4-4955-b590-40168b296c25

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
theorem _root_.solution (a : 𝓞 E) (k) :
    (((RingOfIntegers.basis E).repr a k : ℤ) : ℚ) = Algebra.trace ℚ E (dualInt E k * (a : E)) := by
  classical
  conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr a]
  simp only [map_sum, RingOfIntegers.coe_eq_algebraMap, Finset.mul_sum, map_zsmul, mul_smul_comm,
    ← integralBasis_apply, trace_dualInt]
  simp
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
