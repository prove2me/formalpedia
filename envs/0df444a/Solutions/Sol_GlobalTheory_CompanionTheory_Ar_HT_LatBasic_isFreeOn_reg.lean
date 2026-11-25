-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.isFreeOn_reg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:34:39.40674+00:00
-- url     : https://prove2.me/submissions/74cb8ee0-a41d-4f50-9c6f-6c93497537c3

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
theorem _root_.solution :
    IsFreeOn (A := A) (regAct K E)
      (Submodule.span A (Set.range (Algebra.TensorProduct.basis K (RingOfIntegers.basis E))))
      (fun _ : Fin 1 => 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [regAct_basis]
    exact (Algebra.TensorProduct.basis K (RingOfIntegers.basis E)).linearIndependent.comp
      (fun q : Fin 1 × _ => q.2) (fun p q h => Prod.ext (Subsingleton.elim _ _) h)
  · rw [Submodule.span_span_of_tower, Basis.span_eq]
  · simp only [regAct_basis]
    congr 1
    ext x
    simp
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
