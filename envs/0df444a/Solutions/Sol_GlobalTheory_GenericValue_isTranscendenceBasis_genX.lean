-- Prove2me | solution 1 for GlobalTheory.GenericValue.isTranscendenceBasis_genX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:52.138972+00:00
-- url     : https://prove2.me/submissions/fb0addd1-8d17-446f-a6ca-31e51b50ce51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomOfIsTranscendenceBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenericValue
open MvPolynomial
variable {K : Type} [Field K]
namespace GlobalTheory.GenericValue
theorem _root_.solution (F I : Type) [Field F] : IsTranscendenceBasis F (genX F I) := by
  haveI : Algebra.IsAlgebraic (MvPolynomial I F) (FractionRing (MvPolynomial I F)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  haveI : Algebra.IsAlgebraic (MvPolynomial I F) (Gen F I) :=
    Algebra.IsAlgebraic.trans _ (FractionRing (MvPolynomial I F)) _
  haveI : FaithfulSMul (MvPolynomial I F) (Gen F I) := (faithfulSMul_iff_algebraMap_injective _ _).2 <| by
    rw [IsScalarTower.algebraMap_eq _ (FractionRing (MvPolynomial I F))]
    exact (algebraMap (FractionRing (MvPolynomial I F)) (Gen F I)).injective.comp (IsFractionRing.injective _ _)
  exact (IsTranscendenceBasis.mvPolynomial I F).algebraMap_comp
end GlobalTheory.GenericValue
