-- Prove2me | solution 1 for GlobalTheory.UnitLemma.PrincipalLatDVR.isPrincipalIdealRing_integralClosure_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:11:52.838835+00:00
-- url     : https://prove2.me/submissions/c20ccda1-3d0d-4fba-af68-aab714d52bdf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
import Theorems.Thm_GlobalTheory_isDedekindDomain_integralClosure_of_dimensionLEOne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PrincipalLatDVR
namespace GlobalTheory.UnitLemma.PrincipalLatDVR
theorem _root_.solution {O E L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [Field L]
    [Algebra E L] [Algebra O L] [IsScalarTower O E L] [FiniteDimensional E L] :
    IsPrincipalIdealRing (integralClosure O L) := by
  haveI : IsDedekindDomain (integralClosure O L) :=
    GlobalTheory.isDedekindDomain_integralClosure_of_dimensionLEOne E
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O E L]
    exact (algebraMap E L).injective.comp (IsFractionRing.injective O E)
  haveI : Module.IsTorsionFree O (integralClosure O L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr fun x y h => hinj (congrArg Subtype.val h)
  apply IsPrincipalIdealRing.of_finite_primes
  have hfin := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal O) (integralClosure O L)
  refine (hfin.insert ⊥).subset ?_
  intro P hP
  by_cases h : P = ⊥
  · exact Or.inl h
  · right
    haveI : P.IsPrime := hP
    have hne : P.comap (algebraMap O (integralClosure O L)) ≠ ⊥ := fun h0 => h (Ideal.eq_bot_of_comap_eq_bot h0)
    have hmax : (P.comap (algebraMap O (integralClosure O L))).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime hne inferInstance
    refine ⟨hP, ⟨?_⟩⟩
    exact (IsLocalRing.eq_maximalIdeal hmax).symm
end GlobalTheory.UnitLemma.PrincipalLatDVR
