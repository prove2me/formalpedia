-- Prove2me | solution 1 for GlobalTheory.SmoothTangent.finrank_cotangent_le_finrank_derivation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:25:45.108267+00:00
-- url     : https://prove2.me/submissions/1fec2621-e0cf-4a6c-98b9-44a99459aa8f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Theorems.Thm_GlobalTheory_SmoothTangent_kerCotangentToTensor_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SmoothTangent
namespace GlobalTheory.SmoothTangent
theorem _root_.solution (k : Type*) [Field k] [PerfectField k]
    {R : Type*} [CommRing R] [Algebra k R] [Algebra.FiniteType k R] (m : Ideal R) [m.IsMaximal]
    (C : Type*) [Field C] [Algebra k C] [Algebra R C] [IsScalarTower k R C]
    [Algebra (R ⧸ m) C] [IsScalarTower R (R ⧸ m) C] :
    Module.finrank (R ⧸ m) m.Cotangent ≤ Module.finrank C (Derivation k R C) := by
  let := Ideal.Quotient.field m
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
  have : Algebra.FormallyEtale k (R ⧸ m) := Algebra.FormallyEtale.of_isSeparable k _
  have hs : Function.Surjective (algebraMap R (R ⧸ m)) := Ideal.Quotient.mk_surjective
  have hinj := kerCotangentToTensor_injective k R (R ⧸ m) hs
  let e : m.Cotangent →ₗ[R] (R ⧸ m) ⊗[R] Ω[R⁄k] :=
    KaehlerDifferential.kerCotangentToTensor k R (R ⧸ m) ∘ₗ
      (Ideal.Cotangent.equivOfEq _ _ Ideal.mk_ker.symm).toLinearMap
  have he : Function.Injective (e.extendScalarsOfSurjective hs) :=
    hinj.comp (Ideal.Cotangent.equivOfEq _ _ Ideal.mk_ker.symm).injective
  rw [(derivationEquivDual k R C).finrank_eq, Subspace.dual_finrank_eq,
    ← (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ m) C C Ω[R⁄k]).finrank_eq,
    Module.finrank_baseChange]
  exact LinearMap.finrank_le_finrank_of_injective he
end GlobalTheory.SmoothTangent
