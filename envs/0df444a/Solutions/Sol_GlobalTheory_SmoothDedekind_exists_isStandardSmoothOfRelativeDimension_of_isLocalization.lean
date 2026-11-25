-- Prove2me | solution 1 for GlobalTheory.SmoothDedekind.exists_isStandardSmoothOfRelativeDimension_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:14:43.143137+00:00
-- url     : https://prove2.me/submissions/202de867-2a9d-4004-8278-98e2c7698e73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe

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
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SmoothDedekind
open GlobalTheory.SmoothTangent IsLocalRing
namespace GlobalTheory.SmoothDedekind
theorem _root_.solution (R : Type*) [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] (q : Ideal A)
    [q.IsPrime] (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L q] [Algebra R L]
    [IsScalarTower R A L] [Algebra.FormallySmooth R L] {d : ℕ}
    (hd : Module.finrank L Ω[L⁄R] = d) :
    ∃ f ∉ q, Algebra.IsStandardSmoothOfRelativeDimension d R (Localization.Away f) := by
  let e : L ≃ₐ[A] Localization.AtPrime q := IsLocalization.algEquiv q.primeCompl _ _
  have : Algebra.IsSmoothAt R q := Algebra.FormallySmooth.of_equiv (e.restrictScalars R)
  refine exists_isStandardSmoothOfRelativeDimension_of_isSmoothAt R q ?_
  let : Algebra L (Localization.AtPrime q) := e.toRingHom.toAlgebra
  have : IsScalarTower R L (Localization.AtPrime q) :=
    .of_algebraMap_eq fun r ↦ ((e.restrictScalars R).commutes r).symm
  have : Algebra.FormallyEtale L (Localization.AtPrime q) :=
    .of_equiv (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (R := L) fun _ ↦ rfl)
  have : Algebra.EssFiniteType A L := .of_isLocalization L q.primeCompl
  have : Algebra.EssFiniteType R L := .comp R A L
  have := IsLocalization.AtPrime.isLocalRing L q
  have : Module.Free L Ω[L⁄R] := Module.free_of_flat_of_isLocalRing
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R L
    (Localization.AtPrime q)).finrank_eq, Module.finrank_baseChange, hd]
end GlobalTheory.SmoothDedekind
