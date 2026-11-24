-- Prove2me | solution 1 for GlobalTheory.SS.exists_smooth_of_defect_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:38.280804+00:00
-- url     : https://prove2.me/submissions/a907f02d-6c55-44de-bc7f-abd63c00131a

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero
import Theorems.Thm_GlobalTheory_SS_DefectZero_isSmoothAt_of_torsion_free

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open TensorProduct KaehlerDifferential
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Unr π R' → Defect a π 0 → ∃ f : B, IsUnit (a f) ∧ Algebra.Smooth R (Localization.Away f) := by
  intro R _ _ _ π hπ B _ _ _ _ hsm R' _ _ a hun hdef
  obtain ⟨_, _, hπ'⟩ := hun
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R B›
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) B :=
    .of_algebraMap_eq fun r => (φ.commutes r).symm
  let := a.toRingHom.toAlgebra
  let q := RingHom.ker (algebraMap B R')
  have : q.IsPrime := RingHom.ker_isPrime _
  have : Algebra.IsSmoothAt R q :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hsm
      (show (⟨q, this⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen (algebraMap R B π) from
        fun h => hπ'.ne_zero ((a.commutes π).symm.trans h))
  have := DefectZero.isSmoothAt_of_torsion_free R (MvPolynomial (Fin n) R) B R' hφ q _ rfl rfl
    fun w hw => by simpa using hdef w hw
  obtain ⟨f, hf, h⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R
    ((IsLocalRing.maximalIdeal R').comap (algebraMap B R'))
  exact ⟨f, IsLocalRing.notMem_maximalIdeal.mp hf, h⟩
end GlobalTheory.SS
