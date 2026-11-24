-- Prove2me | solution 1 for GlobalTheory.SS.DefectZero.exists_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:16:46.877844+00:00
-- url     : https://prove2.me/submissions/61d744ed-5c5b-462e-94cd-99643ff3509e

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.DefectZero
namespace GlobalTheory.SS.DefectZero
theorem _root_.solution (A K Q : Type) [CommRing A] [Field K] [Algebra A K] [AddCommGroup Q]
    [Module A Q] [Module.Finite A Q] [Subsingleton (K ⊗[A] Q)] (m : Q) :
    ∃ u : A, algebraMap A K u ≠ 0 ∧ u • m = 0 := by
  let p := RingHom.ker (algebraMap A K)
  have : p.IsPrime := RingHom.ker_isPrime _
  have hp : (⟨p, this⟩ : PrimeSpectrum A) ∉ Module.support A Q := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    intro hn
    let g : p.ResidueField →ₐ[A] K := Ideal.ResidueField.liftₐ p (Algebra.ofId A K) le_rfl
      fun y hy => isUnit_iff_ne_zero.mpr hy
    let := g.toRingHom.toAlgebra
    have : IsScalarTower A p.ResidueField K := .of_algebraMap_eq fun y => (g.commutes y).symm
    have h1 : Nontrivial (K ⊗[p.ResidueField] (p.ResidueField ⊗[A] Q)) :=
      Module.FaithfullyFlat.lTensor_nontrivial _ _ _
    rw [(AlgebraTensorModule.cancelBaseChange A p.ResidueField K K Q).nontrivial_congr] at h1
    exact not_subsingleton _ ‹_›
  exact Module.notMem_support_iff'.mp hp m
end GlobalTheory.SS.DefectZero
