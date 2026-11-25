-- Prove2me | solution 1 for GlobalTheory.NormCurve.dimensionLEOne_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:58:54.923066+00:00
-- url     : https://prove2.me/submissions/d4f7d6b2-db8b-43d4-91b8-4970b0439207

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsPrimeLeNotMemRingKrullDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteIntegralClosureOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsProperCurveThroughPoint
import Theorems.Thm_ReciprocityTheory_CA_exists_dim_trdeg_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.NormCurve
namespace GlobalTheory.NormCurve
theorem _root_.solution {k A R : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [Algebra k R] (g : A →ₐ[k] R)
    (hg : Function.Injective g) (h : Algebra.trdeg k R ≤ 1) : Ring.DimensionLEOne A := by
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
  have h1 := (trdeg_le_of_injective g hg).trans h
  rw [hs2] at h1
  have h2 : s ≤ 1 := by exact_mod_cast h1
  have h3 : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff, hs1]
    exact_mod_cast h2
  exact ⟨fun {p} hp hp' => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h3 p hp hp'⟩
end GlobalTheory.NormCurve
