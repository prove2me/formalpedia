-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_iff_hodgeForm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:37:09.389277+00:00
-- url     : https://prove2.me/submissions/867e1cd5-2e13-428d-97e7-825ff2c555da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_hodgeInnerProduct_iff_hodgeForm
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HodgeForm_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HodgeIP_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable {L : LB G.left} {z : Spec (CommRingCat.of ℂ) ⟶ X} {v w : epsAt z ⟶ G} {c : ℂ}
namespace GlobalTheory.CompanionTheory.Ar
theorem _root_.solution : HodgeIP G L z v w c ↔ HodgeForm G L z v w ((starRingEnd ℂ) c) :=
  ⟨fun h => (hodgeInnerProduct_iff_hodgeForm.1 h).conj, fun h => hodgeInnerProduct_iff_hodgeForm.2 (by simpa using h.conj)⟩
end GlobalTheory.CompanionTheory.Ar
