-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CxVal.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:22.967857+00:00
-- url     : https://prove2.me/submissions/1c3325f4-59f3-49a8-aec9-b4448369f1a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CxVal_isUnit

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
variable {z : Spec (CommRingCat.of ℂ) ⟶ X}
open GlobalTheory.CompanionTheory.Ar.CxVal
namespace GlobalTheory.CompanionTheory.Ar.CxVal
theorem _root_.solution {a : Ω} {r s : ℂ} (h : ValAt ξ z a r) (h' : ValAt ξ z a s) : r = s := by
  obtain ⟨h, x, hx, rfl⟩ := h
  obtain ⟨_, y, hy, rfl⟩ := h'
  by_contra hne
  have hu : IsUnit (x - y) := isUnit _ fun h0 =>
    hne (sub_eq_zero.1 ((map_sub (Scheme.stalkClosedPointTo z).hom x y).symm.trans h0))
  have := hu.map (genMap ξ ⟨centre z, h⟩)
  rw [map_sub, hx, hy, sub_self] at this
  exact not_isUnit_zero this
end GlobalTheory.CompanionTheory.Ar.CxVal
