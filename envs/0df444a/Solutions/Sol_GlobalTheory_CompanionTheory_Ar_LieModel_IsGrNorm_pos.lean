-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.LieModel.IsGrNorm.pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:36:01.784017+00:00
-- url     : https://prove2.me/submissions/080eec5b-5c4c-4e45-a6a2-1b61bad63002

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_leadMinor_pos_of_posDef

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
variable {M : LieModel G ξ E} {L : LB G.left} {V : Lat ξ E} {r : ℕ} {b₀ : Fin r → E} {i : Fin r}
  {z : Spec (CommRingCat.of ℂ) ⟶ X} {t : Ω} {ν : ℝ}
namespace GlobalTheory.CompanionTheory.Ar
namespace LieModel.IsGrNorm
theorem _root_.solution (h : M.IsGrNorm L V b₀ i z t ν) : 0 < ν := by
  obtain ⟨_, _, Γ, -, -, -, -, hΓ, rfl⟩ := h
  exact Real.sqrt_pos.2 (div_pos (leadMinor_pos_of_posDef hΓ i.2) (leadMinor_pos_of_posDef hΓ i.2.le))
end LieModel.IsGrNorm
end GlobalTheory.CompanionTheory.Ar
