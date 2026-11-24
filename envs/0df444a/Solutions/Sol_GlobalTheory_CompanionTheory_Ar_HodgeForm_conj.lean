-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HodgeForm.conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:36:00.874925+00:00
-- url     : https://prove2.me/submissions/b1da2d8b-a7bb-4ebb-9657-65ae99422390

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_conj_hermForm

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
namespace HodgeForm
theorem _root_.solution (h : HodgeForm G L z v w c) : HodgeForm G L z w v ((starRingEnd ℂ) c) := by
  obtain ⟨hL, hv, hw, A, _, φ, g, u, Hm, χ, v', w', a, b, h1, h2, h3, h4, h5, h6, rfl⟩ := h
  refine ⟨hL, hw, hv, A, inferInstance, φ, g, u, Hm, χ, w', v', b, a, h1, h2, h4, h3, h6, h5, ?_⟩
  rw [map_mul, Complex.conj_ofReal, conj_hermForm h2.1]
end HodgeForm
end GlobalTheory.CompanionTheory.Ar
