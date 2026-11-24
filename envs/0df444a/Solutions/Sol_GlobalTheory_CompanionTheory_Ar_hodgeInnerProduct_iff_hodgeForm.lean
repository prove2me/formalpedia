-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_iff_hodgeForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:30.613083+00:00
-- url     : https://prove2.me/submissions/966a8fd2-9eff-402f-ad63-4ccf09cd5448

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj

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
theorem _root_.solution : HodgeIP G L z v w c ↔ HodgeForm G L z w v c := by
  constructor
  · rintro ⟨hL, hv, hw, A, _, φ, g, u, Hm, χ, v', w', a, b, h1, h2, h3, h4, h5, h6, rfl⟩
    exact ⟨hL, hw, hv, A, inferInstance, φ, g, u, Hm, χ, w', v', b, a, h1, h2, h4, h3, h6, h5, rfl⟩
  · rintro ⟨hL, hv, hw, A, _, φ, g, u, Hm, χ, v', w', a, b, h1, h2, h3, h4, h5, h6, rfl⟩
    exact ⟨hL, hw, hv, A, inferInstance, φ, g, u, Hm, χ, w', v', b, a, h1, h2, h4, h3, h6, h5, rfl⟩
end GlobalTheory.CompanionTheory.Ar
