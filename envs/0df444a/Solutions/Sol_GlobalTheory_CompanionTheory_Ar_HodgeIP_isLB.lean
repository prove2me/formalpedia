-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HodgeIP.isLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:33:39.759003+00:00
-- url     : https://prove2.me/submissions/f7b7b93d-b163-4e89-9a64-41f41575e1a0

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
namespace HodgeIP
theorem _root_.solution (h : HodgeIP G L z v w c) : L.IsLB := h.1
end HodgeIP
end GlobalTheory.CompanionTheory.Ar
