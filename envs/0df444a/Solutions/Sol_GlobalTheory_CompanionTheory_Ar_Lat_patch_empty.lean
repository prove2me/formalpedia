-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Lat.patch_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:43:20.70457+00:00
-- url     : https://prove2.me/submissions/4f870e8c-ddaf-4d8a-824a-fc9a4fc21aab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_MemEigSpOfMemHtDual

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
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
namespace GlobalTheory.CompanionTheory.Ar
namespace Lat
theorem _root_.solution (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) : Lat.patch ∅ L₀ Lp = L₀ := by
  funext q; simp [Lat.patch]
end Lat
end GlobalTheory.CompanionTheory.Ar
