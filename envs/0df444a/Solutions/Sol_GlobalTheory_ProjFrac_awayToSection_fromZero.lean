-- Prove2me | solution 1 for GlobalTheory.ProjFrac.awayToSection_fromZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:11:00.143349+00:00
-- url     : https://prove2.me/submissions/ac3ca8b6-e7aa-4283-ae25-d6f25580884a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
open GlobalTheory GlobalTheory.ProjFrac
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {𝒜}
namespace GlobalTheory.ProjFrac
theorem _root_.solution (f : A) (a : 𝒜 0) :
    (Proj.awayToSection 𝒜 f).hom (HomogeneousLocalization.fromZeroRingHom 𝒜 _ a) =
      frac 𝒜 (Proj.basicOpen 𝒜 f) a 1 a.2 (SetLike.one_mem_graded 𝒜) (by simp) := rfl
end GlobalTheory.ProjFrac
