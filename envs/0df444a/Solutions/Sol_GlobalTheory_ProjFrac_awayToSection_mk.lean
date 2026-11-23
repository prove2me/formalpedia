-- Prove2me | solution 1 for GlobalTheory.ProjFrac.awayToSection_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:06:28.110397+00:00
-- url     : https://prove2.me/submissions/56a5893f-2c42-4b9b-8ebf-12149f0aeca3

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
theorem _root_.solution {f a : A} {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (ha : a ∈ 𝒜 (n • d)) :
    (Proj.awayToSection 𝒜 f).hom (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
      frac 𝒜 (Proj.basicOpen 𝒜 f) a (f ^ n) ha (SetLike.pow_mem_graded n hf)
        (fun x hx h => hx (x.isPrime.mem_of_pow_mem n h)) := rfl
end GlobalTheory.ProjFrac
