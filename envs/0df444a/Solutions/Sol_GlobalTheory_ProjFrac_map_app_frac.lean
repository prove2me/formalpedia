-- Prove2me | solution 1 for GlobalTheory.ProjFrac.map_app_frac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:00.106411+00:00
-- url     : https://prove2.me/submissions/43664289-18b3-49b4-9f1f-f081d5f49a26

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
variable {B τ : Type} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ℕ → τ} [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
namespace GlobalTheory.ProjFrac
theorem _root_.solution (U : (Proj 𝒜).Opens) {d : ℕ} (a b : A) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (hU : U ≤ Proj.basicOpen 𝒜 b) :
    ((Proj.map φ hφ).app U).hom (frac 𝒜 U a b ha hb hU) =
      frac ℬ (Proj.map φ hφ ⁻¹ᵁ U) (φ a) (φ b) (φ.2 ha) (φ.2 hb) (fun _ hx => hU hx) := by
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp
end GlobalTheory.ProjFrac
