-- Prove2me | solution 1 for GlobalTheory.ProjFrac.mem_basicOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:01.316807+00:00
-- url     : https://prove2.me/submissions/5e651562-6dbf-4386-98a0-28d49f2e950d

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
theorem _root_.solution {U : (Proj 𝒜).Opens} (s : Γ(Proj 𝒜, U)) (x : Proj 𝒜) (hx : x ∈ U) :
    x ∈ (Proj 𝒜).basicOpen s ↔ IsUnit (ev 𝒜 U x hx s) := by
  rw [Scheme.mem_basicOpen _ _ _ hx]
  refine Iff.trans ?_ (HomogeneousLocalization.isUnit_iff_isUnit_val 𝒜 x.asHomogeneousIdeal.toIdeal
    (s.1 ⟨x, hx⟩)).symm
  rw [← Proj.stalkIso'_germ 𝒜 U x hx s]
  exact (isUnit_map_iff (Proj.stalkIso' 𝒜 x) _).symm
end GlobalTheory.ProjFrac
