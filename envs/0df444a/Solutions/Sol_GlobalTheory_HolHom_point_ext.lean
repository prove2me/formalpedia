-- Prove2me | solution 1 for GlobalTheory.HolHom.point_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:45.139112+00:00
-- url     : https://prove2.me/submissions/b820700a-21ec-4dc2-b4d8-89d6f3c9430c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_AffinePointValues_specMap_appLE_fromSpec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {A : Type} [CommRing A] {X : Scheme.{0}}
namespace GlobalTheory.HolHom
theorem _root_.solution {x x' : Sp A ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (hx : ⊤ ≤ x ⁻¹ᵁ U) (hx' : ⊤ ≤ x' ⁻¹ᵁ U)
    (h : ∀ f, valR x U f = valR x' U f) : x = x' := by
  rw [← AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of A) x hx,
    ← AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of A) x' hx']
  congr 2
  ext1
  refine RingHom.ext fun f => ?_
  have := h f
  rwa [valR_eq _ _ hx, valR_eq _ _ hx'] at this
end GlobalTheory.HolHom
