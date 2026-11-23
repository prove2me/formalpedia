-- Prove2me | solution 1 for GlobalTheory.HolHom.valR_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:34.237822+00:00
-- url     : https://prove2.me/submissions/6fe22825-279e-4002-b06f-d535950ca465

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined

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
theorem _root_.solution (x : Sp A ⟶ X) {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    valR x V ((X.presheaf.map (homOfLE h).op).hom f) = valR x U f := by
  have hx' : ⊤ ≤ x ⁻¹ᵁ U := le_trans hx (x.preimage_mono h)
  rw [valR_eq _ _ hx, valR_eq _ _ hx', evalHom, evalHom, ← Scheme.Hom.map_appLE x hx (homOfLE h).op]
  rfl
end GlobalTheory.HolHom
