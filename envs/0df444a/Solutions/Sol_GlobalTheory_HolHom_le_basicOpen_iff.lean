-- Prove2me | solution 1 for GlobalTheory.HolHom.le_basicOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:12.870322+00:00
-- url     : https://prove2.me/submissions/5d886eed-68d5-4242-812a-d23a248472be

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
theorem _root_.solution (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0 := by
  have h1 := Scheme.basicOpen_appLE x ⊤ U h f
  rw [top_inf_eq] at h1
  rw [← h1, valAt'_eq_valR, valR_eq _ _ h, top_le_iff, ← isUnit_iff_ne_zero]
  have h2 : IsUnit (evalHom x U h f) ↔ IsUnit ((x.appLE U ⊤ h).hom f) :=
    MulEquiv.isUnit_map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  rw [h2]
  exact ⟨fun H => (Sp ℂ).toRingedSpace.isUnit_of_isUnit_germ _ _ fun p hp =>
    ((Sp ℂ).mem_basicOpen _ p hp).1 (H.ge hp), fun H => (Sp ℂ).basicOpen_of_isUnit H⟩
end GlobalTheory.HolHom
