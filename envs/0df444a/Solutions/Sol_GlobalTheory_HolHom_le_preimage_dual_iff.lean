-- Prove2me | solution 1 for GlobalTheory.HolHom.le_preimage_dual_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:26.263193+00:00
-- url     : https://prove2.me/submissions/3824c6bf-4f30-4361-bdf5-662e525e43ec

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
theorem _root_.solution {v : Sp (DualNumber ℂ) ⟶ X} {x : Sp ℂ ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) (U : X.Opens) : ⊤ ≤ v ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  subst h
  refine ⟨fun hx p _ => hx (x := spMap _ p) trivial, fun hx => ?_⟩
  have hl : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  refine (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of (DualNumber ℂ)) v ?_).ge
  have := hx (x := IsLocalRing.closedPoint ℂ) trivial
  rw [← Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)]
  exact this
end GlobalTheory.HolHom
