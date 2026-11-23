-- Prove2me | solution 1 for GlobalTheory.HolHom.valR_spMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:27.074099+00:00
-- url     : https://prove2.me/submissions/5e44176c-5376-4097-aeb3-5c44f17b1682

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
theorem _root_.solution {A' : Type} [CommRing A'] (ρ : A →+* A') (x : Sp A ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR (spMap ρ ≫ x) U f = ρ (valR x U f) := by
  have hx' : ⊤ ≤ (spMap ρ ≫ x) ⁻¹ᵁ U := fun p _ => hx (x := spMap ρ p) trivial
  rw [valR_eq _ _ hx, valR_eq _ _ hx', evalHom, evalHom,
    ← Scheme.Hom.appLE_comp_appLE (spMap ρ) x U ⊤ ⊤ hx le_rfl]
  have h3 : (spMap ρ).appLE ⊤ ⊤ le_rfl = (spMap ρ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [h3, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl
end GlobalTheory.HolHom
