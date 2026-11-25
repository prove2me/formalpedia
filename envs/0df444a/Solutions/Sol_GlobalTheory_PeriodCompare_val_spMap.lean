-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.val_spMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:04:35.094809+00:00
-- url     : https://prove2.me/submissions/027b21e9-7d64-44c0-8dc5-5d27da1de0bc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
namespace GlobalTheory.PeriodCompare
theorem _root_.solution {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) (h : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) (f : Γ(Sp A, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (((spMap φ).appLE ⊤ ⊤ h).hom f) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom f) := by
  have h1 : (spMap φ).appLE ⊤ ⊤ h = (spMap φ).appTop := Scheme.Hom.appLE_eq_app _
  rw [h1]
  exact congrArg (fun k => k.hom f) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
end GlobalTheory.PeriodCompare
