-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.isFinite_fromQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:05.920993+00:00
-- url     : https://prove2.me/submissions/9c5bbc4f-abff-4298-9fde-a27339aa3408

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Theorems.Thm_GlobalTheory_AffineQuotient_of_charts
import Theorems.Thm_GlobalTheory_AffineQuotient_isPullback_fromQuot
import Theorems.Thm_GlobalTheory_AffineQuotient_exists_fromSpec_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineQuotient
open Scheme.AffineZariskiSite
variable {W X Y : Scheme.{0}}
variable (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (p : W ⟶ X) (hp : p ≫ f = g)
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.AffineQuotient
theorem _root_.solution [IsFinite f] [IsLocallyNoetherian Y] :
    IsFinite (fromQuot f g a ha p hp) := by
  refine of_charts _ @IsFinite _ _ _ _ _ (fun y ↦ ?_) (isPullback_fromQuot f g a ha p hp)
    fun U ↦ ?_
  · exact exists_fromSpec_eq (𝟙 Y) y
  · rw [IsFinite.SpecMap_iff]
    have h1 : (f.app U.1).hom.Finite := f.finite_app U.1 U.2
    have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
    let φ : Γ(Y, U.1) →+* invariants f g a ha p hp U.1 :=
      (f.app U.1).hom.codRestrict (invariants f g a ha p hp U.1)
        (app_mem_invariants f g a ha p hp)
    change φ.Finite
    algebraize [(f.app U.1).hom, φ]
    have : IsScalarTower Γ(Y, U.1) (invariants f g a ha p hp U.1) Γ(X, f ⁻¹ᵁ U.1) :=
      .of_algebraMap_eq' rfl
    exact Module.Finite.of_injective
      (IsScalarTower.toAlgHom Γ(Y, U.1) (invariants f g a ha p hp U.1)
        Γ(X, f ⁻¹ᵁ U.1)).toLinearMap Subtype.val_injective
end GlobalTheory.AffineQuotient
