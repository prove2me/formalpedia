-- Prove2me | solution 1 for GlobalTheory.hom_ext_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:58.628295+00:00
-- url     : https://prove2.me/submissions/3d99d25b-e9cb-4a34-b7be-ebf31db13bfb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Theorems.Thm_GlobalTheory_hom_ext_of_fromSpecStalk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A : Type u} [CommRing A] {Y : Scheme.{u}}
    {f g : Spec (.of A) ⟶ Y}
    (h : ∀ (B : Type u) [CommRing B] [IsLocalRing B] (φ : A →+* B),
      Spec.map (CommRingCat.ofHom φ) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ g) : f = g := by
  apply hom_ext_of_fromSpecStalk
  intro x
  rw [Spec.fromSpecStalk_eq']
  exact h ((Spec (.of A)).presheaf.stalk x) (StructureSheaf.toStalk _ _).hom
end GlobalTheory
