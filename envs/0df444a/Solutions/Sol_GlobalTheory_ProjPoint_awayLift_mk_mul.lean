-- Prove2me | solution 1 for GlobalTheory.ProjPoint.awayLift_mk_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:54.737571+00:00
-- url     : https://prove2.me/submissions/5574486e-6aff-44b5-8517-02e628dc7506

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.ProjPoint
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]
namespace GlobalTheory.ProjPoint
theorem _root_.solution (φ : A →+* B) {f : A} (hf : IsUnit (φ f)) {d : ℕ} (hd : f ∈ 𝒜 d) (n : ℕ)
    (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayLift 𝒜 φ f hf (Away.mk 𝒜 hd n a ha) * φ f ^ n = φ a := by
  have h1 : φ f ^ n = IsLocalization.Away.lift (S := Localization.Away f) f hf
      (algebraMap A _ (f ^ n)) := by
    rw [IsLocalization.Away.lift_eq, map_pow]
  rw [h1, awayLift, RingHom.comp_apply, ← map_mul, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.mk'_spec (Localization.Away f) a ⟨f ^ n, _⟩, IsLocalization.Away.lift_eq]
end GlobalTheory.ProjPoint
