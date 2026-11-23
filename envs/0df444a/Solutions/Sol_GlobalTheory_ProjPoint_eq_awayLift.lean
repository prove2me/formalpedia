-- Prove2me | solution 1 for GlobalTheory.ProjPoint.eq_awayLift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:00.484225+00:00
-- url     : https://prove2.me/submissions/68b5a919-ddb4-4fb8-bf51-33856880f9e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
import Theorems.Thm_GlobalTheory_ProjPoint_awayLift_mk_mul

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
theorem _root_.solution (φ : A →+* B) {f : A} (hf : IsUnit (φ f)) {d : ℕ} (hd : f ∈ 𝒜 d)
    (g : Away 𝒜 f →+* B)
    (hg : ∀ n a ha, g (Away.mk 𝒜 hd n a ha) * φ f ^ n = φ a) : g = awayLift 𝒜 φ f hf := by
  ext x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hd x
  apply (hf.pow n).mul_right_cancel
  rw [hg, awayLift_mk_mul]
end GlobalTheory.ProjPoint
