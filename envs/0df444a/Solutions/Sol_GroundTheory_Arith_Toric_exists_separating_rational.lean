-- Prove2me | solution 1 for GroundTheory.Arith.Toric.exists_separating_rational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:37.420424+00:00
-- url     : https://prove2.me/submissions/2ca79d08-887c-45ea-8247-bca12206e41a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
import Theorems.Thm_GroundTheory_Arith_Toric_toRealDual_injective
import Theorems.Thm_GroundTheory_Arith_Toric_mem_dualMonoid
import Theorems.Thm_GroundTheory_Arith_Toric_nonneg_of_mem_hull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
variable {N : Type*} [AddCommGroup N]
variable [Module.Free ℤ N] [Module.Finite ℤ N]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {σ σ' : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) (hσ' : IsRationalPolyhedral (toRealSpan N) σ')
    (h : (σ ⊓ σ').IsFaceOf σ) (h' : (σ ⊓ σ').IsFaceOf σ') :
    ∃ u : Dual ℤ N, u ∈ dualMonoid σ ∧ -u ∈ dualMonoid σ' ∧
      exposedFace σ (toRealDual N u) = σ ⊓ σ' ∧ exposedFace σ' (toRealDual N u) = σ ⊓ σ' := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  obtain ⟨S', rfl⟩ := hσ'
  obtain ⟨TM, hTM⟩ := (show IsRationalPolyhedral (toRealSpan N)
    (hull ℝ (toRealSpan N '' ↑(S ∪ S'.image Neg.neg))) from ⟨_, rfl⟩).dual
  rw [dual_hull] at hTM
  set SR := S.image (toRealSpan N) with hSR
  set SR' := S'.image (toRealSpan N) with hSR'
  have e1 : hull ℝ (toRealSpan N '' (S : Set N)) = hull ℝ (SR : Set (ℝ ⊗[ℤ] N)) := by
    rw [hSR, Finset.coe_image]
  have e2 : hull ℝ (toRealSpan N '' (S' : Set N)) = hull ℝ (SR' : Set (ℝ ⊗[ℤ] N)) := by
    rw [hSR', Finset.coe_image]
  rw [e1, e2] at h h' ⊢
  set TR := TM.image (toRealDual N) with hTR
  have hT : ∀ u : Dual ℝ (ℝ ⊗[ℤ] N), u ∈ hull ℝ (TR : Set (Dual ℝ (ℝ ⊗[ℤ] N))) ↔
      (∀ x ∈ hull ℝ (SR : Set (ℝ ⊗[ℤ] N)), 0 ≤ u x) ∧
        (∀ x ∈ hull ℝ (SR' : Set (ℝ ⊗[ℤ] N)), u x ≤ 0) := by
    intro u
    rw [hTR, Finset.coe_image, hTM]
    constructor
    · intro hu
      refine ⟨fun x hx => nonneg_of_mem_hull (fun y hy => ?_) hx, fun x hx => ?_⟩
      · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
        simpa using hu ⟨n, by simp [hn], rfl⟩
      · have := nonneg_of_mem_hull (f := -u) (s := (SR' : Set (ℝ ⊗[ℤ] N))) (fun y hy => by
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
          simpa using hu ⟨-n, by simp [hn], rfl⟩) hx
        simpa using this
    · rintro ⟨h1, h2⟩ y ⟨n, hn, rfl⟩
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Finset.mem_coe,
        Set.mem_image] at hn
      rcases hn with hn | ⟨n', hn', rfl⟩
      · simpa using h1 _ (subset_hull (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn)))
      · simpa using h2 _ (subset_hull (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn')))
  obtain ⟨hu1, hu2, hE1, hE2⟩ := separation_of_generators SR SR' TR hT h h'
  have hsum : (∑ t ∈ TR, t) = toRealDual N (∑ t ∈ TM, t) := by
    rw [hTR, Finset.sum_image (fun x _ y _ hxy => toRealDual_injective hxy), map_sum]
  rw [hsum] at hu1 hu2 hE1 hE2
  exact ⟨∑ t ∈ TM, t, mem_dualMonoid.2 hu1, mem_dualMonoid.2 fun x hx => by simpa using hu2 x hx,
    hE1, hE2⟩
end GroundTheory.Arith.Toric
