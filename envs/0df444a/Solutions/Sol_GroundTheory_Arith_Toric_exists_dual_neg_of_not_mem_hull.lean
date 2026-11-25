-- Prove2me | solution 1 for GroundTheory.Arith.Toric.exists_dual_neg_of_not_mem_hull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:54:25.712737+00:00
-- url     : https://prove2.me/submissions/4cc392fd-b8e8-46ae-bb72-b68a1a4f6129

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Theorems.Thm_GroundTheory_Arith_Toric_mem_hull_insert
import Theorems.Thm_GroundTheory_Arith_Toric_exists_of_mem_hull_image
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
open Module PointedCone
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {ι : Type*} (s : Finset ι) (v : ι → V) {x : V}
    (hx : x ∉ hull 𝕜 (v '' s)) : ∃ f : Dual 𝕜 V, (∀ i ∈ s, 0 ≤ f (v i)) ∧ f x < 0 := by
  classical
  induction s using Finset.induction_on generalizing v x with
  | empty =>
    have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero 𝕜 hx0
    rcases hf.lt_or_gt with h | h
    · exact ⟨f, by simp, h⟩
    · exact ⟨-f, by simp, by simpa using h⟩
  | insert a s ha ih =>
    have hsub : hull 𝕜 (v '' s) ≤ hull 𝕜 (v '' ↑(insert a s)) :=
      Submodule.span_mono (Set.image_mono (by simp))
    obtain ⟨f, hf, hfx⟩ := ih v (fun h => hx (hsub h))
    by_cases hfa : 0 ≤ f (v a)
    · refine ⟨f, fun i hi => ?_, hfx⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      exacts [hfa, hf i hi]
    replace hfa := not_le.1 hfa
    let φ : V →ₗ[𝕜] V := LinearMap.id - (f (v a))⁻¹ • f.smulRight (v a)
    have hφ : ∀ y, φ y = y - (f y / f (v a)) • v a := by
      intro y
      simp [φ, div_eq_mul_inv, mul_comm, smul_smul]
    have hφa : φ (v a) = 0 := by rw [hφ, div_self hfa.ne, one_smul, sub_self]
    have hnot : φ x ∉ hull 𝕜 ((φ ∘ v) '' s) := by
      intro h
      rw [Set.image_comp] at h
      obtain ⟨z, hz, hzx⟩ := exists_of_mem_hull_image φ h
      apply hx
      have hfz : 0 ≤ f z := nonneg_of_mem_hull (by rintro _ ⟨i, hi, rfl⟩; exact hf i hi) hz
      rw [Finset.coe_insert, Set.image_insert_eq, mem_hull_insert]
      refine ⟨(f x - f z) / f (v a), div_nonneg_of_nonpos (by linarith) hfa.le, z, hz, ?_⟩
      rw [hφ, hφ] at hzx
      rw [sub_div, sub_smul]
      linear_combination (norm := module) -hzx
    obtain ⟨g, hg, hgx⟩ := ih (φ ∘ v) hnot
    refine ⟨g ∘ₗ φ, fun i hi => ?_, hgx⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · simp [hφa]
    · exact hg i hi
end GroundTheory.Arith.Toric
