-- Prove2me | solution 1 for OAI.DiamondDistortion.SegmentSystem.local_energy_le_of_functional_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:26:36.224864+00:00
-- url     : https://prove2.me/submissions/ac039724-ce99-4ded-8a06-2511d32c0832

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean:L817-L850
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.SegmentSystem.local_energy_le_of_functional_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

lemma coordinateTest_sum (K S : Finset ι) (a : T.Coordinates K) (hSK : S ⊆ K) :
    (∑ v ∈ S, T.coordinateTest K a v) =
      ∑ v : K, if v.val ∈ S then a v else 0 := by
  classical
  have hfilter : K.filter (· ∈ S) = S := by ext v; simp; exact fun h => hSK h
  calc
    _ = ∑ v ∈ K, if v ∈ S then T.coordinateTest K a v else 0 := by
      rw [← Finset.sum_filter, hfilter]
    _ = ∑ v : K, if v.val ∈ S then T.coordinateTest K a v.val else 0 :=
      (Finset.sum_coe_sort K _).symm
    _ = _ := by simp only [coordinateTest_mem]

lemma functional_pi_formula (K : Finset ι) (f : T.Coordinates K →L[ℝ] ℝ)
    (z : T.Coordinates K) : f z = ∑ v : K, z v * f (Pi.single v 1) := by
  classical
  have hz : z = ∑ v : K, z v • (Pi.single v 1 : T.Coordinates K) := by
    ext w
    simp [Pi.single_apply, Finset.sum_apply, mul_ite, Finset.sum_ite_eq]
  conv_lhs => rw [hz]
  simp only [map_sum, map_smul, smul_eq_mul]

variable {T}

variable (T)

lemma functional_localMap {K : Finset ι} (F : T.LocalFamily K)
    (f : T.Coordinates K →L[ℝ] ℝ) (a : EuclideanSpace ℝ (T.LocalIndex F)) :
    f (T.localMap F a) = ∑ S : T.LocalIndex F, a S *
      (∑ v ∈ S.val, T.coordinateTest K (fun w => f (Pi.single w 1)) v) := by
  classical
  rw [T.functional_pi_formula]
  simp only [localMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [T.coordinateTest_sum K S.val _ (T.localFamily_subset F S), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

lemma local_energy_le_of_functional_bound {K : Finset ι} (F : T.LocalFamily K)
    (f : T.Coordinates K →L[ℝ] ℝ) {u : ℝ} (hu : 0 ≤ u)
    (hf : ∀ a : EuclideanSpace ℝ (T.LocalIndex F), ‖a‖ ≤ 1 →
      f (T.localMap F a) ≤ u) :
    (∑ S : T.LocalIndex F, (∑ v ∈ S.val,
      T.coordinateTest K (fun w => f (Pi.single w 1)) v) ^ 2) ≤ u ^ 2 := by
  classical
  let b : EuclideanSpace ℝ (T.LocalIndex F) := WithLp.toLp 2
    (fun S => ∑ v ∈ S.val, T.coordinateTest K (fun w => f (Pi.single w 1)) v)
  have he : (∑ S : T.LocalIndex F, (∑ v ∈ S.val,
      T.coordinateTest K (fun w => f (Pi.single w 1)) v) ^ 2) = ‖b‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [b, Real.norm_eq_abs, sq_abs]
  rw [he]
  apply (sq_le_sq₀ (norm_nonneg _) hu).2
  by_cases hb : b = 0
  · simpa only [hb, norm_zero] using hu
  have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hbn : ‖‖b‖⁻¹ • b‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hn]
  have h := hf (‖b‖⁻¹ • b) hbn
  rw [T.functional_localMap] at h
  have hsum : (∑ S : T.LocalIndex F, (‖b‖⁻¹ • b) S *
      (∑ v ∈ S.val, T.coordinateTest K (fun w => f (Pi.single w 1)) v)) = ‖b‖ := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    change (∑ S, ‖b‖⁻¹ * b S * b S) = ‖b‖
    simp_rw [mul_assoc, ← sq]
    rw [← Finset.mul_sum]
    have hb2 : (∑ S, b S ^ 2) = ‖b‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
    rw [hb2, sq, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  rwa [hsum] at h

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.SegmentSystem.local_energy_le_of_functional_bound := @_root_.OAI.DiamondDistortion.SegmentSystem.local_energy_le_of_functional_bound
