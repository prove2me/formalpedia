-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Descent.adaptive_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:02:00.804469+00:00
-- url     : https://prove2.me/submissions/6c5d53ad-ec25-4d65-9488-ba68f1f24b64

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Descent.lean:L20-L87
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Descent.adaptive_step. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension

-- ---- from OAI.Geometry.Arnold.Descent ----
namespace OAI

universe uE uX

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology

open Set
open scoped ContDiff

namespace ArnoldCounterexample.Descent

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A second-derivative bound uniformly converts an infinitesimal descent
`-S` into a strict smooth discrete descent using the step `c*S`.
It works even when `S` vanishes to arbitrarily high order. -/
theorem adaptive_step {K : Set E} (hK : IsCompact K)
    (Φ : ℝ × E → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (S : E → ℝ) (hS : Continuous S)
    (hSnon : ∀ z ∈ K, 0 ≤ S z)
    (hd0 : ∀ z ∈ K, fderiv ℝ Φ (0, z) (1, 0) = -S z) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K,
      0 ≤ c * S z ∧ c * S z ≤ 1 ∧
      Φ (c * S z, z) ≤ Φ (0, z) ∧
      (S z ≠ 0 → Φ (c * S z, z) < Φ (0, z)) := by
  let P : ℝ × E → ℝ := fun p ↦ fderiv ℝ Φ p (1, 0)
  let Q : ℝ × E → ℝ := fun p ↦ fderiv ℝ P p (1, 0)
  have hP : ContDiff ℝ ∞ P := (hΦ.fderiv_right (by simp)).clm_apply contDiff_const
  have hQ : ContDiff ℝ ∞ Q := (hP.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hS.continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hQ.continuous.continuousOn : ContinuousOn Q (Icc (0 : ℝ) 1 ×ˢ K))
  let R := |B| + |M| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let c := (2 * R)⁻¹
  have hc : 0 < c := inv_pos.mpr (mul_pos (by norm_num) hR)
  have hcR : c * R = 1 / 2 := by dsimp [c]; field_simp
  have hBlt : B < R := by dsimp [R]; linarith [le_abs_self B, abs_nonneg M]
  have hMlt : M < R := by dsimp [R]; linarith [le_abs_self M, abs_nonneg B]
  refine ⟨c, hc, fun z hz ↦ ?_⟩
  have hs : 0 ≤ S z := hSnon z hz
  have hsB : S z ≤ B := (le_abs_self (S z)).trans (hB z hz)
  have ht0 : 0 ≤ c * S z := mul_nonneg hc.le hs
  have ht1 : c * S z ≤ 1 := by
    have htR := mul_le_mul_of_nonneg_left (hsB.trans hBlt.le) hc.le
    rw [hcR] at htR
    linarith
  have hp (t : ℝ) : HasDerivAt (fun s ↦ Φ (s, z)) (P (t, z)) t :=
    (hΦ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
  have hq (t : ℝ) : HasDerivAt (fun s ↦ P (s, z)) (Q (t, z)) t :=
    (hP.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
  have hvariation (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |P (t, z) - P (0, z)| ≤ M * t := by
    simpa using norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s (_ : s ∈ Icc (0 : ℝ) 1) ↦ (hq s).hasDerivWithinAt)
      (fun s (hs : s ∈ Ico (0 : ℝ) 1) ↦ hM (s, z) ⟨⟨hs.1, hs.2.le⟩, hz⟩) t ht
  have hstrict (hne : S z ≠ 0) : Φ (c * S z, z) < Φ (0, z) := by
    have hsp : 0 < S z := lt_of_le_of_ne hs hne.symm
    have hneg (t : ℝ) (ht : t ∈ interior (Icc 0 (c * S z))) :
        deriv (fun s ↦ Φ (s, z)) t < 0 := by
      have ht' : t ∈ Icc 0 (c * S z) := interior_subset ht
      have hv := hvariation t ⟨ht'.1, ht'.2.trans ht1⟩
      have hbound : M * t ≤ R * (c * S z) := by
        exact (mul_le_mul_of_nonneg_right hMlt.le ht'.1).trans
          (mul_le_mul_of_nonneg_left ht'.2 hR.le)
      have hrc : R * (c * S z) = S z / 2 := by nlinarith [hcR]
      have hd : P (0, z) = -S z := hd0 z hz
      rw [(hp t).deriv]
      have hu := (abs_le.mp hv).2
      rw [hd] at hu
      rw [hrc] at hbound
      linarith
    exact strictAntiOn_of_deriv_neg (convex_Icc 0 (c * S z))
      (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn hneg
      (left_mem_Icc.mpr ht0) (right_mem_Icc.mpr ht0) (mul_pos hc hsp)
  refine ⟨ht0, ht1, ?_, hstrict⟩
  by_cases hzero : S z = 0
  · simp [hzero]
  · exact (hstrict hzero).le

end ArnoldCounterexample.Descent

open Set Function

namespace ArnoldCounterexample.Descent

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]

end ArnoldCounterexample.Descent

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Descent
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Set
open scoped ContDiff


theorem solution.{uE} : type_of% @_root_.OAI.ArnoldCounterexample.Descent.adaptive_step.{uE} := @_root_.OAI.ArnoldCounterexample.Descent.adaptive_step.{uE}
