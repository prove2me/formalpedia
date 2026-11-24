-- Prove2me | solution 1 for GlobalTheory.NormSign.exists_normSign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:37:39.254512+00:00
-- url     : https://prove2.me/submissions/bf52e51b-a7cf-40c3-aa8b-a2408a5075a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMixedSpaceNormSignCharacter
import Theorems.Thm_GlobalTheory_NormSign_snorm_mul
import Theorems.Thm_GlobalTheory_NormSign_snorm_smul
import Theorems.Thm_GlobalTheory_NormSign_continuous_snorm
import Theorems.Thm_GlobalTheory_NormSign_abs_snorm
import Theorems.Thm_GlobalTheory_NormSign_snorm_mixedEmbedding
import Theorems.Thm_GlobalTheory_NormSign_sgn_mul
import Theorems.Thm_GlobalTheory_NormSign_norm_sgn
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.NormSign
open NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.NormSign
theorem _root_.solution (K : Type) [Field K] [NumberField K] (ε : ℂ) (hε : ε * ε = 1) :
    ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧
      (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) ∧
      ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧
      (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧
      ∀ β : 𝓞 K, β ≠ 0 → φ (mixedEmbedding K β) = if 0 < Algebra.norm ℤ β then 1 else ε := by
  have hne : ∀ x : mixedSpace K, mixedEmbedding.norm x ≠ 0 → snorm x ≠ 0 := fun x hx => by
    rwa [← abs_snorm, abs_ne_zero] at hx
  refine ⟨fun x => sgn ε (snorm x), fun x y => ?_, fun t x ht => ?_, fun x hx => ?_,
    fun x hx => norm_sgn hε (hne x hx), fun β hβ => ?_⟩
  · simp only [snorm_mul, sgn_mul hε]
  · obtain ⟨c, hc, h⟩ := snorm_smul t ht x
    simp only [h, sgn_mul hε]
    simp [sgn, hc]
  · refine ContDiffAt.contDiffWithinAt ?_
    refine (contDiffAt_const (c := sgn ε (snorm x))).congr_of_eventuallyEq ?_
    rcases lt_or_gt_of_ne (hne x hx) with h | h
    · filter_upwards [continuous_snorm.continuousAt.eventually (gt_mem_nhds h)] with y hy
      simp [sgn, h, hy, h.not_gt, hy.not_gt]
    · filter_upwards [continuous_snorm.continuousAt.eventually (lt_mem_nhds h)] with y hy
      simp [sgn, h, hy]
  · have h0 : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
    simp only [snorm_mixedEmbedding, ← Algebra.coe_norm_int, Rat.cast_intCast, sgn,
      Int.cast_pos, Int.cast_lt_zero]
    rcases lt_or_gt_of_ne h0 with h | h
    · simp [h, h.not_gt]
    · simp [h]
end GlobalTheory.NormSign
