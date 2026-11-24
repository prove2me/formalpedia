-- Prove2me | solution 1 for GlobalTheory.Hk.RayForm.unit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:48:48.900804+00:00
-- url     : https://prove2.me/submissions/c93e22ff-8e7a-46e7-a63d-4193a079c580

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PlaneLatticeShortBasisOfBoundPowTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryForm
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_normSq_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayForm
open GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.RayForm
theorem _root_.solution [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) {M : ℕ} (hM : 3 ≤ M)
    (u : (𝓞 K)ˣ) (hu : (u : 𝓞 K) - 1 ∈ Ideal.span {(M : 𝓞 K)}) : u = 1 := by
  let φ : K →+* ℂ := (Classical.arbitrary (InfinitePlace K)).embedding
  by_contra hne
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hu
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hne (Units.val_eq_one.mp (by linear_combination -ht))
  have hu1 : ‖φ ((u : 𝓞 K) : K)‖ ^ 2 = 1 := by
    rw [normSq_eq h2 φ (u : 𝓞 K), Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top]
    simp
  have ht1 : 1 ≤ ‖φ ((t : 𝓞 K) : K)‖ ^ 2 := by
    rw [normSq_eq h2 φ t]
    have : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ht0
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have he : φ ((u : 𝓞 K) : K) - 1 = φ ((t : 𝓞 K) : K) * M := by
    have := congrArg (fun z : 𝓞 K => φ (z : K)) ht
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    simp only [RingOfIntegers.coe_eq_algebraMap]
    rw [← this]
  have hle : ‖φ ((t : 𝓞 K) : K)‖ * M ≤ 2 := by
    have h1 : ‖φ ((u : 𝓞 K) : K)‖ = 1 := by
      have := norm_nonneg (φ ((u : 𝓞 K) : K))
      nlinarith
    calc ‖φ ((t : 𝓞 K) : K)‖ * M = ‖φ ((u : 𝓞 K) : K) - 1‖ := by
          rw [he, norm_mul, Complex.norm_natCast]
      _ ≤ ‖φ ((u : 𝓞 K) : K)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, norm_one]; norm_num
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hn := norm_nonneg (φ ((t : 𝓞 K) : K))
  nlinarith
end GlobalTheory.Hk.RayForm
