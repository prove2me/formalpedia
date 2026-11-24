-- Prove2me | solution 1 for GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:04:01.522688+00:00
-- url     : https://prove2.me/submissions/11552953-8080-4512-b373-14276c73d09e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsValuationSubringComplexOverPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMModel
namespace GlobalTheory.CMModel
theorem _root_.solution :
    ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)),
      ∃ V : ValuationSubring ℂ, ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F := by
  intro F _ w
  set R := w.valuationSubringAtPrime F with hR
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing
    ((algebraMap F ℂ).comp R.subtype)
  refine ⟨V, fun x => ⟨fun hx => ?_, fun hx => hV ⟨x, hx⟩⟩⟩
  by_contra hxR
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxR R.zero_mem
  have hinv : x⁻¹ ∈ R := (R.mem_or_inv_mem x).resolve_left hxR
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hu : IsUnit ((((algebraMap F ℂ).comp R.subtype).codRestrict V.toSubring hV) ⟨x⁻¹, hinv⟩) := by
    refine IsUnit.of_mul_eq_one ⟨(x : ℂ), hx⟩ ?_
    apply Subtype.ext
    change ((x⁻¹ : F) : ℂ) * (x : ℂ) = 1
    rw [IntermediateField.coe_inv, inv_mul_cancel₀ hx0']
  have hu' : IsUnit (⟨x⁻¹, hinv⟩ : R) := hloc.map_nonunit _ hu
  obtain ⟨y, hy⟩ := hu'.exists_right_inv
  have hy' : x⁻¹ * (y : F) = 1 := congrArg Subtype.val hy
  have : x = (y : F) := by
    have h := congrArg (x * ·) hy'
    simp only [← mul_assoc, mul_inv_cancel₀ hx0, one_mul, mul_one] at h
    exact h.symm
  exact hxR (this ▸ y.2)
end GlobalTheory.CMModel
