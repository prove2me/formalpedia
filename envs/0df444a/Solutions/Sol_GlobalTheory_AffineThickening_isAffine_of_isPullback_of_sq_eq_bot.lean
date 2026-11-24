-- Prove2me | solution 1 for GlobalTheory.AffineThickening.isAffine_of_isPullback_of_sq_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:39.851021+00:00
-- url     : https://prove2.me/submissions/14d5c220-0062-4a3c-9778-ec20ec34a859

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_isAffine_of_mul_eq_zero
import Theorems.Thm_GlobalTheory_AffineThickening_exists_ker_app_eq_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}
namespace GlobalTheory.AffineThickening
theorem _root_.solution {A C : CommRingCat.{u}} {β : A ⟶ C}
    (hβ : Function.Surjective β) (hsq : RingHom.ker β.hom ^ 2 = ⊥) {f : Y ⟶ Spec A} {i : Z ⟶ Y}
    {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β)) [IsAffine Z] : IsAffine Y := by
  have h1 := IsClosedImmersion.spec_of_surjective β hβ
  have h2 : Surjective (Spec.map β) := ⟨fun x ↦ by
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker β.hom : Set A) := fun a ha ↦
      x.isPrime.mem_of_pow_mem 2 (by
        have := Ideal.pow_mem_pow ha 2
        rw [hsq, Ideal.mem_bot] at this
        rw [this]
        exact zero_mem _)
    rw [← range_comap_of_surjective _ β.hom hβ] at hx
    exact hx⟩
  have : IsClosedImmersion i := MorphismProperty.of_isPullback h.flip h1
  have : Surjective i := MorphismProperty.of_isPullback h.flip h2
  refine isAffine_of_mul_eq_zero i fun U hU a b ha hb ↦ ?_
  obtain ⟨α, hα⟩ := exists_ker_app_eq_map hβ h hU
  have h0 : RingHom.ker (i.app U).hom ^ 2 = ⊥ := by
    rw [hα, ← Ideal.map_pow, hsq, Ideal.map_bot]
  rw [← Ideal.mem_bot, ← h0, pow_two]
  exact Ideal.mul_mem_mul ha hb
end GlobalTheory.AffineThickening
