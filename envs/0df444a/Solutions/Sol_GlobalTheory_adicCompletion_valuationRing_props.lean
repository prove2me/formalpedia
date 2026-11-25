-- Prove2me | solution 1 for GlobalTheory.adicCompletion_valuationRing_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:47:42.72246+00:00
-- url     : https://prove2.me/submissions/d031cac4-5055-4d69-98ec-7d7a9385ebb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDoma
import Theorems.Thm_P2M_GlobalTheory_ValCompletion_eval__algebraMap_9fca5057166d
import Theorems.Thm_GlobalTheory_ValCompletion_algebraMap_pow_ne_zero
import Theorems.Thm_GlobalTheory_ValCompletion_exists_eq_mul_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory.ValCompletion
namespace GlobalTheory
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : V), x ≠ 0 → ¬ IsUnit x → IsDomain (AdicCompletion (Ideal.span {x}) V) ∧ PreValuationRing (AdicCompletion (Ideal.span {x}) V) ∧ algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 ∧ ¬ IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ∧ IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x}) (AdicCompletion (Ideal.span {x}) V) := by
  intro V _ _ _ x hx0 hxu
  have hne : algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 := by
    simpa using algebraMap_pow_ne_zero hx0 hxu 1
  have hnt : Nontrivial (AdicCompletion (Ideal.span {x}) V) := ⟨⟨_, _, hne⟩⟩
  have hdom : IsDomain (AdicCompletion (Ideal.span {x}) V) := by
    refine @NoZeroDivisors.to_isDomain _ _ hnt ⟨fun {y z} hyz => ?_⟩
    by_contra hc
    push_neg at hc
    obtain ⟨a, n, ⟨c, hc1⟩, u, rfl⟩ := exists_eq_mul_unit hx0 hxu y hc.1
    obtain ⟨b, m, ⟨d, hd1⟩, w, rfl⟩ := exists_eq_mul_unit hx0 hxu z hc.2
    apply algebraMap_pow_ne_zero hx0 hxu (n + m)
    have h1 : algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b = 0 := by
      have h2 : algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b * ((u : AdicCompletion (Ideal.span {x}) V) * w) = 0 := by
        rw [← hyz]; ring
      exact (Units.mul_left_eq_zero (u * w)).1 (by rw [Units.val_mul]; exact h2)
    rw [pow_add, ← map_pow, ← map_pow, hc1, hd1]
    simp only [map_mul]
    calc _ = (algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) b) * (algebraMap V (AdicCompletion (Ideal.span {x}) V) c * algebraMap V (AdicCompletion (Ideal.span {x}) V) d) := by ring
      _ = 0 := by rw [h1, zero_mul]
  refine ⟨hdom, ⟨fun y z => ?_⟩, hne, ?_, ?_⟩
  · by_cases hy : y = 0
    · exact ⟨0, Or.inr (by rw [hy, mul_zero])⟩
    by_cases hz : z = 0
    · exact ⟨0, Or.inl (by rw [hz, mul_zero])⟩
    obtain ⟨a, n, -, u, rfl⟩ := exists_eq_mul_unit hx0 hxu y hy
    obtain ⟨b, m, -, w, rfl⟩ := exists_eq_mul_unit hx0 hxu z hz
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a b
    · refine ⟨algebraMap V (AdicCompletion (Ideal.span {x}) V) c * ((u⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V) * w, Or.inl ?_⟩
      rw [← hc, map_mul]
      calc _ = algebraMap V (AdicCompletion (Ideal.span {x}) V) a * algebraMap V (AdicCompletion (Ideal.span {x}) V) c * w * ((u : AdicCompletion (Ideal.span {x}) V) * ((u⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V)) := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
    · refine ⟨algebraMap V (AdicCompletion (Ideal.span {x}) V) c * ((w⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V) * u, Or.inr ?_⟩
      rw [← hc, map_mul]
      calc _ = algebraMap V (AdicCompletion (Ideal.span {x}) V) b * algebraMap V (AdicCompletion (Ideal.span {x}) V) c * u * ((w : AdicCompletion (Ideal.span {x}) V) * ((w⁻¹ : (AdicCompletion (Ideal.span {x}) V)ˣ) : AdicCompletion (Ideal.span {x}) V)) := by ring
        _ = _ := by rw [Units.mul_inv, mul_one]
  · rintro ⟨v, hv⟩
    apply hxu
    obtain ⟨e, he⟩ := isUnit_iff_exists_inv.1 (⟨v, hv⟩ : IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x))
    have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {x}) 1) he
    have hx1 : Ideal.Quotient.mk (Ideal.span {x} ^ 1) x = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]; exact Ideal.mem_span_singleton_self x
    rw [map_mul, evalₐ_algebraMap, hx1, zero_mul, map_one, eq_comm, ← map_one (Ideal.Quotient.mk _),
      Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton] at h2
    exact isUnit_of_dvd_one h2
  · have e : (Ideal.span {x}).map (algebraMap V (AdicCompletion (Ideal.span {x}) V)) = Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [← e, IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete (Submodule.fg_span_singleton x)
end GlobalTheory
