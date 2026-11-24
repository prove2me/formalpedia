-- Prove2me | solution 1 for GlobalTheory.TwoVarValRing.exists_local_ring_second_variable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:08:25.589463+00:00
-- url     : https://prove2.me/submissions/0d12ac04-9483-4cf5-825b-3366c10de2c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalRingSecondVariable
import Theorems.Thm_GlobalTheory_TwoVarValRing_not_X_one_dvd_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TwoVarValRing
namespace GlobalTheory.TwoVarValRing
theorem _root_.solution : ∀ (k : Type) [Field k] (σ₀ σ₁ : FractionRing (PowerSeries k) →ₐ[k] FractionRing (MvPowerSeries (Fin 2) k)), (∀ x : PowerSeries k, σ₀ (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _ (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k))) → (∀ x : PowerSeries k, σ₁ (algebraMap _ _ x) = algebraMap (MvPowerSeries (Fin 2) k) _ (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))) → ∃ L : Subalgebra k (FractionRing (MvPowerSeries (Fin 2) k)), IsLocalRing L ∧ (∀ (x : FractionRing (MvPowerSeries (Fin 2) k)) (u v : MvPowerSeries (Fin 2) k), ¬ MvPowerSeries.X 1 ∣ v → x * algebraMap (MvPowerSeries (Fin 2) k) _ v = algebraMap (MvPowerSeries (Fin 2) k) _ u → x ∈ L) ∧ (∀ x, σ₀ x ∈ L) ∧ ∀ x, σ₁ x ∈ L → x ∈ Set.range (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) := by
  intro k _ σ₀ σ₁ h₀ h₁
  refine ⟨locSecondVar k, inferInstance, fun x u v hv h => ⟨u, v, hv, h⟩, fun x => ?_, fun x hx => ?_⟩
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := PowerSeries k) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    refine ⟨a.subst (MvPowerSeries.X 0), b.subst (MvPowerSeries.X 0),
      not_X_one_dvd_subst k b hb0, ?_⟩
    rw [← h₀, ← h₀, ← map_mul, div_mul_cancel₀]
    rwa [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  · rcases ValuationRing.isInteger_or_isInteger (PowerSeries k) x with h | ⟨c, hc⟩
    · exact h
    · by_cases hx0 : x = 0
      · exact ⟨0, by rw [hx0, map_zero]⟩
      by_cases hcu : IsUnit c
      · obtain ⟨d, hd⟩ := hcu.exists_right_inv
        refine ⟨d, ?_⟩
        have : x⁻¹ * algebraMap (PowerSeries k) _ d = 1 := by
          rw [← hc, ← map_mul, hd, map_one]
        rw [← mul_one x, ← this, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
      · exfalso
        have hs : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) :=
          PowerSeries.HasSubst.X 1
        have hX : PowerSeries.X ∣ c := by
          rw [PowerSeries.X_dvd_iff]
          by_contra h0
          exact hcu (PowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit h0))
        obtain ⟨c', rfl⟩ := hX
        obtain ⟨u, v, hv, h⟩ := hx
        apply hv
        have h2 : v = (PowerSeries.X * c').subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) * u := by
          apply IsFractionRing.injective (MvPowerSeries (Fin 2) k)
            (FractionRing (MvPowerSeries (Fin 2) k))
          rw [map_mul, ← h₁, hc, ← h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hx0, map_one, one_mul]
        rw [h2, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, mul_assoc]
        exact dvd_mul_right _ _
end GlobalTheory.TwoVarValRing
