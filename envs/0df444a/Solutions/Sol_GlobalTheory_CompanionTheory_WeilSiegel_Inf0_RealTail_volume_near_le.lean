-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail.volume_near_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:54:58.06905+00:00
-- url     : https://prove2.me/submissions/ffa23073-0713-4f21-a4a9-7675b463fc06

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxIntegralSmallBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
variable {P ι : Type} [Fintype P] [Fintype ι]
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
theorem _root_.solution {a : ℕ} {Q : (P → ι → ℝ) → (P → ℝ)} {C : ℝ≥0}
    (hbox : ∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U →
      (volume : Measure (P → ι → ℝ)) (Q ⁻¹' U ∩ boxR t) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (v : P) {U : Set (P → ℝ)} (hU : MeasurableSet U)
    (j : ℕ) :
    (volume : Measure (P → ι → ℝ)) ((Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∩ boxR (fun _ => (2 : ℝ) ^ j)) ≤
      ((C : ℝ≥0∞) * ENNReal.ofReal (δ ^ a) * volume U) *
        ENNReal.ofReal (((2 : ℝ) ^ j) ^ (a * Fintype.card P)) := by
  classical
  set t : P → ℝ := Function.update (fun _ : P => (2 : ℝ) ^ j) v δ with ht_def
  have htv : t v = δ := by simp [ht_def]
  have htw : ∀ w, w ≠ v → t w = (2 : ℝ) ^ j := fun w h => by simp [ht_def, h]
  have ht : ∀ w, 0 < t w := by
    intro w
    by_cases h : w = v
    · rw [h, htv]; exact hδ
    · rw [htw w h]; positivity
  have hsub : (Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∩ boxR (fun _ => (2 : ℝ) ^ j) ⊆
      Q ⁻¹' U ∩ boxR t := by
    rintro x ⟨⟨hxU, hxv⟩, hxb⟩
    refine ⟨hxU, fun w => ?_⟩
    by_cases h : w = v
    · rw [h, htv]; exact le_of_lt hxv
    · rw [htw w h]; exact hxb w
  have hprod : ∏ w, t w ^ a ≤ δ ^ a * ((2 : ℝ) ^ j) ^ (a * Fintype.card P) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), htv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h : ∀ w ∈ Finset.univ.erase v, t w ^ a = ((2 : ℝ) ^ j) ^ a := fun w hw => by
      rw [htw w (Finset.ne_of_mem_erase hw)]
    rw [Finset.prod_congr rfl h, Finset.prod_const, ← pow_mul]
    apply pow_le_pow_right₀ (one_le_pow₀ (by norm_num))
    apply Nat.mul_le_mul_left
    exact Finset.card_le_card (Finset.erase_subset _ _)
  calc (volume : Measure (P → ι → ℝ)) ((Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∩ boxR (fun _ => (2 : ℝ) ^ j))
      ≤ volume (Q ⁻¹' U ∩ boxR t) := measure_mono hsub
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U := hbox t ht U hU
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (δ ^ a * ((2 : ℝ) ^ j) ^ (a * Fintype.card P)) * volume U := by
        gcongr
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
