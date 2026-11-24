-- Prove2me | solution 1 for GlobalTheory.SplitWeil.FourierPi.map_eq_zero_of_translation_invariant_of_fibre_integral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:58:53.805979+00:00
-- url     : https://prove2.me/submissions/4a93e448-bb94-4339-b37e-8dbce8a4254e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsIntegralScaledBoxPiSupersetOfIsCompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetIntegralScaledBoxPiCosetRepsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SumIntegralScaledBoxPiCosetRepsShiftInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralBoxInvariantEqMeasureRealMulSumRepsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatFunctionalZeroOfFibreIntegralZero
import Theorems.Thm_GlobalTheory_SBConv_eventually_translate
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_subset
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isOpen_box
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_T_exists_finset_integralScaledBoxPi_coset_reps
import Theorems.Thm_GlobalTheory_T_exists_integralScaledBoxPi_superset_of_isCompact
import Theorems.Thm_GlobalTheory_T_integral_box_invariant_eq_measureReal_mul_sum_reps
import Theorems.Thm_GlobalTheory_T_sum_integralScaledBoxPi_coset_reps_shift_invariant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
namespace GlobalTheory.SplitWeil.FourierPi
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∀ Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x₀ x₁, ∫ a, Φ.1 (x₀, x₁, a) ∂(Measure.pi fun _ => ν) = 0) → l Φ = 0 := by
  intro k _ _ _ _ _ _ ν hν I₀ I₁ I₂ _ _ _ M _ _ l hl Φ hΦ
  haveI := secondCountable k
  haveI := hν

  have hU : {t : I₂ → k | ∀ g : (I₀ → k) × (I₁ → k) × (I₂ → k), Φ.1 (g + (0, 0, t)) = Φ.1 g} ∈
      𝓝 (0 : I₂ → k) := by
    have ht : Filter.Tendsto
        (fun t : I₂ → k => ((0, 0, -t) : (I₀ → k) × (I₁ → k) × (I₂ → k))) (𝓝 0) (𝓝 0) := by
      have hc : Continuous
          (fun t : I₂ → k => ((0, 0, -t) : (I₀ → k) × (I₁ → k) × (I₂ → k))) := by fun_prop
      have e : (((0 : I₀ → k), (0 : I₁ → k), -(0 : I₂ → k))) = 0 := by rw [neg_zero]; rfl
      have h := hc.tendsto 0
      rwa [e] at h
    filter_upwards [ht.eventually (GlobalTheory.SBConv.eventually_translate Φ.2)] with t h g
    have := h g
    simpa [sub_eq_add_neg] using this
  obtain ⟨r, hr⟩ := exists_box_subset hU
  have hK : IsCompact ((fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => x.2.2) '' tsupport Φ.1) :=
    Φ.2.2.isCompact.image (by fun_prop)
  obtain ⟨R, hrR, hKR⟩ := GlobalTheory.T.exists_integralScaledBoxPi_superset_of_isCompact k I₂ _ hK r
  obtain ⟨S, hSR, hS⟩ := GlobalTheory.T.exists_finset_integralScaledBoxPi_coset_reps k I₂ r R hrR
  have h0R : (0 : I₂ → k) ∈ box I₂ R := fun i _ => by simp [cball]
  have h0r : (0 : I₂ → k) ∈ box I₂ r := fun i _ => by simp [cball]
  have hSne : S.Nonempty := by
    obtain ⟨b, ⟨hb, -⟩, -⟩ := hS 0 h0R
    exact ⟨b, hb⟩

  let T : (I₂ → k) → SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b =>
    ⟨fun x => Φ.1 (x + (0, 0, b)), Φ.2.1.comp_continuous (continuous_add_right _),
      Φ.2.2.comp_homeomorph (Homeomorph.addRight _)⟩
  have hT : ∀ b, l (T b) = l Φ := fun b => hl b Φ (T b) fun _ => rfl

  have hvol : (Measure.pi fun _ : I₂ => ν).real (box I₂ r) ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos ((isOpen_box r).measure_ne_zero _ ⟨0, h0r⟩)
      (isCompact_box r).measure_lt_top.ne).ne'
  have hsum : ∑ b ∈ S, T b = 0 := by
    apply Subtype.ext
    funext x
    obtain ⟨x₀, x₁, a⟩ := x
    have hF1 : ∀ t ∈ box I₂ r, ∀ y, Φ.1 (x₀, x₁, y + t) = Φ.1 (x₀, x₁, y) := fun t ht y => by
      have := hr ht (x₀, x₁, y)
      simpa using this
    have hF2 : ∀ y ∉ box I₂ R, Φ.1 (x₀, x₁, y) = 0 := fun y hy =>
      image_eq_zero_of_notMem_tsupport fun hm => hy (hKR ⟨_, hm, rfl⟩)
    have hval : (∑ b ∈ S, T b).1 (x₀, x₁, a) = ∑ b ∈ S, Φ.1 (x₀, x₁, a + b) := by
      rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [T]
    rw [hval]
    by_cases ha : a ∈ box I₂ R
    · rw [GlobalTheory.T.sum_integralScaledBoxPi_coset_reps_shift_invariant k I₂ r R S hSR hS (fun y => Φ.1 (x₀, x₁, y)) hF1 a ha]
      have h := GlobalTheory.T.integral_box_invariant_eq_measureReal_mul_sum_reps k ν hν I₂ r R S hSR hS (fun y => Φ.1 (x₀, x₁, y)) hF1 hF2
      rw [hΦ x₀ x₁] at h
      have h' := (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast hvol)
      simpa using h'
    · refine Finset.sum_eq_zero fun b hb => hF2 _ fun hab => ha fun i _ => ?_
      have := add_mem_cball (hab i trivial) (neg_mem_cball (hSR b hb i trivial))
      simpa using this
  have hz : (S.card : ℂ) • l Φ = 0 := by
    have h1 : l (∑ b ∈ S, T b) = (S.card : ℂ) • l Φ := by
      rw [map_sum, Finset.sum_congr rfl fun b _ => hT b, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    rw [← h1, hsum, map_zero]
  exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hSne.card_ne_zero)
end GlobalTheory.SplitWeil.FourierPi
