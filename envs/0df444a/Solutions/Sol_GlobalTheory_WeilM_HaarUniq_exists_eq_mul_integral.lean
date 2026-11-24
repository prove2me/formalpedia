-- Prove2me | solution 1 for GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:05:50.549803+00:00
-- url     : https://prove2.me/submissions/1f4be8ff-a9be-4741-a708-2ce8fdc26ec9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_compact_openAddSubgroup
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_indicator_mem
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_invariant
import Theorems.Thm_GlobalTheory_WeilM_HaarUniq_exists_decomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Filter Topology
namespace GlobalTheory.WeilM.HaarUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
open MeasureTheory Filter Topology in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] in
private theorem exists_coeff_form_and_integral [IsTopologicalAddGroup V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (m : (V → ℂ) →ₗ[ℂ] ℂ)
    (hm : ∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, ∀ a : V,
      m (fun x => φ (x + a)) = m φ)
    (H : OpenAddSubgroup V) (hH : IsCompact (H : Set V)) {φ : V → ℂ} (hc : HasCompactSupport φ)
    (hinv : ∀ k ∈ H, ∀ x, φ (x + k) = φ x) :
    ∃ A : ℂ, m φ = A * m (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) ∧
      ∫ x, φ x ∂μ = A * (μ.real (H : Set V) : ℂ) := by
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_decomp H hc hinv
  have hmemH := _root_.GlobalTheory.WeilM.HaarUniq.indicator_mem H hH
  have hint : Integrable (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) μ :=
    (integrable_indicator_iff H.isOpen.measurableSet).2 (integrableOn_const hH.measure_lt_top.ne)
  refine ⟨∑ q ∈ S, φ q.out, ?_, ?_⟩
  · calc m φ = m (∑ q ∈ S, φ q.out •
          (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) (x + -q.out))) := congrArg m hS
      _ = ∑ q ∈ S, φ q.out * m (Set.indicator (H : Set V) (fun _ => (1 : ℂ))) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_smul, smul_eq_mul, hm _ hmemH]
      _ = _ := by rw [Finset.sum_mul]
  · calc ∫ x, φ x ∂μ = ∫ x, (∑ q ∈ S, φ q.out •
          (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) (x + -q.out))) x ∂μ := by
            rw [← hS]
      _ = ∑ q ∈ S, φ q.out * (μ.real (H : Set V) : ℂ) := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [integral_finset_sum]
          · refine Finset.sum_congr rfl fun q _ => ?_
            rw [integral_const_mul,
              integral_add_right_eq_self (fun x => Set.indicator (H : Set V) (fun _ => (1 : ℂ)) x),
              integral_indicator_const _ H.isOpen.measurableSet]
            simp
          · intro q _
            exact (hint.comp_add_right _).const_mul _
      _ = _ := by rw [Finset.sum_mul]
end GlobalTheory.WeilM.HaarUniq
end

set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.WeilM GlobalTheory.WeilM.HaarUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
open MeasureTheory Filter Topology
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
namespace GlobalTheory.WeilM.HaarUniq
namespace _root_.GlobalTheory.WeilM.HaarUniq
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V]
    [TopologicalSpace V] [NonarchimedeanAddGroup V]
    [LocallyCompactSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure]
    (m : (V → ℂ) →ₗ[ℂ] ℂ), (∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, ∀ a : V,
      m (fun x => φ (x + a)) = m φ) →
    ∃ c : ℂ, ∀ φ ∈ _root_.GlobalTheory.WeilM.SB V, m φ = c * ∫ x, φ x ∂μ := by
  intro V _ _ _ _ _ _ _ μ _ m hm
  obtain ⟨K₀, hK₀⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_compact_openAddSubgroup (V := V)
  have hpos : ∀ H : OpenAddSubgroup V, IsCompact (H : Set V) → μ.real (H : Set V) ≠ 0 := by
    intro H hH
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨(H.isOpen.measure_pos μ ⟨0, H.zero_mem⟩).ne', hH.measure_lt_top.ne⟩
  refine ⟨m (Set.indicator (K₀ : Set V) (fun _ => (1 : ℂ))) / (μ.real (K₀ : Set V) : ℂ),
    fun φ hφ => ?_⟩
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := by
    simpa [_root_.GlobalTheory.WeilM.SB] using hφ
  obtain ⟨K₁, hK₁⟩ := _root_.GlobalTheory.WeilM.HaarUniq.exists_invariant hφ
  set H : OpenAddSubgroup V := K₀ ⊓ K₁
  have hH : IsCompact (H : Set V) := by
    refine hK₀.of_isClosed_subset H.isClosed ?_
    rw [OpenAddSubgroup.coe_inf]
    exact Set.inter_subset_left
  have hHK₁ : ∀ k ∈ H, k ∈ K₁ := fun k hk => by
    have : k ∈ (H : Set V) := hk
    rw [OpenAddSubgroup.coe_inf] at this
    exact this.2
  have hHK₀ : ∀ k ∈ H, k ∈ K₀ := fun k hk => by
    have : k ∈ (H : Set V) := hk
    rw [OpenAddSubgroup.coe_inf] at this
    exact this.1
  obtain ⟨A, hA₁, hA₂⟩ := exists_coeff_form_and_integral μ m hm H hH hφ'.2
    (fun k hk x => hK₁ k (hHK₁ k hk) x)
  obtain ⟨B, hB₁, hB₂⟩ := exists_coeff_form_and_integral μ m hm H hH
    (φ := Set.indicator (K₀ : Set V) (fun _ => (1 : ℂ)))
    (HasCompactSupport.intro hK₀ fun x hx => Set.indicator_of_notMem hx _)
    (fun k hk x => by
      by_cases hx : x ∈ K₀ <;>
        simp [Set.indicator_apply, hx, add_mem_cancel_right (hHK₀ k hk)])
  rw [integral_indicator_const _ K₀.isOpen.measurableSet, Complex.real_smul, mul_one] at hB₂
  have hH0 : (μ.real (H : Set V) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos H hH)
  have hK0 : (μ.real (K₀ : Set V) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos K₀ hK₀)
  rw [hA₁, hA₂, hB₁, hB₂]
  have hB0 : B ≠ 0 := by
    rintro rfl
    apply hK0
    rw [hB₂, zero_mul]
  field_simp
end _root_.GlobalTheory.WeilM.HaarUniq
end GlobalTheory.WeilM.HaarUniq
