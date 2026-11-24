-- Prove2me | solution 1 for GlobalTheory.QuotLocInt.integrableOn_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:49.133631+00:00
-- url     : https://prove2.me/submissions/5ed50e4a-b32e-4629-8943-92f24b18a56d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FundamentalDomainL2Bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Set
open scoped ENNReal
namespace GlobalTheory.QuotLocInt
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}
open MeasureTheory Set in
open scoped ENNReal in
private theorem lintegral_compact_le_mul_lintegral_fundamentalDomain (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (C : Set G) (hC : IsCompact C) (n : ℝ)
    (hn : ∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n)
    (g : G → ℝ≥0∞) (hg : Measurable g) (hinv : ∀ (γ : Γ) x, g (γ • x) = g x) :
    ∫⁻ x in C, g x ∂μ ≤ ENNReal.ofReal n * ∫⁻ x in 𝓕, g x ∂μ := by
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hcount : ∀ x : G, ∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ • x) ≤ ENNReal.ofReal n := by
    intro x
    have hS : ∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ • x) =
        ∑' γ : Γ, {γ : Γ | (γ : G) * x ∈ C}.indicator 1 γ := rfl
    rw [hS, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    obtain ⟨hfin, hle⟩ := hn x
    have hE : ({γ : Γ | (γ : G) * x ∈ C}).encard ≤
        (({γ : G | γ ∈ Γ ∧ γ * x ∈ C}.ncard : ℕ) : ℕ∞) := by
      rw [hfin.cast_ncard_eq, ← Subtype.val_injective.encard_image]
      apply Set.encard_le_encard
      rintro _ ⟨γ, hγ, rfl⟩
      exact ⟨γ.2, hγ⟩
    calc ((({γ : Γ | (γ : G) * x ∈ C}).encard : ℕ∞) : ℝ≥0∞)
        ≤ (((({γ : G | γ ∈ Γ ∧ γ * x ∈ C}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞) := ENat.toENNReal_le.mpr hE
      _ = (({γ : G | γ ∈ Γ ∧ γ * x ∈ C}.ncard : ℕ) : ℝ≥0∞) := by simp
      _ ≤ ENNReal.ofReal n := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hle
  calc ∫⁻ x in C, g x ∂μ = ∫⁻ x, C.indicator g x ∂μ := (lintegral_indicator hCm _).symm
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, C.indicator g (γ⁻¹ • x) ∂μ := h𝓕.lintegral_eq_tsum' _
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, C.indicator (1 : G → ℝ≥0∞) (γ⁻¹ • x) * g x ∂μ := by
        congr 1; funext γ; congr 1; funext x
        by_cases hx : γ⁻¹ • x ∈ C <;> simp [hx, hinv]
    _ = ∫⁻ x in 𝓕, ∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ⁻¹ • x) * g x ∂μ := by
        rw [lintegral_tsum]
        intro γ
        exact (((measurable_one.indicator hCm).comp (measurable_const_smul _)).mul hg).aemeasurable
    _ = ∫⁻ x in 𝓕, (∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ • x)) * g x ∂μ := by
        congr 1; funext x
        rw [ENNReal.tsum_mul_right]
        congr 1
        exact (Equiv.inv Γ).tsum_eq (fun γ => C.indicator (1 : G → ℝ≥0∞) (γ • x))
    _ ≤ ∫⁻ x in 𝓕, ENNReal.ofReal n * g x ∂μ :=
        lintegral_mono fun x => by gcongr ?_ * _; exact hcount x
    _ = _ := lintegral_const_mul _ hg
end GlobalTheory.QuotLocInt
end

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
open GlobalTheory GlobalTheory.QuotLocInt
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}
open MeasureTheory Set
open scoped ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}
namespace GlobalTheory.QuotLocInt
namespace _root_.GlobalTheory.QuotLocInt
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ]
    (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ C : Set G, IsCompact C → ∀ n : ℝ,
    (∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n) →
    ∃ M : ℝ, ∀ F : Lp ℂ 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))),
      IntegrableOn (fun x => F (Quotient.mk _ x)) C μ ∧
        ∫ x in C, ‖F (Quotient.mk _ x)‖ ∂μ ≤ M * ‖F‖ := by
  intro G _ _ _ _ _ _ μ _ Γ _ 𝓕 h𝓕 C hC n hn
  refine ⟨(ENNReal.ofReal n ^ (1/2 : ℝ) * μ C ^ (1/2 : ℝ)).toReal, fun F => ?_⟩
  have hπ : Measurable (Quotient.mk (QuotientGroup.rightRel Γ)) := fun _ hs => hs
  have hF := Lp.stronglyMeasurable F
  have hf : StronglyMeasurable fun x => F (Quotient.mk (QuotientGroup.rightRel Γ) x) :=
    hF.comp_measurable hπ
  have hL2 : eLpNorm (fun x => F (Quotient.mk (QuotientGroup.rightRel Γ) x)) 2 (μ.restrict C) ≤
      ENNReal.ofReal n ^ (1/2 : ℝ) *
        eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc ∫⁻ x in C, ‖F (Quotient.mk (QuotientGroup.rightRel Γ) x)‖ₑ ^ (2 : ℝ) ∂μ
        ≤ ENNReal.ofReal n * ∫⁻ x in 𝓕, ‖F (Quotient.mk (QuotientGroup.rightRel Γ) x)‖ₑ ^ (2 : ℝ) ∂μ :=
          lintegral_compact_le_mul_lintegral_fundamentalDomain G μ Γ 𝓕 h𝓕 C hC n hn _
            ((hF.measurable.enorm.pow_const _).comp hπ) fun γ x => by
              rw [show Quotient.mk (QuotientGroup.rightRel Γ) (γ • x) = Quotient.mk _ x from
                Quotient.sound (QuotientGroup.rightRel_apply.2 (by simp [Subgroup.smul_def, mul_inv_rev]))]
      _ = _ := by rw [lintegral_map (hF.measurable.enorm.pow_const _) hπ]
  have hL1 : eLpNorm (fun x => F (Quotient.mk (QuotientGroup.rightRel Γ) x)) 1 (μ.restrict C) ≤
      ENNReal.ofReal n ^ (1/2 : ℝ) * μ C ^ (1/2 : ℝ) *
        eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) := by
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hf.aestronglyMeasurable).trans ?_
    rw [Measure.restrict_apply_univ]
    simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat]
    rw [show (1 / 1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
    calc _ ≤ ENNReal.ofReal n ^ (1/2 : ℝ) *
          eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) *
            μ C ^ (1/2 : ℝ) := by gcongr
      _ = _ := by ring
  have hfin : ENNReal.ofReal n ^ (1/2 : ℝ) * μ C ^ (1/2 : ℝ) *
      eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) < ⊤ := by
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) (Lp.eLpNorm_lt_top F)
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.measure_lt_top.ne
  refine ⟨memLp_one_iff_integrable.1 ⟨hf.aestronglyMeasurable, hL1.trans_lt hfin⟩, ?_⟩
  rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable, ← eLpNorm_one_eq_lintegral_enorm,
    Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono hfin.ne hL1
end _root_.GlobalTheory.QuotLocInt
end GlobalTheory.QuotLocInt
