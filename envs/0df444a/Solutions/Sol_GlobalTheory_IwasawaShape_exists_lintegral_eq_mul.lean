-- Prove2me | solution 1 for GlobalTheory.IwasawaShape.exists_lintegral_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:38.996122+00:00
-- url     : https://prove2.me/submissions/1397aaa9-8691-48f7-841f-4341834eb6f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMapMulRightEqSmul
import Theorems.Thm_GlobalTheory_IwasawaShape_lintegral_mul_left_of_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.IwasawaShape
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
namespace GlobalTheory.IwasawaShape
theorem _root_.solution (μ ρ κ : Measure G) [SigmaFinite μ] [SFinite ρ] [IsProbabilityMeasure κ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (hμ : μ ≠ 0) (P K : Set G)
    (hKl : ∀ k ∈ K, κ.map (fun g => k * g) = κ) (hPl : ∀ p ∈ P, ρ.map (fun g => p * g) = ρ)
    (hPr : ∀ p ∈ P, ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ρ.map (fun g => g * p) = D • ρ)
    (hdec : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) (T : Set G) (hT : MeasurableSet T)
    (hTK : ∀ k ∈ K, ∀ g, k⁻¹ * g ∈ T ↔ g ∈ T) (hT0 : ρ T ≠ 0) (hT1 : ρ T ≠ ⊤) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂μ = c * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ := by
  classical
  have hind : Measurable (T.indicator (1 : G → ENNReal)) := measurable_one.indicator hT
  have ind_ne_top : ∀ x, T.indicator (1 : G → ENNReal) x ≠ ⊤ := fun x => by
    by_cases hx : x ∈ T <;> simp [Set.indicator_apply, hx]
  have hLm : ∀ φ : G → ENNReal, Measurable φ →
      Measurable fun h => T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ :=
    fun φ hφ => (hind.comp measurable_inv).mul
      ((hφ.comp (by fun_prop : Measurable fun y : (G × G) × G => y.1.2 * y.1.1 * y.2)).lintegral_prod_right').lintegral_prod_right'

  have key : ∀ h : G, ∃ D : ENNReal, D ≠ 0 ∧ D ≠ ⊤ ∧ ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ = D * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ := by
    intro h
    obtain ⟨p0, hp0, k0, hk0, rfl⟩ := hdec h
    obtain ⟨D, hD0, hDt, hD⟩ := hPr p0 hp0
    refine ⟨D, hD0, hDt, fun φ hφ => ?_⟩
    have hF : Measurable fun x => ∫⁻ k, φ (x * k) ∂κ := (hφ.comp measurable_mul).lintegral_prod_right'
    have e1 : ∀ q, ∫⁻ k, φ (q * (p0 * k0) * k) ∂κ = ∫⁻ k, φ (q * p0 * k) ∂κ := by
      intro q
      have := lintegral_mul_left_of_map (hKl k0 hk0) (fun k => φ (q * p0 * k))
        (hφ.comp (measurable_const_mul _))
      simpa only [mul_assoc] using this
    simp_rw [e1]
    have := lintegral_map (μ := ρ) hF (measurable_mul_const p0)
    rw [hD, lintegral_smul_measure, smul_eq_mul] at this
    exact this.symm

  have mix : ∀ φ : G → ENNReal, Measurable φ →
      ρ T * ∫⁻ g, φ g ∂μ = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ ∂μ := by
    intro φ hφ
    have s1 : ∫⁻ g, φ g ∂μ = ∫⁻ g, ∫⁻ k, φ (g * k) ∂κ ∂μ := by
      rw [lintegral_lintegral_swap (f := fun g k => φ (g * k)) (by exact (hφ.comp measurable_mul).aemeasurable)]
      simp_rw [lintegral_mul_right_eq_self]
      rw [lintegral_const, measure_univ, mul_one]
    have s2 : ∀ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) ∂ρ = ρ T := by
      intro g
      obtain ⟨p0, hp0, k0, hk0, rfl⟩ := hdec g
      have e : ∀ q, T.indicator (1 : G → ENNReal) ((p0 * k0)⁻¹ * q) = T.indicator 1 (p0⁻¹ * q) := by
        intro q
        have hm : (p0 * k0)⁻¹ * q ∈ T ↔ p0⁻¹ * q ∈ T := by
          rw [mul_inv_rev, mul_assoc]; exact hTK k0 hk0 _
        simp only [Set.indicator_apply, hm, Pi.one_apply]
      simp_rw [e]
      have := lintegral_mul_left_of_map (hPl p0 hp0) (fun x => T.indicator (1 : G → ENNReal) (p0⁻¹ * x))
        (hind.comp (measurable_const_mul _))
      simp only [inv_mul_cancel_left] at this
      rw [← this, lintegral_indicator_one hT]
    have hW1 : ∫⁻ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ ∂μ
        = ρ T * ∫⁻ g, φ g ∂μ := by
      have e : ∀ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ
          = ρ T * ∫⁻ k, φ (g * k) ∂κ := by
        intro g
        exact (lintegral_mul_const _ (hind.comp (measurable_const_mul g⁻¹))).trans (congrArg (· * _) (s2 g))
      simp_rw [e]
      rw [lintegral_const_mul' _ _ hT1, ← s1]
    have hmF : Measurable fun x : G × G =>
        T.indicator (1 : G → ENNReal) (x.1⁻¹ * x.2) * ∫⁻ k, φ (x.1 * k) ∂κ :=
      (hind.comp (measurable_fst.inv.mul measurable_snd)).mul
        (((hφ.comp measurable_mul).lintegral_prod_right').comp measurable_fst)
    have hmG : Measurable fun x : G × G =>
        T.indicator (1 : G → ENNReal) x.2⁻¹ * ∫⁻ k, φ (x.1 * x.2 * k) ∂κ :=
      (hind.comp measurable_snd.inv).mul
        ((hφ.comp (by fun_prop : Measurable fun y : (G × G) × G => y.1.1 * y.1.2 * y.2)).lintegral_prod_right')
    have hW2 : ∫⁻ g, ∫⁻ q, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂ρ ∂μ
        = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, φ (q * h * k) ∂κ ∂ρ ∂μ := by
      rw [lintegral_lintegral_swap (f := fun g q => T.indicator (1 : G → ENNReal) (g⁻¹ * q) *
        ∫⁻ k, φ (g * k) ∂κ) (by exact hmF.aemeasurable)]
      have e : ∀ q, ∫⁻ g, T.indicator (1 : G → ENNReal) (g⁻¹ * q) * ∫⁻ k, φ (g * k) ∂κ ∂μ
          = ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ k, φ (q * h * k) ∂κ ∂μ := by
        intro q
        refine (lintegral_mul_left_eq_self (μ := μ) (fun g => T.indicator (1 : G → ENNReal) (g⁻¹ * q) *
          ∫⁻ k, φ (g * k) ∂κ) q).symm.trans ?_
        simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      simp_rw [e]
      rw [lintegral_lintegral_swap (f := fun q h => T.indicator (1 : G → ENNReal) h⁻¹ *
        ∫⁻ k, φ (q * h * k) ∂κ) (by exact hmG.aemeasurable)]
      exact lintegral_congr fun h => lintegral_const_mul' _ _ (ind_ne_top _)
    rw [← hW1, hW2]

  obtain ⟨S, hS, hS0, hS1⟩ : ∃ S, MeasurableSet S ∧ μ S ≠ 0 ∧ μ S ≠ ⊤ := by
    by_contra hne
    push Not at hne
    apply hμ
    have hz : ∀ n, μ (spanningSets μ n) = 0 := fun n => by
      by_contra hn
      exact (measure_spanningSets_lt_top μ n).ne (hne _ (measurableSet_spanningSets μ n) hn)
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ]
    exact measure_iUnion_null hz
  have hφ0 : Measurable (S.indicator (1 : G → ENNReal)) := measurable_one.indicator hS
  have hμS : ∫⁻ g, S.indicator (1 : G → ENNReal) g ∂μ = μ S := lintegral_indicator_one hS
  have mix0 := mix _ hφ0
  rw [hμS] at mix0
  have hL0 : ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ ≠ 0 := by
    intro h0
    have : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, S.indicator (1 : G → ENNReal) (q * h * k) ∂κ ∂ρ ∂μ = 0 := by
      refine (lintegral_congr fun h => ?_).trans lintegral_zero
      obtain ⟨D, -, -, hD⟩ := key h
      rw [hD _ hφ0, h0, mul_zero, mul_zero]
    rw [this] at mix0
    exact mul_ne_zero hT0 hS0 mix0
  have hLt : ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ ≠ ⊤ := by
    intro ht
    have : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ∫⁻ q, ∫⁻ k, S.indicator (1 : G → ENNReal) (q * h * k) ∂κ ∂ρ ∂μ
        = (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) * ⊤ := by
      rw [← (lintegral_mul_const ⊤ (hind.comp measurable_inv) : ∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ * ⊤ ∂μ = (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) * ⊤)]
      refine lintegral_congr fun h => ?_
      obtain ⟨D, hD0, -, hD⟩ := key h
      rw [hD _ hφ0, ht, ENNReal.mul_top hD0]
    rw [this] at mix0
    rcases eq_or_ne (∫⁻ h, T.indicator (1 : G → ENNReal) h⁻¹ ∂μ) 0 with hz | hz
    · rw [hz, zero_mul] at mix0
      exact mul_ne_zero hT0 hS0 mix0
    · rw [ENNReal.mul_top hz] at mix0
      exact ENNReal.mul_ne_top hT1 hS1 mix0
  refine ⟨μ S / ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ,
    (ENNReal.div_pos_iff.2 ⟨hS0, hLt⟩).ne', ENNReal.div_ne_top hS1 hL0, fun φ hφ => ?_⟩
  have E : ρ T * ((∫⁻ g, φ g ∂μ) * ∫⁻ p, ∫⁻ k, S.indicator (1 : G → ENNReal) (p * k) ∂κ ∂ρ)
      = ρ T * (μ S * ∫⁻ p, ∫⁻ k, φ (p * k) ∂κ ∂ρ) := by
    rw [← mul_assoc]
    rw [mix _ hφ]
    rw [← lintegral_mul_const _ (hLm _ hφ)]
    rw [← mul_assoc]
    rw [mix0]
    rw [← lintegral_mul_const _ (hLm _ hφ0)]
    refine lintegral_congr fun h => ?_
    obtain ⟨D, -, -, hD⟩ := key h
    rw [hD _ hφ, hD _ hφ0]
    ring
  have E' := (ENNReal.mul_right_inj hT0 hT1).1 E
  rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
  exact (ENNReal.eq_div_iff hL0 hLt).2 (by rw [mul_comm]; exact E')
end GlobalTheory.IwasawaShape
