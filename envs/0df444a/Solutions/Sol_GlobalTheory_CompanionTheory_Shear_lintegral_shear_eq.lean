-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Shear.lintegral_shear_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:36:10.995805+00:00
-- url     : https://prove2.me/submissions/913010af-3c96-47d9-be6a-71e839691937

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuotientMeasureByInvariantSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Shear
namespace GlobalTheory.CompanionTheory.Shear
theorem _root_.solution : ∀ (V A : Type) [AddCommGroup V] [AddCommGroup A] [MeasurableSpace V]
    [MeasurableSpace A] [MeasurableAdd₂ V] [MeasurableAdd₂ A] [MeasurableNeg A] [MeasurableNeg V]
    (μ : Measure V) (lam : Measure A) [SFinite μ] [SFinite lam] [μ.IsAddRightInvariant]
    [lam.IsAddRightInvariant] (j : A →+ V), Measurable j → ∀ f : V → A, Measurable f →
    (∀ v a, f (v + j a) = f v) → ∀ K : Set A, MeasurableSet K → lam K ≠ 0 → lam K ≠ ⊤ →
    ∀ ψ : V → ℝ≥0∞, Measurable ψ → ∫⁻ v, ψ (v + j (f v)) ∂μ = ∫⁻ v, ψ v ∂μ := by
  intro V A _ _ _ _ _ _ _ _ μ lam _ _ _ _ j hj f hf hfinv K hK hK0 hKtop ψ hψ
  classical
  have hind : Measurable (K.indicator (1 : A → ℝ≥0∞)) := measurable_one.indicator hK
  have hind_ne : ∀ a, K.indicator (1 : A → ℝ≥0∞) a ≠ ⊤ := fun a => by
    rw [Set.indicator_apply]
    split_ifs <;> simp
  have hfneg : ∀ v a, f (v + -j a) = f v := fun v a => by
    rw [← map_neg]
    exact hfinv v (-a)
  have sA : ∀ a, ∫⁻ v, ψ (v + j a + j (f v)) ∂μ = ∫⁻ v, ψ (v + j (f v)) ∂μ := fun a =>
    (lintegral_add_right_eq_self (μ := μ) (fun v => ψ (v + j a + j (f v))) (-(j a))).symm.trans
      (lintegral_congr fun v => by simp only [neg_add_cancel_right, hfneg])
  have sB : ∀ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v)) ∂lam =
      ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂lam := fun v =>
    (lintegral_add_right_eq_self (μ := lam) (fun a => K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v))) (-(f v))).symm.trans
      (lintegral_congr fun a => by simp only [map_add, map_neg, add_assoc, neg_add_cancel, add_zero])
  have sC : ∀ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂μ = ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂μ :=
    fun a => (lintegral_add_right_eq_self (μ := μ) (fun v => K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a)) (-(j a))).symm.trans
      (lintegral_congr fun v => by simp only [neg_add_cancel_right, hfneg])
  have sD : ∀ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂lam = lam K * ψ v := fun v => by
    have hm : Measurable fun a => K.indicator (1 : A → ℝ≥0∞) (a + -f v) := hind.comp (measurable_add_const (-f v))
    rw [lintegral_mul_const _ hm, lintegral_add_right_eq_self (μ := lam) (K.indicator (1 : A → ℝ≥0∞)) (-f v),
      lintegral_indicator_one hK]
  have hm1 : Measurable fun p : A × V => K.indicator (1 : A → ℝ≥0∞) p.1 * ψ (p.2 + j p.1 + j (f p.2)) :=
    (hind.comp measurable_fst).mul
      (hψ.comp ((measurable_snd.add (hj.comp measurable_fst)).add (hj.comp (hf.comp measurable_snd))))
  have hm2 : Measurable fun p : V × A => K.indicator (1 : A → ℝ≥0∞) (p.2 + -f p.1) * ψ (p.1 + j p.2) :=
    (hind.comp (measurable_snd.add (hf.comp measurable_fst).neg)).mul
      (hψ.comp (measurable_fst.add (hj.comp measurable_snd)))
  have hm3 : Measurable fun p : A × V => K.indicator (1 : A → ℝ≥0∞) (p.1 + -f p.2) * ψ p.2 :=
    (hind.comp (measurable_fst.add (hf.comp measurable_snd).neg)).mul (hψ.comp measurable_snd)
  have key : lam K * ∫⁻ v, ψ (v + j (f v)) ∂μ = lam K * ∫⁻ v, ψ v ∂μ := by
    calc lam K * ∫⁻ v, ψ (v + j (f v)) ∂μ
        = ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) a * ∫⁻ v, ψ (v + j a + j (f v)) ∂μ ∂lam := by
          simp_rw [sA]
          rw [lintegral_mul_const _ hind, lintegral_indicator_one hK]
      _ = ∫⁻ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v)) ∂μ ∂lam := by
          refine lintegral_congr fun a => ?_
          rw [lintegral_const_mul' _ _ (hind_ne a)]
      _ = ∫⁻ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) a * ψ (v + j a + j (f v)) ∂lam ∂μ :=
          lintegral_lintegral_swap hm1.aemeasurable
      _ = ∫⁻ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂lam ∂μ := lintegral_congr fun v => sB v
      _ = ∫⁻ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ (v + j a) ∂μ ∂lam :=
          lintegral_lintegral_swap hm2.aemeasurable
      _ = ∫⁻ a, ∫⁻ v, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂μ ∂lam := lintegral_congr fun a => sC a
      _ = ∫⁻ v, ∫⁻ a, K.indicator (1 : A → ℝ≥0∞) (a + -f v) * ψ v ∂lam ∂μ :=
          lintegral_lintegral_swap hm3.aemeasurable
      _ = ∫⁻ v, lam K * ψ v ∂μ := lintegral_congr fun v => sD v
      _ = lam K * ∫⁻ v, ψ v ∂μ := lintegral_const_mul' _ _ hKtop
  exact (ENNReal.mul_right_inj hK0 hKtop).mp key
end GlobalTheory.CompanionTheory.Shear
