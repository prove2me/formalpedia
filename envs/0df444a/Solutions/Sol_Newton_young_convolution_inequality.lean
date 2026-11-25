-- Prove2me | solution 1 for Newton.young_convolution_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:54.410844+00:00
-- url     : https://prove2.me/submissions/e6851bf6-aa96-4582-aacb-56d63c011f7d

import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Definitions.Def_Newton_Analysis_Convolution_InnerBound
import Definitions.Def_Newton_Analysis_Convolution_Basic
import Theorems.Thm_Newton_young_convolution_r_ne_top
import Theorems.Thm_Newton_young_exponent_r_ge_one


set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f g : (Fin n → ℝ) → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume)
    (hg : MemLp g q volume) :
    MemLp (fun x => ∫ y, f (x - y) * g y) r volume ∧
    eLpNorm (fun x => ∫ y, f (x - y) * g y) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
  -- Case split on r
  by_cases hr_top : r = ⊤
  · -- Case r = ⊤: 1/p + 1/q = 1, and p and q are conjugate exponents
    -- In this case, the convolution belongs to L^∞ and the estimate follows
    subst hr_top
    simp only [ENNReal.div_top, add_zero] at hpqr
    -- From 1/p + 1/q = 1, p and q are conjugate
    have hp_pos : 0 < p := one_pos.trans_le hp
    have hq_pos : 0 < q := one_pos.trans_le hq
    have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
    have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos
    -- Convolution function
    let conv : (Fin n → ℝ) → ℂ := fun x => ∫ y, f (x - y) * g y
    -- Show that convolution is AEStronglyMeasurable
    have h_conv_aesm : AEStronglyMeasurable conv volume := by
      have h_prod_aesm : AEStronglyMeasurable
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (p.1 - p.2) * g p.2)
          (volume.prod volume) := by
        have h_sub_meas : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 - p.2 :=
          measurable_fst.sub measurable_snd
        have hf_comp : AEStronglyMeasurable
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (p.1 - p.2))
            (volume.prod volume) := by
          have h_shear : MeasurePreserving
              (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 - p.2, p.2))
              (volume.prod volume) (volume.prod volume) :=
            measurePreserving_sub_prod (μ := volume) (ν := volume)
          have h_fst : AEStronglyMeasurable
              (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1)
              (volume.prod volume) :=
            hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
          have h_eq : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (p.1 - p.2)) =
              (fun p => f p.1) ∘ (fun p => (p.1 - p.2, p.2)) := by
            ext p; simp
          rw [h_eq]
          exact h_fst.comp_measurePreserving h_shear
        have hg_comp : AEStronglyMeasurable
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g p.2)
            (volume.prod volume) :=
          hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
        exact hf_comp.mul hg_comp
      exact AEStronglyMeasurable.integral_prod_right' h_prod_aesm
    -- The map y ↦ x - y is measure-preserving
    have h_mp : ∀ x, MeasurePreserving (fun y => x - y)
        (volume : Measure (Fin n → ℝ)) volume := by
      intro x
      have h1 : MeasurePreserving (fun y : Fin n → ℝ => -y) volume volume :=
        Measure.measurePreserving_neg volume
      have h2 : MeasurePreserving (fun y : Fin n → ℝ => x + y) volume volume :=
        measurePreserving_add_left volume x
      have h_eq : (fun y : Fin n → ℝ => x - y) = (fun y => x + y) ∘ (fun y => -y) := by
        ext y; simp [sub_eq_add_neg]
      rw [h_eq]
      exact h2.comp h1
    by_cases hp_top : p = ⊤
    · -- Case p = ⊤: q = 1 (from 1/⊤ + 1/q = 1, we get 1/q = 1)
      have hq_eq : q = 1 := by
        rw [hp_top, ENNReal.div_top, zero_add] at hpqr
        have h : 1 / q = 1 := hpqr
        rw [one_div, ENNReal.inv_eq_one] at h
        exact h
      subst hp_top hq_eq
      -- ‖∫ f(x-y) g(y) dy‖ ≤ ‖f‖_∞ ‖g‖_1
      have h_holder_bound : ∀ x, ‖conv x‖ₑ ≤ eLpNorm f ⊤ volume * eLpNorm g 1 volume := by
        intro x
        simp only [conv]
        calc ‖∫ y, f (x - y) * g y‖ₑ
            ≤ ∫⁻ y, ‖f (x - y) * g y‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
          _ = ∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂volume := by
              apply lintegral_congr; intro y; rw [enorm_mul]
          _ ≤ ∫⁻ y, eLpNormEssSup f volume * ‖g y‖ₑ ∂volume := by
              apply lintegral_mono_ae
              have h_ae := enorm_ae_le_eLpNormEssSup f volume
              have h_mp_ae := (h_mp x).quasiMeasurePreserving.ae h_ae
              filter_upwards [h_mp_ae] with y hy
              exact mul_le_mul_left hy _
          _ = eLpNormEssSup f volume * ∫⁻ y, ‖g y‖ₑ ∂volume := by
              rw [lintegral_const_mul'' _ hg.aestronglyMeasurable.enorm]
          _ = eLpNorm f ⊤ volume * eLpNorm g 1 volume := by
              rw [eLpNorm_exponent_top, eLpNorm_one_eq_lintegral_enorm]
      constructor
      · -- Proof of MemLp
        rw [MemLp, and_iff_right h_conv_aesm]
        unfold eLpNorm
        simp only [↓reduceIte]
        unfold eLpNormEssSup
        have h_bound : eLpNorm f ⊤ volume * eLpNorm g 1 volume < ⊤ :=
          ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top
        calc essSup (fun x => ‖conv x‖ₑ) volume
            ≤ eLpNorm f ⊤ volume * eLpNorm g 1 volume :=
              essSup_le_of_ae_le _ (Filter.Eventually.of_forall h_holder_bound)
          _ < ⊤ := h_bound
      · -- Estimate eLpNorm
        unfold eLpNorm
        simp only [↓reduceIte]
        unfold eLpNormEssSup
        exact essSup_le_of_ae_le _ (Filter.Eventually.of_forall h_holder_bound)
    · by_cases hq_top : q = ⊤
      · -- Case q = ⊤: p = 1 (from 1/p + 1/⊤ = 1, we get 1/p = 1)
        have hp_eq : p = 1 := by
          rw [hq_top, ENNReal.div_top, add_zero] at hpqr
          have h : 1 / p = 1 := hpqr
          rw [one_div, ENNReal.inv_eq_one] at h
          exact h
        subst hq_top hp_eq
        -- ‖∫ f(x-y) g(y) dy‖ ≤ ‖f‖_1 ‖g‖_∞
        have h_holder_bound : ∀ x, ‖conv x‖ₑ ≤ eLpNorm f 1 volume * eLpNorm g ⊤ volume := by
          intro x
          simp only [conv]
          calc ‖∫ y, f (x - y) * g y‖ₑ
              ≤ ∫⁻ y, ‖f (x - y) * g y‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
            _ = ∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂volume := by
                apply lintegral_congr; intro y; rw [enorm_mul]
            _ ≤ ∫⁻ y, ‖f (x - y)‖ₑ * eLpNormEssSup g volume ∂volume := by
                apply lintegral_mono_ae
                have h_ae := enorm_ae_le_eLpNormEssSup g volume
                filter_upwards [h_ae] with y hy
                exact mul_le_mul_right hy _
            _ = (∫⁻ y, ‖f (x - y)‖ₑ ∂volume) * eLpNormEssSup g volume := by
                exact lintegral_mul_const'' _
                  (hf.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
                  (h_mp x).quasiMeasurePreserving)
            _ = (∫⁻ y, ‖f y‖ₑ ∂volume) * eLpNormEssSup g volume := by
                congr 1
                -- Transform integral using measure-preservation: ∫ (f ∘ g) = ∫ f
                -- y ↦ x - y is a MeasurableEquiv (self-inverse map)
                have h_emb : MeasurableEmbedding (fun y : Fin n → ℝ => x - y) := by
                  have h_inv : Function.LeftInverse (fun y => x - y) (fun y => x - y) := by
                    intro y; simp
                  exact MeasurableEquiv.measurableEmbedding
                    { toFun := fun y => x - y
                      invFun := fun y => x - y
                      left_inv := h_inv
                      right_inv := h_inv
                      measurable_toFun := (h_mp x).measurable
                      measurable_invFun := (h_mp x).measurable }
                exact (h_mp x).lintegral_comp_emb h_emb (fun y => ‖f y‖ₑ)
            _ = eLpNorm f 1 volume * eLpNorm g ⊤ volume := by
                rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_exponent_top]
        constructor
        · -- Proof of MemLp
          rw [MemLp, and_iff_right h_conv_aesm]
          unfold eLpNorm
          simp only [↓reduceIte]
          unfold eLpNormEssSup
          have h_bound : eLpNorm f 1 volume * eLpNorm g ⊤ volume < ⊤ :=
            ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top
          calc essSup (fun x => ‖conv x‖ₑ) volume
              ≤ eLpNorm f 1 volume * eLpNorm g ⊤ volume :=
                essSup_le_of_ae_le _ (Filter.Eventually.of_forall h_holder_bound)
            _ < ⊤ := h_bound
        · -- Estimate eLpNorm
          unfold eLpNorm
          simp only [↓reduceIte]
          unfold eLpNormEssSup
          exact essSup_le_of_ae_le _ (Filter.Eventually.of_forall h_holder_bound)
      · -- Case p ≠ ⊤ and q ≠ ⊤: use Real.HolderConjugate
        have hpqr_real : p.toReal.HolderConjugate q.toReal := by
          have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
          have hq_toReal_pos : 0 < q.toReal := ENNReal.toReal_pos hq_ne_zero hq_top
          have h1 : (1 : ℝ≥0∞).toReal = 1 := ENNReal.toReal_one
          have hp_inv : (1 / p).toReal = p.toReal⁻¹ := by
            rw [one_div, ENNReal.toReal_inv]
          have hq_inv : (1 / q).toReal = q.toReal⁻¹ := by
            rw [one_div, ENNReal.toReal_inv]
          have h_ne_top_p : 1 / p ≠ ⊤ := by
            simp only [ne_eq, one_div, ENNReal.inv_eq_top]
            exact hp_ne_zero
          have h_ne_top_q : 1 / q ≠ ⊤ := by
            simp only [ne_eq, one_div, ENNReal.inv_eq_top]
            exact hq_ne_zero
          have h := congr_arg ENNReal.toReal hpqr
          rw [ENNReal.toReal_add h_ne_top_p h_ne_top_q] at h
          rw [hp_inv, hq_inv, h1] at h
          exact ⟨by simp [h], hp_toReal_pos, hq_toReal_pos⟩
        have h_holder_bound : ∀ x, ‖conv x‖ₑ ≤ eLpNorm f p volume * eLpNorm g q volume := by
          intro x
          simp only [conv]
          calc ‖∫ y, f (x - y) * g y‖ₑ
              ≤ ∫⁻ y, ‖f (x - y) * g y‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
            _ = ∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂volume := by
                apply lintegral_congr; intro y
                rw [enorm_mul]
            _ ≤ (∫⁻ y, ‖f (x - y)‖ₑ ^ p.toReal ∂volume) ^ (1 / p.toReal) *
                (∫⁻ y, ‖g y‖ₑ ^ q.toReal ∂volume) ^ (1 / q.toReal) := by
                apply ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpqr_real
                · exact hf.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
                    (h_mp x).quasiMeasurePreserving
                · exact hg.aestronglyMeasurable.enorm
            _ = eLpNorm (fun y => f (x - y)) p volume * eLpNorm g q volume := by
                -- Expand eLpNorm
                rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_top]
                rw [eLpNorm_eq_lintegral_rpow_enorm hq_ne_zero hq_top]
            _ = eLpNorm f p volume * eLpNorm g q volume := by
                congr 1
                -- Translation invariance
                have h_comp : (fun y => f (x - y)) = f ∘ (fun y => x - y) := rfl
                rw [h_comp]
                exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (h_mp x)
        constructor
        · -- Proof of MemLp
          rw [MemLp, and_iff_right h_conv_aesm]
          unfold eLpNorm
          simp only [↓reduceIte]
          unfold eLpNormEssSup
          have h_bound : eLpNorm f p volume * eLpNorm g q volume < ⊤ :=
            ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top
          calc essSup (fun x => ‖conv x‖ₑ) volume
              ≤ eLpNorm f p volume * eLpNorm g q volume :=
                essSup_le_of_ae_le _ (Filter.Eventually.of_forall h_holder_bound)
            _ < ⊤ := h_bound
        · -- Estimate eLpNorm
          unfold eLpNorm
          simp only [↓reduceIte]
          unfold eLpNormEssSup
          exact essSup_le_of_ae_le _ (Filter.Eventually.of_forall h_holder_bound)
  · -- Case r ≠ ⊤
    by_cases hp_top : p = ⊤
    · -- Case p = ⊤
      subst hp_top
      simp only [ENNReal.div_top, zero_add] at hpqr
      -- From 1/q = 1 + 1/r, we get q⁻¹ > 1 so q < 1, contradicting hq : 1 ≤ q
      exfalso
      have hq_lt_one : q < 1 := by
        -- hpqr : 1/q = 1 + 1/r, i.e., q⁻¹ = 1 + r⁻¹ > 1
        rw [one_div, one_div] at hpqr
        have h_pos : 0 < r⁻¹ := ENNReal.inv_pos.mpr hr_top
        have h_one_lt : 1 < q⁻¹ := by
          rw [hpqr]
          exact ENNReal.lt_add_right (by simp) (ne_of_gt h_pos)
        exact ENNReal.one_lt_inv.mp h_one_lt
      exact not_lt.mpr hq hq_lt_one
    · -- Case p ≠ ⊤
      by_cases hq_top : q = ⊤
      · -- Case q = ⊤ (symmetric to p)
        subst hq_top
        simp only [ENNReal.div_top, add_zero] at hpqr
        exfalso
        have hp_lt_one : p < 1 := by
          -- hpqr : 1/p = 1 + 1/r, i.e., p⁻¹ = 1 + r⁻¹ > 1
          rw [one_div, one_div] at hpqr
          have h_pos : 0 < r⁻¹ := ENNReal.inv_pos.mpr hr_top
          have h_one_lt : 1 < p⁻¹ := by
            rw [hpqr]
            exact ENNReal.lt_add_right (by simp) (ne_of_gt h_pos)
          exact ENNReal.one_lt_inv.mp h_one_lt
        exact not_lt.mpr hp hp_lt_one
      · -- Case p ≠ ⊤, q ≠ ⊤, r ≠ ⊤
        have hr : 1 ≤ r := young_exponent_r_ge_one hp hq hpqr
        exact young_convolution_r_ne_top f g p q r hp hq hr hp_top hq_top hr_top hpqr hf hg
end Newton
