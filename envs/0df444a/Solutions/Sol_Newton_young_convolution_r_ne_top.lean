-- Prove2me | solution 1 for Newton.young_convolution_r_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:38:08.679035+00:00
-- url     : https://prove2.me/submissions/07f0d439-e5de-4058-916d-6c986170ac3d

import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Definitions.Def_Newton_Analysis_Convolution_InnerBound
import Theorems.Thm_Newton_inner_integral_bound
import Theorems.Thm_Newton_young_exponent_p_le_r
import Theorems.Thm_Newton_young_exponent_q_le_r


set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (f g : (Fin n → ℝ) → ℂ)
    (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hp_ne_top : p ≠ ⊤) (hq_ne_top : q ≠ ⊤) (hr_ne_top : r ≠ ⊤)
    (hpqr : 1 / p + 1 / q = 1 + 1 / r)
    (hf : MemLp f p volume) (hg : MemLp g q volume) :
    MemLp (fun x => ∫ y, f (x - y) * g y) r volume ∧
    eLpNorm (fun x => ∫ y, f (x - y) * g y) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
  -- Basic lemmas
  have hr_pos : 0 < r := one_pos.trans_le hr
  have hr_ne_zero : r ≠ 0 := ne_of_gt hr_pos
  have hp_pos : 0 < p := one_pos.trans_le hp
  have hp_ne_zero : p ≠ 0 := ne_of_gt hp_pos
  have hq_pos : 0 < q := one_pos.trans_le hq
  have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos
  have hr_pos_real : 0 < r.toReal := ENNReal.toReal_pos hr_ne_zero hr_ne_top
  have hp_pos_real : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hq_pos_real : 0 < q.toReal := ENNReal.toReal_pos hq_ne_zero hq_ne_top
  -- Get that eLpNorm is finite
  have hf_eLpNorm_lt_top : eLpNorm f p volume < ⊤ := hf.eLpNorm_lt_top
  have hg_eLpNorm_lt_top : eLpNorm g q volume < ⊤ := hg.eLpNorm_lt_top
  -- Get AEStronglyMeasurable
  have hf_aesm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hg_aesm : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  -- Convolution function
  let conv : (Fin n → ℝ) → ℂ := fun x => ∫ y, f (x - y) * g y
  -- Main estimate: use inner_integral_bound
  have h_inner_bound : ∀ x, ∫⁻ y, ‖f y‖₊ * ‖g (x - y)‖₊ ∂volume ≤
      (∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume)^(1/r.toReal) *
      (eLpNorm f p volume)^(1 - p/r).toReal *
      (eLpNorm g q volume)^(1 - q/r).toReal := fun x =>
    inner_integral_bound f g p q r hp hq hr hp_ne_top hq_ne_top hr_ne_top hpqr hf hg x
  -- Estimate the norm of convolution
  have h_conv_enorm_bound : ∀ x, ‖conv x‖ₑ ≤
      ∫⁻ y, ‖f y‖₊ * ‖g (x - y)‖₊ ∂volume := by
    intro x
    simp only [conv]
    -- The norm of integral is bounded by the integral of norms of integrand
    calc ‖∫ y, f (x - y) * g y‖ₑ
        ≤ ∫⁻ y, ‖f (x - y) * g y‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, ‖f (x - y)‖₊ * ‖g y‖₊ ∂volume := by
          apply lintegral_congr
          intro y
          simp [enorm_eq_nnnorm, nnnorm_mul]
      _ = ∫⁻ y, ‖f y‖₊ * ‖g (x - y)‖₊ ∂volume := by
          -- Change of variables y ↦ x - y
          rw [← lintegral_sub_left_eq_self (fun y => (‖f y‖₊ : ℝ≥0∞) * ‖g (x - y)‖₊) x]
          apply lintegral_congr
          intro y
          simp [sub_sub_cancel]
  have h_conv_aesm : AEStronglyMeasurable conv volume := by
    -- Use that (x, y) ↦ f(x - y) * g(y) is AEStronglyMeasurable with product measure
    have h_prod_aesm : AEStronglyMeasurable
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (p.1 - p.2) * g p.2)
        (volume.prod volume) := by
      -- f ∘ (p.1 - p.2) is AEStronglyMeasurable
      have h_sub_meas : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 - p.2 :=
        measurable_fst.sub measurable_snd
      have hf_comp : AEStronglyMeasurable
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (p.1 - p.2))
          (volume.prod volume) := by
        -- Use shear transformation (x, y) ↦ (x - y, y)
        have h_shear : MeasurePreserving
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 - p.2, p.2))
            (volume.prod volume) (volume.prod volume) :=
          measurePreserving_sub_prod (μ := volume) (ν := volume)
        have h_fst : AEStronglyMeasurable
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1)
            (volume.prod volume) :=
          hf_aesm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
        -- f(p.1 - p.2) = (f ∘ fst)(shear(p))
        have h_eq : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (p.1 - p.2)) =
            (fun p => f p.1) ∘ (fun p => (p.1 - p.2, p.2)) := by
          ext p; simp
        rw [h_eq]
        exact h_fst.comp_measurePreserving h_shear
      have hg_comp : AEStronglyMeasurable
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g p.2)
          (volume.prod volume) :=
        hg_aesm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
      exact hf_comp.mul hg_comp
    exact AEStronglyMeasurable.integral_prod_right' h_prod_aesm
  -- Combine the estimates from inner_integral_bound
  -- ‖conv x‖ₑ ≤ C(x) * A * B
  -- where C(x) = (∫ |f|^p |g(x-·)|^q)^{1/r}, A = ‖f‖_p^{1-p/r}, B = ‖g‖_q^{1-q/r}
  have h_combined_bound : ∀ x, ‖conv x‖ₑ ≤
      (∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume)^(1/r.toReal) *
      (eLpNorm f p volume)^(1 - p/r).toReal *
      (eLpNorm g q volume)^(1 - q/r).toReal := by
    intro x
    calc ‖conv x‖ₑ
        ≤ ∫⁻ y, ‖f y‖₊ * ‖g (x - y)‖₊ ∂volume := h_conv_enorm_bound x
      _ ≤ _ := h_inner_bound x
  constructor
  · -- Proof of MemLp
    rw [MemLp, and_iff_right h_conv_aesm]
    -- Show eLpNorm conv r volume < ⊤
    unfold eLpNorm eLpNorm'
    simp only [hr_ne_top, reduceIte, hr_ne_zero, ↓reduceIte]
    -- Show (∫ ‖conv x‖^r dx)^{1/r} < ⊤
    rw [one_div]
    apply ENNReal.rpow_lt_top_of_nonneg (by positivity : 0 ≤ r.toReal⁻¹)
    -- Show ∫ ‖conv x‖^r dx ≠ ⊤
    apply ne_of_lt
    -- From h_combined_bound, get ‖conv x‖ₑ^r ≤ ... and integrate
    -- Use Tonelli to exchange integration order and show finiteness
    -- Constant parts A := ‖f‖_p^{1-p/r}, B := ‖g‖_q^{1-q/r}
    let A : ℝ≥0∞ := (eLpNorm f p volume) ^ (1 - p/r).toReal
    let B : ℝ≥0∞ := (eLpNorm g q volume) ^ (1 - q/r).toReal
    -- C(x) := (∫ |f|^p |g(x-·)|^q)^{1/r}
    let C : (Fin n → ℝ) → ℝ≥0∞ := fun x =>
      (∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume)^(1/r.toReal)
    -- h_combined_bound: ‖conv x‖ₑ ≤ C(x) * A * B
    have h_bound_r : ∀ x, ‖conv x‖ₑ^r.toReal ≤ (C x * A * B)^r.toReal := by
      intro x
      apply ENNReal.rpow_le_rpow (h_combined_bound x)
      exact le_of_lt hr_pos_real
    -- (C x * A * B)^r = C(x)^r * A^r * B^r
    have h_power_expand : ∀ x, (C x * A * B)^r.toReal =
        (C x)^r.toReal * A^r.toReal * B^r.toReal := by
      intro x
      rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hr_pos_real)]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hr_pos_real)]
    -- C(x)^r = ∫ |f|^p |g(x-·)|^q (by rpow cancellation)
    have h_Cx_r : ∀ x, (C x)^r.toReal =
        ∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume := by
      intro x
      simp only [C]
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hr_pos_real)]
      simp
    -- A and B are finite constants
    have hA_lt_top : A < ⊤ := by
      simp only [A]
      apply ENNReal.rpow_lt_top_of_nonneg
      · have hp_le_r : p ≤ r := young_exponent_p_le_r hq hpqr
        have h_pr_le_one : p / r ≤ 1 := by
          rw [ENNReal.div_le_iff (ne_of_gt hr_pos) hr_ne_top, one_mul]
          exact hp_le_r
        rw [ENNReal.toReal_sub_of_le h_pr_le_one (by simp)]
        have h_pr_toReal_le_one : (p / r).toReal ≤ 1 := by
          rw [ENNReal.toReal_div]
          have h_p_le_r_real : p.toReal ≤ r.toReal :=
            ENNReal.toReal_le_toReal hp_ne_top hr_ne_top |>.mpr hp_le_r
          exact div_le_one_of_le₀ h_p_le_r_real (le_of_lt hr_pos_real)
        simp only [ENNReal.toReal_one]
        linarith
      · exact ne_of_lt hf_eLpNorm_lt_top
    have hB_lt_top : B < ⊤ := by
      simp only [B]
      apply ENNReal.rpow_lt_top_of_nonneg
      · have hq_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
        have h_qr_le_one : q / r ≤ 1 := by
          rw [ENNReal.div_le_iff (ne_of_gt hr_pos) hr_ne_top, one_mul]
          exact hq_le_r
        rw [ENNReal.toReal_sub_of_le h_qr_le_one (by simp)]
        have h_qr_toReal_le_one : (q / r).toReal ≤ 1 := by
          rw [ENNReal.toReal_div]
          have h_q_le_r_real : q.toReal ≤ r.toReal :=
            ENNReal.toReal_le_toReal hq_ne_top hr_ne_top |>.mpr hq_le_r
          exact div_le_one_of_le₀ h_q_le_r_real (le_of_lt hr_pos_real)
        simp only [ENNReal.toReal_one]
        linarith
      · exact ne_of_lt hg_eLpNorm_lt_top
    -- Estimate the integral
    calc ∫⁻ x, ‖conv x‖ₑ^r.toReal ∂volume
        ≤ ∫⁻ x, (C x * A * B)^r.toReal ∂volume := by
          apply lintegral_mono
          intro x
          exact h_bound_r x
      _ = ∫⁻ x, (C x)^r.toReal * A^r.toReal * B^r.toReal ∂volume := by
          apply lintegral_congr
          intro x
          exact h_power_expand x
      _ = A^r.toReal * B^r.toReal * ∫⁻ x, (C x)^r.toReal ∂volume := by
          -- Factor out constants
          have h_const_factor : ∀ x, (C x)^r.toReal * A^r.toReal * B^r.toReal =
              A^r.toReal * B^r.toReal * (C x)^r.toReal := fun x => by ring
          simp_rw [h_const_factor]
          have hAB_ne_top : A^r.toReal * B^r.toReal ≠ ⊤ := by
            apply ne_of_lt
            apply ENNReal.mul_lt_top
            · exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hr_pos_real) (ne_of_lt hA_lt_top)
            · exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hr_pos_real) (ne_of_lt hB_lt_top)
          rw [lintegral_const_mul' _ _ hAB_ne_top]
      _ = A^r.toReal * B^r.toReal *
            ∫⁻ x, ∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume ∂volume := by
          congr 1
          apply lintegral_congr
          intro x
          exact h_Cx_r x
      _ = A^r.toReal * B^r.toReal *
            ((∫⁻ y, ‖f y‖₊^p.toReal ∂volume) * ∫⁻ z, ‖g z‖₊^q.toReal ∂volume) := by
          congr 1
          -- Tonelli: ∫∫ |f(y)|^p |g(x-y)|^q dx dy = ‖f‖_p^p * ‖g‖_q^q
          -- Change of variables z = x - y gives ∫ |g(x-y)|^q dx = ∫ |g(z)|^q dz
          have h_tonelli :
              ∫⁻ x, ∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume ∂volume =
                ∫⁻ y, ∫⁻ x, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume ∂volume := by
            -- Exchange order of integration (Tonelli)
            have h_prod_meas : AEMeasurable
                (fun xy : (Fin n → ℝ) × (Fin n → ℝ) =>
                  (‖f xy.2‖₊ : ℝ≥0∞)^p.toReal * ‖g (xy.1 - xy.2)‖₊^q.toReal)
                (volume.prod volume) := by
              apply AEMeasurable.mul
              · exact (hf.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
                  Measure.quasiMeasurePreserving_snd).pow_const _
              · have h_shear : MeasurePreserving
                    (fun xy : (Fin n → ℝ) × (Fin n → ℝ) => (xy.1 - xy.2, xy.2))
                    (volume.prod volume) (volume.prod volume) :=
                  measurePreserving_sub_prod (μ := volume) (ν := volume)
                have h_fst : AEMeasurable
                    (fun xy : (Fin n → ℝ) × (Fin n → ℝ) => (‖g xy.1‖₊ : ℝ≥0∞)^q.toReal)
                    (volume.prod volume) :=
                  (hg.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
                    Measure.quasiMeasurePreserving_fst).pow_const _
                have h_eq :
                    (fun xy : (Fin n → ℝ) × (Fin n → ℝ) => (‖g (xy.1 - xy.2)‖₊ : ℝ≥0∞)^q.toReal) =
                    (fun xy => (‖g xy.1‖₊ : ℝ≥0∞)^q.toReal) ∘ (fun xy => (xy.1 - xy.2, xy.2)) := by
                  ext xy; simp
                rw [h_eq]
                exact h_fst.comp_quasiMeasurePreserving h_shear.quasiMeasurePreserving
            have h1 := lintegral_prod (μ := volume) (ν := volume)
              (f := fun xy : (Fin n → ℝ) × (Fin n → ℝ) =>
                (‖f xy.2‖₊ : ℝ≥0∞)^p.toReal * ‖g (xy.1 - xy.2)‖₊^q.toReal)
              h_prod_meas
            have h_swap_meas : AEMeasurable
                (fun xy : (Fin n → ℝ) × (Fin n → ℝ) =>
                  (‖f xy.1‖₊ : ℝ≥0∞)^p.toReal * ‖g (xy.2 - xy.1)‖₊^q.toReal)
                (volume.prod volume) := by
              apply AEMeasurable.mul
              · exact (hf.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
                  Measure.quasiMeasurePreserving_fst).pow_const _
              · have h_shear : MeasurePreserving
                    (fun xy : (Fin n → ℝ) × (Fin n → ℝ) => (xy.2 - xy.1, xy.1))
                    (volume.prod volume) (volume.prod volume) := by
                  haveI : SFinite (volume : Measure (Fin n → ℝ)) := inferInstance
                  -- Use swap first, then sub_prod
                  have h_swap :
                    MeasurePreserving Prod.swap (volume.prod volume) (volume.prod volume) :=
                    @Measure.measurePreserving_swap (Fin n → ℝ) (Fin n → ℝ) _ _ volume volume _ _
                  have h_sub : MeasurePreserving
                      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.1 - z.2, z.2))
                      (volume.prod volume) (volume.prod volume) :=
                    measurePreserving_sub_prod (μ := volume) (ν := volume)
                  exact h_sub.comp h_swap
                have h_fst : AEMeasurable
                    (fun xy : (Fin n → ℝ) × (Fin n → ℝ) => (‖g xy.1‖₊ : ℝ≥0∞)^q.toReal)
                    (volume.prod volume) :=
                  (hg.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
                    Measure.quasiMeasurePreserving_fst).pow_const _
                have h_eq :
                    (fun xy : (Fin n → ℝ) × (Fin n → ℝ) => (‖g (xy.2 - xy.1)‖₊ : ℝ≥0∞)^q.toReal) =
                    (fun xy => (‖g xy.1‖₊ : ℝ≥0∞)^q.toReal) ∘ (fun xy => (xy.2 - xy.1, xy.1)) := by
                  ext xy; simp
                rw [h_eq]
                exact h_fst.comp_quasiMeasurePreserving h_shear.quasiMeasurePreserving
            have h2 := lintegral_prod (μ := volume) (ν := volume)
              (f := fun xy : (Fin n → ℝ) × (Fin n → ℝ) =>
                (‖f xy.1‖₊ : ℝ≥0∞)^p.toReal * ‖g (xy.2 - xy.1)‖₊^q.toReal)
              h_swap_meas
            simp only at h1 h2
            -- h1: ∫∫ |f(y)|^p |g(x-y)|^q dy dx = ∫ (x,y) |f(y)|^p |g(x-y)|^q d(vol×vol)
            -- Exchange order: ∫ (x,y) = ∫ (y,x) (by swap) = ∫∫ dy dx
            have h_swap_eq :
                ∫⁻ xy : (Fin n → ℝ) × (Fin n → ℝ),
                  (‖f xy.2‖₊ : ℝ≥0∞)^p.toReal * ‖g (xy.1 - xy.2)‖₊^q.toReal ∂(volume.prod volume) =
                ∫⁻ xy : (Fin n → ℝ) × (Fin n → ℝ),
                  (‖f xy.1‖₊ : ℝ≥0∞)^p.toReal *
                  ‖g (xy.2 - xy.1)‖₊^q.toReal ∂(volume.prod volume) := by
              have h_swap_pres :
                MeasurePreserving Prod.swap (volume.prod volume) (volume.prod volume) :=
                @Measure.measurePreserving_swap (Fin n → ℝ) (Fin n → ℝ) _ _ volume volume _ _
              rw [← h_swap_pres.lintegral_comp_emb MeasurableEquiv.prodComm.measurableEmbedding]
              apply lintegral_congr
              intro xy
              simp only [Prod.swap]
            rw [← h1, h_swap_eq, h2]
          -- ∫∫ |f(y)|^p |g(x-y)|^q dx dy = ∫ |f(y)|^p (∫ |g(x-y)|^q dx) dy
          have h_inner_const : ∀ y,
              ∫⁻ x, (‖f y‖₊ : ℝ≥0∞)^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume =
                (‖f y‖₊ : ℝ≥0∞)^p.toReal * ∫⁻ x, ‖g (x - y)‖₊^q.toReal ∂volume := by
            intro y
            have h_ne_top : (‖f y‖₊ : ℝ≥0∞)^p.toReal ≠ ⊤ :=
              ENNReal.rpow_ne_top_of_nonneg (le_of_lt hp_pos_real) ENNReal.coe_ne_top
            rw [lintegral_const_mul' _ _ h_ne_top]
          have h_translate : ∀ y, ∫⁻ x, ‖g (x - y)‖₊^q.toReal ∂volume =
              ∫⁻ z, ‖g z‖₊^q.toReal ∂volume := by
            intro y
            exact lintegral_sub_right_eq_self (fun z => (‖g z‖₊ : ℝ≥0∞)^q.toReal) y
          have h_gq_int : ∫⁻ z, ‖g z‖₊^q.toReal ∂volume ≠ ⊤ := by
            have :=
              lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq_ne_zero hq_ne_top hg.eLpNorm_lt_top
            simp only [enorm_eq_nnnorm] at this
            exact ne_of_lt this
          calc ∫⁻ x, ∫⁻ y, (‖f y‖₊ : ℝ≥0∞)^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume ∂volume
              = ∫⁻ y, ∫⁻ x, (‖f y‖₊ : ℝ≥0∞)^p.toReal *
                ‖g (x - y)‖₊^q.toReal ∂volume ∂volume := h_tonelli
            _ = ∫⁻ y, (‖f y‖₊ : ℝ≥0∞)^p.toReal * ∫⁻ x, ‖g (x - y)‖₊^q.toReal ∂volume ∂volume := by
                apply lintegral_congr
                intro y
                exact h_inner_const y
            _ = ∫⁻ y, (‖f y‖₊ : ℝ≥0∞)^p.toReal * ∫⁻ z, ‖g z‖₊^q.toReal ∂volume ∂volume := by
                apply lintegral_congr
                intro y
                rw [h_translate y]
            _ = (∫⁻ y, (‖f y‖₊ : ℝ≥0∞)^p.toReal ∂volume) * ∫⁻ z, ‖g z‖₊^q.toReal ∂volume := by
                rw [lintegral_mul_const' _ _ h_gq_int]
      _ < ⊤ := by
          -- A^r * B^r * (‖f‖_p^p * ‖g‖_q^q) < ⊤
          apply ENNReal.mul_lt_top
          · apply ENNReal.mul_lt_top
            · exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hr_pos_real) (ne_of_lt hA_lt_top)
            · exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hr_pos_real) (ne_of_lt hB_lt_top)
          · apply ENNReal.mul_lt_top
            · -- ∫ |f|^p < ⊤
              have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
                hp_ne_zero hp_ne_top hf.eLpNorm_lt_top
              simp only [enorm_eq_nnnorm] at this
              exact this
            · -- ∫ |g|^q < ⊤
              have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
                hq_ne_zero hq_ne_top hg.eLpNorm_lt_top
              simp only [enorm_eq_nnnorm] at this
              exact this
  · -- Estimate eLpNorm
    -- Estimate using h_combined_bound
    -- Reuse the estimate shown in the MemLp proof above
    let A : ℝ≥0∞ := (eLpNorm f p volume) ^ (1 - p/r).toReal
    let B : ℝ≥0∞ := (eLpNorm g q volume) ^ (1 - q/r).toReal
    let C : (Fin n → ℝ) → ℝ≥0∞ := fun x =>
      (∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume)^(1/r.toReal)
    have hA_lt_top : A < ⊤ := by
      simp only [A]
      apply ENNReal.rpow_lt_top_of_nonneg
      · have hp_le_r : p ≤ r := young_exponent_p_le_r hq hpqr
        have h_pr_le_one : p / r ≤ 1 := by
          rw [ENNReal.div_le_iff (ne_of_gt hr_pos) hr_ne_top, one_mul]
          exact hp_le_r
        rw [ENNReal.toReal_sub_of_le h_pr_le_one (by simp)]
        have h_pr_toReal_le_one : (p / r).toReal ≤ 1 := by
          rw [ENNReal.toReal_div]
          have h_p_le_r_real : p.toReal ≤ r.toReal :=
            ENNReal.toReal_le_toReal hp_ne_top hr_ne_top |>.mpr hp_le_r
          exact div_le_one_of_le₀ h_p_le_r_real (le_of_lt hr_pos_real)
        simp only [ENNReal.toReal_one]
        linarith
      · exact ne_of_lt hf_eLpNorm_lt_top
    have hB_lt_top : B < ⊤ := by
      simp only [B]
      apply ENNReal.rpow_lt_top_of_nonneg
      · have hq_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
        have h_qr_le_one : q / r ≤ 1 := by
          rw [ENNReal.div_le_iff (ne_of_gt hr_pos) hr_ne_top, one_mul]
          exact hq_le_r
        rw [ENNReal.toReal_sub_of_le h_qr_le_one (by simp)]
        have h_qr_toReal_le_one : (q / r).toReal ≤ 1 := by
          rw [ENNReal.toReal_div]
          have h_q_le_r_real : q.toReal ≤ r.toReal :=
            ENNReal.toReal_le_toReal hq_ne_top hr_ne_top |>.mpr hq_le_r
          exact div_le_one_of_le₀ h_q_le_r_real (le_of_lt hr_pos_real)
        simp only [ENNReal.toReal_one]
        linarith
      · exact ne_of_lt hg_eLpNorm_lt_top
    have h_Cx_r : ∀ x, (C x)^r.toReal =
        ∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume := by
      intro x
      simp only [C]
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hr_pos_real)]
      simp
    -- eLpNorm conv r = (∫ ‖conv‖^r)^{1/r}
    unfold eLpNorm eLpNorm'
    simp only [hr_ne_top, reduceIte, hr_ne_zero, ↓reduceIte]
    rw [one_div]
    -- Estimate using the upper bound of the integral
    -- Show ∫ ‖conv x‖^r dx ≤ A^r * B^r * (‖f‖_p^p * ‖g‖_q^q)
    have h_bound_r : ∀ x, ‖conv x‖ₑ^r.toReal ≤ (C x * A * B)^r.toReal := by
      intro x
      apply ENNReal.rpow_le_rpow (h_combined_bound x)
      exact le_of_lt hr_pos_real
    have h_power_expand : ∀ x, (C x * A * B)^r.toReal =
        (C x)^r.toReal * A^r.toReal * B^r.toReal := by
      intro x
      rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hr_pos_real)]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hr_pos_real)]
    have h_lintegral_bound : ∫⁻ x, ‖conv x‖ₑ^r.toReal ∂volume ≤
        A^r.toReal * B^r.toReal *
        ((∫⁻ y, ‖f y‖₊^p.toReal ∂volume) * ∫⁻ z, ‖g z‖₊^q.toReal ∂volume) := by
      have hAB_ne_top : A^r.toReal * B^r.toReal ≠ ⊤ := by
        apply ne_of_lt
        apply ENNReal.mul_lt_top
        · exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hr_pos_real) (ne_of_lt hA_lt_top)
        · exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hr_pos_real) (ne_of_lt hB_lt_top)
      have h_tonelli :
          ∫⁻ x, ∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume ∂volume =
            ∫⁻ y, ∫⁻ x, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume ∂volume := by
        have h_prod_meas : AEMeasurable
            (fun xy : (Fin n → ℝ) × (Fin n → ℝ) =>
              (‖f xy.2‖₊ : ℝ≥0∞)^p.toReal * ‖g (xy.1 - xy.2)‖₊^q.toReal)
            (volume.prod volume) := by
          apply AEMeasurable.mul
          · exact (hf.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
              Measure.quasiMeasurePreserving_snd).pow_const _
          · have h_shear : MeasurePreserving
                (fun xy : (Fin n → ℝ) × (Fin n → ℝ) => (xy.1 - xy.2, xy.2))
                (volume.prod volume) (volume.prod volume) :=
              measurePreserving_sub_prod (μ := volume) (ν := volume)
            have h_fst : AEMeasurable
                (fun xy : (Fin n → ℝ) × (Fin n → ℝ) => (‖g xy.1‖₊ : ℝ≥0∞)^q.toReal)
                (volume.prod volume) :=
              (hg.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
                Measure.quasiMeasurePreserving_fst).pow_const _
            have h_eq :
                (fun xy : (Fin n → ℝ) × (Fin n → ℝ) => (‖g (xy.1 - xy.2)‖₊ : ℝ≥0∞)^q.toReal) =
                (fun xy => (‖g xy.1‖₊ : ℝ≥0∞)^q.toReal) ∘ (fun xy => (xy.1 - xy.2, xy.2)) := by
              ext xy; simp
            rw [h_eq]
            exact h_fst.comp_quasiMeasurePreserving h_shear.quasiMeasurePreserving
        have h1 := lintegral_prod (μ := volume) (ν := volume)
          (f := fun xy : (Fin n → ℝ) × (Fin n → ℝ) =>
            (‖f xy.2‖₊ : ℝ≥0∞)^p.toReal * ‖g (xy.1 - xy.2)‖₊^q.toReal)
          h_prod_meas
        have h_swap_meas : AEMeasurable
            (fun xy : (Fin n → ℝ) × (Fin n → ℝ) =>
              (‖f xy.1‖₊ : ℝ≥0∞)^p.toReal * ‖g (xy.2 - xy.1)‖₊^q.toReal)
            (volume.prod volume) := by
          apply AEMeasurable.mul
          · exact (hf.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
              Measure.quasiMeasurePreserving_fst).pow_const _
          · have h_shear : MeasurePreserving
                (fun xy : (Fin n → ℝ) × (Fin n → ℝ) => (xy.2 - xy.1, xy.1))
                (volume.prod volume) (volume.prod volume) := by
              haveI : SFinite (volume : Measure (Fin n → ℝ)) := inferInstance
              have h_swap :
                MeasurePreserving Prod.swap (volume.prod volume) (volume.prod volume) :=
                @Measure.measurePreserving_swap (Fin n → ℝ) (Fin n → ℝ) _ _ volume volume _ _
              have h_sub : MeasurePreserving
                  (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z.1 - z.2, z.2))
                  (volume.prod volume) (volume.prod volume) :=
                measurePreserving_sub_prod (μ := volume) (ν := volume)
              exact h_sub.comp h_swap
            have h_fst : AEMeasurable
                (fun xy : (Fin n → ℝ) × (Fin n → ℝ) => (‖g xy.1‖₊ : ℝ≥0∞)^q.toReal)
                (volume.prod volume) :=
              (hg.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
                Measure.quasiMeasurePreserving_fst).pow_const _
            have h_eq :
                (fun xy : (Fin n → ℝ) × (Fin n → ℝ) => (‖g (xy.2 - xy.1)‖₊ : ℝ≥0∞)^q.toReal) =
                (fun xy => (‖g xy.1‖₊ : ℝ≥0∞)^q.toReal) ∘ (fun xy => (xy.2 - xy.1, xy.1)) := by
              ext xy; simp
            rw [h_eq]
            exact h_fst.comp_quasiMeasurePreserving h_shear.quasiMeasurePreserving
        have h2 := lintegral_prod (μ := volume) (ν := volume)
          (f := fun xy : (Fin n → ℝ) × (Fin n → ℝ) =>
            (‖f xy.1‖₊ : ℝ≥0∞)^p.toReal * ‖g (xy.2 - xy.1)‖₊^q.toReal)
          h_swap_meas
        simp only at h1 h2
        have h_swap_eq :
            ∫⁻ xy : (Fin n → ℝ) × (Fin n → ℝ),
              (‖f xy.2‖₊ : ℝ≥0∞)^p.toReal * ‖g (xy.1 - xy.2)‖₊^q.toReal ∂(volume.prod volume) =
            ∫⁻ xy : (Fin n → ℝ) × (Fin n → ℝ),
              (‖f xy.1‖₊ : ℝ≥0∞)^p.toReal *
              ‖g (xy.2 - xy.1)‖₊^q.toReal ∂(volume.prod volume) := by
          have h_swap_pres :
            MeasurePreserving Prod.swap (volume.prod volume) (volume.prod volume) :=
            @Measure.measurePreserving_swap (Fin n → ℝ) (Fin n → ℝ) _ _ volume volume _ _
          rw [← h_swap_pres.lintegral_comp_emb MeasurableEquiv.prodComm.measurableEmbedding]
          apply lintegral_congr
          intro xy
          simp only [Prod.swap]
        rw [← h1, h_swap_eq, h2]
      have h_inner_const : ∀ y,
          ∫⁻ x, (‖f y‖₊ : ℝ≥0∞)^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume =
            (‖f y‖₊ : ℝ≥0∞)^p.toReal * ∫⁻ x, ‖g (x - y)‖₊^q.toReal ∂volume := by
        intro y
        have h_ne_top : (‖f y‖₊ : ℝ≥0∞)^p.toReal ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_nonneg (le_of_lt hp_pos_real) ENNReal.coe_ne_top
        rw [lintegral_const_mul' _ _ h_ne_top]
      have h_translate : ∀ y, ∫⁻ x, ‖g (x - y)‖₊^q.toReal ∂volume =
          ∫⁻ z, ‖g z‖₊^q.toReal ∂volume := by
        intro y
        exact lintegral_sub_right_eq_self (fun z => (‖g z‖₊ : ℝ≥0∞)^q.toReal) y
      have h_gq_int : ∫⁻ z, ‖g z‖₊^q.toReal ∂volume ≠ ⊤ := by
        have :=
          lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq_ne_zero hq_ne_top hg.eLpNorm_lt_top
        simp only [enorm_eq_nnnorm] at this
        exact ne_of_lt this
      have h_fubini :
          ∫⁻ x, ∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume ∂volume =
          (∫⁻ y, ‖f y‖₊^p.toReal ∂volume) * ∫⁻ z, ‖g z‖₊^q.toReal ∂volume := by
        calc ∫⁻ x, ∫⁻ y, (‖f y‖₊ : ℝ≥0∞)^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume ∂volume
            = ∫⁻ y, ∫⁻ x, (‖f y‖₊ : ℝ≥0∞)^p.toReal *
              ‖g (x - y)‖₊^q.toReal ∂volume ∂volume := h_tonelli
          _ = ∫⁻ y, (‖f y‖₊ : ℝ≥0∞)^p.toReal * ∫⁻ x, ‖g (x - y)‖₊^q.toReal ∂volume ∂volume := by
              apply lintegral_congr
              intro y
              exact h_inner_const y
          _ = ∫⁻ y, (‖f y‖₊ : ℝ≥0∞)^p.toReal * ∫⁻ z, ‖g z‖₊^q.toReal ∂volume ∂volume := by
              apply lintegral_congr
              intro y
              rw [h_translate y]
          _ = (∫⁻ y, (‖f y‖₊ : ℝ≥0∞)^p.toReal ∂volume) * ∫⁻ z, ‖g z‖₊^q.toReal ∂volume := by
              rw [lintegral_mul_const' _ _ h_gq_int]
      calc ∫⁻ x, ‖conv x‖ₑ^r.toReal ∂volume
          ≤ ∫⁻ x, (C x * A * B)^r.toReal ∂volume := by
            apply lintegral_mono
            intro x
            exact h_bound_r x
        _ = ∫⁻ x, (C x)^r.toReal * A^r.toReal * B^r.toReal ∂volume := by
            apply lintegral_congr
            intro x
            exact h_power_expand x
        _ = A^r.toReal * B^r.toReal * ∫⁻ x, (C x)^r.toReal ∂volume := by
            have h_const_factor : ∀ x, (C x)^r.toReal * A^r.toReal * B^r.toReal =
                A^r.toReal * B^r.toReal * (C x)^r.toReal := fun x => by ring
            simp_rw [h_const_factor]
            rw [lintegral_const_mul' _ _ hAB_ne_top]
        _ = A^r.toReal * B^r.toReal *
              ∫⁻ x, ∫⁻ y, ‖f y‖₊^p.toReal * ‖g (x - y)‖₊^q.toReal ∂volume ∂volume := by
            congr 1
            apply lintegral_congr
            intro x
            exact h_Cx_r x
        _ = A^r.toReal * B^r.toReal *
              ((∫⁻ y, ‖f y‖₊^p.toReal ∂volume) * ∫⁻ z, ‖g z‖₊^q.toReal ∂volume) := by
            rw [h_fubini]
    -- Rewrite in the form ‖f‖_p^p = ∫ |f|^p
    have h_fp_eq : ∫⁻ y, ‖f y‖₊^p.toReal ∂volume =
        (eLpNorm f p volume) ^ p.toReal := by
      rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top]
      rw [← ENNReal.rpow_mul]
      simp only [enorm_eq_nnnorm, one_div, inv_mul_cancel₀ (ne_of_gt hp_pos_real),
        ENNReal.rpow_one]
    have h_gq_eq : ∫⁻ z, ‖g z‖₊^q.toReal ∂volume =
        (eLpNorm g q volume) ^ q.toReal := by
      rw [eLpNorm_eq_lintegral_rpow_enorm hq_ne_zero hq_ne_top]
      rw [← ENNReal.rpow_mul]
      simp only [enorm_eq_nnnorm, one_div, inv_mul_cancel₀ (ne_of_gt hq_pos_real),
        ENNReal.rpow_one]
    have hp_le_r : p ≤ r := young_exponent_p_le_r hq hpqr
    have hq_le_r : q ≤ r := young_exponent_q_le_r hp hpqr
    have h_exp_p : r.toReal * (1 - p/r).toReal + p.toReal = r.toReal := by
      have h_pr_le_one : p / r ≤ 1 := by
        rw [ENNReal.div_le_iff (ne_of_gt hr_pos) hr_ne_top, one_mul]
        exact hp_le_r
      rw [ENNReal.toReal_sub_of_le h_pr_le_one (by simp)]
      rw [ENNReal.toReal_one, ENNReal.toReal_div]
      field_simp
      ring
    have h_exp_q : r.toReal * (1 - q/r).toReal + q.toReal = r.toReal := by
      have h_qr_le_one : q / r ≤ 1 := by
        rw [ENNReal.div_le_iff (ne_of_gt hr_pos) hr_ne_top, one_mul]
        exact hq_le_r
      rw [ENNReal.toReal_sub_of_le h_qr_le_one (by simp)]
      rw [ENNReal.toReal_one, ENNReal.toReal_div]
      field_simp
      ring
    have h_A_power : A^r.toReal * (eLpNorm f p volume)^p.toReal =
        (eLpNorm f p volume)^r.toReal := by
      simp only [A]
      -- (a ^ b) ^ c = a ^ (b * c)
      rw [← ENNReal.rpow_mul]
      -- a ^ (b * c) * a ^ d = a ^ (b * c + d)
      rw [← ENNReal.rpow_add_of_nonneg _ _]
      · congr 1
        -- (1 - p/r).toReal * r.toReal + p.toReal = r.toReal
        have h_pr_le_one : p / r ≤ 1 := by
          rw [ENNReal.div_le_iff (ne_of_gt hr_pos) hr_ne_top, one_mul]
          exact hp_le_r
        rw [ENNReal.toReal_sub_of_le h_pr_le_one (by simp)]
        rw [ENNReal.toReal_one, ENNReal.toReal_div]
        field_simp
        ring
      · apply mul_nonneg
        · rw [ENNReal.toReal_sub_of_le]
          · simp only [ENNReal.toReal_one]
            have h_pr_toReal_le_one : (p / r).toReal ≤ 1 := by
              rw [ENNReal.toReal_div]
              have h_p_le_r_real : p.toReal ≤ r.toReal :=
                ENNReal.toReal_le_toReal hp_ne_top hr_ne_top |>.mpr hp_le_r
              exact div_le_one_of_le₀ h_p_le_r_real (le_of_lt hr_pos_real)
            linarith
          · rw [ENNReal.div_le_iff (ne_of_gt hr_pos) hr_ne_top, one_mul]
            exact hp_le_r
          · simp
        · exact le_of_lt hr_pos_real
      · exact le_of_lt hp_pos_real
    have h_B_power : B^r.toReal * (eLpNorm g q volume)^q.toReal =
        (eLpNorm g q volume)^r.toReal := by
      simp only [B]
      rw [← ENNReal.rpow_mul]
      rw [← ENNReal.rpow_add_of_nonneg _ _]
      · congr 1
        have h_qr_le_one : q / r ≤ 1 := by
          rw [ENNReal.div_le_iff (ne_of_gt hr_pos) hr_ne_top, one_mul]
          exact hq_le_r
        rw [ENNReal.toReal_sub_of_le h_qr_le_one (by simp)]
        rw [ENNReal.toReal_one, ENNReal.toReal_div]
        field_simp
        ring
      · apply mul_nonneg
        · rw [ENNReal.toReal_sub_of_le]
          · simp only [ENNReal.toReal_one]
            have h_qr_toReal_le_one : (q / r).toReal ≤ 1 := by
              rw [ENNReal.toReal_div]
              have h_q_le_r_real : q.toReal ≤ r.toReal :=
                ENNReal.toReal_le_toReal hq_ne_top hr_ne_top |>.mpr hq_le_r
              exact div_le_one_of_le₀ h_q_le_r_real (le_of_lt hr_pos_real)
            linarith
          · rw [ENNReal.div_le_iff (ne_of_gt hr_pos) hr_ne_top, one_mul]
            exact hq_le_r
          · simp
        · exact le_of_lt hr_pos_real
      · exact le_of_lt hq_pos_real
    have h_final_bound : A^r.toReal * B^r.toReal *
        ((eLpNorm f p volume) ^ p.toReal * (eLpNorm g q volume) ^ q.toReal) =
        (eLpNorm f p volume * eLpNorm g q volume) ^ r.toReal := by
      calc A^r.toReal * B^r.toReal *
          ((eLpNorm f p volume) ^ p.toReal * (eLpNorm g q volume) ^ q.toReal)
          = (A^r.toReal * (eLpNorm f p volume)^p.toReal) *
            (B^r.toReal * (eLpNorm g q volume)^q.toReal) := by ring
        _ = (eLpNorm f p volume)^r.toReal * (eLpNorm g q volume)^r.toReal := by
            rw [h_A_power, h_B_power]
        _ = (eLpNorm f p volume * eLpNorm g q volume) ^ r.toReal := by
            rw [← ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hr_pos_real)]
    calc (∫⁻ x, ‖conv x‖ₑ^r.toReal ∂volume)^r.toReal⁻¹
        ≤ (A^r.toReal * B^r.toReal *
            ((∫⁻ y, ‖f y‖₊^p.toReal ∂volume) * ∫⁻ z, ‖g z‖₊^q.toReal ∂volume))^r.toReal⁻¹ := by
          apply ENNReal.rpow_le_rpow h_lintegral_bound
          exact le_of_lt (inv_pos_of_pos hr_pos_real)
      _ = (A^r.toReal * B^r.toReal *
            ((eLpNorm f p volume) ^ p.toReal * (eLpNorm g q volume) ^ q.toReal))^r.toReal⁻¹ := by
          rw [h_fp_eq, h_gq_eq]
      _ = ((eLpNorm f p volume * eLpNorm g q volume) ^ r.toReal)^r.toReal⁻¹ := by
          rw [h_final_bound]
      _ = eLpNorm f p volume * eLpNorm g q volume := by
          rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (ne_of_gt hr_pos_real), ENNReal.rpow_one]
end Newton
