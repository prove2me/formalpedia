-- Prove2me | solution 1 for NymanBeurling.damped_spectral_vanishing_of_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T04:33:08.913745+00:00
-- url     : https://prove2.me/submissions/65ef676f-b1fb-4eb4-8285-b0586d981ec7

import Mathlib
import Definitions.Def_NymanBeurling_DampedMellinFrontiers
import Definitions.Def_NymanBeurling_DampedResidualLimits
import Theorems.Thm_GuthMaynard_mu_half_le_twentyseven_div_onesixtyfour

set_option autoImplicit false

open MeasureTheory Filter Topology Complex

namespace DampedSpectralAux

lemma continuous_zeta_comp (f : ℝ → ℂ) (hf : Continuous f) (h1 : ∀ t, f t ≠ 1) :
    Continuous (fun t => riemannZeta (f t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact ((differentiableAt_riemannZeta (h1 t)).continuousAt).comp hf.continuousAt

lemma line_ne_one (t c : ℝ) (hc : c ≠ 1/2) : (1/2:ℂ) - (t:ℂ)*I + (c:ℂ) ≠ 1 := by
  intro h
  apply hc
  have := congrArg Complex.re h
  simp at this
  linarith

lemma continuous_zeta_line (c : ℝ) (hc : c ≠ 1/2) :
    Continuous (fun t : ℝ => riemannZeta ((1/2:ℂ) - (t:ℂ)*I + (c:ℂ))) :=
  continuous_zeta_comp _ (by fun_prop) (fun t => line_ne_one t c hc)

lemma continuous_zeta_line0 :
    Continuous (fun t : ℝ => riemannZeta ((1/2:ℂ) - (t:ℂ)*I)) := by
  have := continuous_zeta_line 0 (by norm_num)
  simpa using this

lemma norm_line_ge (t : ℝ) : (1 + |t|)/4 ≤ ‖(1/2:ℂ) - (t:ℂ)*I‖ := by
  have h1 := Complex.abs_re_le_norm ((1/2:ℂ) - (t:ℂ)*I)
  have h2 := Complex.abs_im_le_norm ((1/2:ℂ) - (t:ℂ)*I)
  have hre : ((1/2:ℂ) - (t:ℂ)*I).re = 1/2 := by simp
  have him : ((1/2:ℂ) - (t:ℂ)*I).im = -t := by simp
  rw [hre] at h1
  rw [him, abs_neg] at h2
  have : |(1/2:ℝ)| = 1/2 := by norm_num
  linarith

lemma rpow_aux {x : ℝ} (hx : 0 < x) : (x^(1/4:ℝ))^2 / x^2 = x^(-(3/2:ℝ)) := by
  rw [← Real.rpow_natCast (x^(1/4:ℝ)) 2, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x 2,
    ← Real.rpow_sub hx]
  norm_num

lemma sq_norm_div_le (w s : ℂ) (x K : ℝ) (hx : 0 < x) (_hK : 0 ≤ K)
    (hs : x/4 ≤ ‖s‖) (hw : ‖w‖ ≤ K * x^(1/4:ℝ)) :
    ‖w / s‖^2 ≤ 16 * K^2 * x^(-(3/2:ℝ)) := by
  have hx4 : 0 < x/4 := by positivity
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hx4 hs
  rw [norm_div, div_pow, ← rpow_aux hx]
  have hw2 : ‖w‖^2 ≤ (K * x^(1/4:ℝ))^2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hs2 : (x/4)^2 ≤ ‖s‖^2 := pow_le_pow_left₀ hx4.le hs 2
  rw [div_le_iff₀ (by positivity)]
  have hxne : x ≠ 0 := hx.ne'
  calc ‖w‖^2 ≤ (K * x^(1/4:ℝ))^2 := hw2
    _ = 16 * K^2 * ((x^(1/4:ℝ))^2 / x^2) * (x/4)^2 := by field_simp; ring
    _ ≤ 16 * K^2 * ((x^(1/4:ℝ))^2 / x^2) * ‖s‖^2 := by gcongr

lemma norm_zeta_line_eq (t : ℝ) :
    ‖riemannZeta ((1/2:ℂ) - (t:ℂ)*I)‖ = ‖riemannZeta ((1/2:ℂ) + ((|t|:ℝ):ℂ)*I)‖ := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have : (1/2:ℂ) - (t:ℂ)*I = (starRingEnd ℂ) ((1/2:ℂ) + (t:ℂ)*I) := by
      apply Complex.ext <;> simp
    rw [this, riemannZeta_conj, Complex.norm_conj]
  · rw [abs_of_neg ht]
    congr 2
    push_cast
    ring

/-- Growth of `ζ` on the critical line, from the platform's proved bound `μ(1/2) ≤ 27/164`. -/
lemma zeta_line_growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖riemannZeta ((1/2:ℂ) - (t:ℂ)*I)‖ ≤ C * (1 + |t|)^(1/4:ℝ) := by
  have hmu := GuthMaynard.mu_half_le_twentyseven_div_onesixtyfour
  have hlt : LindelofHypothesis.mu (1/2) < ((1/4:ℝ):EReal) :=
    lt_of_le_of_lt hmu (EReal.coe_lt_coe_iff.2 (by norm_num))
  unfold LindelofHypothesis.mu at hlt
  obtain ⟨_, ⟨a, ha, rfl⟩, hab⟩ := sInf_lt_iff.1 hlt
  have hab' : a < 1/4 := EReal.coe_lt_coe_iff.1 hab
  simp only [Set.mem_ofPred_eq] at ha
  obtain ⟨c, hc⟩ := ha.bound
  rw [eventually_atTop] at hc
  obtain ⟨T₀, hT₀⟩ := hc
  have hcont : Continuous (fun u : ℝ => riemannZeta ((1/2:ℂ) + (u:ℂ)*I)) := by
    refine continuous_zeta_comp _ (by fun_prop) (fun u h => ?_)
    have := congrArg Complex.re h
    norm_num at this
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := max T₀ 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨|c| + |M|, by positivity, fun t => ?_⟩
  rw [norm_zeta_line_eq]
  have hu : 0 ≤ |t| := abs_nonneg t
  have h1 : 1 ≤ (1 + |t|)^(1/4:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hcM : 0 ≤ |c| + |M| := by positivity
  rcases le_or_gt |t| (max T₀ 1) with h | h
  · have := hM |t| ⟨hu, h⟩
    calc _ ≤ M := this
      _ ≤ |M| := le_abs_self M
      _ ≤ (|c| + |M|) * 1 := by linarith [abs_nonneg c]
      _ ≤ _ := by gcongr
  · have hT : T₀ ≤ |t| := le_trans (le_max_left _ _) h.le
    have h1t : 1 ≤ |t| := le_trans (le_max_right _ _) h.le
    have := hT₀ |t| hT
    push_cast at this
    have hpow : ‖|t|^a‖ ≤ (1+|t|)^(1/4:ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu _)]
      calc |t|^a ≤ |t|^(1/4:ℝ) := Real.rpow_le_rpow_of_exponent_le h1t hab'.le
        _ ≤ (1+|t|)^(1/4:ℝ) := Real.rpow_le_rpow hu (by linarith) (by norm_num)
    calc _ ≤ c * ‖|t|^a‖ := this
      _ ≤ |c| * ‖|t|^a‖ := by gcongr; exact le_abs_self c
      _ ≤ |c| * (1+|t|)^(1/4:ℝ) := by gcongr
      _ ≤ _ := by gcongr; linarith [abs_nonneg M]

/-- The ordinates of zeros of `ζ` on the critical line form a countable set. -/
lemma countable_zeros_line : {t : ℝ | riemannZeta ((1/2:ℂ) - (t:ℂ)*I) = 0}.Countable := by
  have hZ : riemannZetaZeros.Countable :=
    IsLindelof.countable_of_isDiscrete
      (HereditarilyLindelofSpace.isHereditarilyLindelof_univ.isLindelof_subset
        (Set.subset_univ _)) isDiscrete_riemannZetaZeros
  have hinj : Function.Injective (fun t : ℝ => (1/2:ℂ) - (t:ℂ)*I) := by
    intro a b h
    have := congrArg Complex.im h
    simpa using this
  exact hZ.preimage hinj

lemma tendsto_inv_zeta_one_add :
    Tendsto (fun ε : ℝ => (riemannZeta (1 + (ε:ℂ)))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hmap : Tendsto (fun ε : ℝ => (1:ℂ) + (ε:ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun ε : ℝ => (1:ℂ) + (ε:ℂ)) (𝓝 0) (𝓝 (1 + ((0:ℝ):ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0:ℝ) < ε := hε
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
  have h1 := riemannZeta_residue_one.comp hmap
  have h2 : Tendsto (fun ε : ℝ => ((ε:ℂ) * riemannZeta (1 + (ε:ℂ)))⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have := h1.inv₀ one_ne_zero
    rw [inv_one] at this
    refine this.congr (fun ε => ?_)
    simp only [Function.comp, add_sub_cancel_left]
  have h3 : Tendsto (fun ε : ℝ => (ε:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ε : ℝ => (ε:ℂ)) (𝓝 0) (𝓝 ((0:ℝ):ℂ)) :=
      Complex.continuous_ofReal.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h4 := h3.mul h2
  rw [zero_mul] at h4
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (ε:ℂ) ≠ 0 := by
    have : (0:ℝ) < ε := hε
    exact_mod_cast this.ne'
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hε0, one_mul]

end DampedSpectralAux

open DampedSpectralAux in
theorem solution
    (hratio : NymanBeurling.ShiftedZetaRatioBound) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1/2 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      Integrable (fun t : ℝ => ‖NymanBeurling.dampedSpectralResidual ε t‖^2) ∧
      (∫ t : ℝ, ‖NymanBeurling.dampedSpectralResidual ε t‖^2) < δ := by
  obtain ⟨Cr, hCr0, hCr⟩ := hratio
  obtain ⟨Cz, hCz0, hCz⟩ := zeta_line_growth
  have hgi : Integrable (fun t : ℝ => (1 + |t|)^(-(3/2:ℝ))) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3/2) (by norm_num)
    simpa [Real.norm_eq_abs] using this
  have hKi := hgi.const_mul (32*(1+Cr)^2 + 32*Cz^2)
  -- the pointwise domination
  have hbound : ∀ ε : ℝ, 0 < ε → ε < 1/2 → ‖(riemannZeta (1 + (ε:ℂ)))⁻¹‖ ≤ 1 → ∀ t : ℝ,
      ‖NymanBeurling.dampedSpectralResidual ε t‖^2 ≤
        (32*(1+Cr)^2 + 32*Cz^2) * (1 + |t|)^(-(3/2:ℝ)) := by
    intro ε hε hε2 hv t
    have hx1 : (1:ℝ) ≤ 1 + |t| := le_add_of_nonneg_right (abs_nonneg t)
    have hx0 : (0:ℝ) < 1 + |t| := by linarith
    have hsx := norm_line_ge t
    have hA : ‖1 - riemannZeta ((1/2:ℂ) - (t:ℂ)*I) *
        (riemannZeta ((1/2:ℂ) - (t:ℂ)*I + (ε:ℂ)))⁻¹‖ ≤ (1 + Cr) * (1 + |t|)^(1/4:ℝ) := by
      have hr : ‖riemannZeta ((1/2:ℂ) - (t:ℂ)*I) / riemannZeta ((1/2:ℂ) - (t:ℂ)*I + (ε:ℂ))‖
          ≤ Cr * (1 + |t|)^(ε/2) := hCr ε hε hε2 t
      have hpow : (1 + |t|)^(ε/2) ≤ (1 + |t|)^(1/4:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have hq1 : 1 ≤ (1 + |t|)^(1/4:ℝ) := Real.one_le_rpow hx1 (by norm_num)
      calc _ ≤ ‖(1:ℂ)‖ + ‖riemannZeta ((1/2:ℂ) - (t:ℂ)*I) *
              (riemannZeta ((1/2:ℂ) - (t:ℂ)*I + (ε:ℂ)))⁻¹‖ := norm_sub_le _ _
        _ = 1 + ‖riemannZeta ((1/2:ℂ) - (t:ℂ)*I) /
              riemannZeta ((1/2:ℂ) - (t:ℂ)*I + (ε:ℂ))‖ := by rw [norm_one, ← div_eq_mul_inv]
        _ ≤ 1 + Cr * (1 + |t|)^(ε/2) := by linarith
        _ ≤ 1 + Cr * (1 + |t|)^(1/4:ℝ) := by gcongr
        _ ≤ (1 + Cr) * (1 + |t|)^(1/4:ℝ) := by nlinarith
    have hB : ‖riemannZeta ((1/2:ℂ) - (t:ℂ)*I) * (riemannZeta (1 + (ε:ℂ)))⁻¹‖ ≤
        Cz * (1 + |t|)^(1/4:ℝ) := by
      rw [norm_mul]
      calc _ ≤ ‖riemannZeta ((1/2:ℂ) - (t:ℂ)*I)‖ * 1 := by gcongr
        _ ≤ Cz * (1 + |t|)^(1/4:ℝ) := by rw [mul_one]; exact hCz t
    have hsplit : NymanBeurling.dampedSpectralResidual ε t =
        (1 - riemannZeta ((1/2:ℂ) - (t:ℂ)*I) *
          (riemannZeta ((1/2:ℂ) - (t:ℂ)*I + (ε:ℂ)))⁻¹) / ((1/2:ℂ) - (t:ℂ)*I) +
        (riemannZeta ((1/2:ℂ) - (t:ℂ)*I) * (riemannZeta (1 + (ε:ℂ)))⁻¹) /
          ((1/2:ℂ) - (t:ℂ)*I) := by
      simp only [NymanBeurling.dampedSpectralResidual]
      ring
    have e1 := sq_norm_div_le _ _ _ (1 + Cr) hx0 (by linarith) hsx hA
    have e2 := sq_norm_div_le _ _ _ Cz hx0 hCz0 hsx hB
    rw [hsplit]
    set A := (1 - riemannZeta ((1/2:ℂ) - (t:ℂ)*I) *
          (riemannZeta ((1/2:ℂ) - (t:ℂ)*I + (ε:ℂ)))⁻¹) / ((1/2:ℂ) - (t:ℂ)*I)
    set B := (riemannZeta ((1/2:ℂ) - (t:ℂ)*I) * (riemannZeta (1 + (ε:ℂ)))⁻¹) /
          ((1/2:ℂ) - (t:ℂ)*I)
    have htri : ‖A + B‖^2 ≤ 2*‖A‖^2 + 2*‖B‖^2 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le A B) 2
      nlinarith [sq_nonneg (‖A‖ - ‖B‖)]
    nlinarith
  -- measurability
  have hmeas : ∀ ε : ℝ, 0 < ε → ε < 1/2 → AEStronglyMeasurable
      (fun t : ℝ => ‖NymanBeurling.dampedSpectralResidual ε t‖^2) volume := by
    intro ε hε hε2
    have c1 := continuous_zeta_line0
    have c2 := continuous_zeta_line ε (by linarith)
    have m : Measurable (fun t : ℝ => NymanBeurling.dampedSpectralResidual ε t) := by
      have hs : Measurable (fun t : ℝ => (1/2:ℂ) - (t:ℂ)*I) := by fun_prop
      exact (measurable_const.sub (c1.measurable.mul
        (c2.measurable.inv.sub measurable_const))).div hs
    exact (m.norm.pow_const 2).aestronglyMeasurable
  -- eventual properties of the damping parameter
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε ∧ ε < 1/2 ∧ ‖(riemannZeta (1 + (ε:ℂ)))⁻¹‖ ≤ 1 := by
    have e1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
    have e2 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1/2 :=
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
    have e3 : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), ‖(riemannZeta (1 + (ε:ℂ)))⁻¹‖ ≤ 1 := by
      have := tendsto_inv_zeta_one_add.norm
      rw [norm_zero] at this
      exact this.eventually (ge_mem_nhds (show (0:ℝ) < 1 by norm_num))
    exact e1.and (e2.and e3)
  -- pointwise limit off the (countable) set of critical zeros
  have hlim : ∀ᵐ t ∂(volume : Measure ℝ),
      Tendsto (fun ε : ℝ => ‖NymanBeurling.dampedSpectralResidual ε t‖^2) (𝓝[>] 0) (𝓝 0) := by
    rw [ae_iff]
    refine measure_mono_null ?_ (countable_zeros_line.measure_zero volume)
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    by_contra hz
    apply ht
    have hs1 : (1/2:ℂ) - (t:ℂ)*I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    have hcont : ContinuousAt riemannZeta ((1/2:ℂ) - (t:ℂ)*I) :=
      (differentiableAt_riemannZeta hs1).continuousAt
    have h0 : Tendsto (fun ε : ℝ => (1/2:ℂ) - (t:ℂ)*I + (ε:ℂ)) (𝓝 0)
        (𝓝 ((1/2:ℂ) - (t:ℂ)*I)) := by
      have : Tendsto (fun ε : ℝ => (1/2:ℂ) - (t:ℂ)*I + (ε:ℂ)) (𝓝 0)
          (𝓝 ((1/2:ℂ) - (t:ℂ)*I + ((0:ℝ):ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this
    have hu : Tendsto (fun ε : ℝ => riemannZeta ((1/2:ℂ) - (t:ℂ)*I + (ε:ℂ))) (𝓝[>] 0)
        (𝓝 (riemannZeta ((1/2:ℂ) - (t:ℂ)*I))) :=
      (hcont.tendsto.comp h0).mono_left nhdsWithin_le_nhds
    have hF : Tendsto (fun ε : ℝ => NymanBeurling.dampedSpectralResidual ε t) (𝓝[>] 0)
        (𝓝 ((1 - riemannZeta ((1/2:ℂ) - (t:ℂ)*I) *
          ((riemannZeta ((1/2:ℂ) - (t:ℂ)*I))⁻¹ - 0)) / ((1/2:ℂ) - (t:ℂ)*I))) :=
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul
        ((hu.inv₀ hz).sub tendsto_inv_zeta_one_add))).div_const _
    rw [sub_zero, mul_inv_cancel₀ hz, sub_self, zero_div] at hF
    have := hF.norm.pow 2
    simpa using this
  -- dominated convergence
  have hT := tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => (32*(1+Cr)^2 + 32*Cz^2) * (1 + |t|)^(-(3/2:ℝ)))
    (hev.mono fun ε h => hmeas ε h.1 h.2.1)
    (hev.mono fun ε h => ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound ε h.1 h.2.1 h.2.2 t)
    hKi hlim
  rw [integral_zero] at hT
  have hev2 := hev.and (hT.eventually (gt_mem_nhds hδ))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev2
  have hu0 : (0:ℝ) < u := hu
  refine ⟨min u (1/2), lt_min hu0 (by norm_num), min_le_right _ _, fun ε hε hεu => ?_⟩
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hsub ⟨hε, lt_of_lt_of_le hεu (min_le_left _ _)⟩
  refine ⟨Integrable.mono' hKi (hmeas ε h1 h2) (ae_of_all _ fun t => ?_), h4⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hbound ε h1 h2 h3 t
