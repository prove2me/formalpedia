-- Prove2me | solution 1 for ModernConvex.Relaxations.opt_ge_asin_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T19:47:36.215601+00:00
-- url     : https://prove2.me/submissions/0aea93aa-7a38-42ca-9fec-756390258edf

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open MeasureTheory ProbabilityTheory Real Set

noncomputable def g72mnb_sg (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

lemma g72mnb_sg_meas : Measurable g72mnb_sg := by
  unfold g72mnb_sg
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
    measurable_const

lemma g72mnb_sg_abs (t : ℝ) : |g72mnb_sg t| = 1 := by
  unfold g72mnb_sg; split_ifs <;> simp

lemma g72mnb_sg_sq (t : ℝ) : g72mnb_sg t * g72mnb_sg t = 1 := by
  unfold g72mnb_sg; split_ifs <;> norm_num

lemma g72mnb_piece (f : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (h : ∀ x ∈ Ioo a b, f x = c) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = (b - a) * c := by
  have hI : IntegrableOn f (Ioo a b) := by
    refine (continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
      (fun x hx => (h x hx).symm) measurableSet_Ioo
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hI, ?_⟩
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo h, setIntegral_const]
  simp [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]

lemma g72mnb_angle (φ : ℝ) (h0 : 0 ≤ φ) (hπ : φ ≤ π) :
    ∫ θ in (-π)..π, g72mnb_sg (cos θ) * g72mnb_sg (cos (θ - φ)) = 2 * π - 4 * φ := by
  set f := fun θ => g72mnb_sg (cos θ) * g72mnb_sg (cos (θ - φ)) with hf
  have hper : Function.Periodic f (2 * π) := by
    intro θ; simp only [hf]
    rw [cos_add_two_pi, show θ + 2 * π - φ = (θ - φ) + 2 * π by ring, cos_add_two_pi]
  have e1 : ∫ θ in (-π)..π, f θ = ∫ θ in (-(π / 2))..(-(π / 2) + 2 * π), f θ := by
    have := hper.intervalIntegral_add_eq (-π) (-(π / 2))
    rw [show -π + 2 * π = π by ring] at this; exact this
  have pos : ∀ x, x ∈ Ioo (-(π / 2)) (π / 2) → g72mnb_sg (cos x) = 1 := fun x hx => by
    unfold g72mnb_sg; rw [if_pos (cos_pos_of_mem_Ioo hx).le]
  have neg : ∀ x, x - π ∈ Ioo (-(π / 2)) (π / 2) → g72mnb_sg (cos x) = -1 := fun x hx => by
    have := cos_pos_of_mem_Ioo hx; rw [cos_sub_pi] at this
    unfold g72mnb_sg; rw [if_neg (by linarith)]
  have neg' : ∀ x, x + π ∈ Ioo (-(π / 2)) (π / 2) → g72mnb_sg (cos x) = -1 := fun x hx => by
    have := cos_pos_of_mem_Ioo hx; rw [cos_add_pi] at this
    unfold g72mnb_sg; rw [if_neg (by linarith)]
  obtain ⟨i1, v1⟩ := g72mnb_piece f (-(π / 2)) (φ - π / 2) (-1) (by linarith) (fun x hx => by
    simp only [hf]
    rw [pos x ⟨hx.1, by linarith [hx.2]⟩, neg' (x - φ) ⟨by linarith [hx.1], by linarith [hx.2]⟩]
    ring)
  obtain ⟨i2, v2⟩ := g72mnb_piece f (φ - π / 2) (π / 2) 1 (by linarith) (fun x hx => by
    simp only [hf]
    rw [pos x ⟨by linarith [hx.1], hx.2⟩, pos (x - φ) ⟨by linarith [hx.1], by linarith [hx.2]⟩]
    ring)
  obtain ⟨i3, v3⟩ := g72mnb_piece f (π / 2) (φ + π / 2) (-1) (by linarith) (fun x hx => by
    simp only [hf]
    rw [neg x ⟨by linarith [hx.1], by linarith [hx.2]⟩,
      pos (x - φ) ⟨by linarith [hx.1], by linarith [hx.2]⟩]
    ring)
  obtain ⟨i4, v4⟩ := g72mnb_piece f (φ + π / 2) (-(π / 2) + 2 * π) 1 (by linarith) (fun x hx => by
    simp only [hf]
    rw [neg x ⟨by linarith [hx.1], by linarith [hx.2]⟩,
      neg (x - φ) ⟨by linarith [hx.1], by linarith [hx.2]⟩]
    ring)
  rw [e1, ← intervalIntegral.integral_add_adjacent_intervals i1 (i2.trans (i3.trans i4)),
    ← intervalIntegral.integral_add_adjacent_intervals i2 (i3.trans i4),
    ← intervalIntegral.integral_add_adjacent_intervals i3 i4, v1, v2, v3, v4]
  ring

noncomputable def g72mnb_phi (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

lemma g72mnb_phi_mul (a b : ℝ) :
    g72mnb_phi a * g72mnb_phi b = (2 * π)⁻¹ * exp (-(a ^ 2 + b ^ 2) / 2) := by
  simp only [g72mnb_phi, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  calc _ = ((√(2 * π))⁻¹ * (√(2 * π))⁻¹) * (exp (-a ^ 2 / 2) * exp (-b ^ 2 / 2)) := by ring
    _ = _ := by rw [this, ← exp_add]; ring_nf

lemma g72mnb_polar (F : ℝ × ℝ → ℝ) (Θ : ℝ → ℝ)
    (hF : ∀ r θ, 0 < r → F (r * cos θ, r * sin θ) = Θ θ) :
    ∫ p : ℝ × ℝ, F p * (g72mnb_phi p.1 * g72mnb_phi p.2) =
      (∫ r in Ioi (0 : ℝ), r * ((2 * π)⁻¹ * exp (-(r ^ 2) / 2))) * ∫ θ in Ioo (-π) π, Θ θ := by
  rw [← integral_comp_polarCoord_symm, polarCoord_target,
    show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, ← setIntegral_prod_mul]
  refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) (fun p hp => ?_)
  obtain ⟨r, θ⟩ := p
  simp only [polarCoord_symm_apply, smul_eq_mul]
  rw [hF r θ hp.1, g72mnb_phi_mul]
  have : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by nlinarith [sin_sq_add_cos_sq θ]
  rw [this]; ring

lemma g72mnb_R : (∫ r in Ioi (0 : ℝ), r * ((2 * π)⁻¹ * exp (-(r ^ 2) / 2))) * (2 * π) = 1 := by
  have h := g72mnb_polar (fun _ => 1) (fun _ => 1) (fun _ _ _ => rfl)
  have h1 : ∫ p : ℝ × ℝ, (fun _ => (1 : ℝ)) p * (g72mnb_phi p.1 * g72mnb_phi p.2) = 1 := by
    simp only [one_mul]
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl, integral_prod_mul]
    have : ∫ x, g72mnb_phi x = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero
    rw [this]; norm_num
  rw [h1, setIntegral_const] at h
  have h2 : volume.real (Ioo (-π) π) = 2 * π := by
    simp [Measure.real, Real.volume_Ioo]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [h2, smul_eq_mul, mul_one] at h
  exact h.symm

lemma g72mnb_2d (φ : ℝ) (h0 : 0 ≤ φ) (hπ : φ ≤ π) :
    ∫ p : ℝ × ℝ, g72mnb_sg p.1 * g72mnb_sg (cos φ * p.1 + sin φ * p.2) *
      (g72mnb_phi p.1 * g72mnb_phi p.2) = 1 - 2 * φ / π := by
  rw [g72mnb_polar _ (fun θ => g72mnb_sg (cos θ) * g72mnb_sg (cos (θ - φ)))]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
      g72mnb_angle φ h0 hπ]
    have hR := g72mnb_R
    have hpi := pi_pos
    set R := ∫ r in Ioi (0 : ℝ), r * ((2 * π)⁻¹ * exp (-(r ^ 2) / 2))
    have : R = 1 / (2 * π) := by field_simp; linarith
    rw [this]; field_simp; ring
  · intro r θ hr
    simp only
    have e : cos φ * (r * cos θ) + sin φ * (r * sin θ) = r * cos (θ - φ) := by
      rw [cos_sub]; ring
    rw [e]
    unfold g72mnb_sg
    simp only [mul_nonneg_iff_of_pos_left hr]

open Matrix

lemma g72mnb_prod_gauss (f : ℝ × ℝ → ℝ) (hf : Measurable f) (hb : ∀ p, |f p| ≤ 1) :
    ∫ p, f p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ p : ℝ × ℝ, f p * (g72mnb_phi p.1 * g72mnb_phi p.2) := by
  have hφm : Measurable g72mnb_phi := measurable_gaussianPDFReal 0 1
  have hφi : Integrable g72mnb_phi := integrable_gaussianPDFReal 0 1
  have hφ0 : ∀ x, 0 ≤ g72mnb_phi x := fun x => gaussianPDFReal_nonneg 0 1 x
  have hI1 : Integrable f ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    Integrable.mono' (integrable_const 1) hf.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hb p)
  have hI2 : Integrable (fun p : ℝ × ℝ => f p * (g72mnb_phi p.1 * g72mnb_phi p.2))
      ((volume : Measure ℝ).prod volume) := by
    refine Integrable.mono' (hφi.mul_prod hφi)
      (hf.mul ((hφm.comp measurable_fst).mul (hφm.comp measurable_snd))).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hφ0 _) (hφ0 _))]
    exact mul_le_of_le_one_left (mul_nonneg (hφ0 _) (hφ0 _)) (hb p)
  rw [integral_prod _ hI1, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    integral_prod _ hI2, integral_gaussianReal_eq_integral_smul one_ne_zero]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul]
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, g72mnb_phi]; ring

noncomputable def g72mnb_L {n : ℕ} (u v : Fin n → ℝ) (x : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![u ⬝ᵥ x, v ⬝ᵥ x]

noncomputable def g72mnb_M (c s : ℝ) (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![p.1, c * p.1 + s * p.2]

lemma g72mnb_inner2 (a b : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2)) t = a * t 0 + b * t 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

lemma g72mnb_L_meas {n : ℕ} (u v : Fin n → ℝ) : Measurable (g72mnb_L u v) := by
  unfold g72mnb_L; fun_prop

lemma g72mnb_M_meas (c s : ℝ) : Measurable (g72mnb_M c s) := by
  unfold g72mnb_M; fun_prop

lemma g72mnb_cf_L {n : ℕ} (u v : Fin n → ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    charFun ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map (g72mnb_L u v)) t =
      Complex.exp (-((∑ i, (t 0 * u i + t 1 * v i) ^ 2 : ℝ) : ℂ) / 2) := by
  set w : Fin n → ℝ := fun i => t 0 * u i + t 1 * v i
  have h1 : charFun ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map (g72mnb_L u v)) t =
      charFun ((Measure.pi fun _ : Fin n => gaussianReal 0 1).map (WithLp.toLp 2))
        (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n)) := by
    rw [charFun_apply, charFun_apply, integral_map (g72mnb_L_meas u v).aemeasurable (by fun_prop),
      integral_map (by fun_prop) (by fun_prop)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    congr 3
    rw [g72mnb_L, g72mnb_inner2]
    simp [PiLp.inner_apply, w, dotProduct, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h1, charFun_pi]
  simp only [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp [w, Finset.sum_neg_distrib]
  rw [neg_div, Finset.sum_div]

lemma g72mnb_cf_M (c s : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    charFun (((gaussianReal 0 1).prod (gaussianReal 0 1)).map (g72mnb_M c s)) t =
      Complex.exp (-(((t 0 + t 1 * c) ^ 2 + (t 1 * s) ^ 2 : ℝ) : ℂ) / 2) := by
  rw [charFun_apply, integral_map (g72mnb_M_meas c s).aemeasurable (by fun_prop)]
  have h : ∀ p : ℝ × ℝ, Complex.exp (inner ℝ (g72mnb_M c s p) t * Complex.I) =
      Complex.exp (((t 0 + t 1 * c : ℝ) : ℂ) * p.1 * Complex.I) *
        Complex.exp (((t 1 * s : ℝ) : ℂ) * p.2 * Complex.I) := by
    intro p
    rw [← Complex.exp_add, g72mnb_M, g72mnb_inner2]
    congr 1; push_cast; ring
  simp_rw [h]
  rw [integral_prod_mul (f := fun x : ℝ => Complex.exp (((t 0 + t 1 * c : ℝ) : ℂ) * x * Complex.I))
    (g := fun y : ℝ => Complex.exp (((t 1 * s : ℝ) : ℂ) * y * Complex.I)),
    ← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma g72mnb_law {n : ℕ} (u v : Fin n → ℝ) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (c s : ℝ)
    (hc : u ⬝ᵥ v = c) (hcs : c ^ 2 + s ^ 2 = 1) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).map (g72mnb_L u v) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (g72mnb_M c s) := by
  haveI := Measure.isProbabilityMeasure_map (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1)
    (g72mnb_L_meas u v).aemeasurable
  haveI := Measure.isProbabilityMeasure_map (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
    (g72mnb_M_meas c s).aemeasurable
  apply Measure.ext_of_charFun
  funext t
  rw [g72mnb_cf_L, g72mnb_cf_M]
  have e : ∑ i, (t 0 * u i + t 1 * v i) ^ 2 =
      t 0 ^ 2 * (u ⬝ᵥ u) + 2 * t 0 * t 1 * (u ⬝ᵥ v) + t 1 ^ 2 * (v ⬝ᵥ v) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (t 0 * u i + t 1 * v i) ^ 2 = (t 0 + t 1 * c) ^ 2 + (t 1 * s) ^ 2 := by
    rw [e, hu, hv, hc]
    linear_combination (-(t 1) ^ 2) * hcs
  rw [e2]

lemma g72mnb_cs {n : ℕ} (u v : Fin n → ℝ) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) :
    -1 ≤ u ⬝ᵥ v ∧ u ⬝ᵥ v ≤ 1 := by
  have a : 0 ≤ ∑ i, (u i - v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have b : 0 ≤ ∑ i, (u i + v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have ea : ∑ i, (u i - v i) ^ 2 = u ⬝ᵥ u - 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have eb : ∑ i, (u i + v i) ^ 2 = u ⬝ᵥ u + 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  constructor <;> nlinarith

lemma g72mnb_ident {n : ℕ} (u v : Fin n → ℝ) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) :
    ∫ x, g72mnb_sg (u ⬝ᵥ x) * g72mnb_sg (v ⬝ᵥ x) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      2 / π * arcsin (u ⬝ᵥ v) := by
  obtain ⟨h1, h2⟩ := g72mnb_cs u v hu hv
  set φ := arccos (u ⬝ᵥ v) with hφ
  have hc : cos φ = u ⬝ᵥ v := cos_arccos h1 h2
  have hcs : cos φ ^ 2 + sin φ ^ 2 = 1 := by rw [add_comm]; exact sin_sq_add_cos_sq φ
  let G : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => g72mnb_sg (z 0) * g72mnb_sg (z 1)
  have hG : Measurable G :=
    (g72mnb_sg_meas.comp (by fun_prop)).mul (g72mnb_sg_meas.comp (by fun_prop))
  have step1 : ∫ x, g72mnb_sg (u ⬝ᵥ x) * g72mnb_sg (v ⬝ᵥ x)
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      ∫ z, G z ∂((Measure.pi fun _ : Fin n => gaussianReal 0 1).map (g72mnb_L u v)) := by
    rw [integral_map (g72mnb_L_meas u v).aemeasurable hG.aestronglyMeasurable]
    simp [G, g72mnb_L]
  rw [step1, g72mnb_law u v hu hv (cos φ) (sin φ) hc.symm hcs,
    integral_map (g72mnb_M_meas _ _).aemeasurable hG.aestronglyMeasurable]
  have e : (fun p => G (g72mnb_M (cos φ) (sin φ) p)) =
      fun p : ℝ × ℝ => g72mnb_sg p.1 * g72mnb_sg (cos φ * p.1 + sin φ * p.2) := by
    funext p; simp [G, g72mnb_M]
  rw [e, g72mnb_prod_gauss _ (by
      exact (g72mnb_sg_meas.comp measurable_fst).mul (g72mnb_sg_meas.comp (by fun_prop)))
      (fun p => by rw [abs_mul, g72mnb_sg_abs, g72mnb_sg_abs]; norm_num),
    g72mnb_2d φ (arccos_nonneg _) (arccos_le_pi _), arcsin_eq_pi_div_two_sub_arccos, ← hφ]
  have := pi_pos
  field_simp

open ModernConvex.Relaxations

open scoped MatrixOrder

lemma g72mnb_herm_T {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) : Mᵀ = M := by
  have := hM.eq
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma g72mnb_factor {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (hd : ∀ i, X i i = 1) :
    ∃ b : Fin n → Fin n → ℝ, (∀ i, b i ⬝ᵥ b i = 1) ∧ ∀ i j, X i j = b i ⬝ᵥ b j := by
  set S := CFC.sqrt X with hSdef
  have hSS : S * S = X := CFC.sqrt_mul_sqrt_self X hX.nonneg
  have hSpsd : S.PosSemidef := (CFC.sqrt_nonneg X).posSemidef
  have hST : Sᵀ = S := g72mnb_herm_T hSpsd.1
  have key : ∀ i j, X i j = (fun k => S k i) ⬝ᵥ (fun k => S k j) := by
    intro i j
    rw [← hSS, mul_apply, dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : S k i = S i k := by
      have := congrFun (congrFun hST i) k; simpa [transpose_apply] using this
    rw [this]
  exact ⟨fun i k => S k i, fun i => by rw [← key, hd], key⟩

lemma g72mnb_sg_int {n : ℕ} (u v : Fin n → ℝ) :
    Integrable (fun x => g72mnb_sg (u ⬝ᵥ x) * g72mnb_sg (v ⬝ᵥ x))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_const 1)
    ((g72mnb_sg_meas.comp (by fun_prop)).mul (g72mnb_sg_meas.comp (by fun_prop))).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, g72mnb_sg_abs, g72mnb_sg_abs]; norm_num

lemma g72mnb_part1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (OPT : ℝ)
    (hOPT : IsSignQPValue A OPT) (X : Matrix (Fin n) (Fin n) ℝ) (hX : IsUnitDiagPSD X) :
    2 / π * ∑ i, ∑ j, A i j * arcsin (X i j) ≤ OPT := by
  obtain ⟨b, hb1, hbX⟩ := g72mnb_factor X hX.1 hX.2
  set μ := Measure.pi fun _ : Fin n => gaussianReal 0 1 with hμ
  let s : (Fin n → ℝ) → Fin n → ℝ := fun x i => g72mnb_sg (b i ⬝ᵥ x)
  have hs : ∀ x, s x ∈ signVectors n := fun x i => by
    show g72mnb_sg _ = 1 ∨ g72mnb_sg _ = -1
    unfold g72mnb_sg; split_ifs <;> simp
  have hle : ∀ x, s x ⬝ᵥ (A *ᵥ s x) ≤ OPT := fun x => hOPT.1 ⟨s x, hs x, rfl⟩
  have hexp : ∀ x, s x ⬝ᵥ (A *ᵥ s x) =
      ∑ i, ∑ j, A i j * (g72mnb_sg (b i ⬝ᵥ x) * g72mnb_sg (b j ⬝ᵥ x)) := by
    intro x
    simp only [dotProduct, mulVec, Finset.mul_sum, s]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hint : ∀ i j, Integrable (fun x => g72mnb_sg (b i ⬝ᵥ x) * g72mnb_sg (b j ⬝ᵥ x)) μ :=
    fun i j => g72mnb_sg_int (b i) (b j)
  calc 2 / π * ∑ i, ∑ j, A i j * arcsin (X i j)
      = ∑ i, ∑ j, A i j * ∫ x, g72mnb_sg (b i ⬝ᵥ x) * g72mnb_sg (b j ⬝ᵥ x) ∂μ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hμ, g72mnb_ident (b i) (b j) (hb1 i) (hb1 j), hbX]; ring
    _ = ∫ x, ∑ i, ∑ j, A i j * (g72mnb_sg (b i ⬝ᵥ x) * g72mnb_sg (b j ⬝ᵥ x)) ∂μ := by
        symm
        rw [integral_finset_sum _ (fun i _ => ?_)]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finset_sum _ (fun j _ => ?_)]
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [integral_const_mul]
          · exact (hint i j).const_mul _
        · exact integrable_finset_sum _ fun j _ => (hint i j).const_mul _
    _ ≤ ∫ _x, OPT ∂μ := by
        refine integral_mono (integrable_finset_sum _ fun i _ => integrable_finset_sum _
          fun j _ => (hint i j).const_mul _) (integrable_const _) fun x => ?_
        rw [← hexp]; exact hle x
    _ = OPT := by simp

lemma g72mnb_K_closed {n : ℕ} : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | IsUnitDiagPSD X} := by
  have hK : {X : Matrix (Fin n) (Fin n) ℝ | IsUnitDiagPSD X} =
      ({X | Xᵀ = X} ∩ ⋂ v : Fin n → ℝ, {X | 0 ≤ v ⬝ᵥ (X *ᵥ v)}) ∩ ⋂ i, {X | X i i = 1} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, IsUnitDiagPSD,
      posSemidef_iff_dotProduct_mulVec, IsHermitian, conjTranspose_eq_transpose_of_trivial,
      star_trivial]
  rw [hK]
  refine ((isClosed_eq (by fun_prop) continuous_id).inter
    (isClosed_iInter fun v => isClosed_le continuous_const (by fun_prop))).inter
    (isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const)

lemma g72mnb_K_compact {n : ℕ} : IsCompact {X : Matrix (Fin n) (Fin n) ℝ | IsUnitDiagPSD X} := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset g72mnb_K_closed ?_
  intro X hX
  obtain ⟨b, hb1, hbX⟩ := g72mnb_factor X hX.1 hX.2
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i j
  rw [hbX]; exact g72mnb_cs (b i) (b j) (hb1 i) (hb1 j)

theorem g72mnb_main {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (OPT : ℝ) (hOPT : IsSignQPValue A OPT) :
    (∀ X : Matrix (Fin n) (Fin n) ℝ, IsUnitDiagPSD X →
        2 / Real.pi * ∑ i, ∑ j, A i j * Real.arcsin (X i j) ≤ OPT) ∧
      ∃ M : ℝ, IsGreatest ((fun X => (A * asinMatrix X).trace) '' {X | IsUnitDiagPSD X}) M ∧
        2 / Real.pi * M ≤ OPT := by
  refine ⟨fun X hX => g72mnb_part1 A OPT hOPT X hX, ?_⟩
  have hf : ∀ X : Matrix (Fin n) (Fin n) ℝ,
      (A * asinMatrix X).trace = ∑ i, ∑ j, A i j * arcsin (X j i) := by
    intro X; simp [Matrix.trace, mul_apply, asinMatrix]
  have hcont : Continuous fun X : Matrix (Fin n) (Fin n) ℝ => (A * asinMatrix X).trace := by
    simp_rw [hf]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      continuous_const.mul (Real.continuous_arcsin.comp ?_)
    exact (continuous_apply i).comp (continuous_apply j)
  have hne : ({X | IsUnitDiagPSD X} : Set (Matrix (Fin n) (Fin n) ℝ)).Nonempty :=
    ⟨1, PosSemidef.one, fun i => by simp⟩
  obtain ⟨X0, hX0, hmax⟩ := g72mnb_K_compact.exists_isMaxOn hne hcont.continuousOn
  refine ⟨(A * asinMatrix X0).trace, ⟨⟨X0, hX0, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨X, hX, rfl⟩; exact hmax hX
  · rw [hf]
    have hsym : ∀ i j, X0 j i = X0 i j := by
      intro i j
      have := congrFun (congrFun (g72mnb_herm_T hX0.1.1) i) j
      simpa [transpose_apply] using this
    simp_rw [hsym]
    exact g72mnb_part1 A OPT hOPT X0 hX0

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (OPT : ℝ) (hOPT : IsSignQPValue A OPT) :
    (∀ X : Matrix (Fin n) (Fin n) ℝ, IsUnitDiagPSD X →
        2 / Real.pi * ∑ i, ∑ j, A i j * Real.arcsin (X i j) ≤ OPT) ∧
      ∃ M : ℝ, IsGreatest ((fun X => (A * asinMatrix X).trace) '' {X | IsUnitDiagPSD X}) M ∧
        2 / Real.pi * M ≤ OPT :=
  g72mnb_main A hA OPT hOPT
