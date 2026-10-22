-- Prove2me | solution 1 for ModernConvex.MatrixCube.theta_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T19:18:05.122032+00:00
-- url     : https://prove2.me/submissions/01b5952e-877a-4820-9d70-b14a987eb03d

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

open Matrix MeasureTheory ProbabilityTheory
open ModernConvex.MatrixCube

noncomputable def g72mn_phi (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

lemma g72mn_phi_eq (x : ℝ) : g72mn_phi x = (2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / 2) := by
  simp only [g72mn_phi, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
  norm_num

lemma g72mn_density {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(∑ i, u i ^ 2) / 2) =
      ∏ i, g72mn_phi (u i) := by
  simp only [g72mn_phi_eq, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  · rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1; ring
  · rw [← Real.exp_sum]; congr 1
    simp only [neg_div, Finset.sum_div, Finset.sum_neg_distrib]

lemma g72mn_gd (k : ℕ) (u : Fin k → ℝ) : gaussDensity k u = ∏ i, g72mn_phi (u i) := by
  rw [gaussDensity, ← g72mn_density, Fintype.card_fin]

lemma g72mn_int_phi (f : ℝ → ℝ) : ∫ x, f x * g72mn_phi x = ∫ x, f x ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul, g72mn_phi]
  congr 1; funext x; ring

lemma g72mn_m0 : ∫ x, 1 * g72mn_phi x = 1 := by
  rw [g72mn_int_phi]; simp

lemma g72mn_m1 : ∫ x, x * g72mn_phi x = 0 := by
  rw [g72mn_int_phi]; exact integral_id_gaussianReal

lemma g72mn_m2 : ∫ x, x ^ 2 * g72mn_phi x = 1 := by
  rw [g72mn_int_phi]
  have h := variance_eq_integral (X := fun x : ℝ => x) (μ := gaussianReal 0 1) measurable_id.aemeasurable
  rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at h
  simp only [sub_zero] at h
  exact_mod_cast h.symm

lemma g72mn_phi_int_pow (m : ℕ) : Integrable (fun x : ℝ => x ^ m * g72mn_phi x) := by
  have := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (s := m)
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)).const_mul ((2 * Real.pi) ^ (-(1 : ℝ) / 2))
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only [g72mn_phi_eq, Real.rpow_natCast]
  rw [show -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 by ring]
  ring

lemma g72mn_pair {n : ℕ} (i j : Fin n) :
    Integrable (fun u : Fin n → ℝ => u i * u j * gaussDensity n u) ∧
    ∫ u : Fin n → ℝ, u i * u j * gaussDensity n u = if i = j then 1 else 0 := by
  let g : Fin n → ℝ → ℝ := fun k x => (if k = i then x else 1) * (if k = j then x else 1) * g72mn_phi x
  have hfun : (fun u : Fin n → ℝ => u i * u j * gaussDensity n u) = fun u => ∏ k, g k (u k) := by
    funext u
    simp only [g, Finset.prod_mul_distrib, g72mn_gd, Finset.prod_ite_eq', Finset.mem_univ, if_true,
      Finset.prod_const_one]
  have hint : ∀ k, Integrable (g k) := by
    intro k
    by_cases hi : k = i <;> by_cases hj : k = j
    · simp only [g, if_pos hi, if_pos hj]; simpa [pow_two] using g72mn_phi_int_pow 2
    · simp only [g, if_pos hi, if_neg hj, mul_one]; simpa using g72mn_phi_int_pow 1
    · simp only [g, if_neg hi, if_pos hj, one_mul]; simpa using g72mn_phi_int_pow 1
    · simp only [g, if_neg hi, if_neg hj, one_mul]; simpa using g72mn_phi_int_pow 0
  rw [hfun]
  refine ⟨?_, ?_⟩
  · rw [volume_pi]; exact Integrable.fintype_prod hint
  · rw [volume_pi, integral_fintype_prod_eq_prod]
    split_ifs with hij
    · subst hij
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      rw [Finset.prod_eq_one]
      · simp only [g, if_true, mul_one]; rw [← g72mn_m2]; congr 1; funext x; ring
      · intro k hk
        have : k ≠ i := Finset.ne_of_mem_erase hk
        simp only [g, this, if_false, mul_one, one_mul]
        simpa using g72mn_m0
    · refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp only [g, if_true, if_neg hij, mul_one]
      exact g72mn_m1

lemma g72mn_rotG {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℝ) (hU : Uᵀ * U = 1)
    (F : (ι → ℝ) → ℝ) (hF : Continuous F) :
    ∫ x, F (U *ᵥ x) = ∫ x, F x := by
  have hdet2 : U.det * U.det = 1 := by
    have := congrArg Matrix.det hU
    rwa [det_mul, det_transpose, det_one] at this
  have hdet : LinearMap.det (Matrix.toLin' U) ≠ 0 := by
    rw [LinearMap.det_toLin']; intro h; rw [h] at hdet2; simp at hdet2
  have habs : |(LinearMap.det (Matrix.toLin' U))⁻¹| = 1 := by
    rw [LinearMap.det_toLin', abs_inv]
    have : |U.det| * |U.det| = 1 := by rw [← abs_mul, hdet2, abs_one]
    have h0 : 0 ≤ |U.det| := abs_nonneg _
    have : |U.det| = 1 := by nlinarith
    rw [this, inv_one]
  have hmap : Measure.map (Matrix.toLin' U) volume = (volume : Measure (ι → ℝ)) := by
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet, habs, ENNReal.ofReal_one, one_smul]
  have hmeas : Measurable (Matrix.toLin' U) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  calc ∫ x, F (U *ᵥ x) = ∫ x, F (Matrix.toLin' U x) := by simp [toLin'_apply]
    _ = ∫ x, F x ∂(Measure.map (Matrix.toLin' U) volume) :=
        (integral_map hmeas.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by rw [hmap]

/-- product Gaussian density -/
noncomputable def g72mn_P {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∏ i, g72mn_phi (x i)

lemma g72mn_phi_nonneg (x : ℝ) : 0 ≤ g72mn_phi x := gaussianPDFReal_nonneg _ _ _

lemma g72mn_P_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ g72mn_P x :=
  Finset.prod_nonneg fun i _ => g72mn_phi_nonneg _

lemma g72mn_P_cont {ι : Type*} [Fintype ι] : Continuous (g72mn_P (ι := ι)) := by
  unfold g72mn_P; simp only [g72mn_phi_eq]; fun_prop

lemma g72mn_P_rot {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) (x : ι → ℝ) :
    g72mn_P (U *ᵥ x) = g72mn_P x := by
  unfold g72mn_P
  rw [← g72mn_density, ← g72mn_density]
  have h : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hU, one_mulVec]
  have : ∑ i, (U *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by simpa [dotProduct, pow_two] using h
  rw [this]

lemma g72mn_int_prod {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ) (hg : ∀ i, Integrable (g i)) :
    Integrable (fun x : ι → ℝ => ∏ i, g i (x i)) ∧
      ∫ x : ι → ℝ, ∏ i, g i (x i) = ∏ i, ∫ t, g i t := by
  rw [volume_pi]
  exact ⟨Integrable.fintype_prod hg, integral_fintype_prod_eq_prod _⟩

lemma g72mn_phi_int : Integrable g72mn_phi := by simpa using g72mn_phi_int_pow 0

lemma g72mn_absphi_int : Integrable (fun x => |x| * g72mn_phi x) := by
  have := (g72mn_phi_int_pow 1).norm
  refine this.congr (ae_of_all _ fun x => ?_)
  simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (g72mn_phi_nonneg x)]

lemma g72mn_P_int {ι : Type*} [Fintype ι] : Integrable (g72mn_P (ι := ι)) ∧ ∫ x, g72mn_P (ι := ι) x = 1 := by
  have h := g72mn_int_prod (ι := ι) (fun _ => g72mn_phi) fun _ => g72mn_phi_int
  refine ⟨h.1, ?_⟩
  unfold g72mn_P; rw [h.2]; simp [show ∫ x, g72mn_phi x = 1 by simpa using g72mn_m0]

noncomputable def g72mn_M1 : ℝ := ∫ x, |x| * g72mn_phi x

lemma g72mn_M1_val : g72mn_M1 = 2 * (2 * Real.pi) ^ (-(1 : ℝ) / 2) := by
  unfold g72mn_M1
  have h := integral_comp_abs (f := fun t => t * ((2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-t ^ 2 / 2)))
  have e1 : (fun x => |x| * g72mn_phi x) =
      fun x => |x| * ((2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-|x| ^ 2 / 2)) := by
    funext x; rw [g72mn_phi_eq, sq_abs]
  rw [e1, h]
  have h2 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  have e2 : ∫ x in Set.Ioi (0 : ℝ), x * ((2 * Real.pi) ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / 2)) =
      (2 * Real.pi) ^ (-(1 : ℝ) / 2) * ∫ x in Set.Ioi (0 : ℝ), x ^ (1 : ℝ) * Real.exp (-(1 / 2) * x ^ (2 : ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [Real.rpow_one, Real.rpow_two]
    ring_nf
  rw [e2, h2]
  norm_num

lemma g72mn_M1_sq : g72mn_M1 ^ 2 = 2 / Real.pi := by
  have h : ((2 * Real.pi) ^ (-(1:ℝ) / 2)) ^ 2 = (2 * Real.pi)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num [Real.rpow_neg_one]
  rw [g72mn_M1_val, mul_pow, h]
  field_simp

lemma g72mn_M1_nonneg : 0 ≤ g72mn_M1 :=
  integral_nonneg fun x => mul_nonneg (abs_nonneg x) (g72mn_phi_nonneg x)

/-- integral of |x_{i0}| against the product density -/
lemma g72mn_abs_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) :
    Integrable (fun x : ι → ℝ => |x i0| * g72mn_P x) ∧
      ∫ x : ι → ℝ, |x i0| * g72mn_P x = g72mn_M1 := by
  let g : ι → ℝ → ℝ := fun i t => (if i = i0 then |t| else 1) * g72mn_phi t
  have hfun : (fun x : ι → ℝ => |x i0| * g72mn_P x) = fun x => ∏ i, g i (x i) := by
    funext x
    simp only [g, Finset.prod_mul_distrib, g72mn_P, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hg : ∀ i, Integrable (g i) := by
    intro i
    by_cases h : i = i0
    · simp only [g, if_pos h]; exact g72mn_absphi_int
    · simp only [g, if_neg h, one_mul]; exact g72mn_phi_int
  have h := g72mn_int_prod g hg
  rw [hfun]
  refine ⟨h.1, ?_⟩
  rw [h.2, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i0), Finset.prod_eq_one]
  · simp only [g, if_true, mul_one]; rfl
  · intro i hi
    simp only [g, if_neg (Finset.ne_of_mem_erase hi), one_mul]
    simpa using g72mn_m0

/-- Householder: a reflection sending `c` to `‖c‖ e_{i0}` -/
lemma g72mn_householder {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (i0 : ι) :
    ∃ H : Matrix ι ι ℝ, Hᵀ * H = 1 ∧
      ∀ x, c ⬝ᵥ (H *ᵥ x) = Real.sqrt (c ⬝ᵥ c) * x i0 := by
  set r := Real.sqrt (c ⬝ᵥ c) with hr
  have hrr : r * r = c ⬝ᵥ c := Real.mul_self_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg (c i))
  set v := c - Pi.single i0 r with hv
  have hvc : v ⬝ᵥ c = r * r - r * c i0 := by
    rw [hv, sub_dotProduct, single_dotProduct, hrr]
  have hvv : v ⬝ᵥ v = 2 * (r * r - r * c i0) := by
    rw [hv, sub_dotProduct, dotProduct_sub, dotProduct_sub, single_dotProduct, dotProduct_single,
      single_dotProduct, hrr]
    simp only [Pi.single_eq_same]; linear_combination hrr
  by_cases h0 : v ⬝ᵥ v = 0
  · refine ⟨1, by simp, fun x => ?_⟩
    have hv0 : v = 0 := dotProduct_self_eq_zero.mp h0
    have hc : c = Pi.single i0 r := by rw [hv, sub_eq_zero] at hv0; exact hv0
    rw [one_mulVec, hc, single_dotProduct]
  · set s := v ⬝ᵥ v
    let H : Matrix ι ι ℝ := 1 - (2 / s) • vecMulVec v v
    have hHx : ∀ x, H *ᵥ x = x - (2 / s * (v ⬝ᵥ x)) • v := by
      intro x
      simp only [H, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec]
      congr 1
      rw [op_smul_eq_smul, smul_smul]
    have hHT : Hᵀ = H := by
      simp only [H, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]
    refine ⟨H, ?_, fun x => ?_⟩
    · rw [hHT, ext_iff_mulVec]
      intro x
      rw [← mulVec_mulVec, hHx, hHx, one_mulVec]
      have : v ⬝ᵥ (x - (2 / s * (v ⬝ᵥ x)) • v) = -(v ⬝ᵥ x) := by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
        change v ⬝ᵥ x - 2 / s * (v ⬝ᵥ x) * s = _
        field_simp; ring
      rw [this]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [hHx, dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm c v, hvc]
      have hs : s = 2 * (r * r - r * c i0) := hvv
      have hne : r * r - r * c i0 ≠ 0 := by intro h; apply h0; rw [hvv, h, mul_zero]
      have : 2 / s * (v ⬝ᵥ x) * (r * r - r * c i0) = v ⬝ᵥ x := by
        have hne' : r * (r - c i0) ≠ 0 := by
          intro h; apply hne; linear_combination h
        rw [hs]; field_simp
        exact mul_div_cancel_left₀ _ hne'
      rw [this, hv, sub_dotProduct, single_dotProduct]
      ring

lemma g72mn_C3 {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) (i0 : ι) :
    ∫ x : ι → ℝ, |c ⬝ᵥ x| * g72mn_P x = g72mn_M1 * Real.sqrt (c ⬝ᵥ c) := by
  obtain ⟨H, hH, hHc⟩ := g72mn_householder c i0
  have hF : Continuous fun x : ι → ℝ => |c ⬝ᵥ x| * g72mn_P x := by
    refine (continuous_abs.comp ?_).mul g72mn_P_cont
    show Continuous fun x : ι → ℝ => ∑ i, c i * x i
    fun_prop
  rw [← g72mn_rotG H hH _ hF]
  show ∫ x, |c ⬝ᵥ (H *ᵥ x)| * g72mn_P (H *ᵥ x) = _
  simp_rw [hHc, g72mn_P_rot H hH, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
  rw [integral_const_mul, (g72mn_abs_coord i0).2, mul_comm]

lemma g72mn_sq_int {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι) :
    Integrable (fun x : ι → ℝ => x i0 ^ 2 * g72mn_P x) ∧ ∫ x : ι → ℝ, x i0 ^ 2 * g72mn_P x = 1 := by
  let g : ι → ℝ → ℝ := fun i t => (if i = i0 then t ^ 2 else 1) * g72mn_phi t
  have hfun : (fun x : ι → ℝ => x i0 ^ 2 * g72mn_P x) = fun x => ∏ i, g i (x i) := by
    funext x
    simp only [g, Finset.prod_mul_distrib, g72mn_P, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hg : ∀ i, Integrable (g i) := by
    intro i
    by_cases h : i = i0
    · simp only [g, if_pos h]; exact g72mn_phi_int_pow 2
    · simp only [g, if_neg h, one_mul]; exact g72mn_phi_int
  have h := g72mn_int_prod g hg
  rw [hfun]
  refine ⟨h.1, ?_⟩
  rw [h.2, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i0), Finset.prod_eq_one]
  · simp only [g, if_true, mul_one]; exact g72mn_m2
  · intro i hi
    simp only [g, if_neg (Finset.ne_of_mem_erase hi), one_mul]
    simpa using g72mn_m0

noncomputable def g72mn_E {k : ℕ} (α : Fin k → ℝ) : ℝ :=
  ∫ x : Fin k → ℝ, |∑ i, α i * x i ^ 2| * g72mn_P x

lemma g72mn_E_eq {k : ℕ} (α : Fin k → ℝ) : thetaIntegral k α = g72mn_E α := by
  unfold thetaIntegral g72mn_E
  simp_rw [g72mn_gd]; rfl

lemma g72mn_E_int {k : ℕ} (α : Fin k → ℝ) :
    Integrable (fun x : Fin k → ℝ => |∑ i, α i * x i ^ 2| * g72mn_P x) := by
  refine Integrable.mono' (g := fun x => ∑ i, |α i| * (x i ^ 2 * g72mn_P x))
    (integrable_finset_sum _ fun i _ => (g72mn_sq_int i).1.const_mul _) ?_ (ae_of_all _ fun x => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact (continuous_abs.comp (by fun_prop)).mul g72mn_P_cont
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (g72mn_P_nonneg x), abs_abs]
    calc |∑ i, α i * x i ^ 2| * g72mn_P x ≤ (∑ i, |α i * x i ^ 2|) * g72mn_P x :=
          mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (g72mn_P_nonneg x)
      _ = _ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (sq_nonneg (x i))]; ring

lemma g72mn_E_nonneg {k : ℕ} (α : Fin k → ℝ) : 0 ≤ g72mn_E α :=
  integral_nonneg fun x => mul_nonneg (abs_nonneg _) (g72mn_P_nonneg x)

lemma g72mn_split {k : ℕ} (f g : (Fin k → ℝ) → ℝ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun w : Fin k ⊕ Fin k → ℝ => f (fun i => w (Sum.inl i)) * g (fun i => w (Sum.inr i))) ∧
    ∫ w : Fin k ⊕ Fin k → ℝ, f (fun i => w (Sum.inl i)) * g (fun i => w (Sum.inr i)) =
      (∫ x, f x) * ∫ y, g y := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin k => ℝ)
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    measurePreserving_sumPiEquivProdPi (fun _ => volume)
  have hcomp : (fun w : Fin k ⊕ Fin k → ℝ => f (fun i => w (Sum.inl i)) * g (fun i => w (Sum.inr i)))
      = (fun z : (Fin k → ℝ) × (Fin k → ℝ) => f z.1 * g z.2) ∘ e := rfl
  rw [hcomp]
  refine ⟨(hmp.integrable_comp_emb e.measurableEmbedding).mpr (hf.mul_prod hg), ?_⟩
  rw [Function.comp_def, hmp.integral_comp' (fun z : (Fin k → ℝ) × (Fin k → ℝ) => f z.1 * g z.2)]
  exact integral_prod_mul f g

lemma g72mn_P_sum {k : ℕ} (w : Fin k ⊕ Fin k → ℝ) :
    g72mn_P w = g72mn_P (fun i => w (Sum.inl i)) * g72mn_P (fun i => w (Sum.inr i)) := by
  unfold g72mn_P; rw [Fintype.prod_sum_type]

/-- the 45-degree rotation on pairs -/
noncomputable def g72mn_R (k : ℕ) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ :=
  fromBlocks (Real.sqrt (1 / 2) • 1) (Real.sqrt (1 / 2) • 1) (Real.sqrt (1 / 2) • 1)
    (-(Real.sqrt (1 / 2)) • 1)

lemma g72mn_R_orth (k : ℕ) : (g72mn_R k)ᵀ * g72mn_R k = 1 := by
  have hc : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = 1 / 2 := Real.mul_self_sqrt (by norm_num)
  unfold g72mn_R
  rw [fromBlocks_transpose, fromBlocks_multiply, ← fromBlocks_one]
  simp only [transpose_smul, transpose_one, smul_mul_smul_comm, Matrix.one_mul, neg_mul, mul_neg,
    neg_neg, hc]
  congr 1 <;> rw [← add_smul] <;> norm_num

lemma g72mn_R_apply (k : ℕ) (w : Fin k ⊕ Fin k → ℝ) (i : Fin k) :
    (g72mn_R k *ᵥ w) (Sum.inl i) * (g72mn_R k *ᵥ w) (Sum.inr i) =
      (w (Sum.inl i) ^ 2 - w (Sum.inr i) ^ 2) / 2 := by
  have hc : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = 1 / 2 := Real.mul_self_sqrt (by norm_num)
  unfold g72mn_R
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, smul_mulVec, one_mulVec, Pi.smul_apply,
    smul_eq_mul, Function.comp_apply]
  linear_combination (w (Sum.inl i) ^ 2 - w (Sum.inr i) ^ 2) * hc

lemma g72mn_cs {k : ℕ} (c : Fin k → ℝ) :
    ∑ i, |c i| ≤ Real.sqrt k * Real.sqrt (c ⬝ᵥ c) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg k)]
  apply Real.le_sqrt_of_sq_le
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => |c i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at this
  simpa [dotProduct, pow_two] using this

noncomputable def g72mn_D {k : ℕ} (α : Fin k → ℝ) : ℝ :=
  ∫ w : Fin k ⊕ Fin k → ℝ, |∑ i, α i * (w (Sum.inl i) * w (Sum.inr i))| * g72mn_P w

lemma g72mn_D_le {k : ℕ} (α : Fin k → ℝ) : g72mn_D α ≤ g72mn_E α := by
  have hF : Continuous fun w : Fin k ⊕ Fin k → ℝ =>
      |∑ i, α i * (w (Sum.inl i) * w (Sum.inr i))| * g72mn_P w :=
    (continuous_abs.comp (by fun_prop)).mul g72mn_P_cont
  unfold g72mn_D
  rw [← g72mn_rotG _ (g72mn_R_orth k) _ hF]
  simp only [g72mn_P_rot _ (g72mn_R_orth k), g72mn_R_apply]
  have h1 := g72mn_split (fun x => |∑ i, α i * x i ^ 2| * g72mn_P x) g72mn_P (g72mn_E_int α)
    g72mn_P_int.1
  have h2 := g72mn_split g72mn_P (fun x => |∑ i, α i * x i ^ 2| * g72mn_P x) g72mn_P_int.1
    (g72mn_E_int α)
  have hint := (h1.1.add h2.1).const_mul (1 / 2 : ℝ)
  refine (integral_mono_of_nonneg (ae_of_all _ fun w => mul_nonneg (abs_nonneg _)
    (g72mn_P_nonneg w)) hint (ae_of_all _ fun w => ?_)).trans ?_
  · simp only
    rw [g72mn_P_sum w]
    have hP1 := g72mn_P_nonneg (fun i => w (Sum.inl i))
    have hP2 := g72mn_P_nonneg (fun i => w (Sum.inr i))
    have : |∑ i, α i * ((w (Sum.inl i) ^ 2 - w (Sum.inr i) ^ 2) / 2)| ≤
        1 / 2 * (|∑ i, α i * w (Sum.inl i) ^ 2| + |∑ i, α i * w (Sum.inr i) ^ 2|) := by
      have e : ∑ i, α i * ((w (Sum.inl i) ^ 2 - w (Sum.inr i) ^ 2) / 2) =
          1 / 2 * (∑ i, α i * w (Sum.inl i) ^ 2 - ∑ i, α i * w (Sum.inr i) ^ 2) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_; ring
      rw [e, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
    calc |∑ i, α i * ((w (Sum.inl i) ^ 2 - w (Sum.inr i) ^ 2) / 2)| *
          (g72mn_P (fun i => w (Sum.inl i)) * g72mn_P (fun i => w (Sum.inr i)))
        ≤ 1 / 2 * (|∑ i, α i * w (Sum.inl i) ^ 2| + |∑ i, α i * w (Sum.inr i) ^ 2|) *
          (g72mn_P (fun i => w (Sum.inl i)) * g72mn_P (fun i => w (Sum.inr i))) :=
          mul_le_mul_of_nonneg_right this (mul_nonneg hP1 hP2)
      _ = _ := by simp only [Pi.add_apply]; ring
  · have hadd := integral_add h1.1 h2.1
    rw [integral_const_mul]
    simp only [Pi.add_apply] at hadd ⊢
    rw [hadd, h1.2, h2.2, g72mn_P_int.2]
    unfold g72mn_E; apply le_of_eq; ring

lemma g72mn_D_ge {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ) :
    g72mn_M1 ^ 2 * (∑ i, |α i|) / Real.sqrt k ≤ g72mn_D α := by
  have i0 : Fin k := ⟨0, hk⟩
  let G : (Fin k → ℝ) × (Fin k → ℝ) → ℝ := fun z =>
    |∑ i, α i * (z.1 i * z.2 i)| * (g72mn_P z.1 * g72mn_P z.2)
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin k => ℝ)
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    measurePreserving_sumPiEquivProdPi (fun _ => volume)
  have hD : g72mn_D α = ∫ z, G z ∂(volume.prod volume) := by
    unfold g72mn_D
    rw [← hmp.integral_comp' G]
    congr 1; funext w
    simp only [G, g72mn_P_sum w]; rfl
  have hGc : Continuous G := by
    refine (continuous_abs.comp ?_).mul ((g72mn_P_cont.comp continuous_fst).mul
      (g72mn_P_cont.comp continuous_snd))
    fun_prop
  have hGint : Integrable G (volume.prod volume) := by
    refine Integrable.mono' (g := fun z => ∑ i, |α i| * ((|z.1 i| * g72mn_P z.1) *
      (|z.2 i| * g72mn_P z.2))) (integrable_finset_sum _ fun i _ =>
        (((g72mn_abs_coord i).1.mul_prod (g72mn_abs_coord i).1)).const_mul _)
      hGc.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    have hP1 := g72mn_P_nonneg z.1
    have hP2 := g72mn_P_nonneg z.2
    simp only [G, Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hP1, abs_of_nonneg hP2]
    calc |∑ i, α i * (z.1 i * z.2 i)| * (g72mn_P z.1 * g72mn_P z.2)
        ≤ (∑ i, |α i * (z.1 i * z.2 i)|) * (g72mn_P z.1 * g72mn_P z.2) :=
          mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (mul_nonneg hP1 hP2)
      _ = _ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_mul, abs_mul]; ring
  have hinner : ∀ x : Fin k → ℝ, ∫ y, G (x, y) =
      g72mn_P x * (g72mn_M1 * Real.sqrt ((fun i => α i * x i) ⬝ᵥ (fun i => α i * x i))) := by
    intro x
    rw [← g72mn_C3 (fun i => α i * x i) i0, ← integral_const_mul]
    congr 1; funext y
    simp only [G, dotProduct]
    rw [show ∑ i, α i * (x i * y i) = ∑ i, α i * x i * y i from
      Finset.sum_congr rfl fun i _ => by ring]
    ring
  have hli := hGint.integral_prod_left
  simp only [hinner] at hli
  rw [hD, integral_prod G hGint]
  simp only [hinner]
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hlow : ∀ x : Fin k → ℝ, g72mn_M1 / Real.sqrt k * ∑ i, |α i| * (|x i| * g72mn_P x) ≤
      g72mn_P x * (g72mn_M1 * Real.sqrt ((fun i => α i * x i) ⬝ᵥ (fun i => α i * x i))) := by
    intro x
    have hcs := g72mn_cs (fun i => α i * x i)
    have hP := g72mn_P_nonneg x
    have hM := g72mn_M1_nonneg
    have e : ∑ i, |α i| * (|x i| * g72mn_P x) = (∑ i, |α i * x i|) * g72mn_P x := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; rw [abs_mul]; ring
    rw [e, div_mul_eq_mul_div, div_le_iff₀ hsk]
    calc g72mn_M1 * ((∑ i, |α i * x i|) * g72mn_P x)
        ≤ g72mn_M1 * ((Real.sqrt k * Real.sqrt ((fun i => α i * x i) ⬝ᵥ (fun i => α i * x i)))
          * g72mn_P x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcs hP) hM
      _ = _ := by ring
  have hlint : Integrable fun x : Fin k → ℝ =>
      g72mn_M1 / Real.sqrt k * ∑ i, |α i| * (|x i| * g72mn_P x) :=
    (integrable_finset_sum _ fun i _ => (g72mn_abs_coord i).1.const_mul _).const_mul _
  refine le_trans (le_of_eq ?_) (integral_mono hlint hli hlow)
  rw [integral_const_mul, integral_finset_sum _ fun i _ => (g72mn_abs_coord i).1.const_mul _]
  simp_rw [integral_const_mul, (g72mn_abs_coord _).2]
  rw [← Finset.sum_mul]
  ring

lemma g72mn_E_ge {k : ℕ} (hk : 1 ≤ k) (α : Fin k → ℝ) (hα : ∑ i, |α i| = 1) :
    2 / (Real.pi * Real.sqrt k) ≤ g72mn_E α := by
  have := (g72mn_D_ge hk α).trans (g72mn_D_le α)
  rw [hα, g72mn_M1_sq, mul_one, div_div] at this
  exact this

lemma g72mn_theta_le (k : ℕ) (hk : 1 ≤ k) : theta k ≤ Real.pi * Real.sqrt k / 2 := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hL : 0 < 2 / (Real.pi * Real.sqrt k) := by positivity
  have hne : (thetaIntegral k '' {α : Fin k → ℝ | ∑ i, |α i| = 1}).Nonempty :=
    ⟨_, ⟨Pi.single ⟨0, hk⟩ 1, by
      show ∑ i, |Pi.single (⟨0, hk⟩ : Fin k) (1 : ℝ) i| = 1
      rw [Fintype.sum_eq_single ⟨0, hk⟩ (fun j hj => by simp [Pi.single_apply, hj])]; simp, rfl⟩⟩
  have hinf : 2 / (Real.pi * Real.sqrt k) ≤ sInf (thetaIntegral k '' {α : Fin k → ℝ | ∑ i, |α i| = 1}) := by
    refine le_csInf hne ?_
    rintro _ ⟨α, hα, rfl⟩
    rw [g72mn_E_eq]; exact g72mn_E_ge hk α hα
  unfold theta
  calc 1 / sInf (thetaIntegral k '' {α : Fin k → ℝ | ∑ i, |α i| = 1})
      ≤ 1 / (2 / (Real.pi * Real.sqrt k)) := one_div_le_one_div_of_le hL hinf
    _ = _ := by field_simp

lemma g72mn_E2 (a b : ℝ) :
    g72mn_E ![a, b] = ∫ x : Fin 2 → ℝ, |a * x 0 ^ 2 + b * x 1 ^ 2| * g72mn_P x := by
  unfold g72mn_E; simp [Fin.sum_univ_two]

lemma g72mn_E2_int (a b : ℝ) :
    Integrable fun x : Fin 2 → ℝ => |a * x 0 ^ 2 + b * x 1 ^ 2| * g72mn_P x := by
  have := g72mn_E_int ![a, b]
  simpa [Fin.sum_univ_two] using this

lemma g72mn_swap (F : (Fin 2 → ℝ) → ℝ) (hF : Continuous F) :
    ∫ x : Fin 2 → ℝ, F ![x 1, x 0] = ∫ x, F x := by
  let S : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
  have hS : Sᵀ * S = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [S, Matrix.mul_apply, Fin.sum_univ_two]
  have hSx : ∀ x : Fin 2 → ℝ, S *ᵥ x = ![x 1, x 0] := by
    intro x; ext i; fin_cases i <;> simp [S, mulVec, dotProduct, Fin.sum_univ_two]
  rw [← g72mn_rotG S hS F hF]
  simp_rw [hSx]

lemma g72mn_P2_swap (x : Fin 2 → ℝ) : g72mn_P ![x 1, x 0] = g72mn_P x := by
  unfold g72mn_P; simp [Fin.prod_univ_two, mul_comm]

lemma g72mn_Estar : g72mn_E ![1 / 2, -(1 / 2)] = 2 / Real.pi := by
  rw [g72mn_E2]
  have hc : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = 1 / 2 := Real.mul_self_sqrt (by norm_num)
  let R : Matrix (Fin 2) (Fin 2) ℝ :=
    !![Real.sqrt (1 / 2), Real.sqrt (1 / 2); Real.sqrt (1 / 2), -Real.sqrt (1 / 2)]
  have hR : Rᵀ * R = 1 := by
    have h2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2:ℝ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    ext i j; fin_cases i <;> fin_cases j <;> simp [R, Matrix.mul_apply, Fin.sum_univ_two, hc]
    all_goals (rw [h2]; norm_num)
  have hRx : ∀ x : Fin 2 → ℝ, (R *ᵥ x) 0 * (R *ᵥ x) 1 = (x 0 ^ 2 - x 1 ^ 2) / 2 := by
    intro x
    simp only [R, mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, head_cons]
    linear_combination (x 0 ^ 2 - x 1 ^ 2) * hc
  have hF : Continuous fun x : Fin 2 → ℝ => |x 0 * x 1| * g72mn_P x :=
    (continuous_abs.comp (by fun_prop)).mul g72mn_P_cont
  have h1 := g72mn_rotG R hR _ hF
  simp only [hRx, g72mn_P_rot R hR] at h1
  have e : (fun x : Fin 2 → ℝ => |1 / 2 * x 0 ^ 2 + -(1 / 2) * x 1 ^ 2| * g72mn_P x) =
      fun x => |(x 0 ^ 2 - x 1 ^ 2) / 2| * g72mn_P x := by
    funext x; congr 2; ring
  rw [e, h1]
  -- ∫ |x0 x1| P = M1^2
  have hg := g72mn_int_prod (ι := Fin 2) (fun _ t => |t| * g72mn_phi t) fun _ => g72mn_absphi_int
  have e2 : (fun x : Fin 2 → ℝ => |x 0 * x 1| * g72mn_P x) =
      fun x => ∏ i, (fun _ t => |t| * g72mn_phi t) i (x i) := by
    funext x; simp only [g72mn_P, Fin.prod_univ_two, abs_mul]; ring
  rw [e2, hg.2, Fin.prod_univ_two, ← g72mn_M1_sq]
  unfold g72mn_M1; ring

lemma g72mn_E2_lower (a b : ℝ) (hab : |a| + |b| = 1) : 2 / Real.pi ≤ g72mn_E ![a, b] := by
  rcases le_or_gt 0 (a * b) with hs | hs
  · -- same sign: value 1
    have hval : g72mn_E ![a, b] = 1 := by
      rw [g72mn_E2]
      have e : (fun x : Fin 2 → ℝ => |a * x 0 ^ 2 + b * x 1 ^ 2| * g72mn_P x) =
          fun x => |a| * (x 0 ^ 2 * g72mn_P x) + |b| * (x 1 ^ 2 * g72mn_P x) := by
        funext x
        have h0 := sq_nonneg (x 0)
        have h1 := sq_nonneg (x 1)
        rcases mul_nonneg_iff.mp hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [abs_of_nonneg (by positivity), abs_of_nonneg ha, abs_of_nonneg hb]; ring
        · rw [abs_of_nonpos (by nlinarith), abs_of_nonpos ha, abs_of_nonpos hb]; ring
      rw [e, integral_add ((g72mn_sq_int 0).1.const_mul _) ((g72mn_sq_int 1).1.const_mul _),
        integral_const_mul, integral_const_mul, (g72mn_sq_int 0).2, (g72mn_sq_int 1).2]
      linarith
    rw [hval, div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  · -- opposite signs: convexity
    have hab' : |a - b| = 1 := by
      rcases lt_or_gt_of_ne (show a ≠ 0 by rintro rfl; simp at hs) with ha | ha
      · have hb : 0 < b := by nlinarith
        rw [abs_of_neg ha, abs_of_pos hb] at hab
        rw [abs_of_neg (by linarith)]; linarith
      · have hb : b < 0 := by nlinarith
        rw [abs_of_pos ha, abs_of_neg hb] at hab
        rw [abs_of_pos (by linarith)]; linarith
    have hβ : g72mn_E ![-b, -a] = g72mn_E ![a, b] := by
      rw [g72mn_E2, g72mn_E2]
      have hF : Continuous fun x : Fin 2 → ℝ => |a * x 0 ^ 2 + b * x 1 ^ 2| * g72mn_P x :=
        (continuous_abs.comp (by fun_prop)).mul g72mn_P_cont
      rw [← g72mn_swap _ hF]
      congr 1; funext x
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, g72mn_P2_swap]
      congr 1
      rw [← abs_neg]; congr 1; ring
    have hm : g72mn_E ![1 / 2, -(1 / 2)] ≤ (g72mn_E ![a, b] + g72mn_E ![-b, -a]) / 2 := by
      rw [g72mn_E2, g72mn_E2, g72mn_E2, ← integral_add (g72mn_E2_int a b) (g72mn_E2_int (-b) (-a)),
        ← integral_div]
      refine integral_mono_of_nonneg (ae_of_all _ fun x => mul_nonneg (abs_nonneg _)
        (g72mn_P_nonneg x)) (((g72mn_E2_int a b).add (g72mn_E2_int (-b) (-a))).div_const 2)
        (ae_of_all _ fun x => ?_)
      have hP := g72mn_P_nonneg x
      simp only [Pi.add_apply]
      have key : |1 / 2 * x 0 ^ 2 + -(1 / 2) * x 1 ^ 2| ≤
          (|a * x 0 ^ 2 + b * x 1 ^ 2| + |-b * x 0 ^ 2 + -a * x 1 ^ 2|) / 2 := by
        have e1 : |1 / 2 * x 0 ^ 2 + -(1 / 2) * x 1 ^ 2| =
            |(a * x 0 ^ 2 + b * x 1 ^ 2) + (-b * x 0 ^ 2 + -a * x 1 ^ 2)| / 2 := by
          have : (a * x 0 ^ 2 + b * x 1 ^ 2) + (-b * x 0 ^ 2 + -a * x 1 ^ 2) =
              (a - b) * (x 0 ^ 2 - x 1 ^ 2) := by ring
          rw [this, abs_mul, hab', show 1 / 2 * x 0 ^ 2 + -(1 / 2) * x 1 ^ 2 =
            (x 0 ^ 2 - x 1 ^ 2) / 2 by ring, abs_div, abs_two]
          ring
        rw [e1]
        exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
      calc |1 / 2 * x 0 ^ 2 + -(1 / 2) * x 1 ^ 2| * g72mn_P x
          ≤ (|a * x 0 ^ 2 + b * x 1 ^ 2| + |-b * x 0 ^ 2 + -a * x 1 ^ 2|) / 2 * g72mn_P x :=
            mul_le_mul_of_nonneg_right key hP
        _ = _ := by ring
    rw [hβ, g72mn_Estar] at hm
    linarith

lemma g72mn_theta2 : theta 2 = Real.pi / 2 := by
  have hset : IsLeast (thetaIntegral 2 '' {α : Fin 2 → ℝ | ∑ i, |α i| = 1}) (2 / Real.pi) := by
    refine ⟨⟨![1 / 2, -(1 / 2)], ?_, ?_⟩, ?_⟩
    · simp [Fin.sum_univ_two, abs_of_pos]; norm_num
    · rw [g72mn_E_eq, g72mn_Estar]
    · rintro _ ⟨α, hα, rfl⟩
      rw [g72mn_E_eq]
      have hαe : α = ![α 0, α 1] := by ext i; fin_cases i <;> rfl
      rw [hαe]
      exact g72mn_E2_lower _ _ (by simpa [Fin.sum_univ_two] using hα)
  unfold theta
  rw [hset.csInf_eq]
  field_simp

theorem g72mn_theta_main :
    (∀ k : ℕ, 1 ≤ k → theta k ≤ Real.pi * Real.sqrt k / 2) ∧ theta 2 = Real.pi / 2 :=
  ⟨g72mn_theta_le, g72mn_theta2⟩

theorem solution :
    (∀ k : ℕ, 1 ≤ k → theta k ≤ Real.pi * Real.sqrt k / 2) ∧ theta 2 = Real.pi / 2 :=
  g72mn_theta_main
