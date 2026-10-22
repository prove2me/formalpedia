-- Prove2me | solution 1 for ModernConvex.MatrixCube.gaussian_quadratic_form
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:57:11.864857+00:00
-- url     : https://prove2.me/submissions/e853d6ce-e6f3-4ee2-adf9-225c6b447e86

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

open Matrix
open MeasureTheory ProbabilityTheory
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

lemma g72mn_part_a {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∫ u : Fin n → ℝ, (u ⬝ᵥ (A *ᵥ u)) * gaussDensity n u = A.trace := by
  have : (fun u : Fin n → ℝ => (u ⬝ᵥ (A *ᵥ u)) * gaussDensity n u) =
      fun u => ∑ i, ∑ j, A i j * (u i * u j * gaussDensity n u) := by
    funext u
    simp only [dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this, integral_finset_sum]
  · have h2 : ∀ i, ∫ u : Fin n → ℝ, ∑ j, A i j * (u i * u j * gaussDensity n u) = A i i := by
      intro i
      rw [integral_finset_sum]
      · simp_rw [integral_const_mul, (g72mn_pair _ _).2]
        simp
      · exact fun j _ => (g72mn_pair i j).1.const_mul _
    simp_rw [h2]
    rfl
  · exact fun i _ => integrable_finset_sum _ fun j _ => (g72mn_pair i j).1.const_mul _

lemma g72mn_spec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      M = U * diagonal hM.eigenvalues * Uᵀ := by
  refine ⟨(hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ), ?_, ?_, ?_⟩
  · have := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := Unitary.coe_mul_star_self hM.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  · conv_lhs => rw [hM.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]

lemma g72mn_rot {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
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
  have hmap : Measure.map (Matrix.toLin' U) volume = (volume : Measure (Fin n → ℝ)) := by
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet, habs, ENNReal.ofReal_one, one_smul]
  have hmeas : Measurable (Matrix.toLin' U) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  calc ∫ x, F (U *ᵥ x) = ∫ x, F (Matrix.toLin' U x) := by simp [toLin'_apply]
    _ = ∫ x, F x ∂(Measure.map (Matrix.toLin' U) volume) :=
        (integral_map hmeas.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by rw [hmap]

lemma g72mn_gd_rot {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (hU : Uᵀ * U = 1) (x : Fin n → ℝ) :
    gaussDensity n (U *ᵥ x) = gaussDensity n x := by
  have : ∑ i, (U *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
    have h : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
      rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hU, one_mulVec]
    simpa [dotProduct, pow_two] using h
  simp only [gaussDensity, this]

lemma g72mn_gd_nonneg (k : ℕ) (u : Fin k → ℝ) : 0 ≤ gaussDensity k u := by
  unfold gaussDensity; positivity

lemma g72mn_part_b {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    1 / theta A.rank * eigL1 A ≤ ∫ u : Fin n → ℝ, |u ⬝ᵥ (A *ᵥ u)| * gaussDensity n u := by
  have hrank : A.rank = Fintype.card {i // hA.eigenvalues i ≠ 0} := hA.rank_eq_card_non_zero_eigs
  have hL1 : eigL1 A = ∑ i, |hA.eigenvalues i| := by unfold eigL1 eigVec; rw [dif_pos hA]
  obtain ⟨U, hU1, hU2, hAU⟩ := g72mn_spec A hA
  generalize hA.eigenvalues = lam at hAU hrank hL1
  have hLHS0 : 0 ≤ ∫ u : Fin n → ℝ, |u ⬝ᵥ (A *ᵥ u)| * gaussDensity n u :=
    integral_nonneg fun u => mul_nonneg (abs_nonneg _) (g72mn_gd_nonneg n u)
  set N := ∑ i, |lam i| with hN
  rcases (Finset.sum_nonneg fun i _ => abs_nonneg (lam i) : 0 ≤ N).eq_or_lt with hN0 | hNpos
  · rw [hL1, hN, ← hN0, mul_zero]; exact hLHS0
  -- rotate
  have hDiag : Uᵀ * A * U = diagonal lam := by
    rw [hAU]
    calc Uᵀ * (U * diagonal lam * Uᵀ) * U = (Uᵀ * U) * diagonal lam * (Uᵀ * U) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
  have hF : Continuous fun v : Fin n → ℝ => |v ⬝ᵥ (A *ᵥ v)| * gaussDensity n v := by
    unfold gaussDensity; simp only [dotProduct, mulVec]; fun_prop
  have step1 : ∫ u : Fin n → ℝ, |u ⬝ᵥ (A *ᵥ u)| * gaussDensity n u =
      ∫ u : Fin n → ℝ, |∑ k, lam k * u k ^ 2| * ∏ k, g72mn_phi (u k) := by
    rw [← g72mn_rot U hU1 _ hF]
    congr 1; funext u
    rw [g72mn_gd_rot U hU1, g72mn_gd]
    congr 2
    have key : (U *ᵥ u) ⬝ᵥ (A *ᵥ (U *ᵥ u)) = u ⬝ᵥ ((Uᵀ * A * U) *ᵥ u) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u Uᵀ, ← mulVec_transpose,
        transpose_transpose]
    rw [key, hDiag]
    simp only [dotProduct, mulVec_diagonal]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hφ1 : ∫ x, g72mn_phi x = 1 := by simpa using g72mn_m0
  let H : ({k // lam k ≠ 0} → ℝ) → ℝ := fun y =>
    |∑ k : {k // lam k ≠ 0}, lam k * y k ^ 2| * ∏ k, g72mn_phi (y k)
  let Φ : ({k // ¬ lam k ≠ 0} → ℝ) → ℝ := fun z => ∏ k, g72mn_phi (z k)
  have hΦ1 : ∫ z, Φ z = 1 := by
    simp only [Φ]; rw [integral_fintype_prod_volume_eq_prod]; simp [hφ1]
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun k => lam k ≠ 0)
  have hpt : ∀ u : Fin n → ℝ, |∑ k, lam k * u k ^ 2| * ∏ k, g72mn_phi (u k) =
      (fun yz : ({k // lam k ≠ 0} → ℝ) × ({k // ¬ lam k ≠ 0} → ℝ) => H yz.1 * Φ yz.2) (e u) := by
    intro u
    change _ = |∑ k : {k // lam k ≠ 0}, lam k * u k ^ 2| * (∏ k : {k // lam k ≠ 0}, g72mn_phi (u k))
      * ∏ k : {k // ¬ lam k ≠ 0}, g72mn_phi (u k)
    rw [mul_assoc, Fintype.prod_subtype_mul_prod_subtype (fun k => lam k ≠ 0) (fun k => g72mn_phi (u k))]
    congr 2
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k => lam k ≠ 0)]
    have : ∑ k : {k // ¬ lam k ≠ 0}, lam k * u k ^ 2 = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [not_not.mp k.2, zero_mul]
    rw [this, add_zero]
  have hmp := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun k => lam k ≠ 0)
  have step2 : ∫ u : Fin n → ℝ, |∑ k, lam k * u k ^ 2| * ∏ k, g72mn_phi (u k) = ∫ y, H y := by
    calc _ = ∫ u, (fun yz : ({k // lam k ≠ 0} → ℝ) × ({k // ¬ lam k ≠ 0} → ℝ) =>
            H yz.1 * Φ yz.2) (e u) := by
          congr 1; funext u; exact hpt u
      _ = ∫ yz, (fun yz : ({k // lam k ≠ 0} → ℝ) × ({k // ¬ lam k ≠ 0} → ℝ) =>
            H yz.1 * Φ yz.2) yz := by
          convert hmp.integral_comp' (fun yz : ({k // lam k ≠ 0} → ℝ) × ({k // ¬ lam k ≠ 0} → ℝ) =>
            H yz.1 * Φ yz.2) using 1
      _ = (∫ y, H y) * ∫ z, Φ z := by rw [Measure.volume_eq_prod]; exact integral_prod_mul H Φ
      _ = ∫ y, H y := by rw [hΦ1, mul_one]
  let eK : Fin A.rank ≃ {k // lam k ≠ 0} := (Fintype.equivFinOfCardEq hrank.symm).symm
  let α : Fin A.rank → ℝ := fun j => lam (eK j) / N
  have step3 : ∫ y, H y = N * thetaIntegral A.rank α := by
    rw [← (volume_measurePreserving_piCongrLeft (fun _ => ℝ) eK).integral_comp' H, thetaIntegral,
      ← integral_const_mul]
    congr 1; funext y
    simp only [H]
    rw [← Equiv.sum_comp eK, ← Equiv.prod_comp eK]
    simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rw [g72mn_gd, ← mul_assoc]
    congr 1
    rw [← abs_of_pos (show (0:ℝ) < N from hNpos), ← abs_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [α]
    have hN' : N ≠ 0 := hNpos.ne'
    field_simp
  have hα : ∑ j, |α j| = 1 := by
    simp only [α, abs_div, abs_of_pos (show 0 < N from hNpos)]
    rw [← Finset.sum_div, div_eq_one_iff_eq hNpos.ne']
    rw [Equiv.sum_comp eK (fun k => |lam k|),
      ← Fintype.sum_subtype_add_sum_subtype (fun k => lam k ≠ 0) (fun k => |lam k|)]
    have : ∑ k : {k // ¬ lam k ≠ 0}, |lam k| = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [not_not.mp k.2, abs_zero]
    rw [this, add_zero]
  have hbdd : BddBelow (thetaIntegral A.rank '' {α : Fin A.rank → ℝ | ∑ i, |α i| = 1}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨β, _, rfl⟩
    exact integral_nonneg fun u => mul_nonneg (abs_nonneg _) (g72mn_gd_nonneg _ u)
  have hle := csInf_le hbdd ⟨α, hα, rfl⟩
  rw [step1, step2, step3, hL1, theta, one_div_one_div, mul_comm]
  exact mul_le_mul_of_nonneg_left hle hNpos.le

theorem g72mn_gauss_main {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    ∫ u : Fin n → ℝ, (u ⬝ᵥ (A *ᵥ u)) * gaussDensity n u = A.trace ∧
    ∫ u : Fin n → ℝ, |u ⬝ᵥ (A *ᵥ u)| * gaussDensity n u ≥ 1 / theta A.rank * eigL1 A :=
  ⟨g72mn_part_a A, g72mn_part_b A hA⟩




/-- Ben-Tal–Nemirovski, Lemma 4.4.4, p. 192, (4.4.43): with `ξ ∼ 𝒩(0, Iₙ)` (density
`pₙ(u) = (2π)^{−n/2} exp{−uᵀu/2}` on `ℝⁿ`), for every symmetric `n × n` matrix `A`
(a) `E{ξᵀAξ} = Tr(A)`,
(b) `E{|ξᵀAξ|} ≥ (1/θ(Rank(A))) ‖λ(A)‖₁`,
with `θ` the function of (4.4.38). Expectations are written as integrals against `pₙ` over
`ℝⁿ` with Lebesgue measure. -/
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    ∫ u : Fin n → ℝ, (u ⬝ᵥ (A *ᵥ u)) * gaussDensity n u = A.trace ∧
    ∫ u : Fin n → ℝ, |u ⬝ᵥ (A *ᵥ u)| * gaussDensity n u ≥ 1 / theta A.rank * eigL1 A := by
  exact g72mn_gauss_main A hA


