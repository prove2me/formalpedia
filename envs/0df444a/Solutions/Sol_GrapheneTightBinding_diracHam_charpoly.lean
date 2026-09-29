-- Prove2me | solution 1 for GrapheneTightBinding.diracHam_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:57:45.754653+00:00
-- url     : https://prove2.me/submissions/d256924b-4f16-45ff-ad32-12d114deba76

import Definitions.Def_graphene_tb_hamiltonian

open Asymptotics Polynomial
open GrapheneTightBinding

theorem W2m_GrapheneTightBinding_Delta_closed_form (a : ℝ) (k : ℝ × ℝ) :
    Delta a k =
      Complex.exp (-(Complex.I * (k.1 * a : ℝ))) *
        (1 + 2 * Complex.exp (Complex.I * (3 * k.1 * a / 2 : ℝ)) *
          (Real.cos (Real.sqrt 3 * k.2 * a / 2) : ℂ)) := by
  have hcos : ((Real.cos (Real.sqrt 3 * k.2 * a / 2) : ℝ) : ℂ)
      = (Complex.exp (((Real.sqrt 3 * k.2 * a / 2 : ℝ) : ℂ) * Complex.I)
        + Complex.exp (-((Real.sqrt 3 * k.2 * a / 2 : ℝ) : ℂ) * Complex.I)) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos]
  rw [hcos]
  have hR : Complex.exp (-(Complex.I * (k.1 * a : ℝ))) *
      (1 + 2 * Complex.exp (Complex.I * (3 * k.1 * a / 2 : ℝ)) *
        ((Complex.exp (((Real.sqrt 3 * k.2 * a / 2 : ℝ) : ℂ) * Complex.I)
          + Complex.exp (-((Real.sqrt 3 * k.2 * a / 2 : ℝ) : ℂ) * Complex.I)) / 2))
      = Complex.exp (-(Complex.I * (k.1 * a : ℝ)) + Complex.I * (3 * k.1 * a / 2 : ℝ)
          + ((Real.sqrt 3 * k.2 * a / 2 : ℝ) : ℂ) * Complex.I)
        + Complex.exp (-(Complex.I * (k.1 * a : ℝ)) + Complex.I * (3 * k.1 * a / 2 : ℝ)
          + -((Real.sqrt 3 * k.2 * a / 2 : ℝ) : ℂ) * Complex.I)
        + Complex.exp (-(Complex.I * (k.1 * a : ℝ))) := by
    simp only [Complex.exp_add]
    ring
  rw [hR]
  simp only [Delta, Fin.sum_univ_three, dotp, nnVec]
  push_cast
  ring_nf

theorem W2m_GrapheneTightBinding_Delta_diracK_eq_zero_and_Delta_diracKp_eq_zero (a : ℝ)
    (ha : 0 < a) :
    Delta a (diracK a) = 0 ∧ Delta a (diracKp a) = 0 := by
  have ha' : a ≠ 0 := ha.ne'
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have e1 : 3 * (diracK a).1 * a / 2 = Real.pi := by
    simp only [diracK]; first | (field_simp; ring1) | field_simp
  have e2 : Real.sqrt 3 * (diracK a).2 * a / 2 = Real.pi / 3 := by
    simp only [diracK]; first | (field_simp; ring1) | field_simp
  have e1' : 3 * (diracKp a).1 * a / 2 = Real.pi := by
    simp only [diracKp]; first | (field_simp; ring1) | field_simp
  have e2' : Real.sqrt 3 * (diracKp a).2 * a / 2 = -(Real.pi / 3) := by
    simp only [diracKp]; first | (field_simp; ring1) | field_simp
  have hexp : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [mul_comm]; exact Complex.exp_pi_mul_I
  constructor
  · rw [W2m_GrapheneTightBinding_Delta_closed_form, e1, e2, Real.cos_pi_div_three, hexp]
    push_cast
    ring
  · rw [W2m_GrapheneTightBinding_Delta_closed_form, e1', e2', Real.cos_neg,
      Real.cos_pi_div_three, hexp]
    push_cast
    ring

theorem W2m_GrapheneTightBinding_Delta_eq_sum (a : ℝ) (k : ℝ × ℝ) :
    Delta a k = ∑ j : Fin 3, ((Real.cos (dotp k (nnVec a j)) : ℂ)
      + (Real.sin (dotp k (nnVec a j)) : ℂ) * Complex.I) := by
  unfold Delta
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem W2m_GrapheneTightBinding_hMat_eq_pauli_sum (a t : ℝ) (k : ℝ × ℝ) :
    hMat a t k =
      -(t : ℂ) • ∑ j : Fin 3,
        ((Real.cos (dotp k (nnVec a j)) : ℂ) • pauliX
          - (Real.sin (dotp k (nnVec a j)) : ℂ) • pauliY) := by
  have hD := W2m_GrapheneTightBinding_Delta_eq_sum a k
  have hDc : (starRingEnd ℂ) (Delta a k) = ∑ j : Fin 3, ((Real.cos (dotp k (nnVec a j)) : ℂ)
      - (Real.sin (dotp k (nnVec a j)) : ℂ) * Complex.I) := by
    rw [hD, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hsum : ∑ j : Fin 3, ((Real.cos (dotp k (nnVec a j)) : ℂ) • pauliX
      - (Real.sin (dotp k (nnVec a j)) : ℂ) • pauliY)
      = !![0, Delta a k; (starRingEnd ℂ) (Delta a k), 0] := by
    rw [hDc, hD]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliX, pauliY, Matrix.sum_apply, Fin.sum_univ_three] <;>
      first | ring1 | exact Or.inl trivial | (left; ring1) | simp
  unfold hMat
  rw [hsum]

theorem W2m_GrapheneTightBinding_charpoly_offdiag (u v : ℂ) :
    (!![0, u; v, 0] : Matrix (Fin 2) (Fin 2) ℂ).charpoly = X ^ 2 - C (u * v) := by
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  simp only [map_add, map_sub, map_mul, map_zero]
  ring

theorem W2m_GrapheneTightBinding_hMat_charpoly (a t : ℝ) (k : ℝ × ℝ) :
    (hMat a t k).charpoly =
      X ^ 2 - C ((t : ℂ) ^ 2 * (Delta a k * (starRingEnd ℂ) (Delta a k))) := by
  have hM : hMat a t k = !![0, -(t : ℂ) * Delta a k; -(t : ℂ) * (starRingEnd ℂ) (Delta a k), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hMat]
  rw [hM, W2m_GrapheneTightBinding_charpoly_offdiag]
  congr 2
  ring

theorem W2m_GrapheneTightBinding_diracHam_charpoly (a t : ℝ) (q : ℝ × ℝ) :
    (diracHamK a t q).charpoly = X ^ 2 - C ((fermiVel a t * euclidNorm q : ℝ) ^ 2 : ℂ) ∧
      (diracHamKp a t q).charpoly = X ^ 2 - C ((fermiVel a t * euclidNorm q : ℝ) ^ 2 : ℂ) := by
  have hK : diracHamK a t q = !![0, (fermiVel a t : ℂ) * ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I);
      (fermiVel a t : ℂ) * ((q.1 : ℂ) - (q.2 : ℂ) * Complex.I), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diracHamK, pauliX, pauliY] <;>
      first | ring1 | exact Or.inl trivial | (left; ring1) | simp
  have hKp : diracHamKp a t q = !![0, (fermiVel a t : ℂ) * ((q.1 : ℂ) - (q.2 : ℂ) * Complex.I);
      (fermiVel a t : ℂ) * ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diracHamKp, pauliX, pauliY] <;>
      first | ring1 | exact Or.inl trivial | (left; ring1) | simp
  have hE : ((euclidNorm q : ℝ) : ℂ) ^ 2 = (q.1 : ℂ) ^ 2 + (q.2 : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, euclidNorm, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  constructor
  · rw [hK, W2m_GrapheneTightBinding_charpoly_offdiag]
    congr 2
    push_cast
    rw [mul_pow, hE]
    linear_combination (-(fermiVel a t : ℂ) ^ 2 * (q.2 : ℂ) ^ 2) * Complex.I_sq
  · rw [hKp, W2m_GrapheneTightBinding_charpoly_offdiag]
    congr 2
    push_cast
    rw [mul_pow, hE]
    linear_combination (-(fermiVel a t : ℂ) ^ 2 * (q.2 : ℂ) ^ 2) * Complex.I_sq

theorem W2m_GrapheneTightBinding_massiveDiracHam_charpoly_and_gap (a t M : ℝ) (ha : 0 < a)
    (ht : 0 < t) (hM : M ≠ 0) :
    (∀ q : ℝ × ℝ, (massiveDiracHam a t M q).charpoly =
        X ^ 2 - C ((fermiVel a t ^ 2 * (q.1 ^ 2 + q.2 ^ 2 + M ^ 2) : ℝ) : ℂ)) ∧
      0 < fermiVel a t * |M| ∧
      ∀ q : ℝ × ℝ, fermiVel a t * |M|
        ≤ fermiVel a t * Real.sqrt (q.1 ^ 2 + q.2 ^ 2 + M ^ 2) := by
  have hv : 0 < fermiVel a t := by unfold fermiVel; positivity
  refine ⟨?_, mul_pos hv (abs_pos.2 hM), ?_⟩
  · intro q
    have hK : massiveDiracHam a t M q = !![(fermiVel a t : ℂ) * (M : ℂ),
        (fermiVel a t : ℂ) * ((q.1 : ℂ) - (q.2 : ℂ) * Complex.I);
        (fermiVel a t : ℂ) * ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I),
        -((fermiVel a t : ℂ) * (M : ℂ))] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [massiveDiracHam, pauliX, pauliY, pauliZ] <;>
        first | ring1 | exact Or.inl trivial | (left; ring1) | simp
    rw [hK, Matrix.charpoly_fin_two, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
    have htr : (fermiVel a t : ℂ) * (M : ℂ) + -((fermiVel a t : ℂ) * (M : ℂ)) = 0 := by ring
    have hdet : (fermiVel a t : ℂ) * (M : ℂ) * -((fermiVel a t : ℂ) * (M : ℂ))
        - (fermiVel a t : ℂ) * ((q.1 : ℂ) - (q.2 : ℂ) * Complex.I)
          * ((fermiVel a t : ℂ) * ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I))
        = -(((fermiVel a t ^ 2 * (q.1 ^ 2 + q.2 ^ 2 + M ^ 2) : ℝ) : ℂ)) := by
      push_cast
      linear_combination ((fermiVel a t : ℂ) ^ 2 * (q.2 : ℂ) ^ 2) * Complex.I_sq
    rw [htr, hdet, map_zero, zero_mul, sub_zero, map_neg, ← sub_eq_add_neg]
  · intro q
    apply mul_le_mul_of_nonneg_left ?_ hv.le
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg q.1, sq_nonneg q.2]

theorem W2m_GrapheneTightBinding_exp_re (x : ℝ) :
    (Complex.exp (Complex.I * (x : ℂ))).re = Real.cos x := by
  rw [mul_comm]; exact Complex.exp_ofReal_mul_I_re x

theorem W2m_GrapheneTightBinding_exp_im (x : ℝ) :
    (Complex.exp (Complex.I * (x : ℂ))).im = Real.sin x := by
  rw [mul_comm]; exact Complex.exp_ofReal_mul_I_im x

theorem W2m_GrapheneTightBinding_normsq (a : ℝ) (k : ℝ × ℝ) :
    ‖Delta a k‖ ^ 2 = 3 + bandFun a k := by
  have hre : (Delta a k).re = Real.cos (dotp k (nnVec a 0)) + Real.cos (dotp k (nnVec a 1))
      + Real.cos (dotp k (nnVec a 2)) := by
    simp only [Delta, Fin.sum_univ_three, Complex.add_re, W2m_GrapheneTightBinding_exp_re]
  have him : (Delta a k).im = Real.sin (dotp k (nnVec a 0)) + Real.sin (dotp k (nnVec a 1))
      + Real.sin (dotp k (nnVec a 2)) := by
    simp only [Delta, Fin.sum_univ_three, Complex.add_im, W2m_GrapheneTightBinding_exp_im]
  have h0 : dotp k (nnVec a 0) = k.1 * a / 2 + Real.sqrt 3 * k.2 * a / 2 := by
    simp only [dotp, nnVec]; ring
  have h1 : dotp k (nnVec a 1) = k.1 * a / 2 - Real.sqrt 3 * k.2 * a / 2 := by
    simp only [dotp, nnVec]; ring
  have h2 : dotp k (nnVec a 2) = -(2 * (k.1 * a / 2)) := by
    simp only [dotp, nnVec]; ring
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him, h0, h1, h2]
  simp only [bandFun]
  have h4 : 3 * k.1 * a / 2 = 3 * (k.1 * a / 2) := by ring
  rw [h4]
  generalize hq : Real.sqrt 3 * k.2 * a / 2 = q
  have h3 : Real.sqrt 3 * k.2 * a = 2 * q := by rw [← hq]; ring
  rw [h3]
  generalize k.1 * a / 2 = p
  simp only [Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub, Real.cos_neg, Real.sin_neg,
    Real.cos_two_mul, Real.sin_two_mul, Real.cos_three_mul]
  linear_combination 4 * (Real.cos q - Real.cos p) ^ 2 * Real.sin_sq_add_cos_sq p

theorem W2m_GrapheneTightBinding_bandEnergy_eq_sqrt_three_add_bandFun (a t : ℝ) (ht : 0 ≤ t)
    (k : ℝ × ℝ) :
    bandEnergy a t k = t * Real.sqrt (3 + bandFun a k) := by
  unfold bandEnergy
  rw [← W2m_GrapheneTightBinding_normsq a k, Real.sqrt_sq (norm_nonneg _)]

theorem W2m_GrapheneTightBinding_bandEnergy_eq (a t : ℝ) (ht : 0 ≤ t) (k : ℝ × ℝ) :
    bandEnergy a t k =
      t * Real.sqrt (1 + 4 * Real.cos (3 * k.1 * a / 2) * Real.cos (Real.sqrt 3 * k.2 * a / 2)
        + 4 * Real.cos (Real.sqrt 3 * k.2 * a / 2) ^ 2) := by
  rw [W2m_GrapheneTightBinding_bandEnergy_eq_sqrt_three_add_bandFun a t ht k]
  congr 2
  simp only [bandFun]
  generalize hq : Real.sqrt 3 * k.2 * a / 2 = q
  have h3 : Real.sqrt 3 * k.2 * a = 2 * q := by rw [← hq]; ring
  rw [h3, Real.cos_two_mul]
  ring

theorem W2m_GrapheneTightBinding_expI (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem W2m_GrapheneTightBinding_cos23 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three] <;> norm_num

theorem W2m_GrapheneTightBinding_sin23 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
    Real.sin_pi_div_three]

theorem W2m_GrapheneTightBinding_abs_le (a e x : ℝ) (ha : 0 ≤ a) (he : 0 ≤ e)
    (h : x ^ 2 ≤ a ^ 2 * e ^ 2) : |x| ≤ a * e := by
  have h2 : |x| ≤ Real.sqrt ((a * e) ^ 2) := Real.abs_le_sqrt (by rw [mul_pow]; exact h)
  rwa [Real.sqrt_sq (by positivity)] at h2

theorem W2m_GrapheneTightBinding_dot_bound (a : ℝ) (ha : 0 < a) (j : Fin 3) (q : ℝ × ℝ) :
    |dotp q (nnVec a j)| ≤ a * euclidNorm q := by
  have he : 0 ≤ euclidNorm q := Real.sqrt_nonneg _
  have he2 : euclidNorm q ^ 2 = q.1 ^ 2 + q.2 ^ 2 := Real.sq_sqrt (by positivity)
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply W2m_GrapheneTightBinding_abs_le a _ _ ha.le he
  rw [he2]
  fin_cases j
  · simp only [dotp, nnVec]
    have key : a ^ 2 * (q.1 ^ 2 + q.2 ^ 2) - (q.1 * (a / 2) + q.2 * (Real.sqrt 3 * a / 2)) ^ 2
        - (a * (Real.sqrt 3 * q.1 - q.2)) ^ 2 / 4 = 0 := by
      linear_combination (-(a ^ 2 * (q.1 ^ 2 + q.2 ^ 2)) / 4) * hs3
    nlinarith [sq_nonneg (a * (Real.sqrt 3 * q.1 - q.2))]
  · simp only [dotp, nnVec]
    have key : a ^ 2 * (q.1 ^ 2 + q.2 ^ 2) - (q.1 * (a / 2) + q.2 * -(Real.sqrt 3 * a / 2)) ^ 2
        - (a * (Real.sqrt 3 * q.1 + q.2)) ^ 2 / 4 = 0 := by
      linear_combination (-(a ^ 2 * (q.1 ^ 2 + q.2 ^ 2)) / 4) * hs3
    nlinarith [sq_nonneg (a * (Real.sqrt 3 * q.1 + q.2))]
  · simp only [dotp, nnVec]
    nlinarith [sq_nonneg (a * q.2)]

theorem W2m_GrapheneTightBinding_expansion_gen (a : ℝ) (ha : 0 < a) (K : ℝ × ℝ)
    (hK : Delta a K = 0) :
    (fun q : ℝ × ℝ => Delta a (K + q) - ∑ j : Fin 3,
        Complex.exp (Complex.I * (dotp K (nnVec a j) : ℝ)) *
          (Complex.I * (dotp q (nnVec a j) : ℝ)))
      =o[nhds (0 : ℝ × ℝ)] fun q : ℝ × ℝ => euclidNorm q := by
  have hsplit : ∀ q : ℝ × ℝ, Delta a (K + q) - ∑ j : Fin 3,
        Complex.exp (Complex.I * (dotp K (nnVec a j) : ℝ)) *
          (Complex.I * (dotp q (nnVec a j) : ℝ))
      = ∑ j : Fin 3, Complex.exp (Complex.I * (dotp K (nnVec a j) : ℝ)) *
          (Complex.exp (Complex.I * (dotp q (nnVec a j) : ℝ)) - 1
            - Complex.I * (dotp q (nnVec a j) : ℝ)) := by
    intro q
    have h0 := hK
    unfold Delta at h0 ⊢
    have e : ∀ j : Fin 3, Complex.exp (Complex.I * (dotp (K + q) (nnVec a j) : ℝ))
        = Complex.exp (Complex.I * (dotp K (nnVec a j) : ℝ))
          * Complex.exp (Complex.I * (dotp q (nnVec a j) : ℝ)) := by
      intro j
      rw [← Complex.exp_add]
      congr 1
      simp only [dotp, Prod.fst_add, Prod.snd_add]
      push_cast
      ring
    simp only [e]
    rw [Fin.sum_univ_three] at h0
    simp only [Fin.sum_univ_three]
    linear_combination h0
  have hnorm1 : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
    intro x; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  have hnz : ∀ x : ℝ, ‖Complex.I * (x : ℂ)‖ = |x| := by
    intro x; simp
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hcont : Continuous (fun q : ℝ × ℝ => euclidNorm q) := by
    unfold euclidNorm; fun_prop
  have hlim : Filter.Tendsto (fun q : ℝ × ℝ => euclidNorm q) (nhds 0) (nhds 0) := by
    have := hcont.tendsto (0 : ℝ × ℝ)
    simpa [euclidNorm] using this
  have hδ : 0 < min (1 / a) (c / (3 * a ^ 2)) := lt_min (by positivity) (by positivity)
  filter_upwards [hlim (Iio_mem_nhds hδ)] with q hq
  beta_reduce
  have hq' : euclidNorm q < min (1 / a) (c / (3 * a ^ 2)) := hq
  rw [hsplit q]
  have he0 : 0 ≤ euclidNorm q := Real.sqrt_nonneg _
  have h1 : euclidNorm q < 1 / a := lt_of_lt_of_le hq' (min_le_left _ _)
  have h2 : euclidNorm q < c / (3 * a ^ 2) := lt_of_lt_of_le hq' (min_le_right _ _)
  have hae : a * euclidNorm q ≤ 1 := by
    rw [lt_div_iff₀ ha] at h1; linarith
  have hce : 3 * a ^ 2 * euclidNorm q ≤ c := by
    rw [lt_div_iff₀ (by positivity)] at h2; linarith
  have hterm : ∀ j : Fin 3,
      ‖Complex.exp (Complex.I * (dotp K (nnVec a j) : ℝ)) *
        (Complex.exp (Complex.I * (dotp q (nnVec a j) : ℝ)) - 1
          - Complex.I * (dotp q (nnVec a j) : ℝ))‖ ≤ (a * euclidNorm q) ^ 2 := by
    intro j
    rw [norm_mul, hnorm1, one_mul]
    have hb := W2m_GrapheneTightBinding_dot_bound a ha j q
    have hz1 : ‖Complex.I * ((dotp q (nnVec a j) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [hnz]; linarith
    calc _ ≤ ‖Complex.I * ((dotp q (nnVec a j) : ℝ) : ℂ)‖ ^ 2 :=
          Complex.norm_exp_sub_one_sub_id_le hz1
      _ ≤ (a * euclidNorm q) ^ 2 := by
          rw [hnz]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  calc _ ≤ ∑ j : Fin 3, ‖Complex.exp (Complex.I * (dotp K (nnVec a j) : ℝ)) *
        (Complex.exp (Complex.I * (dotp q (nnVec a j) : ℝ)) - 1
          - Complex.I * (dotp q (nnVec a j) : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, (a * euclidNorm q) ^ 2 := Finset.sum_le_sum fun j _ => hterm j
    _ = 3 * (a * euclidNorm q) ^ 2 := by first | simp | (simp; ring1)
    _ ≤ c * ‖euclidNorm q‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg he0]
      nlinarith [mul_le_mul_of_nonneg_left hce he0]

theorem W2m_GrapheneTightBinding_Delta_expansion_diracK (a : ℝ) (ha : 0 < a) :
    (fun q : ℝ × ℝ => Delta a (diracK a + q) -
        (-Complex.I * Complex.exp (-(Complex.I * ((diracK a).1 * a : ℝ))) *
          (3 * a / 2 : ℝ) * ((q.1 : ℂ) + Complex.I * (q.2 : ℂ))))
      =o[nhds (0 : ℝ × ℝ)] fun q : ℝ × ℝ => euclidNorm q := by
  have hK0 := (W2m_GrapheneTightBinding_Delta_diracK_eq_zero_and_Delta_diracKp_eq_zero a ha).1
  have H := W2m_GrapheneTightBinding_expansion_gen a ha (diracK a) hK0
  refine H.congr_left (fun q => ?_)
  congr 1
  have ha' : a ≠ 0 := ha.ne'
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have d0 : dotp (diracK a) (nnVec a 0) = 2 * Real.pi / 3 := by
    simp only [dotp, nnVec, diracK]; first | (field_simp; ring1) | field_simp
  have d1 : dotp (diracK a) (nnVec a 1) = 0 := by
    simp only [dotp, nnVec, diracK]; first | (field_simp; ring1) | field_simp
  have d2 : dotp (diracK a) (nnVec a 2) = -(2 * Real.pi / 3) := by
    simp only [dotp, nnVec, diracK]; first | (field_simp; ring1) | field_simp
  have dk : (diracK a).1 * a = 2 * Real.pi / 3 := by
    simp only [diracK]; first | (field_simp; ring1) | field_simp
  have hneg : -(Complex.I * ((2 * Real.pi / 3 : ℝ) : ℂ))
      = Complex.I * ((-(2 * Real.pi / 3) : ℝ) : ℂ) := by push_cast; ring
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [Fin.sum_univ_three, d0, d1, d2, dk, hneg, W2m_GrapheneTightBinding_expI,
    Real.cos_neg, Real.sin_neg, W2m_GrapheneTightBinding_cos23,
    W2m_GrapheneTightBinding_sin23, Real.cos_zero, Real.sin_zero]
  simp only [dotp, nnVec]
  push_cast
  linear_combination
    ((-3/4 : ℂ) * a * q.2 + (1/4 : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * a * q.2
      + (-3/4 : ℂ) * Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * a * q.2) * Complex.I_sq
    + ((-1/4 : ℂ) * a * q.2) * hs3

theorem W2m_GrapheneTightBinding_Delta_expansion_diracKp (a : ℝ) (ha : 0 < a) :
    (fun q : ℝ × ℝ => Delta a (diracKp a + q) -
        (-Complex.I * Complex.exp (-(Complex.I * ((diracKp a).1 * a : ℝ))) *
          (3 * a / 2 : ℝ) * ((q.1 : ℂ) - Complex.I * (q.2 : ℂ))))
      =o[nhds (0 : ℝ × ℝ)] fun q : ℝ × ℝ => euclidNorm q := by
  have hK0 := (W2m_GrapheneTightBinding_Delta_diracK_eq_zero_and_Delta_diracKp_eq_zero a ha).2
  have H := W2m_GrapheneTightBinding_expansion_gen a ha (diracKp a) hK0
  refine H.congr_left (fun q => ?_)
  congr 1
  have ha' : a ≠ 0 := ha.ne'
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  have d0 : dotp (diracKp a) (nnVec a 0) = 0 := by
    simp only [dotp, nnVec, diracKp]; first | (field_simp; ring1) | field_simp
  have d1 : dotp (diracKp a) (nnVec a 1) = 2 * Real.pi / 3 := by
    simp only [dotp, nnVec, diracKp]; first | (field_simp; ring1) | field_simp
  have d2 : dotp (diracKp a) (nnVec a 2) = -(2 * Real.pi / 3) := by
    simp only [dotp, nnVec, diracKp]; first | (field_simp; ring1) | field_simp
  have dk : (diracKp a).1 * a = 2 * Real.pi / 3 := by
    simp only [diracKp]; first | (field_simp; ring1) | field_simp
  have hneg : -(Complex.I * ((2 * Real.pi / 3 : ℝ) : ℂ))
      = Complex.I * ((-(2 * Real.pi / 3) : ℝ) : ℂ) := by push_cast; ring
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [Fin.sum_univ_three, d0, d1, d2, dk, hneg, W2m_GrapheneTightBinding_expI,
    Real.cos_neg, Real.sin_neg, W2m_GrapheneTightBinding_cos23,
    W2m_GrapheneTightBinding_sin23, Real.cos_zero, Real.sin_zero]
  simp only [dotp, nnVec]
  push_cast
  linear_combination
    ((3/4 : ℂ) * a * q.2 + (-1/4 : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * a * q.2
      + (3/4 : ℂ) * Complex.I * ((Real.sqrt 3 : ℝ) : ℂ) * a * q.2) * Complex.I_sq
    + ((1/4 : ℂ) * a * q.2) * hs3

theorem W2m_GrapheneTightBinding_graphene_dirac_cone (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    (∀ k : ℝ × ℝ, (hMat a t k).charpoly = X ^ 2 - C ((bandEnergy a t k : ℂ) ^ 2)) ∧
      bandEnergy a t (diracK a) = 0 ∧
      (fun q : ℝ × ℝ => bandEnergy a t (diracK a + q) - fermiVel a t * euclidNorm q)
        =o[nhds (0 : ℝ × ℝ)] fun q : ℝ × ℝ => euclidNorm q := by
  have hK0 := (W2m_GrapheneTightBinding_Delta_diracK_eq_zero_and_Delta_diracKp_eq_zero a ha).1
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rw [W2m_GrapheneTightBinding_hMat_charpoly]
    congr 2
    unfold bandEnergy
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  · simp [bandEnergy, hK0]
  · have H := (W2m_GrapheneTightBinding_Delta_expansion_diracK a ha).const_mul_left (t : ℂ)
    refine (Asymptotics.isBigO_of_le _ (fun q => ?_)).trans_isLittleO H
    have hL : ‖-Complex.I * Complex.exp (-(Complex.I * ((diracK a).1 * a : ℝ))) *
        ((3 * a / 2 : ℝ) : ℂ) * ((q.1 : ℂ) + Complex.I * (q.2 : ℂ))‖
        = 3 * a / 2 * euclidNorm q := by
      have hn1 : ‖Complex.exp (-(Complex.I * (((diracK a).1 * a : ℝ) : ℂ)))‖ = 1 := by
        rw [show -(Complex.I * (((diracK a).1 * a : ℝ) : ℂ))
            = ((-((diracK a).1 * a) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      have hq : ‖(q.1 : ℂ) + Complex.I * (q.2 : ℂ)‖ = euclidNorm q := by
        rw [mul_comm, Complex.norm_add_mul_I]; rfl
      rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, hn1, hq, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht]
    unfold bandEnergy fermiVel
    rw [show t * ‖Delta a (diracK a + q)‖ - 3 * a * t / 2 * euclidNorm q
        = t * (‖Delta a (diracK a + q)‖ - 3 * a / 2 * euclidNorm q) by ring, abs_mul,
      abs_of_pos ht, ← hL]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) ht.le

theorem solution (a t : ℝ) (q : ℝ × ℝ) :
    (diracHamK a t q).charpoly = X ^ 2 - C ((fermiVel a t * euclidNorm q : ℝ) ^ 2 : ℂ) ∧
      (diracHamKp a t q).charpoly = X ^ 2 - C ((fermiVel a t * euclidNorm q : ℝ) ^ 2 : ℂ) := by
  apply W2m_GrapheneTightBinding_diracHam_charpoly <;> assumption
