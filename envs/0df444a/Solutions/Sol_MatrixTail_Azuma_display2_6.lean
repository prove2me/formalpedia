-- Prove2me | solution 1 for MatrixTail.Azuma.display2_6
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T18:49:22.174302+00:00
-- url     : https://prove2.me/submissions/cde03b8d-1288-485a-8ecb-a0b874f08276

import Definitions.Def_MatrixTail_Azuma_Model

open Matrix Unitary InnerProductSpace
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

private lemma weighted_diagonal {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (lam : Fin d → ℝ) (i : Fin d) :
    ((Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℂ) U)
      (diagonal (fun j => (lam j : ℂ))) i i).re = ∑ j, ‖U i j‖ ^ 2 * lam j := by
  simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    star_eq_conjTranspose, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

lemma psd_diagonal_power_le {d : ℕ} (D : Matrix (Fin d) (Fin d) ℂ)
    (hD : D.PosSemidef) (n : ℕ) (i : Fin d) : (D i i).re ^ n ≤ ((D ^ n) i i).re := by
  let U := hD.1.eigenvectorUnitary
  let phi := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℂ) U
  let lam := hD.1.eigenvalues
  have hsp : D = phi (diagonal (fun j => (lam j : ℂ))) := by
    simpa [phi, U, lam, Function.comp_def] using hD.1.spectral_theorem
  have hp : D ^ n = phi (diagonal (fun j => ((lam j ^ n : ℝ) : ℂ))) := by
    rw [hsp, ← map_pow, diagonal_pow]
    apply congrArg phi
    apply congrArg diagonal
    funext j
    exact (Complex.ofReal_pow (lam j) n).symm
  have hw : ∑ j, ‖U i j‖ ^ 2 = 1 := by
    have he := weighted_diagonal U (fun _ => 1) i
    simpa [phi, map_one] using he.symm
  have hd : (D i i).re = ∑ j, ‖U i j‖ ^ 2 * lam j := by
    rw [hsp]
    exact weighted_diagonal U lam i
  have hdp : ((D ^ n) i i).re = ∑ j, ‖U i j‖ ^ 2 * lam j ^ n := by
    rw [hp]
    exact weighted_diagonal U (fun j => lam j ^ n) i
  rw [hd, hdp]
  simpa only [smul_eq_mul] using
    (convexOn_pow (𝕜 := ℝ) n).map_sum_le
      (fun j (_ : j ∈ Finset.univ) => sq_nonneg ‖U i j‖) hw
      (fun j (_ : j ∈ Finset.univ) => hD.eigenvalues_nonneg j)

lemma upper_diagonal_pow {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ)
    (hT : T.IsUpperTriangular) (n : ℕ) (i : Fin d) : (T ^ n) i i = T i i ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, pow_succ, ← ih]
    apply Finset.sum_eq_single i
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hj | hj
      · rw [hT.pow n hj, zero_mul]
      · rw [hT hj, mul_zero]
    · simp

lemma upper_trace_even_le {d : ℕ} (T : Matrix (Fin d) (Fin d) ℂ)
    (hT : T.IsUpperTriangular) (n : ℕ) :
    (trace (T ^ (2*n))).re ≤ (trace ((Tᴴ * T) ^ n)).re := by
  have hD : (Tᴴ * T).PosSemidef := posSemidef_conjTranspose_mul_self T
  simp only [trace, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  change ((T ^ (2*n)) i i).re ≤ (((Tᴴ * T) ^ n) i i).re
  rw [upper_diagonal_pow T hT]
  have hd : ‖T i i‖ ^ 2 ≤ ((Tᴴ * T) i i).re := by
    have he : ((Tᴴ * T) i i).re = ∑ j, ‖T j i‖ ^ 2 := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply]
    rw [he]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖T j i‖) (Finset.mem_univ i)
  calc
    (T i i ^ (2*n)).re ≤ ‖T i i ^ (2*n)‖ := Complex.re_le_norm _
    _ = (‖T i i‖ ^ 2) ^ n := by rw [norm_pow, pow_mul]
    _ ≤ ((Tᴴ * T) i i).re ^ n := pow_le_pow_left₀ (sq_nonneg _) hd n
    _ ≤ _ := psd_diagonal_power_le _ hD n i

lemma trace_unitary_conj {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    trace (Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℂ) U X) = trace X := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  change trace ((star (U : Matrix (Fin d) (Fin d) ℂ) * (U : Matrix (Fin d) (Fin d) ℂ)) * X) = trace X
  rw [Unitary.star_mul_self_of_mem U.property, one_mul]

lemma conjugated_trace_even_le {d : ℕ} (C T : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (hT : T.IsUpperTriangular)
    (hC : C = (U : Matrix (Fin d) (Fin d) ℂ) * T * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)
    (n : ℕ) : (trace (C ^ (2*n))).re ≤ (trace ((Cᴴ*C)^n)).re := by
  let phi := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℂ) U
  have hc : C = phi T := by simpa [phi, Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose] using hC
  have ht (X : Matrix (Fin d) (Fin d) ℂ) : trace (phi X) = trace X := trace_unitary_conj U X
  have hs : (phi T)ᴴ = phi Tᴴ := by simpa only [Matrix.star_eq_conjTranspose] using (map_star phi T).symm
  rw [hc, ← map_pow, ht, hs, ← map_mul, ← map_pow, ht]
  exact upper_trace_even_le T hT n

lemma trace_product_pow_comm {d : ℕ} (X Y : Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    trace ((X*Y)^n) = trace ((Y*X)^n) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [pow_succ, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.mul_assoc, mul_pow_mul]
    simp only [← Matrix.mul_assoc, ← pow_succ']

open Matrix InnerProductSpace Module
open scoped ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
lemma triangularize_basis {d : ℕ} (C : Matrix (Fin d) (Fin d) ℂ)
    (b : Basis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (lam : Fin d → ℂ)
    (hb : ∀ i, C.toEuclideanLin (b i) = lam i • b i) :
    ∃ (U : Matrix.unitaryGroup (Fin d) ℂ) (T : Matrix (Fin d) (Fin d) ℂ),
      T.IsUpperTriangular ∧ C = (U : Matrix (Fin d) (Fin d) ℂ) * T * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  let hd : Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = Fintype.card (Fin d) := by simp
  let q := gramSchmidtOrthonormalBasis hd b
  let s := EuclideanSpace.basisFun (Fin d) ℂ
  let T := LinearMap.toMatrix q.toBasis q.toBasis C.toEuclideanLin
  have hq (j : Fin d) : q j = gramSchmidtNormed ℂ b j := by
    apply gramSchmidtOrthonormalBasis_apply hd
    have h := gramSchmidtNormed_unit_length j b.linearIndependent
    intro he
    rw [he, norm_zero] at h
    exact zero_ne_one h
  have ht : T.IsUpperTriangular := by
    intro i j hji
    dsimp only [T]
    rw [LinearMap.toMatrix_apply]
    change q.toBasis.repr (C.toEuclideanLin (q j)) i = 0
    rw [OrthonormalBasis.coe_toBasis_repr_apply]
    rw [← b.sum_repr (q j), map_sum]
    simp only [map_smul, hb, smul_smul, map_sum, map_smul]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hjk : j < k
    · have hz : b.repr (q j) k = 0 := by
        rw [hq, gramSchmidtNormed, map_smul, Finsupp.smul_apply,
          gramSchmidt_triangular hjk b, smul_zero]
      simp [hz]
    · have hki : k < i := (le_of_not_gt hjk).trans_lt hji
      have hz : q.repr (b k) i = 0 :=
        gramSchmidtOrthonormalBasis_inv_triangular' hd b hki
      simp [hz]
  let U : Matrix.unitaryGroup (Fin d) ℂ :=
    ⟨s.toBasis.toMatrix q.toBasis, s.toMatrix_orthonormalBasis_mem_unitary q⟩
  refine ⟨U, T, ht, ?_⟩
  have hu : (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = q.toBasis.toMatrix s.toBasis := by
    have hleft := s.toMatrix_orthonormalBasis_conjTranspose_mul_self q
    have hright := s.toBasis.toMatrix_mul_toMatrix_flip q.toBasis
    exact left_inv_eq_right_inv hleft hright
  rw [hu]
  change C = s.toBasis.toMatrix q.toBasis *
    LinearMap.toMatrix q.toBasis q.toBasis C.toEuclideanLin * q.toBasis.toMatrix s.toBasis
  rw [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

open Matrix Module InnerProductSpace
open scoped ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
lemma product_eigenbasis {d : ℕ} (R B : Matrix (Fin d) (Fin d) ℂ)
    (hR : R.IsHermitian) (hB : B.IsHermitian) (hRu : IsUnit R) :
    ∃ (b : Basis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) (lam : Fin d → ℂ),
      ∀ i, (R ^ 2 * B).toEuclideanLin (b i) = lam i • b i := by
  let s := (EuclideanSpace.basisFun (Fin d) ℂ).toBasis
  let D := R * B * R
  have hD : D.IsHermitian := by
    dsimp [D]
    simp only [Matrix.IsHermitian, conjTranspose_mul, hR.eq, hB.eq, Matrix.mul_assoc]
  let e := Matrix.toLinearEquiv s R ((Matrix.isUnit_iff_isUnit_det R).mp hRu)
  let b := hD.eigenvectorBasis.toBasis.map e
  refine ⟨b, fun i => (hD.eigenvalues i : ℂ), ?_⟩
  intro i
  have he (v : EuclideanSpace ℂ (Fin d)) : e v = R.toEuclideanLin v := by
    change Matrix.toLin s s R v = R.toEuclideanLin v
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hde (i : Fin d) : D.toEuclideanLin (hD.eigenvectorBasis i) =
      (hD.eigenvalues i : ℂ) • hD.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    simpa only [Matrix.ofLp_toEuclideanLin_apply, WithLp.ofLp_smul,
      Pi.smul_apply, smul_eq_mul, Complex.real_smul] using
      congrFun (hD.mulVec_eigenvectorBasis i) j
  change (R ^ 2 * B).toEuclideanLin (e (hD.eigenvectorBasis i)) =
    (hD.eigenvalues i : ℂ) • e (hD.eigenvectorBasis i)
  rw [he, ← map_smul R.toEuclideanLin, ← hde]
  have hm : (R ^ 2 * B) * R = R * D := by simp only [D, pow_two, Matrix.mul_assoc]
  have hl (X Y : Matrix (Fin d) (Fin d) ℂ) (v : EuclideanSpace ℂ (Fin d)) :
      X.toEuclideanLin (Y.toEuclideanLin v) = (X*Y).toEuclideanLin v := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact congrArg (fun f : Module.End ℂ (EuclideanSpace ℂ (Fin d)) => f v)
      (Matrix.toLin_mul s s s X Y).symm
  rw [hl, hl, hm]

open Filter Asymptotics NormedSpace
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma norm_pow_difference {E : Type*} [NormedRing E] [NormOneClass E]
    (x y : E) (c : ℝ) (hc : 1 ≤ c) (hx : ‖x‖ ≤ c) (hy : ‖y‖ ≤ c) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ (n : ℝ) * c ^ n * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : x ^ (n+1) - y ^ (n+1) = (x ^ n - y ^ n) * x + y ^ n * (x - y) := by
      rw [pow_succ, pow_succ, sub_mul, mul_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖(x ^ n - y ^ n) * x‖ + ‖y ^ n * (x - y)‖ := norm_add_le _ _
      _ ≤ ‖x ^ n - y ^ n‖ * ‖x‖ + ‖y ^ n‖ * ‖x - y‖ := by gcongr <;> apply norm_mul_le
      _ ≤ ((n : ℝ) * c ^ n * ‖x - y‖) * c + c ^ n * ‖x - y‖ := by
        gcongr
        exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hy n)
      _ ≤ (n+1 : ℕ) * c ^ (n+1) * ‖x - y‖ := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        nlinarith [mul_nonneg (pow_nonneg (by linarith : 0 ≤ c) n) (norm_nonneg (x-y))]

lemma product_derivative {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
    (A B : E) :
    HasDerivAt (fun t : ℝ => exp (t • A) * exp (t • B) - exp (t • (A+B))) 0 0 := by
  have ha : HasDerivAt (fun t : ℝ => exp (t • A)) A 0 := by
    simpa using hasDerivAt_exp_smul_const A (0 : ℝ)
  have hb : HasDerivAt (fun t : ℝ => exp (t • B)) B 0 := by
    simpa using hasDerivAt_exp_smul_const B (0 : ℝ)
  have hab : HasDerivAt (fun t : ℝ => exp (t • (A+B))) (A+B) 0 := by
    simpa using hasDerivAt_exp_smul_const (A+B) (0 : ℝ)
  simpa using (ha.fun_mul hb).fun_sub hab


lemma tendsto_power_from_derivative {E : Type*} [NormedRing E] [NormedAlgebra ℝ E]
    [CompleteSpace E] [NormOneClass E] (f : ℝ → E) (a : E)
    (hf : HasDerivAt f a 0) (hf0 : f 0 = 1) :
    Tendsto (fun n : ℕ => f (1 / (n+1 : ℝ)) ^ (n+1)) atTop (nhds (exp a)) := by
  letI : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  let g := fun t : ℝ => exp (t • a)
  have hg : HasDerivAt g a 0 := by
    simpa [g] using hasDerivAt_exp_smul_const a (0 : ℝ)
  have hg0 : g 0 = 1 := by simp [g]
  obtain ⟨C, hC, hfC⟩ := hf.isBigO_sub.exists_nonneg
  obtain ⟨D, hD, hgD⟩ := hg.isBigO_sub.exists_nonneg
  let K := max C D
  have hK : 0 ≤ K := hC.trans (le_max_left _ _)
  have hnorm : ∀ᶠ t in nhds (0 : ℝ),
      ‖f t‖ ≤ 1 + K * ‖t‖ ∧ ‖g t‖ ≤ 1 + K * ‖t‖ := by
    filter_upwards [hfC.bound, hgD.bound] with t hft hgt
    simp only [hf0, hg0, sub_zero] at hft hgt
    constructor
    · calc
        ‖f t‖ = ‖(f t - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ ‖f t - 1‖ + ‖(1 : E)‖ := norm_add_le _ _
        _ ≤ C * ‖t‖ + 1 := by rw [norm_one]; linarith only [hft]
        _ ≤ 1 + K * ‖t‖ := by
          have hm := mul_le_mul_of_nonneg_right (le_max_left C D) (norm_nonneg t)
          simpa only [add_comm] using add_le_add_left hm 1
    · calc
        ‖g t‖ = ‖(g t - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ ‖g t - 1‖ + ‖(1 : E)‖ := norm_add_le _ _
        _ ≤ D * ‖t‖ + 1 := by rw [norm_one]; linarith only [hgt]
        _ ≤ 1 + K * ‖t‖ := by
          have hm := mul_le_mul_of_nonneg_right (le_max_right C D) (norm_nonneg t)
          simpa only [add_comm] using add_le_add_left hm 1
  have he : HasDerivAt (fun t => f t - g t) 0 0 := by
    simpa using hf.fun_sub hg
  have herr : Tendsto (fun t : ℝ => ‖t‖⁻¹ * ‖f t - g t‖) (nhds 0) (nhds 0) := by
    simpa only [hf0, hg0, sub_self, smul_zero, sub_zero] using
      (hasDerivAt_iff_tendsto.mp he)
  have ht : Tendsto (fun n : ℕ => 1 / (n+1 : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hn (n : ℕ) : 0 < (n+1 : ℝ) := by positivity
  have hr (n : ℕ) : 0 < 1 / (n+1 : ℝ) := by positivity
  have hb (n : ℕ) : (1 + K * (1 / (n+1 : ℝ))) ^ (n+1) ≤ Real.exp K := by
    calc
      _ ≤ (Real.exp (K * (1 / (n+1 : ℝ)))) ^ (n+1) := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp (K * (1 / (n+1 : ℝ)))]
      _ = Real.exp K := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        field_simp
  have hnear : ∀ᶠ n : ℕ in atTop,
      ‖f (1 / (n+1 : ℝ)) ^ (n+1) - exp a‖ ≤
        Real.exp K * ((n+1 : ℝ) * ‖f (1 / (n+1 : ℝ)) - g (1 / (n+1 : ℝ))‖) := by
    filter_upwards [ht.eventually hnorm] with n hng
    have heq : g (1 / (n+1 : ℝ)) ^ (n+1) = exp a := by
      change exp ((1 / (n+1 : ℝ)) • a) ^ (n+1) = exp a
      rw [← NormedSpace.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      have hi : ((n+1 : ℕ) : ℝ) * (1 / (n+1 : ℝ)) = 1 := by push_cast; field_simp
      rw [hi, one_smul]
    rw [← heq]
    have hp := norm_pow_difference (f (1 / (n+1 : ℝ))) (g (1 / (n+1 : ℝ)))
      (1 + K * (1 / (n+1 : ℝ))) (by nlinarith [mul_nonneg hK (hr n).le]) (by simpa only [Real.norm_of_nonneg (hr n).le] using hng.1)
      (by simpa only [Real.norm_of_nonneg (hr n).le] using hng.2) (n+1)
    calc
      _ ≤ (n+1 : ℕ) * (1 + K * (1 / (n+1 : ℝ))) ^ (n+1) *
          ‖f (1 / (n+1 : ℝ)) - g (1 / (n+1 : ℝ))‖ := hp
      _ ≤ Real.exp K * ((n+1 : ℝ) * ‖f (1 / (n+1 : ℝ)) - g (1 / (n+1 : ℝ))‖) := by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left (hb n)
          (mul_nonneg (hn n).le (norm_nonneg (f (1 / (n+1 : ℝ)) - g (1 / (n+1 : ℝ)))))]
  have hzero : Tendsto (fun n : ℕ => (n+1 : ℝ) *
      ‖f (1 / (n+1 : ℝ)) - g (1 / (n+1 : ℝ))‖) atTop (nhds 0) := by
    have heq (n : ℕ) : ‖1 / (n+1 : ℝ)‖⁻¹ = n+1 := by
      rw [Real.norm_eq_abs, abs_of_pos (hr n), one_div, inv_inv]
    simpa only [Function.comp_def, heq] using herr.comp ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hnear
      (by simpa using hzero.const_mul (Real.exp K)))

open NormedSpace
open scoped Matrix.Norms.L2Operator
lemma exp_two {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : exp X ^ 2 = exp ((2 : ℝ) • X) := by
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  rw [pow_two, ← NormedSpace.exp_add_of_commute (Commute.refl X)]
  congr 1
  module
lemma exp_hermitian {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) :
    (exp X).IsHermitian := hX.isSelfAdjoint.exp

lemma exp_trace_double {d : ℕ} (X Y : Matrix (Fin d) (Fin d) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (n : ℕ) :
    (trace ((exp X * exp Y)^(2*n))).re ≤
      (trace ((exp ((2 : ℝ) • X) * exp ((2 : ℝ) • Y))^n)).re := by
  let R := exp ((1/2 : ℝ) • X)
  have hR : R.IsHermitian := exp_hermitian _ (hX.smul (show IsSelfAdjoint (1/2 : ℝ) from by simp [IsSelfAdjoint]))
  have hRR : R ^ 2 = exp X := by
    rw [exp_two, smul_smul]
    norm_num
  obtain ⟨b, lam, hb⟩ := product_eigenbasis R (exp Y) hR (exp_hermitian Y hY) (isUnit_exp _)
  rw [hRR] at hb
  obtain ⟨U, T, ht, hc⟩ := triangularize_basis (exp X*exp Y) b lam hb
  have h := conjugated_trace_even_le _ T U ht hc n
  have hg : (exp X * exp Y)ᴴ * (exp X * exp Y) = exp Y * (exp X ^ 2 * exp Y) := by
    simp only [conjTranspose_mul, (exp_hermitian X hX).eq,
      (exp_hermitian Y hY).eq, pow_two, Matrix.mul_assoc]
  have htrace : trace ((exp Y * (exp X ^ 2 * exp Y))^n) =
      trace ((exp ((2 : ℝ) • X)*exp ((2 : ℝ) • Y))^n) := by
    rw [trace_product_pow_comm (exp Y) (exp X ^ 2 * exp Y) n]
    simp only [Matrix.mul_assoc, ← pow_two, exp_two]
  rw [hg, htrace] at h
  exact h

lemma exp_trace_dyadic {d : ℕ} (X Y : Matrix (Fin d) (Fin d) ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (k : ℕ) :
    (trace ((exp X*exp Y)^(2^k))).re ≤ (trace (exp X^(2^k)*exp Y^(2^k))).re := by
  induction k generalizing X Y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    have h2 := ih ((2 : ℝ) • X) ((2 : ℝ) • Y)
      (hX.smul (show IsSelfAdjoint (2 : ℝ) from by simp [IsSelfAdjoint]))
      (hY.smul (show IsSelfAdjoint (2 : ℝ) from by simp [IsSelfAdjoint]))
    rw [← exp_two X, ← exp_two Y, ← pow_mul, ← pow_mul] at h2
    have h1 := exp_trace_double X Y hX hY (2^k)
    rw [← exp_two X, ← exp_two Y] at h1
    exact h1.trans h2

lemma exp_scaled_pow {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) (hm : m ≠ 0) :
    exp ((1 / (m : ℝ)) • X) ^ m = exp X := by
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  rw [← NormedSpace.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [hm]

open MatrixTail.Azuma
theorem solution {d : ℕ} (A H : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hH : H.IsHermitian) :
    trExp (A+H) ≤ (Matrix.trace (mexp A * mexp H)).re := by
  have hexp (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) :
      mexp X = exp X := CFC.real_exp_eq_normedSpace_exp hX.isSelfAdjoint
  rw [trExp, hexp (A+H) (hA.add hH), hexp A hA, hexp H hH]
  by_cases hd : d = 0
  · subst d
    simp [Matrix.trace]
  letI : NeZero d := ⟨hd⟩
  let f := fun t : ℝ => exp (t • A) * exp (t • H)
  have ha : HasDerivAt (fun t : ℝ => exp (t • A)) A 0 := by
    simpa using hasDerivAt_exp_smul_const A (0 : ℝ)
  have hh : HasDerivAt (fun t : ℝ => exp (t • H)) H 0 := by
    simpa using hasDerivAt_exp_smul_const H (0 : ℝ)
  have hf : HasDerivAt f (A+H) 0 := by simpa [f] using ha.fun_mul hh
  have hf0 : f 0 = 1 := by simp [f]
  have hlimit := tendsto_power_from_derivative f (A+H) hf hf0
  have hk : Tendsto (fun k : ℕ => 2^k-1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2 : ℕ) by norm_num)).eventually_ge_atTop (n+1)] with k hk
    omega
  have heq (k : ℕ) : 2^k-1+1 = 2^k := Nat.sub_add_cancel (Nat.one_le_pow k 2 (by omega))
  have hm : Tendsto (fun k : ℕ => (exp ((1 / ((2^k : ℕ) : ℝ)) • A) *
      exp ((1 / ((2^k : ℕ) : ℝ)) • H))^(2^k)) atTop (nhds (exp (A+H))) := by
    have h := hlimit.comp hk
    have hcast (k : ℕ) : ((2^k-1 : ℕ) : ℝ) + 1 = ((2^k : ℕ) : ℝ) := by
      exact_mod_cast heq k
    simpa only [Function.comp_def, f, hcast, heq] using h
  have hc : Continuous (fun X : Matrix (Fin d) (Fin d) ℂ => (trace X).re) := by
    exact Complex.continuous_re.comp (Matrix.traceLinearMap (Fin d) ℂ ℂ).continuous_of_finiteDimensional
  apply le_of_tendsto (hc.tendsto _ |>.comp hm)
  apply Eventually.of_forall
  intro k
  have h := exp_trace_dyadic ((1 / ((2^k : ℕ) : ℝ)) • A)
    ((1 / ((2^k : ℕ) : ℝ)) • H)
    (hA.smul (by simp [IsSelfAdjoint])) (hH.smul (by simp [IsSelfAdjoint])) k
  rw [exp_scaled_pow A _ (by positivity), exp_scaled_pow H _ (by positivity)] at h
  exact h
