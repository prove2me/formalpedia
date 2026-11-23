-- Prove2me | solution 1 for MomentPolytopes.QuantumFunctionals.lemma_7_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:46:15.792645+00:00
-- url     : https://prove2.me/submissions/7b5d1c4f-ebac-4b92-a6f4-0bd48a7522fb

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntanglementPolytope
import Definitions.Def_MomentPolytopes_QuantumFunctionals_QuantumFunctional
import Definitions.Def_MomentPolytopes_QuantumFunctionals_MirrorDescent
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntropicScaling

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace Aux74

open MomentPolytopes.QuantumFunctionals

/-! ### 1. Basic complex & Frobenius norm helpers -/

lemma star_mul_self_eq_norm_sq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq]
  apply Complex.ext <;> (simp [Complex.normSq_apply]; try ring)

lemma mul_star_self_eq_norm_sq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, star_mul_self_eq_norm_sq]

lemma frobNorm_sq_eq_trace_conjTranspose_mul {m : Type} [Fintype m] (M : Matrix m m ℂ) :
    ∑ i, ∑ j, ‖M i j‖ ^ 2 = (Mᴴ * M).trace.re := by
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul_self_eq_norm_sq, Complex.ofReal_re]

lemma norm_entry_le_frobNorm {m : Type} [Fintype m] (M : Matrix m m ℂ) (i j : m) :
    ‖M i j‖ ≤ frobNorm M := by
  unfold frobNorm
  rw [← Real.sqrt_sq (norm_nonneg (M i j))]
  apply Real.sqrt_le_sqrt
  have h1 : ‖M i j‖ ^ 2 ≤ ∑ j', ‖M i j'‖ ^ 2 :=
    Finset.single_le_sum (fun j' _ => sq_nonneg ‖M i j'‖) (Finset.mem_univ j)
  have h2 : ∑ j', ‖M i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖M i' j'‖ ^ 2 :=
    Finset.single_le_sum (fun i' _ => Finset.sum_nonneg fun j' _ => sq_nonneg ‖M i' j'‖)
      (Finset.mem_univ i)
  exact le_trans h1 h2

/-! ### 2. Spectrum, `cfc`, and `vnEntropy` -/

lemma sum_spec_eq_sum_eigenvalues {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.IsHermitian) (g : ℝ → ℝ) :
    ∑ i : Fin m, g (spec A i) = ∑ i : Fin m, g (hA.eigenvalues i) := by
  unfold spec
  rw [dif_pos hA]
  let e1 : Fin m ≃ Fin (Fintype.card (Fin m)) :=
    (Fin.castOrderIso (Fintype.card_fin m).symm).toEquiv
  let e2 : Fin m ≃ Fin (Fintype.card (Fin m)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin m)))).symm
  have h1 : ∑ i : Fin m, g (hA.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm i)) =
      ∑ k : Fin (Fintype.card (Fin m)), g (hA.eigenvalues₀ k) :=
    Equiv.sum_comp e1 (fun k => g (hA.eigenvalues₀ k))
  have h2 : ∑ i : Fin m, g (hA.eigenvalues i) =
      ∑ k : Fin (Fintype.card (Fin m)), g (hA.eigenvalues₀ k) :=
    Equiv.sum_comp e2 (fun k => g (hA.eigenvalues₀ k))
  exact h1.trans h2.symm

lemma spec_nonneg_of_posSemidef {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosSemidef) (i : Fin m) : 0 ≤ spec A i := by
  unfold spec
  rw [dif_pos hA.isHermitian]
  let e2 : Fin m ≃ Fin (Fintype.card (Fin m)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin m)))).symm
  let k := Fin.cast (Fintype.card_fin m).symm i
  have hk : hA.isHermitian.eigenvalues₀ k = hA.isHermitian.eigenvalues (e2.symm k) := by
    simp [Matrix.IsHermitian.eigenvalues, e2]
  rw [hk]
  exact hA.eigenvalues_nonneg (e2.symm k)

lemma cfc_eq_unitary_diag {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
      Matrix.diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ)) *
      (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc]
  rfl

lemma self_eq_unitary_diag {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
      Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ := by
  exact hA.spectral_theorem

lemma isHermitian_unitary_diag {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℝ) :
    (U * Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ)) * Uᴴ).IsHermitian := by
  set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ))
  have hD : Dᴴ = D := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [D]
    · simp [D, hij, Ne.symm hij]
  simp [Matrix.IsHermitian, Matrix.conjTranspose_mul, hD, Matrix.mul_assoc]

lemma isHermitian_cfc {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) : (cfc f A).IsHermitian := by
  rw [cfc_eq_unitary_diag hA f]
  exact isHermitian_unitary_diag _ _

lemma dotProduct_unitary_diag {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ) (μ : Fin m → ℝ)
    (x : Fin m → ℂ) :
    star x ⬝ᵥ (U * Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ)) * Uᴴ) *ᵥ x =
      ∑ i : Fin m, ((μ i * ‖(Uᴴ *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
  set y : Fin m → ℂ := Uᴴ *ᵥ x
  set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ))
  have hmv : (U * D * Uᴴ) *ᵥ x = U *ᵥ (D *ᵥ y) := by
    simp [y, Matrix.mul_assoc, Matrix.mulVec_mulVec]
  have hst : star x ᵥ* U = star y := by
    simp [y, Matrix.star_mulVec]
  rw [hmv, Matrix.dotProduct_mulVec, hst]
  simp only [dotProduct, Pi.star_apply, D, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc
    star (y i) * (((μ i : ℝ) : ℂ) * y i) = ((μ i : ℝ) : ℂ) * (star (y i) * y i) := by ring
    _ = ((μ i * ‖y i‖ ^ 2 : ℝ) : ℂ) := by rw [star_mul_self_eq_norm_sq]; push_cast; ring

lemma posDef_cfc_of_pos {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (hf : ∀ i, 0 < f (hA.eigenvalues i)) :
    (cfc f A).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (isHermitian_cfc hA f) ?_
  intro x hx
  rw [cfc_eq_unitary_diag hA f, dotProduct_unitary_diag]
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  set y : Fin m → ℂ := Uᴴ *ᵥ x
  have hy : y ≠ 0 := by
    intro hy0
    have hUx : U *ᵥ y = x := by
      have hUU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
      calc
        U *ᵥ y = (U * Uᴴ) *ᵥ x := by simp [y, Matrix.mulVec_mulVec]
        _ = x := by rw [hUU, Matrix.one_mulVec]
    rw [hy0, Matrix.mulVec_zero] at hUx
    exact hx hUx.symm
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy
  have hpos : 0 < ∑ i : Fin m, f (hA.eigenvalues i) * ‖y i‖ ^ 2 :=
    lt_of_lt_of_le (mul_pos (hf i₀) (sq_pos_of_pos (norm_pos_iff.mpr hi₀)))
      (Finset.single_le_sum (fun i _ => mul_nonneg (le_of_lt (hf i)) (sq_nonneg ‖y i‖))
        (Finset.mem_univ i₀))
  rw [← Complex.ofReal_sum]
  exact_mod_cast hpos

lemma posDef_det_ne_zero {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef) : A.det ≠ 0 := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  have hpos : 0 < ∏ i : Fin m, hA.isHermitian.eigenvalues i :=
    Finset.prod_pos fun i _ => hA.eigenvalues_pos i
  have hne : (∏ i : Fin m, hA.isHermitian.eigenvalues i : ℝ) ≠ 0 := ne_of_gt hpos
  intro h0
  apply hne
  have hcast : ((∏ i : Fin m, hA.isHermitian.eigenvalues i : ℝ) : ℂ) = 0 := by simpa using h0
  exact Complex.ofReal_injective hcast

lemma posDef_of_posSemidef_det_ne_zero {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosSemidef) (hdet : A.det ≠ 0) : A.PosDef := by
  have heig_pos : ∀ i : Fin m, 0 < hA.isHermitian.eigenvalues i := by
    intro i
    have hnn := hA.eigenvalues_nonneg i
    have hne : hA.isHermitian.eigenvalues i ≠ 0 := by
      intro hi0
      apply hdet
      rw [hA.isHermitian.det_eq_prod_eigenvalues]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi0])
    exact lt_of_le_of_ne hnn hne.symm
  have hself : cfc (fun x : ℝ => x) A = A := by
    rw [cfc_eq_unitary_diag hA.isHermitian (fun x => x), ← self_eq_unitary_diag hA.isHermitian]
  rw [← hself]
  exact posDef_cfc_of_pos hA.isHermitian (fun x => x) heig_pos

lemma cfc_const_one {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) :
    cfc (fun _ : ℝ => (1 : ℝ)) A = 1 := by
  rw [cfc_eq_unitary_diag hA]
  have hdiag : Matrix.diagonal (fun _ : Fin m => ((1 : ℝ) : ℂ)) = 1 := by
    ext i j; by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [hdiag, mul_one]
  exact Unitary.coe_mul_star_self hA.eigenvectorUnitary

lemma trace_cfc {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i : Fin m, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [cfc_eq_unitary_diag hA f, Matrix.trace_mul_cycle]
  have hUU : (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ *
      (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) = 1 :=
    Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [hUU, one_mul, Matrix.trace_diagonal]

lemma cfc_mul_cfc {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    cfc f A * cfc g A = cfc (fun x => f x * g x) A := by
  rw [cfc_eq_unitary_diag hA f, cfc_eq_unitary_diag hA g, cfc_eq_unitary_diag hA]
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  set Df := Matrix.diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ))
  set Dg := Matrix.diagonal (fun i => ((g (hA.eigenvalues i) : ℝ) : ℂ))
  have hUU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hmid : (U * Df * Uᴴ) * (U * Dg * Uᴴ) = U * (Df * Dg) * Uᴴ := by
    calc
      (U * Df * Uᴴ) * (U * Dg * Uᴴ) = U * (Df * ((Uᴴ * U) * (Dg * Uᴴ))) := by
        simp only [Matrix.mul_assoc]
      _ = U * (Df * (Dg * Uᴴ)) := by rw [hUU, one_mul]
      _ = U * (Df * Dg) * Uᴴ := by simp only [Matrix.mul_assoc]
  rw [hmid]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Df, Dg]
  · simp [Df, Dg, hij]

lemma vnEntropy_eq_neg_trace_mul_log {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.IsHermitian) : vnEntropy A = -(A * cfc Real.log A).trace.re := by
  unfold vnEntropy shannonEntropy
  rw [sum_spec_eq_sum_eigenvalues hA]
  have hself : A = cfc (fun x : ℝ => x) A := by
    rw [cfc_eq_unitary_diag hA (fun x => x), ← self_eq_unitary_diag hA]
  have hprod : A * cfc Real.log A = cfc (fun x => x * Real.log x) A := by
    calc
      A * cfc Real.log A = cfc (fun x : ℝ => x) A * cfc Real.log A :=
        congrArg (· * cfc Real.log A) hself
      _ = cfc (fun x => x * Real.log x) A := cfc_mul_cfc hA (fun x => x) Real.log
  rw [hprod, trace_cfc hA]
  simp [Complex.re_sum, Real.negMulLog]

lemma unitary_diag_pow {m : ℕ} (U : Matrix (Fin m) (Fin m) ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (d : Fin m → ℂ) (k : ℕ) :
    (U * Matrix.diagonal d * Uᴴ) ^ k = U * Matrix.diagonal (fun i => d i ^ k) * Uᴴ := by
  induction k with
  | zero =>
    simp [Matrix.diagonal_one, hU2]
  | succ k ih =>
    rw [pow_succ, ih]
    calc
      (U * Matrix.diagonal (fun i => d i ^ k) * Uᴴ) * (U * Matrix.diagonal d * Uᴴ)
          = U * (Matrix.diagonal (fun i => d i ^ k) * ((Uᴴ * U) * (Matrix.diagonal d * Uᴴ))) := by
        simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal (fun i => d i ^ k) * (Matrix.diagonal d * Uᴴ)) := by
        rw [hU1, one_mul]
      _ = U * (Matrix.diagonal (fun i => d i ^ k) * Matrix.diagonal d) * Uᴴ := by
        simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (fun i => d i ^ (k + 1)) * Uᴴ := by
        congr 2
        ext i j
        by_cases hij : i = j
        · subst hij; simp [pow_succ]
        · simp [hij]

lemma sum_cont_eq_of_unitary_diag {m : ℕ} {B U : Matrix (Fin m) (Fin m) ℂ}
    (hB : B.IsHermitian) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (μ : Fin m → ℝ)
    (hBU : B = U * Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ)) * Uᴴ)
    {g : ℝ → ℝ} (hg : Continuous g) :
    ∑ i : Fin m, g (hB.eigenvalues i) = ∑ i : Fin m, g (μ i) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · simp
  have hpow_eq : ∀ k : ℕ, ∑ i : Fin m, hB.eigenvalues i ^ k = ∑ i : Fin m, μ i ^ k := by
    intro k
    have htr1 : (B ^ k).trace.re = ∑ i : Fin m, μ i ^ k := by
      rw [hBU, unitary_diag_pow U hU1 hU2 _ k, Matrix.trace_mul_cycle, hU1, one_mul,
        Matrix.trace_diagonal, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    set V : Matrix (Fin m) (Fin m) ℂ := (hB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
    have hV1 : Vᴴ * V = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
    have hV2 : V * Vᴴ = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
    have htr2 : (B ^ k).trace.re = ∑ i : Fin m, hB.eigenvalues i ^ k := by
      conv_lhs => rw [self_eq_unitary_diag hB]
      rw [unitary_diag_pow V hV1 hV2 _ k, Matrix.trace_mul_cycle, hV1, one_mul,
        Matrix.trace_diagonal, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact htr2.symm.trans htr1
  have hpoly_eq : ∀ P : Polynomial ℝ,
      ∑ i : Fin m, P.eval (hB.eigenvalues i) = ∑ i : Fin m, P.eval (μ i) := by
    intro P
    simp only [Polynomial.eval_eq_sum_range]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, hpow_eq k]
  apply eq_of_forall_dist_le
  intro ε hε
  rw [Real.dist_eq]
  set fsum : Fin m → ℝ := fun j => |hB.eigenvalues j| + |μ j|
  set M : ℝ := 1 + ∑ j : Fin m, fsum j
  have heig_mem : ∀ i : Fin m, hB.eigenvalues i ∈ Set.Icc (-M) M := by
    intro i
    have hle : |hB.eigenvalues i| ≤ M := by
      have h1 : |hB.eigenvalues i| ≤ fsum i := le_add_of_nonneg_right (abs_nonneg _)
      have h2 : fsum i ≤ ∑ j : Fin m, fsum j :=
        Finset.single_le_sum (f := fsum) (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
          (Finset.mem_univ i)
      linarith
    exact abs_le.mp hle
  have hμ_mem : ∀ i : Fin m, μ i ∈ Set.Icc (-M) M := by
    intro i
    have hle : |μ i| ≤ M := by
      have h1 : |μ i| ≤ fsum i := le_add_of_nonneg_left (abs_nonneg _)
      have h2 : fsum i ≤ ∑ j : Fin m, fsum j :=
        Finset.single_le_sum (f := fsum) (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
          (Finset.mem_univ i)
      linarith
    exact abs_le.mp hle
  have hm_cast_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-M) M g hg.continuousOn
    (ε / (2 * (m : ℝ))) (by positivity)
  have h1 : |(∑ i : Fin m, g (hB.eigenvalues i)) - ∑ i : Fin m, P.eval (hB.eigenvalues i)| ≤
      ε / 2 := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i : Fin m, (g (hB.eigenvalues i) - P.eval (hB.eigenvalues i))|
          ≤ ∑ i : Fin m, |g (hB.eigenvalues i) - P.eval (hB.eigenvalues i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, (ε / (2 * (m : ℝ))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_sub_comm]
        exact le_of_lt (hP (hB.eigenvalues i) (heig_mem i))
      _ = ε / 2 := by
        simp [Finset.sum_const]
        field_simp
  have h2 : |(∑ i : Fin m, P.eval (μ i)) - ∑ i : Fin m, g (μ i)| ≤ ε / 2 := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i : Fin m, (P.eval (μ i) - g (μ i))|
          ≤ ∑ i : Fin m, |P.eval (μ i) - g (μ i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, (ε / (2 * (m : ℝ))) :=
        Finset.sum_le_sum fun i _ => le_of_lt (hP (μ i) (hμ_mem i))
      _ = ε / 2 := by
        simp [Finset.sum_const]
        field_simp
  rw [← hpoly_eq P] at h2
  calc
    |(∑ i : Fin m, g (hB.eigenvalues i)) - ∑ i : Fin m, g (μ i)|
        = |((∑ i : Fin m, g (hB.eigenvalues i)) - ∑ i : Fin m, P.eval (hB.eigenvalues i)) +
            ((∑ i : Fin m, P.eval (hB.eigenvalues i)) - ∑ i : Fin m, g (μ i))| := by ring_nf
    _ ≤ |(∑ i : Fin m, g (hB.eigenvalues i)) - ∑ i : Fin m, P.eval (hB.eigenvalues i)| +
          |(∑ i : Fin m, P.eval (hB.eigenvalues i)) - ∑ i : Fin m, g (μ i)| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := add_halves ε

lemma vnEntropy_smul_pos {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian)
    {r : ℝ} (hr : 0 < r) :
    vnEntropy (((r : ℝ) : ℂ) • A) = r * vnEntropy A - r * A.trace.re * Real.log r := by
  set B : Matrix (Fin m) (Fin m) ℂ := ((r : ℝ) : ℂ) • A
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  have hA_eq : A = U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ :=
    self_eq_unitary_diag hA
  have hBU : B = U * Matrix.diagonal (fun i => (((r * hA.eigenvalues i) : ℝ) : ℂ)) * Uᴴ := by
    have hD : ((r : ℝ) : ℂ) • Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) =
        Matrix.diagonal (fun i => (((r * hA.eigenvalues i) : ℝ) : ℂ)) := by
      ext i j; by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    calc
      B = ((r : ℝ) : ℂ) • (U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ) :=
        congrArg (((r : ℝ) : ℂ) • ·) hA_eq
      _ = (U * (((r : ℝ) : ℂ) • Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)))) * Uᴴ := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = U * Matrix.diagonal (fun i => (((r * hA.eigenvalues i) : ℝ) : ℂ)) * Uᴴ := by rw [hD]
  have hB : B.IsHermitian := by
    rw [hBU]
    exact isHermitian_unitary_diag U _
  have hU1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hU2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  unfold vnEntropy shannonEntropy
  rw [sum_spec_eq_sum_eigenvalues hB, sum_spec_eq_sum_eigenvalues hA,
    sum_cont_eq_of_unitary_diag hB hU1 hU2 (fun i => r * hA.eigenvalues i) hBU
      Real.continuous_negMulLog]
  have hterm : ∀ x : ℝ, Real.negMulLog (r * x) = r * Real.negMulLog x - r * x * Real.log r := by
    intro x
    by_cases hx : x = 0
    · simp [hx, Real.negMulLog]
    · simp only [Real.negMulLog, Real.log_mul (ne_of_gt hr) hx]
      ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have htr : A.trace.re = ∑ i : Fin m, hA.eigenvalues i := by
    have h0 : A.trace = ((∑ i : Fin m, hA.eigenvalues i : ℝ) : ℂ) := by
      simpa using hA.trace_eq_sum_eigenvalues
    simpa using congrArg Complex.re h0
  rw [htr]
  congr 1
  rw [← Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]

/-! ### 3. Klein's inequality & gradient of `phiTheta` -/

lemma klein_ineq {m : ℕ} {P Q : Matrix (Fin m) (Fin m) ℂ} (hP : P.PosDef) (hQ : Q.PosDef) :
    (P - Q).trace.re ≤ (P * cfc Real.log P - P * cfc Real.log Q).trace.re := by
  have hPh := hP.isHermitian
  have hQh := hQ.isHermitian
  set U : Matrix (Fin m) (Fin m) ℂ := (hPh.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  set V : Matrix (Fin m) (Fin m) ℂ := (hQh.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  set W : Matrix (Fin m) (Fin m) ℂ := Uᴴ * V
  set p : Fin m → ℝ := hPh.eigenvalues
  set q : Fin m → ℝ := hQh.eigenvalues
  have hU1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self hPh.eigenvectorUnitary
  have hU2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self hPh.eigenvectorUnitary
  have hV1 : Vᴴ * V = 1 := Unitary.coe_star_mul_self hQh.eigenvectorUnitary
  have hV2 : V * Vᴴ = 1 := Unitary.coe_mul_star_self hQh.eigenvectorUnitary
  have hW_row : ∀ i : Fin m, ∑ j : Fin m, ‖W i j‖ ^ 2 = 1 := by
    intro i
    have hWW : W * Wᴴ = 1 := by
      simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc
        Uᴴ * V * (Vᴴ * U) = Uᴴ * ((V * Vᴴ) * U) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hV2, one_mul, hU1]
    have hii := congrArg Complex.re (congrFun (congrFun hWW i) i)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      Complex.one_re, Complex.re_sum, mul_star_self_eq_norm_sq, Complex.ofReal_re] at hii
    exact hii
  have hW_col : ∀ j : Fin m, ∑ i : Fin m, ‖W i j‖ ^ 2 = 1 := by
    intro j
    have hWW : Wᴴ * W = 1 := by
      simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc
        Vᴴ * U * (Uᴴ * V) = Vᴴ * ((U * Uᴴ) * V) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hU2, one_mul, hV1]
    have hjj := congrArg Complex.re (congrFun (congrFun hWW j) j)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      Complex.one_re, Complex.re_sum, star_mul_self_eq_norm_sq, Complex.ofReal_re] at hjj
    exact hjj
  have htrP : P.trace.re = ∑ i : Fin m, ∑ j : Fin m, ‖W i j‖ ^ 2 * p i := by
    have h0 : P.trace = ((∑ i : Fin m, p i : ℝ) : ℂ) := by simpa [p] using hPh.trace_eq_sum_eigenvalues
    have h1 : P.trace.re = ∑ i : Fin m, p i := by simpa using congrArg Complex.re h0
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hW_row i, one_mul]
  have htrQ : Q.trace.re = ∑ i : Fin m, ∑ j : Fin m, ‖W i j‖ ^ 2 * q j := by
    have h0 : Q.trace = ((∑ j : Fin m, q j : ℝ) : ℂ) := by simpa [q] using hQh.trace_eq_sum_eigenvalues
    have h1 : Q.trace.re = ∑ j : Fin m, q j := by simpa using congrArg Complex.re h0
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hW_col j, one_mul]
  have htrPP : (P * cfc Real.log P).trace.re =
      ∑ i : Fin m, ∑ j : Fin m, ‖W i j‖ ^ 2 * (p i * Real.log (p i)) := by
    have hself : P = cfc (fun x : ℝ => x) P := by
      rw [cfc_eq_unitary_diag hPh (fun x => x), ← self_eq_unitary_diag hPh]
    have hprod : P * cfc Real.log P = cfc (fun x => x * Real.log x) P := by
      calc
        P * cfc Real.log P = cfc (fun x : ℝ => x) P * cfc Real.log P :=
          congrArg (· * cfc Real.log P) hself
        _ = cfc (fun x => x * Real.log x) P := cfc_mul_cfc hPh (fun x => x) Real.log
    rw [hprod, trace_cfc hPh]
    simp only [Complex.re_sum, Complex.ofReal_re]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hW_row i, one_mul]
  have htrPQ : (P * cfc Real.log Q).trace.re =
      ∑ i : Fin m, ∑ j : Fin m, ‖W i j‖ ^ 2 * (p i * Real.log (q j)) := by
    set Dp := Matrix.diagonal (fun i => ((p i : ℝ) : ℂ))
    set Dlogq := Matrix.diagonal (fun j => ((Real.log (q j) : ℝ) : ℂ))
    have hP_eq : P = U * Dp * Uᴴ := self_eq_unitary_diag hPh
    have hlogQ_eq : cfc Real.log Q = V * Dlogq * Vᴴ := cfc_eq_unitary_diag hQh Real.log
    have hmul : (P * cfc Real.log Q).trace = (Dp * W * Dlogq * Wᴴ).trace := by
      rw [hP_eq, hlogQ_eq]
      calc
        ((U * Dp * Uᴴ) * (V * Dlogq * Vᴴ)).trace
            = (((U * Dp * Uᴴ) * (V * Dlogq)) * Vᴴ).trace := by simp only [Matrix.mul_assoc]
        _ = (Vᴴ * ((U * Dp * Uᴴ) * (V * Dlogq))).trace := Matrix.trace_mul_comm _ Vᴴ
        _ = ((Wᴴ * (Dp * W)) * Dlogq).trace := by
          simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = ((Dp * W * Dlogq) * Wᴴ).trace := by
          calc
            ((Wᴴ * (Dp * W)) * Dlogq).trace = (Wᴴ * ((Dp * W) * Dlogq)).trace := by
              simp only [Matrix.mul_assoc]
            _ = (((Dp * W) * Dlogq) * Wᴴ).trace := Matrix.trace_mul_comm Wᴴ _
    rw [hmul]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Dp, Dlogq, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hterm : ((p i : ℝ) : ℂ) * W i j * ((Real.log (q j) : ℝ) : ℂ) * star (W i j) =
        ((‖W i j‖ ^ 2 * (p i * Real.log (q j)) : ℝ) : ℂ) := by
      calc
        ((p i : ℝ) : ℂ) * W i j * ((Real.log (q j) : ℝ) : ℂ) * star (W i j)
            = (W i j * star (W i j)) * (((p i : ℝ) : ℂ) * ((Real.log (q j) : ℝ) : ℂ)) := by ring
        _ = ((‖W i j‖ ^ 2 * (p i * Real.log (q j)) : ℝ) : ℂ) := by
          rw [mul_star_self_eq_norm_sq]; push_cast; ring
    rw [hterm, Complex.ofReal_re]
  rw [Matrix.trace_sub, Complex.sub_re, Matrix.trace_sub, Complex.sub_re,
    htrP, htrQ, htrPP, htrPQ, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hp_pos : 0 < p i := hP.eigenvalues_pos i
  have hq_pos : 0 < q j := hQ.eigenvalues_pos j
  have hlog_le := Real.log_le_sub_one_of_pos (div_pos hq_pos hp_pos)
  rw [Real.log_div (ne_of_gt hq_pos) (ne_of_gt hp_pos)] at hlog_le
  have hscalar : p i - q j ≤ p i * Real.log (p i) - p i * Real.log (q j) := by
    have hmul := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hp_pos)
    have hdiv : p i * (q j / p i - 1) = q j - p i := by field_simp
    linarith
  have hw_nn : 0 ≤ ‖W i j‖ ^ 2 := sq_nonneg ‖W i j‖
  nlinarith

lemma frobNorm_cfc_sub_poly {m : ℕ} {B : Matrix (Fin m) (Fin m) ℂ} (hB : B.IsHermitian)
    (f : ℝ → ℝ) (P : Polynomial ℝ) :
    frobNorm (cfc f B - ∑ k ∈ P.support, ((P.coeff k : ℝ) : ℂ) • B ^ k) =
      Real.sqrt (∑ i : Fin m, (f (hB.eigenvalues i) - P.eval (hB.eigenvalues i)) ^ 2) := by
  set U : Matrix (Fin m) (Fin m) ℂ := (hB.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  have hU1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have hU2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have hpoly : ∑ k ∈ P.support, ((P.coeff k : ℝ) : ℂ) • B ^ k =
      U * Matrix.diagonal (fun i => ((P.eval (hB.eigenvalues i) : ℝ) : ℂ)) * Uᴴ := by
    have hBk : ∀ k : ℕ, ((P.coeff k : ℝ) : ℂ) • B ^ k =
        U * (((P.coeff k : ℝ) : ℂ) •
          Matrix.diagonal (fun i => (((hB.eigenvalues i ^ k : ℝ)) : ℂ))) * Uᴴ := by
      intro k
      have hk0 : B ^ k = U * Matrix.diagonal (fun i => (((hB.eigenvalues i ^ k : ℝ)) : ℂ)) * Uᴴ := by
        conv_lhs => rw [self_eq_unitary_diag hB]
        simpa using unitary_diag_pow U hU1 hU2 (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) k
      rw [hk0, Matrix.mul_smul, Matrix.smul_mul]
    simp_rw [hBk, ← Finset.sum_mul, ← Finset.mul_sum]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul,
        Polynomial.eval_eq_sum, Polynomial.sum_def]
      push_cast
      rfl
    · simp [Matrix.sum_apply, hij]
  set D := Matrix.diagonal
    (fun i => (((f (hB.eigenvalues i) - P.eval (hB.eigenvalues i)) : ℝ) : ℂ))
  have hdiff : cfc f B - ∑ k ∈ P.support, ((P.coeff k : ℝ) : ℂ) • B ^ k = U * D * Uᴴ := by
    have hcfc_eq : cfc f B =
        U * Matrix.diagonal (fun i => ((f (hB.eigenvalues i) : ℝ) : ℂ)) * Uᴴ :=
      cfc_eq_unitary_diag hB f
    rw [hcfc_eq, hpoly, ← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst hij; simp [D]
    · simp [D, hij]
  unfold frobNorm
  congr 1
  rw [frobNorm_sq_eq_trace_conjTranspose_mul, hdiff]
  have hD_herm : Dᴴ = D := by
    ext i j; by_cases hij : i = j
    · subst hij; simp [D]
    · simp [D, hij, Ne.symm hij]
  have hprod : (U * D * Uᴴ)ᴴ * (U * D * Uᴴ) = U * (D * D) * Uᴴ := by
    calc
      (U * D * Uᴴ)ᴴ * (U * D * Uᴴ) = U * (D * ((Uᴴ * U) * (D * Uᴴ))) := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD_herm,
          Matrix.mul_assoc]
      _ = U * (D * (D * Uᴴ)) := by rw [hU1, one_mul]
      _ = U * (D * D) * Uᴴ := by simp only [Matrix.mul_assoc]
  rw [hprod, Matrix.trace_mul_cycle, hU1, one_mul]
  simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum, sq]

lemma eigenvalues_perturbation_bounds {m : ℕ} [NeZero m]
    {A Y : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef) (hY : Y.IsHermitian) :
    ∃ a b δ : ℝ, 0 < a ∧ a ≤ b ∧ 0 < δ ∧
      ∀ t : ℝ, |t| < δ →
        ∃ hBt : (A + (t : ℂ) • Y).PosDef,
          ∀ i : Fin m, hBt.isHermitian.eigenvalues i ∈ Set.Icc a b := by
  have huniv : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty
  set hAh := hA.isHermitian
  set cmin : ℝ := Finset.univ.inf' huniv hAh.eigenvalues
  set cmax : ℝ := Finset.univ.sup' huniv hAh.eigenvalues
  have hcmin_pos : 0 < cmin :=
    (Finset.lt_inf'_iff huniv).mpr fun i _ => hA.eigenvalues_pos i
  have hcmax_ge : cmin ≤ cmax := by
    obtain ⟨i₀, hi₀⟩ := huniv
    exact le_trans (Finset.inf'_le _ hi₀) (Finset.le_sup' _ hi₀)
  set S_Y : ℝ := 1 + ∑ i : Fin m, ∑ j : Fin m, ‖Y i j‖
  have hSY_pos : 0 < S_Y := by
    have : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, ‖Y i j‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  refine ⟨cmin / 2, cmax + cmin / 2, (cmin / 2) / S_Y, by linarith, by linarith, by positivity, ?_⟩
  intro t ht
  have htSY : |t| * S_Y < cmin / 2 := (lt_div_iff₀ hSY_pos).mp ht
  have hBt_herm : (A + (t : ℂ) • Y).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      hAh.eq, hY.eq, Complex.star_def, Complex.conj_ofReal]
  have hrayleigh : ∀ v : Fin m → ℂ, ∑ i : Fin m, ‖v i‖ ^ 2 = 1 →
      cmin / 2 ≤ (star v ⬝ᵥ (A + (t : ℂ) • Y) *ᵥ v).re ∧
        (star v ⬝ᵥ (A + (t : ℂ) • Y) *ᵥ v).re ≤ cmax + cmin / 2 := by
    intro v hv1
    have hvi_le1 : ∀ i : Fin m, ‖v i‖ ≤ 1 := by
      intro i
      have hsq : ‖v i‖ ^ 2 ≤ 1 := by
        rw [← hv1]
        exact Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
      nlinarith [norm_nonneg (v i)]
    set U : Matrix (Fin m) (Fin m) ℂ := (hAh.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
    set w : Fin m → ℂ := Uᴴ *ᵥ v
    have hw_norm : ∑ i : Fin m, ‖w i‖ ^ 2 = 1 := by
      have h1 : ((∑ i : Fin m, ‖w i‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
        simp only [dotProduct, Pi.star_apply, star_mul_self_eq_norm_sq, Complex.ofReal_sum]
      have h2 : star w ⬝ᵥ w = star v ⬝ᵥ v := by
        have hU2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self hAh.eigenvectorUnitary
        calc
          star w ⬝ᵥ w = (star v ᵥ* U) ⬝ᵥ (Uᴴ *ᵥ v) := by simp [w, Matrix.star_mulVec]
          _ = star v ⬝ᵥ (U *ᵥ (Uᴴ *ᵥ v)) := (Matrix.dotProduct_mulVec (star v) U (Uᴴ *ᵥ v)).symm
          _ = star v ⬝ᵥ ((U * Uᴴ) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
          _ = star v ⬝ᵥ v := by rw [hU2, Matrix.one_mulVec]
      have h3 : star v ⬝ᵥ v = ((∑ i : Fin m, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
        simp only [dotProduct, Pi.star_apply, star_mul_self_eq_norm_sq, Complex.ofReal_sum]
      have heq_sum : ∑ i : Fin m, ‖w i‖ ^ 2 = ∑ i : Fin m, ‖v i‖ ^ 2 :=
        Complex.ofReal_injective (h1.trans (h2.trans h3))
      exact heq_sum.trans hv1
    have hA_quad : (star v ⬝ᵥ A *ᵥ v).re = ∑ i : Fin m, hAh.eigenvalues i * ‖w i‖ ^ 2 := by
      conv_lhs => rw [self_eq_unitary_diag hAh]
      rw [dotProduct_unitary_diag]
      change (∑ i : Fin m, ((hAh.eigenvalues i * ‖w i‖ ^ 2 : ℝ) : ℂ)).re = _
      rw [Complex.re_sum]
      exact Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
    have hA_lo : cmin ≤ (star v ⬝ᵥ A *ᵥ v).re := by
      rw [hA_quad, ← mul_one cmin, ← hw_norm, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ i)) (sq_nonneg _)
    have hA_hi : (star v ⬝ᵥ A *ᵥ v).re ≤ cmax := by
      rw [hA_quad, ← mul_one cmax, ← hw_norm, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (Finset.le_sup' _ (Finset.mem_univ i)) (sq_nonneg _)
    have hY_abs : |((t : ℂ) * (star v ⬝ᵥ Y *ᵥ v)).re| ≤ |t| * S_Y := by
      have hnormY : ‖star v ⬝ᵥ Y *ᵥ v‖ ≤ ∑ i : Fin m, ∑ j : Fin m, ‖Y i j‖ := by
        simp only [dotProduct, Matrix.mulVec]
        calc
          ‖∑ i : Fin m, star (v i) * ∑ j : Fin m, Y i j * v j‖
              ≤ ∑ i : Fin m, ‖star (v i) * ∑ j : Fin m, Y i j * v j‖ := norm_sum_le _ _
          _ ≤ ∑ i : Fin m, ∑ j : Fin m, ‖Y i j‖ := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_mul, norm_star]
            calc
              ‖v i‖ * ‖∑ j : Fin m, Y i j * v j‖
                  ≤ 1 * ∑ j : Fin m, ‖Y i j * v j‖ :=
                mul_le_mul (hvi_le1 i) (norm_sum_le _ _) (norm_nonneg _) zero_le_one
              _ ≤ ∑ j : Fin m, ‖Y i j‖ := by
                rw [one_mul]
                refine Finset.sum_le_sum fun j _ => ?_
                rw [norm_mul]
                exact mul_le_of_le_one_right (norm_nonneg _) (hvi_le1 j)
      calc
        |((t : ℂ) * (star v ⬝ᵥ Y *ᵥ v)).re|
            ≤ ‖(t : ℂ) * (star v ⬝ᵥ Y *ᵥ v)‖ := Complex.abs_re_le_norm _
        _ = |t| * ‖star v ⬝ᵥ Y *ᵥ v‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |t| * S_Y := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
          linarith
    have hexpand : (star v ⬝ᵥ (A + (t : ℂ) • Y) *ᵥ v).re =
        (star v ⬝ᵥ A *ᵥ v).re + ((t : ℂ) * (star v ⬝ᵥ Y *ᵥ v)).re := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
        smul_eq_mul, Complex.add_re]
    rw [hexpand]
    have habs := abs_le.mp hY_abs
    constructor <;> linarith
  have heig_mem : ∀ i : Fin m, hBt_herm.eigenvalues i ∈ Set.Icc (cmin / 2) (cmax + cmin / 2) := by
    intro i
    set v : Fin m → ℂ := (hBt_herm.eigenvectorBasis i).ofLp
    have hv_norm : ∑ j : Fin m, ‖v j‖ ^ 2 = 1 := by
      have h1 := hBt_herm.eigenvectorBasis.orthonormal.1 i
      have h2 : ‖hBt_herm.eigenvectorBasis i‖ ^ 2 = 1 := by rw [h1, one_pow]
      rw [EuclideanSpace.norm_sq_eq] at h2
      exact h2
    have heq : hBt_herm.eigenvalues i = (star v ⬝ᵥ (A + (t : ℂ) • Y) *ᵥ v).re := by
      simpa [v] using hBt_herm.eigenvalues_eq i
    rw [heq]
    exact hrayleigh v hv_norm
  have hBt_posDef : (A + (t : ℂ) • Y).PosDef := by
    have hself : cfc (fun x : ℝ => x) (A + (t : ℂ) • Y) = A + (t : ℂ) • Y := by
      rw [cfc_eq_unitary_diag hBt_herm (fun x => x), ← self_eq_unitary_diag hBt_herm]
    rw [← hself]
    exact posDef_cfc_of_pos hBt_herm (fun x => x) fun i =>
      lt_of_lt_of_le (by linarith) (heig_mem i).1
  exact ⟨hBt_posDef, heig_mem⟩

lemma tendsto_cfc_log_add_entry {m : ℕ} {A Y : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosDef) (hY : Y.IsHermitian) (i j : Fin m) :
    Filter.Tendsto (fun t : ℝ => cfc Real.log (A + (t : ℂ) • Y) i j)
      (nhds 0) (nhds (cfc Real.log A i j)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · exact Fin.elim0 i
  have : NeZero m := ⟨Nat.ne_of_gt hm_pos⟩
  obtain ⟨a, b, δ, ha_pos, _, hδ_pos, hpert⟩ := eigenvalues_perturbation_bounds hA hY
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hm_sqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm_pos)
  have hlog_cont : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono fun x hx => ne_of_gt (lt_of_lt_of_le ha_pos hx.1)
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn a b Real.log hlog_cont
    (ε / (3 * Real.sqrt (m : ℝ))) (by positivity)
  set polyF : ℝ → Matrix (Fin m) (Fin m) ℂ :=
    fun t => ∑ k ∈ P.support, ((P.coeff k : ℝ) : ℂ) • (A + (t : ℂ) • Y) ^ k
  have hpoly_cont : Continuous fun t : ℝ => polyF t i j := by
    simp only [polyF, Matrix.sum_apply, Matrix.smul_apply]
    refine continuous_finsetSum _ fun k _ => ?_
    have hmat_cont : Continuous fun t : ℝ => (A + (t : ℂ) • Y) ^ k :=
      Continuous.pow (continuous_const.add (Complex.continuous_ofReal.smul continuous_const)) k
    exact (((continuous_apply j).comp ((continuous_apply i).comp hmat_cont)).const_smul
      (((P.coeff k : ℝ) : ℂ)))
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.mp hpoly_cont.continuousAt (ε / 3) (by positivity)
  rw [Metric.eventually_nhds_iff]
  refine ⟨min δ δ₂, lt_min hδ_pos hδ₂_pos, ?_⟩
  intro t ht
  simp only [Real.dist_eq, sub_zero] at ht
  have ht1 : |t| < δ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht2 : dist t 0 < δ₂ := by
    rw [Real.dist_eq, sub_zero]
    exact lt_of_lt_of_le ht (min_le_right _ _)
  have happrox : ∀ (B : Matrix (Fin m) (Fin m) ℂ) (hB : B.IsHermitian),
      (∀ k : Fin m, hB.eigenvalues k ∈ Set.Icc a b) →
      ‖(cfc Real.log B - ∑ k ∈ P.support, ((P.coeff k : ℝ) : ℂ) • B ^ k) i j‖ ≤ ε / 3 := by
    intro B hB hBeig
    calc
      ‖(cfc Real.log B - ∑ k ∈ P.support, ((P.coeff k : ℝ) : ℂ) • B ^ k) i j‖
          ≤ frobNorm (cfc Real.log B - ∑ k ∈ P.support, ((P.coeff k : ℝ) : ℂ) • B ^ k) :=
        norm_entry_le_frobNorm _ i j
      _ = Real.sqrt (∑ k : Fin m, (Real.log (hB.eigenvalues k) - P.eval (hB.eigenvalues k)) ^ 2) :=
        frobNorm_cfc_sub_poly hB Real.log P
      _ ≤ Real.sqrt (∑ _k : Fin m, (ε / (3 * Real.sqrt (m : ℝ))) ^ 2) := by
        apply Real.sqrt_le_sqrt
        refine Finset.sum_le_sum fun k _ => ?_
        rw [← sq_abs (Real.log (hB.eigenvalues k) - P.eval (hB.eigenvalues k)), abs_sub_comm,
          sq, sq]
        exact mul_self_le_mul_self (abs_nonneg _) (le_of_lt (hP _ (hBeig k)))
      _ = ε / 3 := by
        have hsqn : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
        have hsum : ∑ _k : Fin m, (ε / (3 * Real.sqrt (m : ℝ))) ^ 2 = (ε / 3) ^ 2 := by
          simp [Finset.sum_const]
          field_simp
          rw [hsqn]
        rw [hsum, Real.sqrt_sq (by positivity)]
  obtain ⟨hBt_pos, hBt_eig⟩ := hpert t ht1
  obtain ⟨h0_pos, h0_eig⟩ := hpert 0 (by simpa using hδ_pos)
  have hb1 : ‖cfc Real.log (A + (t : ℂ) • Y) i j - polyF t i j‖ ≤ ε / 3 :=
    happrox (A + (t : ℂ) • Y) hBt_pos.isHermitian hBt_eig
  have hb2 : ‖polyF t i j - polyF 0 i j‖ < ε / 3 := by
    simpa [dist_eq_norm] using hδ₂ ht2
  have hb3 : ‖polyF 0 i j - cfc Real.log A i j‖ ≤ ε / 3 := by
    have hA0 : A + ((0 : ℝ) : ℂ) • Y = A := by simp
    have h0' := happrox (A + ((0 : ℝ) : ℂ) • Y) h0_pos.isHermitian h0_eig
    rw [norm_sub_rev]
    simpa [polyF, hA0] using h0'
  rw [dist_eq_norm]
  calc
    ‖cfc Real.log (A + (t : ℂ) • Y) i j - cfc Real.log A i j‖
        = ‖(cfc Real.log (A + (t : ℂ) • Y) i j - polyF t i j) +
            (polyF t i j - polyF 0 i j) + (polyF 0 i j - cfc Real.log A i j)‖ := by ring_nf
    _ ≤ ‖cfc Real.log (A + (t : ℂ) • Y) i j - polyF t i j‖ +
          ‖polyF t i j - polyF 0 i j‖ + ‖polyF 0 i j - cfc Real.log A i j‖ :=
      le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

lemma hasDerivAt_trace_mul_log {m : ℕ} {A Y : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosDef) (hY : Y.IsHermitian) :
    HasDerivAt (fun t : ℝ => ((A + (t : ℂ) • Y) * cfc Real.log (A + (t : ℂ) • Y)).trace.re)
      (((cfc Real.log A + 1) * Y).trace.re) 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · have hzero : (fun t : ℝ => ((A + (t : ℂ) • Y) * cfc Real.log (A + (t : ℂ) • Y)).trace.re) =
        fun _ => 0 := by ext t; simp [Matrix.trace]
    have hval : (((cfc Real.log A + 1) * Y).trace.re) = 0 := by simp [Matrix.trace]
    rw [hzero, hval]
    exact hasDerivAt_const 0 0
  have : NeZero m := ⟨Nat.ne_of_gt hm_pos⟩
  obtain ⟨_, _, δ, _, _, hδ_pos, hpert⟩ := eigenvalues_perturbation_bounds hA hY
  rw [hasDerivAt_iff_tendsto_slope]
  set f : ℝ → ℝ := fun t => ((A + (t : ℂ) • Y) * cfc Real.log (A + (t : ℂ) • Y)).trace.re
  set L : ℝ → ℝ := fun t => (((cfc Real.log (A + (t : ℂ) • Y) + 1) * Y).trace.re)
  have hL0 : L 0 = (((cfc Real.log A + 1) * Y).trace.re) := by simp [L]
  rw [← hL0]
  have hL_tendsto : Filter.Tendsto L (nhds 0) (nhds (L 0)) := by
    have hL_eq : ∀ t : ℝ, L t =
        ∑ i : Fin m, ∑ k : Fin m,
          ((cfc Real.log (A + (t : ℂ) • Y) i k + (1 : Matrix (Fin m) (Fin m) ℂ) i k) * Y k i).re := by
      intro t
      simp [L, Matrix.trace, Matrix.diag, Complex.re_sum, Matrix.mul_apply, Matrix.add_apply]
    have hfun : L = fun t : ℝ => ∑ i : Fin m, ∑ k : Fin m,
        ((cfc Real.log (A + (t : ℂ) • Y) i k + (1 : Matrix (Fin m) (Fin m) ℂ) i k) * Y k i).re :=
      funext hL_eq
    rw [hfun]
    refine tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun i _ => ?_
    refine tendsto_finsetSum (Finset.univ : Finset (Fin m)) fun k _ => ?_
    have h1 : Filter.Tendsto
        (fun t : ℝ => (cfc Real.log (A + (t : ℂ) • Y) i k + (1 : Matrix (Fin m) (Fin m) ℂ) i k) * Y k i)
        (nhds 0)
        (nhds ((cfc Real.log (A + ((0 : ℝ) : ℂ) • Y) i k + (1 : Matrix (Fin m) (Fin m) ℂ) i k) * Y k i)) := by
      have hc := tendsto_cfc_log_add_entry hA hY i k
      have hA0 : A + ((0 : ℝ) : ℂ) • Y = A := by simp
      rw [hA0]
      exact (hc.add tendsto_const_nhds).mul tendsto_const_nhds
    exact Complex.continuous_re.continuousAt.tendsto.comp h1
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := (Metric.tendsto_nhds.mp hL_tendsto ε hε |> Metric.eventually_nhds_iff.mp)
  refine ⟨min δ δ₂, lt_min hδ_pos hδ₂_pos, ?_⟩
  intro t ht_ne ht_dist
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht_ne
  have ht_abs : |t| < min δ δ₂ := by simpa [Real.dist_eq] using ht_dist
  obtain ⟨hBt_pos, _⟩ := hpert t (lt_of_lt_of_le ht_abs (min_le_left _ _))
  let B : Matrix (Fin m) (Fin m) ℂ := A + (t : ℂ) • Y
  have hlo : t * L 0 ≤ f t - f 0 := by
    have hk : (B - A).trace.re ≤ (B * cfc Real.log B - B * cfc Real.log A).trace.re :=
      klein_ineq hBt_pos hA
    have hBA : B.trace.re - A.trace.re = t * Y.trace.re := by
      have : B - A = (t : ℂ) • Y := by simp [B]
      rw [← Complex.sub_re, ← Matrix.trace_sub, this, Matrix.trace_smul, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hBlogA : (B * cfc Real.log A).trace.re - (A * cfc Real.log A).trace.re =
        t * (Y * cfc Real.log A).trace.re := by
      have : B * cfc Real.log A - A * cfc Real.log A = (t : ℂ) • (Y * cfc Real.log A) := by
        simp [B, add_mul]
      rw [← Complex.sub_re, ← Matrix.trace_sub, this, Matrix.trace_smul, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have htL0 : t * L 0 = t * (Y * cfc Real.log A).trace.re + t * Y.trace.re := by
      have hcomm : L 0 = (Y * cfc Real.log A).trace.re + Y.trace.re := by
        rw [hL0, add_mul, one_mul, Matrix.trace_add, Complex.add_re,
          Matrix.trace_mul_comm (cfc Real.log A) Y]
      rw [hcomm]; ring
    have hf_diff : f t - f 0 = (B * cfc Real.log B).trace.re - (A * cfc Real.log A).trace.re := by
      simp [f, B]
    rw [Matrix.trace_sub, Complex.sub_re, Matrix.trace_sub, Complex.sub_re] at hk
    linarith
  have hhi : f t - f 0 ≤ t * L t := by
    have hk : (A - B).trace.re ≤ (A * cfc Real.log A - A * cfc Real.log B).trace.re :=
      klein_ineq hA hBt_pos
    have hAB : A.trace.re - B.trace.re = -t * Y.trace.re := by
      have : A - B = ((-t : ℝ) : ℂ) • Y := by simp [B]
      rw [← Complex.sub_re, ← Matrix.trace_sub, this, Matrix.trace_smul, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hBlogB : (B * cfc Real.log B).trace.re - (A * cfc Real.log B).trace.re =
        t * (Y * cfc Real.log B).trace.re := by
      have : B * cfc Real.log B - A * cfc Real.log B = (t : ℂ) • (Y * cfc Real.log B) := by
        simp [B, add_mul]
      rw [← Complex.sub_re, ← Matrix.trace_sub, this, Matrix.trace_smul, smul_eq_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have htLt : t * L t = t * (Y * cfc Real.log B).trace.re + t * Y.trace.re := by
      have hcomm : L t = (Y * cfc Real.log B).trace.re + Y.trace.re := by
        change (((cfc Real.log B + 1) * Y).trace.re) = _
        rw [add_mul, one_mul, Matrix.trace_add, Complex.add_re, Matrix.trace_mul_comm (cfc Real.log B) Y]
      rw [hcomm]; ring
    have hf_diff : f t - f 0 = (B * cfc Real.log B).trace.re - (A * cfc Real.log A).trace.re := by
      simp [f, B]
    rw [Matrix.trace_sub, Complex.sub_re, Matrix.trace_sub, Complex.sub_re] at hk
    linarith
  have hslope_eq : slope f 0 t = (f t - f 0) / t := by
    simp [slope_def_field]
  rw [Real.dist_eq, hslope_eq]
  have hsandwich : |(f t - f 0) / t - L 0| ≤ |L t - L 0| := by
    rcases lt_trichotomy t 0 with ht_neg | rfl | ht_pos
    · have hnt : 0 < -t := neg_pos.mpr ht_neg
      have hdiv_neg : (f 0 - f t) / (-t) = (f t - f 0) / t := by
        have ht0 : t ≠ 0 := ne_of_lt ht_neg
        field_simp
        ring
      have h1 : L t ≤ (f 0 - f t) / (-t) := (le_div_iff₀ hnt).mpr (by linarith)
      have h2 : (f 0 - f t) / (-t) ≤ L 0 := (div_le_iff₀ hnt).mpr (by linarith)
      rw [hdiv_neg] at h1 h2
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · exact absurd rfl ht_ne
    · have h1 : L 0 ≤ (f t - f 0) / t := (le_div_iff₀ ht_pos).mpr (by linarith)
      have h2 : (f t - f 0) / t ≤ L t := (div_le_iff₀ ht_pos).mpr (by linarith)
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  have hLt_close : |L t - L 0| < ε := by
    have ht2 : dist t 0 < δ₂ := by
      rw [Real.dist_eq, sub_zero]
      exact lt_of_lt_of_le ht_abs (min_le_right _ _)
    simpa [Real.dist_eq] using hδ₂ ht2
  exact lt_of_le_of_lt hsandwich hLt_close

lemma PhiR_phiTheta_of_posSemidef {d : ℕ} {n : Fin d → ℕ} (θ : Fin d → ℝ)
    (X : MatTuple n) (hX : ∀ ℓ, (X ℓ).PosSemidef) :
    PhiR (phiTheta θ) X = -∑ ℓ, θ ℓ * vnEntropy (X ℓ) := by
  unfold PhiR phiTheta specTuple
  have hnn : ∀ ℓ i, 0 ≤ spec (X ℓ) i := fun ℓ i => spec_nonneg_of_posSemidef (hX ℓ) i
  rw [if_pos hnn, EReal.toReal_coe]
  rfl

lemma dirDeriv_phiTheta_eq {d : ℕ} {n : Fin d → ℕ} (θ : Fin d → ℝ)
    (X : MatTuple n) (hX : ∀ ℓ, (X ℓ).PosDef) (ℓ : Fin d)
    (Y : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ) (hY : Y.IsHermitian) :
    dirDeriv (phiTheta θ) X ℓ Y = θ ℓ * (((cfc Real.log (X ℓ) + 1) * Y).trace.re) := by
  unfold dirDeriv
  apply HasDerivAt.deriv
  rcases Nat.eq_zero_or_pos (n ℓ) with hn0 | hn_pos
  · have hconst : (fun t : ℝ => PhiR (phiTheta θ) (Function.update X ℓ (X ℓ + (t : ℂ) • Y))) =
        fun _ => PhiR (phiTheta θ) X := by
      ext t
      congr 1
      ext m a b
      by_cases hm : m = ℓ
      · subst hm; exact Fin.elim0 (hn0 ▸ a)
      · simp [hm]
    have hrhs : θ ℓ * (((cfc Real.log (X ℓ) + 1) * Y).trace.re) = 0 := by
      have : ((cfc Real.log (X ℓ) + 1) * Y).trace = 0 := by
        simp only [Matrix.trace]
        exact Finset.sum_eq_zero fun i _ => Fin.elim0 (hn0 ▸ i)
      simp [this]
    rw [hconst, hrhs]
    exact hasDerivAt_const 0 _
  have : NeZero (n ℓ) := ⟨Nat.ne_of_gt hn_pos⟩
  obtain ⟨_, _, δ, _, _, hδ_pos, hpert⟩ := eigenvalues_perturbation_bounds (hX ℓ) hY
  set g : ℝ → ℝ := fun t =>
    -(∑ m ∈ Finset.univ.erase ℓ, θ m * vnEntropy (X m)) +
      θ ℓ * (((X ℓ + (t : ℂ) • Y) * cfc Real.log (X ℓ + (t : ℂ) • Y)).trace.re)
  have hg_deriv : HasDerivAt g (θ ℓ * (((cfc Real.log (X ℓ) + 1) * Y).trace.re)) 0 := by
    simpa [g] using ((hasDerivAt_trace_mul_log (hX ℓ) hY).const_mul (θ ℓ)).const_add
      (-(∑ m ∈ Finset.univ.erase ℓ, θ m * vnEntropy (X m)))
  refine hg_deriv.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.ball 0 δ, Metric.ball_mem_nhds 0 hδ_pos, ?_⟩
  intro t ht
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  obtain ⟨hBt_pos, _⟩ := hpert t ht
  have hupd_psd : ∀ m, (Function.update X ℓ (X ℓ + (t : ℂ) • Y) m).PosSemidef := by
    intro m
    by_cases hm : m = ℓ
    · subst hm; simpa using hBt_pos.posSemidef
    · simpa [hm] using (hX m).posSemidef
  dsimp only
  rw [PhiR_phiTheta_of_posSemidef θ _ hupd_psd]
  have hsplit := (Finset.add_sum_erase Finset.univ
    (fun m => θ m * vnEntropy (Function.update X ℓ (X ℓ + (t : ℂ) • Y) m))
    (Finset.mem_univ ℓ)).symm
  rw [hsplit]
  have herase : ∑ m ∈ Finset.univ.erase ℓ,
      θ m * vnEntropy (Function.update X ℓ (X ℓ + (t : ℂ) • Y) m) =
      ∑ m ∈ Finset.univ.erase ℓ, θ m * vnEntropy (X m) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
  rw [Function.update_self, herase, vnEntropy_eq_neg_trace_mul_log hBt_pos.isHermitian]
  simp only [g]
  ring

lemma hsGrad_phiTheta_eq {d : ℕ} {n : Fin d → ℕ} (θ : Fin d → ℝ)
    (X : MatTuple n) (hX : ∀ ℓ, (X ℓ).PosDef) (ℓ : Fin d) :
    hsGrad (phiTheta θ) X ℓ = ((θ ℓ : ℝ) : ℂ) • (cfc Real.log (X ℓ) + 1) := by
  set G : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ := ((θ ℓ : ℝ) : ℂ) • (cfc Real.log (X ℓ) + 1)
  have hG_herm : G.IsHermitian := by
    have hlog := (isHermitian_cfc (hX ℓ).isHermitian Real.log).eq
    rw [Matrix.IsHermitian]
    simp [G, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hlog]
  have hdir : ∀ Y : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ, Y.IsHermitian →
      dirDeriv (phiTheta θ) X ℓ Y = (G * Y).trace.re := by
    intro Y hY
    rw [dirDeriv_phiTheta_eq θ X hX ℓ Y hY]
    have hmulG : G * Y = ((θ ℓ : ℝ) : ℂ) • ((cfc Real.log (X ℓ) + 1) * Y) := by
      dsimp only [G]
      rw [Matrix.smul_mul]
    rw [hmulG, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have htr_single : ∀ (p q : Fin (n ℓ)) (c : ℂ), (G * Matrix.single p q c).trace = G q p * c := by
    intro p q c
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
    rw [Finset.sum_eq_single q]
    · rw [Finset.sum_eq_single p]
      · simp
      · intro k _ hk; simp [Ne.symm hk]
      · intro hp; exact absurd (Finset.mem_univ p) hp
    · intro i _ hi
      exact Finset.sum_eq_zero fun k _ => by simp [Ne.symm hi]
    · intro hq; exact absurd (Finset.mem_univ q) hq
  ext a b
  unfold hsGrad
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have hY0 : (Matrix.single a a (1 : ℂ)).IsHermitian := by
      ext i j; simp [Matrix.single_apply, and_comm]
    rw [hdir _ hY0, htr_single a a 1, mul_one]
    have hGaa_im : (G a a).im = 0 := by
      have := congrArg Complex.im (congrFun (congrFun hG_herm a) a)
      simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_im] at this
      linarith
    apply Complex.ext <;> simp [hGaa_im]
  · rw [if_neg hab]
    set Y1 : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ := Matrix.single a b 1 + Matrix.single b a 1
    set Y2 : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ :=
      Matrix.single a b Complex.I - Matrix.single b a Complex.I
    have hY1 : Y1.IsHermitian := by
      ext i j; simp [Y1, Matrix.single_apply, and_comm, add_comm]
    have hY2 : Y2.IsHermitian := by
      ext i j
      simp only [Y2, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.single_apply, star_sub,
        apply_ite star, star_zero, Complex.star_def, Complex.conj_I]
      by_cases h1 : a = j ∧ b = i
      · rcases h1 with ⟨rfl, rfl⟩; simp [hab]
      · by_cases h2 : b = j ∧ a = i
        · rcases h2 with ⟨rfl, rfl⟩; simp [Ne.symm hab]
        · have h1' : ¬(b = i ∧ a = j) := fun ⟨h, k⟩ => h1 ⟨k, h⟩
          have h2' : ¬(a = i ∧ b = j) := fun ⟨h, k⟩ => h2 ⟨k, h⟩
          simp [h1, h2, h1', h2']
    rw [hdir Y1 hY1, hdir Y2 hY2]
    have htr1 : (G * Y1).trace = G b a + G a b := by
      rw [show G * Y1 = G * Matrix.single a b 1 + G * Matrix.single b a 1 by simp [Y1, mul_add],
        Matrix.trace_add, htr_single, htr_single, mul_one, mul_one]
    have htr2 : (G * Y2).trace = Complex.I * G b a - Complex.I * G a b := by
      rw [show G * Y2 = G * Matrix.single a b Complex.I - G * Matrix.single b a Complex.I by
        simp [Y2, mul_sub], Matrix.trace_sub, htr_single, htr_single]
      ring
    have hGba : G b a = star (G a b) := by
      have := congrFun (congrFun hG_herm b) a
      simpa [Matrix.conjTranspose_apply] using this.symm
    rw [htr1, htr2, hGba]
    apply Complex.ext <;> simp

/-! ### 4. Product decomposition `midxSplit`, `densityOp`, `partialTrace`, `IsConcise` -/

abbrev MIdxOther {d : ℕ} (n : Fin d → ℕ) (ℓ : Fin d) : Type :=
  (m : {m : Fin d // m ≠ ℓ}) → Fin (n m.1)

def midxJoin {d : ℕ} {n : Fin d → ℕ} (ℓ : Fin d) (a : Fin (n ℓ)) (r : MIdxOther n ℓ) : MIdx n :=
  fun m => if hm : m = ℓ then hm ▸ a else r ⟨m, hm⟩

@[simp] lemma midxJoin_self {d : ℕ} {n : Fin d → ℕ} (ℓ : Fin d)
    (a : Fin (n ℓ)) (r : MIdxOther n ℓ) : midxJoin ℓ a r ℓ = a := by
  simp [midxJoin]

@[simp] lemma midxJoin_ne {d : ℕ} {n : Fin d → ℕ} (ℓ : Fin d)
    (a : Fin (n ℓ)) (r : MIdxOther n ℓ) {m : Fin d} (hm : m ≠ ℓ) :
    midxJoin ℓ a r m = r ⟨m, hm⟩ := by
  simp [midxJoin, hm]

@[simp] lemma update_midxJoin {d : ℕ} {n : Fin d → ℕ} (ℓ : Fin d)
    (a b : Fin (n ℓ)) (r : MIdxOther n ℓ) :
    Function.update (midxJoin ℓ a r) ℓ b = midxJoin ℓ b r := by
  ext m
  by_cases hm : m = ℓ
  · subst hm; simp
  · simp [hm]

def midxSplit {d : ℕ} {n : Fin d → ℕ} (ℓ : Fin d) : MIdx n ≃ Fin (n ℓ) × MIdxOther n ℓ where
  toFun j := (j ℓ, fun m => j m.1)
  invFun p := midxJoin ℓ p.1 p.2
  left_inv j := by
    ext m
    by_cases hm : m = ℓ
    · subst hm; simp
    · simp [hm]
  right_inv p := by
    rcases p with ⟨a, r⟩
    ext
    · simp
    · rename_i m
      simp [midxJoin_ne ℓ a r m.2]

lemma partialTrace_eq_sum_other {d : ℕ} {n : Fin d → ℕ} (ℓ : Fin d)
    (M : Matrix (MIdx n) (MIdx n) ℂ) (a b : Fin (n ℓ)) :
    partialTrace ℓ M a b = ∑ r : MIdxOther n ℓ, M (midxJoin ℓ a r) (midxJoin ℓ b r) := by
  unfold partialTrace
  rw [← Equiv.sum_comp (midxSplit ℓ).symm, Fintype.sum_prod_type]
  simp only [midxSplit, Equiv.coe_fn_symm_mk, midxJoin_self, update_midxJoin]
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx; simp [hx]
  · intro ha; exact absurd (Finset.mem_univ a) ha

def rawDensity {d n0 : ℕ} {n : Fin d → ℕ} (T : Ten d n0 n) : Matrix (MIdx n) (MIdx n) ℂ :=
  fun j j' => ∑ i : Fin n0, T (i, j) * star (T (i, j'))

lemma tnorm_sq_eq_sum {d n0 : ℕ} {n : Fin d → ℕ} (T : Ten d n0 n) :
    tnorm T ^ 2 = ∑ x : Fin n0 × MIdx n, ‖T x‖ ^ 2 := by
  unfold tnorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg ‖T x‖)

lemma tnorm_sq_pos_of_ne_zero {d n0 : ℕ} {n : Fin d → ℕ} {T : Ten d n0 n} (hT : T ≠ 0) :
    0 < tnorm T ^ 2 := by
  rw [tnorm_sq_eq_sum]
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hT
  exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hx₀))
    (Finset.single_le_sum (fun x _ => sq_nonneg ‖T x‖) (Finset.mem_univ x₀))

lemma rawDensity_trace {d n0 : ℕ} {n : Fin d → ℕ} (T : Ten d n0 n) :
    (rawDensity T).trace = ((tnorm T ^ 2 : ℝ) : ℂ) := by
  rw [tnorm_sq_eq_sum, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, rawDensity, mul_star_self_eq_norm_sq, Complex.ofReal_sum]

lemma rawDensity_posSemidef {d n0 : ℕ} {n : Fin d → ℕ} (T : Ten d n0 n) :
    (rawDensity T).PosSemidef := by
  have hHerm : (rawDensity T).IsHermitian := by
    ext j j'
    simp [rawDensity, Matrix.conjTranspose_apply, mul_comm]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun v => ?_
  have hcalc : star v ⬝ᵥ (rawDensity T) *ᵥ v =
      ((∑ i : Fin n0, ‖∑ j : MIdx n, star (v j) * T (i, j)‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Matrix.mulVec, rawDensity, Pi.star_apply,
      ← mul_star_self_eq_norm_sq, star_sum, star_mul, star_star, Complex.ofReal_sum]
    calc
      ∑ j : MIdx n, star (v j) * ∑ j' : MIdx n, (∑ i : Fin n0, T (i, j) * star (T (i, j'))) * v j'
          = ∑ j : MIdx n, ∑ i : Fin n0, ∑ j' : MIdx n,
              star (v j) * T (i, j) * (v j' * star (T (i, j'))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j' _ => by ring
      _ = ∑ i : Fin n0, ∑ j : MIdx n, ∑ j' : MIdx n,
            star (v j) * T (i, j) * (v j' * star (T (i, j'))) := Finset.sum_comm
      _ = ∑ i : Fin n0, (∑ j : MIdx n, star (v j) * T (i, j)) *
            ∑ j' : MIdx n, star (T (i, j')) * v j' := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j' _ => by ring
  rw [hcalc]
  have hnn : 0 ≤ ∑ i : Fin n0, ‖∑ j : MIdx n, star (v j) * T (i, j)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  exact_mod_cast hnn

lemma densityOp_eq_inv_smul_rawDensity {d n0 : ℕ} {n : Fin d → ℕ} (T : Ten d n0 n) :
    densityOp T = (((tnorm T ^ 2 : ℝ) : ℂ))⁻¹ • rawDensity T := by
  ext j j'
  simp [densityOp, rawDensity, div_eq_inv_mul]

lemma densityOp_posSemidef {d n0 : ℕ} {n : Fin d → ℕ} {T : Ten d n0 n} (hT : T ≠ 0) :
    (densityOp T).PosSemidef := by
  rw [densityOp_eq_inv_smul_rawDensity]
  have hpos : (0 : ℝ) ≤ (tnorm T ^ 2)⁻¹ := inv_nonneg.mpr (le_of_lt (tnorm_sq_pos_of_ne_zero hT))
  have hsmul : (((tnorm T ^ 2 : ℝ) : ℂ))⁻¹ • rawDensity T = (tnorm T ^ 2)⁻¹ • rawDensity T := by
    ext j j'
    simp [Complex.real_smul]
  rw [hsmul]
  exact (rawDensity_posSemidef T).smul hpos

lemma densityOp_trace {d n0 : ℕ} {n : Fin d → ℕ} {T : Ten d n0 n} (hT : T ≠ 0) :
    (densityOp T).trace = 1 := by
  rw [densityOp_eq_inv_smul_rawDensity, Matrix.trace_smul, rawDensity_trace, smul_eq_mul]
  have hne : ((tnorm T ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (tnorm_sq_pos_of_ne_zero hT)
  exact inv_mul_cancel₀ hne

lemma rawDensity_act {d n0 : ℕ} {n : Fin d → ℕ} (A : MatTuple n) (T : Ten d n0 n) :
    rawDensity (act A T) = kron A * rawDensity T * (kron A)ᴴ := by
  ext j j'
  simp only [rawDensity, act, Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul]
  calc
    ∑ i : Fin n0, (∑ k, kron A j k * T (i, k)) * ∑ k', star (T (i, k')) * star (kron A j' k')
        = ∑ i : Fin n0, ∑ k, ∑ k', kron A j k * (T (i, k) * star (T (i, k'))) * star (kron A j' k') := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k' _ => by ring
    _ = ∑ k', (∑ k, kron A j k * ∑ i : Fin n0, T (i, k) * star (T (i, k'))) * star (kron A j' k') := by
      rw [Finset.sum_comm]
      conv_lhs =>
        arg 2; ext k
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]

lemma kron_mul {d : ℕ} {n : Fin d → ℕ} (A B : MatTuple n) :
    kron A * kron B = kron (fun ℓ => A ℓ * B ℓ) := by
  ext j j'
  simp only [Matrix.mul_apply, kron]
  simp_rw [← Finset.prod_mul_distrib]
  symm
  simpa [Fintype.piFinset_univ] using
    (Fintype.prod_sum (fun ℓ (k : Fin (n ℓ)) => A ℓ (j ℓ) k * B ℓ k (j' ℓ)))

lemma kron_one {d : ℕ} {n : Fin d → ℕ} :
    kron (fun ℓ : Fin d => (1 : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ)) = 1 := by
  ext j j'
  simp only [kron, Matrix.one_apply]
  by_cases h : j = j'
  · subst h; simp
  · obtain ⟨ℓ₀, hℓ₀⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ ℓ₀) (by simp [hℓ₀])

lemma kron_conjTranspose {d : ℕ} {n : Fin d → ℕ} (A : MatTuple n) :
    (kron A)ᴴ = kron (fun ℓ => (A ℓ)ᴴ) := by
  ext j j'
  simp [kron, Matrix.conjTranspose_apply, star_prod]

lemma act_act {d n0 : ℕ} {n : Fin d → ℕ} (A B : MatTuple n) (T : Ten d n0 n) :
    act A (act B T) = act (fun ℓ => A ℓ * B ℓ) T := by
  ext ⟨i, j⟩
  simp only [act, ← kron_mul, Matrix.mul_apply]
  calc
    ∑ k, kron A j k * ∑ k', kron B k k' * T (i, k')
        = ∑ k, ∑ k', kron A j k * kron B k k' * T (i, k') := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k' _ => by ring
    _ = ∑ k', (∑ k, kron A j k * kron B k k') * T (i, k') := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k' _ => by rw [Finset.sum_mul]

lemma act_one {d n0 : ℕ} {n : Fin d → ℕ} (T : Ten d n0 n) :
    act (fun ℓ : Fin d => (1 : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ)) T = T := by
  ext ⟨i, j⟩
  simp [act, kron_one (n := n), Matrix.one_apply]

lemma act_ne_zero_of_det_ne_zero {d n0 : ℕ} {n : Fin d → ℕ} {A : MatTuple n}
    (hdet : ∀ ℓ, (A ℓ).det ≠ 0) {T : Ten d n0 n} (hT : T ≠ 0) :
    act A T ≠ 0 := by
  intro h0
  have hinv : ∀ ℓ, (A ℓ)⁻¹ * A ℓ = 1 := fun ℓ =>
    Matrix.nonsing_inv_mul _ (Ne.isUnit (hdet ℓ))
  have hrec : act (fun ℓ => (A ℓ)⁻¹) (act A T) = T := by
    rw [act_act]
    simp_rw [hinv]
    exact act_one T
  have hz : act (fun ℓ => (A ℓ)⁻¹) (0 : Ten d n0 n) = 0 := by
    ext x; simp [act]
  rw [h0, hz] at hrec
  exact hT hrec.symm

lemma partialTrace_trace {d : ℕ} {n : Fin d → ℕ} (ℓ : Fin d) (M : Matrix (MIdx n) (MIdx n) ℂ) :
    (partialTrace ℓ M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, partialTrace_eq_sum_other]
  symm
  rw [← Equiv.sum_comp (midxSplit ℓ).symm, Fintype.sum_prod_type]
  rfl

lemma partialTrace_smul {d : ℕ} {n : Fin d → ℕ} (ℓ : Fin d) (c : ℂ)
    (M : Matrix (MIdx n) (MIdx n) ℂ) :
    partialTrace ℓ (c • M) = c • partialTrace ℓ M := by
  ext a b
  simp only [partialTrace_eq_sum_other, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma partialTrace_posSemidef {d : ℕ} {n : Fin d → ℕ} (ℓ : Fin d)
    {M : Matrix (MIdx n) (MIdx n) ℂ} (hM : M.PosSemidef) :
    (partialTrace ℓ M).PosSemidef := by
  have hHerm : (partialTrace ℓ M).IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, partialTrace_eq_sum_other, star_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have := congrFun (congrFun hM.isHermitian (midxJoin ℓ a r)) (midxJoin ℓ b r)
    simpa [Matrix.conjTranspose_apply] using this
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun v => ?_
  have hsum : star v ⬝ᵥ (partialTrace ℓ M) *ᵥ v =
      ∑ r : MIdxOther n ℓ,
        star (fun j : MIdx n => if (midxSplit ℓ j).2 = r then v (j ℓ) else 0) ⬝ᵥ
          M *ᵥ (fun j : MIdx n => if (midxSplit ℓ j).2 = r then v (j ℓ) else 0) := by
    have hterm : ∀ r : MIdxOther n ℓ,
        star (fun j : MIdx n => if (midxSplit ℓ j).2 = r then v (j ℓ) else 0) ⬝ᵥ
          M *ᵥ (fun j : MIdx n => if (midxSplit ℓ j).2 = r then v (j ℓ) else 0) =
        ∑ a : Fin (n ℓ), star (v a) * ∑ b : Fin (n ℓ), M (midxJoin ℓ a r) (midxJoin ℓ b r) * v b := by
      intro r
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      rw [← Equiv.sum_comp (midxSplit ℓ).symm, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hsymm_app : ∀ (x : Fin (n ℓ)) (y : MIdxOther n ℓ),
          (midxSplit ℓ).symm (x, y) = midxJoin ℓ x y := fun _ _ => rfl
      rw [Finset.sum_eq_single r]
      · have hcond_a : (midxSplit ℓ ((midxSplit ℓ).symm (a, r))).2 = r := by simp
        rw [if_pos hcond_a, hsymm_app a r, midxJoin_self]
        congr 1
        rw [← Equiv.sum_comp (midxSplit ℓ).symm, Fintype.sum_prod_type, Finset.sum_comm]
        rw [Finset.sum_eq_single r]
        · simp only [Equiv.apply_symm_apply, ↓reduceIte]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hsymm_app b r, midxJoin_self]
        · intro r' _ hr'
          exact Finset.sum_eq_zero fun b _ => by simp [hr']
        · intro hr; exact absurd (Finset.mem_univ r) hr
      · intro r' _ hr'
        have hcond_ne : (midxSplit ℓ ((midxSplit ℓ).symm (a, r'))).2 ≠ r := by simp [hr']
        rw [if_neg hcond_ne, star_zero, zero_mul]
      · intro hr; exact absurd (Finset.mem_univ r) hr
    simp_rw [hterm]
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, partialTrace_eq_sum_other]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    conv_lhs =>
      arg 2; ext b
      rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
  rw [hsum]
  exact Finset.sum_nonneg fun r _ => hM.dotProduct_mulVec_nonneg _

lemma dotProduct_partialTrace_rawDensity_eq {d n0 : ℕ} {n : Fin d → ℕ}
    (ℓ : Fin d) (S : Ten d n0 n) (w : Fin (n ℓ) → ℂ) :
    star w ⬝ᵥ (partialTrace ℓ (rawDensity S)) *ᵥ w =
      ((∑ i : Fin n0, ∑ r : MIdxOther n ℓ,
        ‖∑ a : Fin (n ℓ), star (w a) * S (i, midxJoin ℓ a r)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Matrix.mulVec, partialTrace_eq_sum_other, rawDensity, Pi.star_apply,
    ← mul_star_self_eq_norm_sq, star_sum, star_mul, star_star, Complex.ofReal_sum]
  calc
    ∑ a : Fin (n ℓ), star (w a) *
        ∑ b : Fin (n ℓ), (∑ r : MIdxOther n ℓ, ∑ i : Fin n0,
          S (i, midxJoin ℓ a r) * star (S (i, midxJoin ℓ b r))) * w b
        = ∑ a : Fin (n ℓ), ∑ i : Fin n0, ∑ r : MIdxOther n ℓ, ∑ b : Fin (n ℓ),
            star (w a) * S (i, midxJoin ℓ a r) * (star (S (i, midxJoin ℓ b r)) * w b) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have h1 : ∀ b : Fin (n ℓ),
          (∑ r : MIdxOther n ℓ, ∑ i : Fin n0,
            S (i, midxJoin ℓ a r) * star (S (i, midxJoin ℓ b r))) * w b =
          ∑ i : Fin n0, ∑ r : MIdxOther n ℓ,
            S (i, midxJoin ℓ a r) * star (S (i, midxJoin ℓ b r)) * w b := by
        intro b
        rw [Finset.sum_mul]
        conv_lhs =>
          arg 2; ext r
          rw [Finset.sum_mul]
        exact Finset.sum_comm
      simp_rw [h1, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ i : Fin n0, ∑ r : MIdxOther n ℓ, ∑ a : Fin (n ℓ), ∑ b : Fin (n ℓ),
          star (w a) * S (i, midxJoin ℓ a r) * (star (S (i, midxJoin ℓ b r)) * w b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i : Fin n0, ∑ r : MIdxOther n ℓ,
          (∑ a : Fin (n ℓ), star (w a) * S (i, midxJoin ℓ a r)) *
            ∑ b : Fin (n ℓ), star (S (i, midxJoin ℓ b r)) * w b := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm

lemma isConcise_act_of_det_ne_zero {d n0 : ℕ} {n : Fin d → ℕ} {A : MatTuple n}
    (hdet : ∀ ℓ, (A ℓ).det ≠ 0) {T : Ten d n0 n} (hT : T ≠ 0) (hconc : IsConcise T) :
    IsConcise (act A T) := by
  intro ℓ
  set S : Ten d n0 n := act A T
  have hS : S ≠ 0 := act_ne_zero_of_det_ne_zero hdet hT
  have hM_psd : (momentMap S ℓ).PosSemidef :=
    partialTrace_posSemidef ℓ (densityOp_posSemidef hS)
  suffices (momentMap S ℓ).PosDef from posDef_det_ne_zero this
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hM_psd.isHermitian ?_
  intro v hv
  have hge := hM_psd.dotProduct_mulVec_nonneg v
  have hre_ge : 0 ≤ (star v ⬝ᵥ (momentMap S ℓ) *ᵥ v).re := (RCLike.nonneg_iff.mp hge).1
  have him_eq : (star v ⬝ᵥ (momentMap S ℓ) *ᵥ v).im = 0 := (RCLike.nonneg_iff.mp hge).2
  have hne0 : star v ⬝ᵥ (momentMap S ℓ) *ᵥ v ≠ 0 := by
    intro h0
    have hraw0 : star v ⬝ᵥ (partialTrace ℓ (rawDensity S)) *ᵥ v = 0 := by
      have hm : momentMap S ℓ = (((tnorm S ^ 2 : ℝ) : ℂ))⁻¹ • partialTrace ℓ (rawDensity S) := by
        unfold momentMap
        rw [densityOp_eq_inv_smul_rawDensity, partialTrace_smul]
      rw [hm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h0
      have hc_ne : (((tnorm S ^ 2 : ℝ) : ℂ))⁻¹ ≠ 0 :=
        inv_ne_zero (by exact_mod_cast ne_of_gt (tnorm_sq_pos_of_ne_zero hS))
      exact (mul_eq_zero.mp h0).resolve_left hc_ne
    have hsliceS : ∀ (i : Fin n0) (r : MIdxOther n ℓ),
        ∑ a : Fin (n ℓ), star (v a) * S (i, midxJoin ℓ a r) = 0 := by
      intro i r
      rw [dotProduct_partialTrace_rawDensity_eq] at hraw0
      have hre : ∑ i' : Fin n0, ∑ r' : MIdxOther n ℓ,
          ‖∑ a : Fin (n ℓ), star (v a) * S (i', midxJoin ℓ a r')‖ ^ 2 = 0 :=
        Complex.ofReal_injective (by simpa using hraw0)
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i' _ =>
        Finset.sum_nonneg fun _ _ => sq_nonneg _).mp hre i (Finset.mem_univ i)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp h1 r (Finset.mem_univ r)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp h2)
    set w : Fin (n ℓ) → ℂ := (A ℓ)ᴴ *ᵥ v
    have hw_ne : w ≠ 0 := by
      intro hw0
      have hdetH : (A ℓ)ᴴ.det ≠ 0 := by
        rw [Matrix.det_conjTranspose]
        exact star_ne_zero.mpr (hdet ℓ)
      have hunit : IsUnit (A ℓ)ᴴ := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hdetH)
      exact hv (Matrix.mulVec_injective_of_isUnit hunit (by simpa [w] using hw0))
    have hsliceT : ∀ (i : Fin n0) (r : MIdxOther n ℓ),
        ∑ b : Fin (n ℓ), star (w b) * T (i, midxJoin ℓ b r) = 0 := by
      intro i r
      set Ainv_other : MatTuple n := Function.update (fun m => (A m)⁻¹) ℓ 1
      set A_only : MatTuple n := Function.update (fun m => (1 : Matrix (Fin (n m)) (Fin (n m)) ℂ)) ℓ (A ℓ)
      have hprod_other : (fun m => Ainv_other m * A m) = A_only := by
        funext m
        by_cases hm : m = ℓ
        · subst hm; simp [Ainv_other, A_only]
        · simp [Ainv_other, A_only, hm, Matrix.nonsing_inv_mul _ (Ne.isUnit (hdet m))]
      have hrel : act Ainv_other S = act A_only T := by
        rw [show S = act A T from rfl, act_act Ainv_other A T, hprod_other]
      have hlhs : ∑ a : Fin (n ℓ), star (v a) * (act Ainv_other S) (i, midxJoin ℓ a r) = 0 := by
        have hact_other : ∀ a : Fin (n ℓ),
            (act Ainv_other S) (i, midxJoin ℓ a r) =
            ∑ r' : MIdxOther n ℓ,
              (∏ m : {m : Fin d // m ≠ ℓ}, Ainv_other m.1 (r m) (r' m)) * S (i, midxJoin ℓ a r') := by
          intro a
          simp only [act]
          rw [← Equiv.sum_comp (midxSplit ℓ).symm, Fintype.sum_prod_type]
          simp only [midxSplit, Equiv.coe_fn_symm_mk]
          have hzero_ne : ∀ (a' : Fin (n ℓ)) (r' : MIdxOther n ℓ), a' ≠ a →
              kron Ainv_other (midxJoin ℓ a r) (midxJoin ℓ a' r') = 0 := by
            intro a' r' hne
            refine Finset.prod_eq_zero (Finset.mem_univ ℓ) ?_
            simp [Ainv_other, Ne.symm hne]
          have hdiag_eq : ∀ r' : MIdxOther n ℓ,
              kron Ainv_other (midxJoin ℓ a r) (midxJoin ℓ a r') =
              ∏ m : {m : Fin d // m ≠ ℓ}, Ainv_other m.1 (r m) (r' m) := by
            intro r'
            unfold kron
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ℓ)]
            simp only [Ainv_other, midxJoin_self, Function.update_self, Matrix.one_apply_eq, one_mul]
            refine Finset.prod_bij (fun m hm => ⟨m, Finset.ne_of_mem_erase hm⟩)
              (fun _ _ => Finset.mem_univ _)
              (fun m₁ _ m₂ _ h => congrArg Subtype.val h)
              (fun m _ => ⟨m.1, Finset.mem_erase.mpr ⟨m.2, Finset.mem_univ _⟩, rfl⟩)
              (fun m hm => ?_)
            have hne := Finset.ne_of_mem_erase hm
            simp [hne]
          calc
            ∑ a' : Fin (n ℓ), ∑ r' : MIdxOther n ℓ,
                kron Ainv_other (midxJoin ℓ a r) (midxJoin ℓ a' r') * S (i, midxJoin ℓ a' r')
                = ∑ r' : MIdxOther n ℓ,
                    kron Ainv_other (midxJoin ℓ a r) (midxJoin ℓ a r') * S (i, midxJoin ℓ a r') := by
              rw [Finset.sum_eq_single a]
              · intro a' _ hne
                exact Finset.sum_eq_zero fun r' _ => by rw [hzero_ne a' r' hne, zero_mul]
              · intro ha; exact absurd (Finset.mem_univ a) ha
            _ = ∑ r' : MIdxOther n ℓ,
                  (∏ m : {m : Fin d // m ≠ ℓ}, Ainv_other m.1 (r m) (r' m)) * S (i, midxJoin ℓ a r') := by
              refine Finset.sum_congr rfl fun r' _ => by rw [hdiag_eq r']
        simp_rw [hact_other, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun r' _ => ?_
        have : (∑ a : Fin (n ℓ), star (v a) *
            ((∏ m : {m : Fin d // m ≠ ℓ}, Ainv_other m.1 (r m) (r' m)) * S (i, midxJoin ℓ a r'))) =
            (∏ m : {m : Fin d // m ≠ ℓ}, Ainv_other m.1 (r m) (r' m)) *
              ∑ a : Fin (n ℓ), star (v a) * S (i, midxJoin ℓ a r') := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => by ring
        rw [this, hsliceS i r', mul_zero]
      rw [hrel] at hlhs
      have hrhs : ∑ a : Fin (n ℓ), star (v a) * (act A_only T) (i, midxJoin ℓ a r) =
          ∑ b : Fin (n ℓ), star (w b) * T (i, midxJoin ℓ b r) := by
        have hact1 : ∀ a : Fin (n ℓ),
            (act A_only T) (i, midxJoin ℓ a r) =
            ∑ b : Fin (n ℓ), A ℓ a b * T (i, midxJoin ℓ b r) := by
          intro a
          simp only [act]
          rw [← Equiv.sum_comp (midxSplit ℓ).symm, Fintype.sum_prod_type]
          simp only [midxSplit, Equiv.coe_fn_symm_mk]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_eq_single r]
          · congr 1
            unfold kron
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ℓ)]
            simp only [A_only, midxJoin_self, Function.update_self]
            have h1 : ∏ m ∈ Finset.univ.erase ℓ,
                Function.update (fun m => (1 : Matrix (Fin (n m)) (Fin (n m)) ℂ)) ℓ (A ℓ) m
                  (midxJoin ℓ a r m) (midxJoin ℓ b r m) = 1 := by
              refine Finset.prod_eq_one fun m hm => ?_
              have hne := Finset.ne_of_mem_erase hm
              simp [hne]
            rw [h1, mul_one]
          · intro r' _ hr'
            have ⟨m₀, hm₀⟩ := Function.ne_iff.mp hr'
            have hk0 : kron A_only (midxJoin ℓ a r) (midxJoin ℓ b r') = 0 := by
              refine Finset.prod_eq_zero (Finset.mem_univ m₀.1) ?_
              simp [A_only, m₀.2, Ne.symm hm₀]
            rw [hk0, zero_mul]
          · intro hr; exact absurd (Finset.mem_univ r) hr
        simp_rw [hact1, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [w, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum,
          star_mul, star_star, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => by ring
      exact hrhs.symm.trans hlhs
    have hrawT0 : star w ⬝ᵥ (partialTrace ℓ (rawDensity T)) *ᵥ w = 0 := by
      rw [dotProduct_partialTrace_rawDensity_eq]
      have hsum0 : ∑ i : Fin n0, ∑ r : MIdxOther n ℓ,
          ‖∑ a : Fin (n ℓ), star (w a) * T (i, midxJoin ℓ a r)‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun r _ => ?_
        rw [hsliceT i r, norm_zero, zero_pow two_ne_zero]
      rw [hsum0, Complex.ofReal_zero]
    have hmT0 : star w ⬝ᵥ (momentMap T ℓ) *ᵥ w = 0 := by
      unfold momentMap
      rw [densityOp_eq_inv_smul_rawDensity, partialTrace_smul, Matrix.smul_mulVec,
        dotProduct_smul, hrawT0, smul_zero]
    have hposT := posDef_of_posSemidef_det_ne_zero
      (partialTrace_posSemidef ℓ (densityOp_posSemidef hT)) (hconc ℓ)
    exact ne_of_gt (hposT.dotProduct_mulVec_pos hw_ne) hmT0
  have hre_pos : 0 < (star v ⬝ᵥ (momentMap S ℓ) *ᵥ v).re := by
    refine lt_of_le_of_ne hre_ge ?_
    intro hre0
    apply hne0
    apply Complex.ext <;> simp [← hre0, him_eq]
  rw [RCLike.pos_iff]
  exact ⟨hre_pos, him_eq⟩

/-! ### 5. Properties of `sigmaOf` and `entropicScalingSeq` -/

lemma sigmaOf_posSemidef_and_trace_pos {d : ℕ} {n : Fin d → ℕ} (η : ℝ) (θ : Fin d → ℝ)
    {ρ : Matrix (MIdx n) (MIdx n) ℂ} (hρ_psd : ρ.PosSemidef) (hρ_tr : ρ.trace = 1)
    (hρ_inv : ∀ ℓ, (partialTrace ℓ ρ).det ≠ 0) :
    (sigmaOf η θ ρ).PosSemidef ∧ 0 < (sigmaOf η θ ρ).trace.re ∧
      (sigmaOf η θ ρ).trace.im = 0 := by
  set M : Matrix (MIdx n) (MIdx n) ℂ :=
    kron (fun ℓ => cfc (fun x : ℝ => x ^ (-(η * θ ℓ / 2))) (partialTrace ℓ ρ))
  have hM_herm : M.IsHermitian := by
    rw [Matrix.IsHermitian, kron_conjTranspose]
    congr 1; funext ℓ
    exact (isHermitian_cfc (partialTrace_posSemidef ℓ hρ_psd).isHermitian _).eq
  set Minv : Matrix (MIdx n) (MIdx n) ℂ :=
    kron (fun ℓ => cfc (fun x : ℝ => x ^ (η * θ ℓ / 2)) (partialTrace ℓ ρ))
  have hMinv : Minv * M = 1 := by
    rw [kron_mul]
    have h1 : (fun ℓ => cfc (fun x : ℝ => x ^ (η * θ ℓ / 2)) (partialTrace ℓ ρ) *
        cfc (fun x : ℝ => x ^ (-(η * θ ℓ / 2))) (partialTrace ℓ ρ)) =
        fun ℓ => (1 : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ) := by
      funext ℓ
      have hpos := posDef_of_posSemidef_det_ne_zero (partialTrace_posSemidef ℓ hρ_psd) (hρ_inv ℓ)
      rw [cfc_mul_cfc hpos.isHermitian]
      have hdiag_eq : cfc (fun x : ℝ => x ^ (η * θ ℓ / 2) * x ^ (-(η * θ ℓ / 2))) (partialTrace ℓ ρ) =
          cfc (fun _ : ℝ => (1 : ℝ)) (partialTrace ℓ ρ) := by
        rw [cfc_eq_unitary_diag hpos.isHermitian, cfc_eq_unitary_diag hpos.isHermitian]
        congr 2; ext i j
        by_cases hij : i = j
        · subst hij
          have heig_pos := hpos.eigenvalues_pos i
          have hmul1 : (hpos.isHermitian.eigenvalues i) ^ (η * θ ℓ / 2) *
              (hpos.isHermitian.eigenvalues i) ^ (-(η * θ ℓ / 2)) = 1 := by
            rw [← Real.rpow_add heig_pos, add_neg_cancel, Real.rpow_zero]
          simp only [Matrix.diagonal_apply_eq]
          exact congrArg Complex.ofReal hmul1
        · simp [hij]
      rw [hdiag_eq, cfc_const_one hpos.isHermitian]
    rw [h1, kron_one (n := n)]
  have hMM : M * Minv = 1 := by
    have hMinv_herm : Minv.IsHermitian := by
      rw [Matrix.IsHermitian, kron_conjTranspose]
      congr 1; funext ℓ
      exact (isHermitian_cfc (partialTrace_posSemidef ℓ hρ_psd).isHermitian _).eq
    have := congrArg Matrix.conjTranspose hMinv
    simpa [Matrix.conjTranspose_mul, hM_herm.eq, hMinv_herm.eq] using this
  have hσ_eq : sigmaOf η θ ρ = Mᴴ * ρ * M := by
    unfold sigmaOf
    rw [hM_herm.eq]
  have hσ_psd : (sigmaOf η θ ρ).PosSemidef := by
    rw [hσ_eq]
    exact hρ_psd.conjTranspose_mul_mul_same M
  have hdiag_nn : ∀ j : MIdx n, 0 ≤ (sigmaOf η θ ρ j j).re ∧ (sigmaOf η θ ρ j j).im = 0 := by
    intro j
    have hj := hσ_psd.dotProduct_mulVec_nonneg (Pi.single j 1)
    have hjj : star (Pi.single (M := fun _ => ℂ) j 1) ⬝ᵥ (sigmaOf η θ ρ) *ᵥ Pi.single j 1 =
        sigmaOf η θ ρ j j := by
      simp [dotProduct, Matrix.mulVec, Pi.single_apply]
    rw [hjj] at hj
    exact RCLike.nonneg_iff.mp hj
  have htr_im : (sigmaOf η θ ρ).trace.im = 0 := by
    simp only [Matrix.trace, Matrix.diag, Complex.im_sum]
    exact Finset.sum_eq_zero fun j _ => (hdiag_nn j).2
  have htr_pos : 0 < (sigmaOf η θ ρ).trace.re := by
    have hge0 : 0 ≤ (sigmaOf η θ ρ).trace.re := by
      simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
      exact Finset.sum_nonneg fun j _ => (hdiag_nn j).1
    refine lt_of_le_of_ne hge0 ?_
    intro htr0
    have hdiag0 : ∀ j : MIdx n, sigmaOf η θ ρ j j = 0 := by
      have hsum0 : ∑ j : MIdx n, (sigmaOf η θ ρ j j).re = 0 := by
        simpa [Matrix.trace, Matrix.diag, Complex.re_sum] using htr0.symm
      intro j
      have hre0 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => (hdiag_nn k).1).mp hsum0 j (Finset.mem_univ j)
      apply Complex.ext <;> simp [hre0, (hdiag_nn j).2]
    have hσ0 : sigmaOf η θ ρ = 0 := by
      ext j k
      by_cases hjk : j = k
      · subst hjk; exact hdiag0 j
      · set z := sigmaOf η θ ρ j k
        have hkj : sigmaOf η θ ρ k j = star z := by
          have := congrFun (congrFun hσ_psd.isHermitian k) j
          simpa [Matrix.conjTranspose_apply, z] using this.symm
        set v : MIdx n → ℂ := fun x => if x = j then 1 else if x = k then -star z else 0
        have hv0 := (RCLike.nonneg_iff.mp (hσ_psd.dotProduct_mulVec_nonneg v)).1
        have hv : 0 ≤ (star v ⬝ᵥ (sigmaOf η θ ρ) *ᵥ v).re := hv0
        have hexp : star v ⬝ᵥ (sigmaOf η θ ρ) *ᵥ v = -(2 : ℂ) * (z * star z) := by
          have hmv_jk : ∀ a : MIdx n, (sigmaOf η θ ρ *ᵥ v) a =
              sigmaOf η θ ρ a j + sigmaOf η θ ρ a k * (-star z) := by
            intro a
            simp only [Matrix.mulVec, dotProduct, v]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
            have hk_mem : k ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩
            rw [← Finset.add_sum_erase _ _ hk_mem]
            have hrest : ∑ x ∈ (Finset.univ.erase j).erase k,
                sigmaOf η θ ρ a x * (if x = j then 1 else if x = k then -star z else 0) = 0 := by
              refine Finset.sum_eq_zero fun x hx => ?_
              have hxk : x ≠ k := (Finset.mem_erase.mp hx).1
              have hxj : x ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
              simp [hxj, hxk]
            rw [hrest, add_zero]
            simp [Ne.symm hjk]
          simp only [dotProduct, Pi.star_apply]
          simp_rw [hmv_jk]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          have hk_mem : k ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩
          rw [← Finset.add_sum_erase _ _ hk_mem]
          have hrest : ∑ x ∈ (Finset.univ.erase j).erase k,
              star (v x) * (sigmaOf η θ ρ x j + sigmaOf η θ ρ x k * -star z) = 0 := by
            refine Finset.sum_eq_zero fun x hx => ?_
            have hxk : x ≠ k := (Finset.mem_erase.mp hx).1
            have hxj : x ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
            simp [v, hxj, hxk]
          rw [hrest, add_zero]
          simp only [v, if_true, if_neg (Ne.symm hjk), star_one, one_mul, star_neg, star_star,
            hdiag0 j, hdiag0 k, zero_add, zero_mul, add_zero, hkj]
          ring
        rw [hexp] at hv
        have hz_re : (-(2 : ℂ) * (z * star z)).re = -2 * ‖z‖ ^ 2 := by
          rw [mul_star_self_eq_norm_sq z, ← Complex.ofReal_ofNat, ← Complex.ofReal_neg,
            ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [hz_re] at hv
        have hzn : ‖z‖ = 0 := le_antisymm (by nlinarith [norm_nonneg z]) (norm_nonneg z)
        exact norm_eq_zero.mp hzn
    have hρ0 : ρ = 0 := by
      calc
        ρ = 1 * ρ * 1 := by simp
        _ = (Minv * M) * ρ * (M * Minv) := by rw [hMinv, hMM]
        _ = Minv * sigmaOf η θ ρ * Minv := by
          unfold sigmaOf; simp only [M, Matrix.mul_assoc]
        _ = 0 := by rw [hσ0]; simp
    rw [hρ0, Matrix.trace_zero] at hρ_tr
    exact zero_ne_one hρ_tr
  exact ⟨hσ_psd, htr_pos, htr_im⟩

lemma entropicScalingSeq_ne_zero_and_concise {d n0 : ℕ} {n : Fin d → ℕ}
    (η : ℝ) (θ : Fin d → ℝ) {T : Ten d n0 n} (hT : T ≠ 0) (hconc : IsConcise T) :
    ∀ k : ℕ, entropicScalingSeq η θ T k ≠ 0 ∧ IsConcise (entropicScalingSeq η θ T k) := by
  intro k
  induction k with
  | zero => exact ⟨hT, hconc⟩
  | succ k ih =>
    rcases ih with ⟨hTk, hconc_k⟩
    set Tk := entropicScalingSeq η θ T k
    have hdetA : ∀ ℓ, (cfc (fun x : ℝ => x ^ (-(η * θ ℓ / 2))) (momentMap Tk ℓ)).det ≠ 0 := by
      intro ℓ
      have hpos := posDef_of_posSemidef_det_ne_zero
        (partialTrace_posSemidef ℓ (densityOp_posSemidef hTk)) (hconc_k ℓ)
      exact posDef_det_ne_zero (posDef_cfc_of_pos hpos.isHermitian _ fun i =>
        Real.rpow_pos_of_pos (hpos.eigenvalues_pos i) _)
    exact ⟨act_ne_zero_of_det_ne_zero hdetA hTk,
      isConcise_act_of_det_ne_zero hdetA hTk hconc_k⟩

/-! ### 6. Part (ii) dimension-extension helper -/

def extShape {d : ℕ} (n : Fin d → ℕ) : Fin (d + 1) → ℕ := Fin.cases 1 n

def extProb {d : ℕ} (η : ℝ) (θ : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases (1 - η) (fun ℓ => η * θ ℓ)

lemma extShape_zero_eq {d : ℕ} {n : Fin d → ℕ} (a b : Fin (extShape n 0)) : a = b :=
  @Subsingleton.elim (Fin 1) inferInstance a b

def extEquiv {d : ℕ} (n : Fin d → ℕ) : MIdx (extShape n) ≃ MIdx n where
  toFun j' ℓ := j' ℓ.succ
  invFun j := Fin.cases (0 : Fin 1) j
  left_inv j' := by
    funext k
    refine Fin.cases ?_ ?_ k
    · exact extShape_zero_eq _ _
    · intro ℓ; rfl
  right_inv j := by funext ℓ; rfl

lemma cfc_rpow_one_mat {m : ℕ} (s : ℝ) :
    cfc (fun x : ℝ => x ^ s) (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ).IsHermitian := Matrix.isHermitian_one
  have heig : ∀ i : Fin m, h1.eigenvalues i = 1 := by
    intro i
    have hv := h1.mulVec_eigenvectorBasis i
    have hne0 := h1.eigenvectorBasis.orthonormal.ne_zero i
    have hne : (h1.eigenvectorBasis i).ofLp ≠ 0 := fun h0 => hne0 (WithLp.ofLp_injective _ h0)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have hjeq := congrFun hv j
    simp only [Matrix.one_mulVec, Pi.smul_apply, RCLike.real_smul_eq_coe_mul] at hjeq
    have hmul : (((h1.eigenvalues i : ℝ) : ℂ) - 1) * (h1.eigenvectorBasis i).ofLp j = 0 := by
      linear_combination hjeq.symm
    rcases mul_eq_zero.mp hmul with hsub | hzero
    · have : ((h1.eigenvalues i : ℝ) : ℂ) = 1 := sub_eq_zero.mp hsub
      exact_mod_cast this
    · exact absurd hzero hj
  rw [cfc_eq_unitary_diag h1]
  have hdiag : Matrix.diagonal (fun i : Fin m => (((h1.eigenvalues i ^ s : ℝ)) : ℂ)) = 1 := by
    ext i j; by_cases hij : i = j
    · subst hij; simp [heig i]
    · simp [hij]
  rw [hdiag, mul_one]
  exact Unitary.coe_mul_star_self h1.eigenvectorUnitary

lemma vnEntropy_one_mat {m : ℕ} : vnEntropy (1 : Matrix (Fin m) (Fin m) ℂ) = 0 := by
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ).IsHermitian := Matrix.isHermitian_one
  rw [vnEntropy_eq_neg_trace_mul_log h1, one_mul, cfc_eq_unitary_diag h1]
  have heig : ∀ i : Fin m, h1.eigenvalues i = 1 := by
    intro i
    have hv := h1.mulVec_eigenvectorBasis i
    have hne0 := h1.eigenvectorBasis.orthonormal.ne_zero i
    have hne : (h1.eigenvectorBasis i).ofLp ≠ 0 := fun h0 => hne0 (WithLp.ofLp_injective _ h0)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have hjeq := congrFun hv j
    simp only [Matrix.one_mulVec, Pi.smul_apply, RCLike.real_smul_eq_coe_mul] at hjeq
    have hmul : (((h1.eigenvalues i : ℝ) : ℂ) - 1) * (h1.eigenvectorBasis i).ofLp j = 0 := by
      linear_combination hjeq.symm
    rcases mul_eq_zero.mp hmul with hsub | hzero
    · have : ((h1.eigenvalues i : ℝ) : ℂ) = 1 := sub_eq_zero.mp hsub
      exact_mod_cast this
    · exact absurd hzero hj
  have hdiag : Matrix.diagonal (fun i : Fin m => ((Real.log (h1.eigenvalues i) : ℝ) : ℂ)) = 0 := by
    ext i j; by_cases hij : i = j
    · subst hij; simp [heig i]
    · simp [hij]
  rw [hdiag, mul_zero, zero_mul, Matrix.trace_zero, Complex.zero_re, neg_zero]

end Aux74

open MomentPolytopes.QuantumFunctionals

theorem solution :
    (∀ (d : ℕ) (n : Fin d → ℕ) (θ : Fin d → ℝ) (η : ℝ), IsProbVec θ → 0 < η →
      (∀ ρ : Matrix (MIdx n) (MIdx n) ℂ, ρ.PosSemidef → ρ.trace = 1 →
        (∀ ℓ, (partialTrace ℓ ρ).det ≠ 0) → EntropyIneq76 η θ ρ) →
      ∀ (n0 : ℕ) (T : Ten d n0 n), T ≠ 0 → IsConcise T →
        StepSizeCondition (phiTheta θ) η (entropicScalingSeq η θ T)
          (fun _ => ((Real.exp (η / 2) : ℝ) : ℂ))) ∧
    ((∀ (d : ℕ) (n : Fin d → ℕ) (θ : Fin d → ℝ), IsProbVec θ →
        ∀ ρ : Matrix (MIdx n) (MIdx n) ℂ, ρ.PosSemidef → ρ.trace = 1 →
          (∀ ℓ, (partialTrace ℓ ρ).det ≠ 0) → EntropyIneq76 1 θ ρ) →
      ∀ (d : ℕ) (n : Fin d → ℕ) (θ : Fin d → ℝ) (η : ℝ), IsProbVec θ → 0 < η → η ≤ 1 →
        ∀ ρ : Matrix (MIdx n) (MIdx n) ℂ, ρ.PosSemidef → ρ.trace = 1 →
          (∀ ℓ, (partialTrace ℓ ρ).det ≠ 0) → EntropyIneq76 η θ ρ) ∧
    (∀ (d : ℕ) (n : Fin d → ℕ) (θ : Fin d → ℝ), IsProbVec θ →
      ∀ ρ : Matrix (MIdx n) (MIdx n) ℂ, ρ.PosSemidef → ρ.trace = 1 →
        (∀ ℓ, (partialTrace ℓ ρ).det ≠ 0) →
          (EntropyIneq76 1 θ ρ ↔
            0 ≤ ∑ ℓ, θ ℓ * vnEntropy (partialTrace ℓ (sigmaOf 1 θ ρ)))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part (i)
    intro d n θ η hθ hη hineq n0 T hT hconc k
    obtain ⟨hTk, hconc_k⟩ := Aux74.entropicScalingSeq_ne_zero_and_concise η θ hT hconc k
    obtain ⟨hTk1, _⟩ := Aux74.entropicScalingSeq_ne_zero_and_concise η θ hT hconc (k + 1)
    set Tk := entropicScalingSeq η θ T k
    set Tk1 := entropicScalingSeq η θ T (k + 1)
    have hpos_k : ∀ ℓ, (momentMap Tk ℓ).PosDef := fun ℓ =>
      Aux74.posDef_of_posSemidef_det_ne_zero
        (Aux74.partialTrace_posSemidef ℓ (Aux74.densityOp_posSemidef hTk)) (hconc_k ℓ)
    have hpsd_k : ∀ ℓ, (momentMap Tk ℓ).PosSemidef := fun ℓ => (hpos_k ℓ).posSemidef
    have hpsd_k1 : ∀ ℓ, (momentMap Tk1 ℓ).PosSemidef := fun ℓ =>
      Aux74.partialTrace_posSemidef ℓ (Aux74.densityOp_posSemidef hTk1)
    have hPhi_k : PhiR (phiTheta θ) (momentMap Tk) = -∑ ℓ, θ ℓ * vnEntropy (momentMap Tk ℓ) :=
      Aux74.PhiR_phiTheta_of_posSemidef θ (momentMap Tk) hpsd_k
    have hPhi_k1 : PhiR (phiTheta θ) (momentMap Tk1) = -∑ ℓ, θ ℓ * vnEntropy (momentMap Tk1 ℓ) :=
      Aux74.PhiR_phiTheta_of_posSemidef θ (momentMap Tk1) hpsd_k1
    have htr_grad : ∑ ℓ, (Matrix.trace (momentMap Tk ℓ * hsGrad (phiTheta θ) (momentMap Tk) ℓ)).re =
        -(∑ ℓ, θ ℓ * vnEntropy (momentMap Tk ℓ)) + 1 := by
      have hterm : ∀ ℓ, (Matrix.trace (momentMap Tk ℓ * hsGrad (phiTheta θ) (momentMap Tk) ℓ)).re =
          θ ℓ * (-vnEntropy (momentMap Tk ℓ)) + θ ℓ := by
        intro ℓ
        rw [Aux74.hsGrad_phiTheta_eq θ (momentMap Tk) hpos_k ℓ, Matrix.mul_smul,
          Matrix.trace_smul, smul_eq_mul, mul_add, mul_one, Matrix.trace_add]
        have htr1 : (momentMap Tk ℓ).trace = 1 := by
          unfold momentMap
          rw [Aux74.partialTrace_trace, Aux74.densityOp_trace hTk]
        rw [htr1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.add_re, Complex.one_re,
          ← neg_neg ((momentMap Tk ℓ * cfc Real.log (momentMap Tk ℓ)).trace.re),
          ← Aux74.vnEntropy_eq_neg_trace_mul_log (hpos_k ℓ).isHermitian]
        ring
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, hθ.2]
      congr 1
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun ℓ _ => by ring
    set ρ := densityOp Tk
    have hρ_psd : ρ.PosSemidef := Aux74.densityOp_posSemidef hTk
    have hρ_tr : ρ.trace = 1 := Aux74.densityOp_trace hTk
    have hρ_inv : ∀ ℓ, (partialTrace ℓ ρ).det ≠ 0 := hconc_k
    have h76 := hineq ρ hρ_psd hρ_tr hρ_inv
    unfold EntropyIneq76 at h76
    have hσ_eq : sigmaOf η θ ρ = (((tnorm Tk ^ 2 : ℝ) : ℂ))⁻¹ • Aux74.rawDensity Tk1 := by
      set A : MatTuple n := fun ℓ => cfc (fun x : ℝ => x ^ (-(η * θ ℓ / 2))) (momentMap Tk ℓ)
      have hA_herm : (kron A)ᴴ = kron A := by
        rw [Aux74.kron_conjTranspose]
        congr 1; funext ℓ
        exact (Aux74.isHermitian_cfc (hpos_k ℓ).isHermitian _).eq
      have hTk1_eq : Tk1 = act A Tk := rfl
      rw [hTk1_eq, Aux74.rawDensity_act, hA_herm]
      unfold sigmaOf
      change kron A * densityOp Tk * kron A = _
      rw [Aux74.densityOp_eq_inv_smul_rawDensity, Matrix.mul_smul, Matrix.smul_mul]
    have htr_σ : (sigmaOf η θ ρ).trace = ((tnorm Tk1 ^ 2 / tnorm Tk ^ 2 : ℝ) : ℂ) := by
      rw [hσ_eq, Matrix.trace_smul, Aux74.rawDensity_trace, smul_eq_mul, div_eq_inv_mul]
      push_cast; rfl
    have htr_σ_re : (sigmaOf η θ ρ).trace.re = tnorm Tk1 ^ 2 / tnorm Tk ^ 2 := by
      rw [htr_σ, Complex.ofReal_re]
    have hnorm_k_pos : 0 < tnorm Tk ^ 2 := Aux74.tnorm_sq_pos_of_ne_zero hTk
    have hnorm_k1_pos : 0 < tnorm Tk1 ^ 2 := Aux74.tnorm_sq_pos_of_ne_zero hTk1
    have hmarg_eq : ∀ ℓ, ((sigmaOf η θ ρ).trace)⁻¹ • partialTrace ℓ (sigmaOf η θ ρ) =
        momentMap Tk1 ℓ := by
      intro ℓ
      rw [htr_σ, hσ_eq, Aux74.partialTrace_smul, smul_smul]
      unfold momentMap
      rw [Aux74.densityOp_eq_inv_smul_rawDensity, Aux74.partialTrace_smul]
      congr 1
      have hk_ne : ((tnorm Tk ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hnorm_k_pos
      have hk1_ne : ((tnorm Tk1 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hnorm_k1_pos
      have hdiv_inv : (((tnorm Tk1 ^ 2 / tnorm Tk ^ 2 : ℝ) : ℂ))⁻¹ * (((tnorm Tk ^ 2 : ℝ) : ℂ))⁻¹ =
          (((tnorm Tk1 ^ 2 : ℝ) : ℂ))⁻¹ := by
        rw [Complex.ofReal_div]
        field_simp
      exact hdiv_inv
    simp_rw [hmarg_eq, htr_σ_re] at h76
    have hc_norm : ‖((Real.exp (η / 2) : ℝ) : ℂ)‖ ^ 2 = Real.exp η := by
      rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _)),
        sq, ← Real.exp_add]
      ring_nf
    have hrhs : (1 / η) * Real.log (tnorm Tk1 ^ 2 / (‖((Real.exp (η / 2) : ℝ) : ℂ)‖ ^ 2 * tnorm Tk ^ 2)) =
        (1 / η) * Real.log (tnorm Tk1 ^ 2 / tnorm Tk ^ 2) - 1 := by
      rw [hc_norm]
      have hdiv_eq : tnorm Tk1 ^ 2 / (Real.exp η * tnorm Tk ^ 2) =
          (tnorm Tk1 ^ 2 / tnorm Tk ^ 2) * (Real.exp η)⁻¹ := by field_simp
      rw [hdiv_eq, Real.log_mul (ne_of_gt (div_pos hnorm_k1_pos hnorm_k_pos))
        (inv_ne_zero (ne_of_gt (Real.exp_pos η))), Real.log_inv, Real.log_exp]
      have hη_ne : η ≠ 0 := ne_of_gt hη
      field_simp
      ring
    change PhiR (phiTheta θ) (momentMap Tk) - PhiR (phiTheta θ) (momentMap Tk1) -
        ∑ ℓ, (Matrix.trace (momentMap Tk ℓ * hsGrad (phiTheta θ) (momentMap Tk) ℓ)).re ≥
      (1 / η) * Real.log (tnorm Tk1 ^ 2 / (‖((Real.exp (η / 2) : ℝ) : ℂ)‖ ^ 2 * tnorm Tk ^ 2))
    rw [hPhi_k, hPhi_k1, htr_grad, hrhs]
    have hdiv_ineq : (1 / η) * Real.log (tnorm Tk1 ^ 2 / tnorm Tk ^ 2) ≤
        ∑ ℓ, θ ℓ * vnEntropy (momentMap Tk1 ℓ) := by
      have hm := mul_le_mul_of_nonneg_left h76 (le_of_lt (one_div_pos.mpr hη))
      have hcancel : (1 / η) * (η * ∑ ℓ, θ ℓ * vnEntropy (momentMap Tk1 ℓ)) =
          ∑ ℓ, θ ℓ * vnEntropy (momentMap Tk1 ℓ) := by
        have hη_ne : η ≠ 0 := ne_of_gt hη
        field_simp
      linarith
    linarith
  · -- Part (ii): η = 1 implies η ∈ (0, 1]
    intro h1 d n θ η hθ hη_pos hη_le1 ρ hρ_psd hρ_tr hρ_inv
    have hθ' : IsProbVec (Aux74.extProb η θ) := by
      refine ⟨?_, ?_⟩
      · intro k
        refine Fin.cases ?_ ?_ k
        · simp [Aux74.extProb]; linarith
        · intro ℓ; simp [Aux74.extProb]; exact mul_nonneg (le_of_lt hη_pos) (hθ.1 ℓ)
      · rw [Fin.sum_univ_succ]
        simp only [Aux74.extProb, Fin.cases_zero, Fin.cases_succ, ← Finset.mul_sum, hθ.2, mul_one]
        ring
    let e := Aux74.extEquiv n
    let ρ' : Matrix (MIdx (Aux74.extShape n)) (MIdx (Aux74.extShape n)) ℂ :=
      fun j₁ j₂ => ρ (e j₁) (e j₂)
    have hρ'_psd : ρ'.PosSemidef := by
      have hHerm : ρ'.IsHermitian := by
        ext j₁ j₂
        have h := congrFun (congrFun hρ_psd.isHermitian (e j₁)) (e j₂)
        rw [Matrix.conjTranspose_apply] at h
        exact h
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun v => ?_
      have hquad : star v ⬝ᵥ ρ' *ᵥ v = star (v ∘ e.symm) ⬝ᵥ ρ *ᵥ (v ∘ e.symm) := by
        simp only [dotProduct, Matrix.mulVec, ρ', Function.comp_apply]
        rw [← Equiv.sum_comp e.symm]
        refine Finset.sum_congr rfl fun j₁ _ => ?_
        simp only [Pi.star_apply, Equiv.apply_symm_apply]
        congr 1
        rw [← Equiv.sum_comp e.symm]
        refine Finset.sum_congr rfl fun j₂ _ => by simp [Equiv.apply_symm_apply]
      rw [hquad]
      exact hρ_psd.dotProduct_mulVec_nonneg _
    have hρ'_tr : ρ'.trace = 1 := by
      have htr_eq : ρ'.trace = ρ.trace := by
        simp only [Matrix.trace, Matrix.diag, ρ']
        exact Equiv.sum_comp e fun j => ρ j j
      rw [htr_eq, hρ_tr]
    have hpt0 : ∀ M : Matrix (MIdx n) (MIdx n) ℂ,
        partialTrace (0 : Fin (d + 1))
          (fun j₁ j₂ : MIdx (Aux74.extShape n) => M (e j₁) (e j₂)) =
          M.trace • (1 : Matrix (Fin (Aux74.extShape n 0)) (Fin (Aux74.extShape n 0)) ℂ) := by
      intro M
      ext a b
      have hab : a = b := Aux74.extShape_zero_eq a b
      subst hab
      simp only [partialTrace, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      have hja : ∀ j' : MIdx (Aux74.extShape n), j' 0 = a := fun j' => Aux74.extShape_zero_eq _ _
      have hupd : ∀ j' : MIdx (Aux74.extShape n), e (Function.update j' 0 a) = e j' := by
        intro j'
        funext ℓ
        change Function.update j' 0 a ℓ.succ = j' ℓ.succ
        rw [Function.update_of_ne (Fin.succ_ne_zero ℓ)]
      simp_rw [hja, if_true, hupd]
      exact Equiv.sum_comp e fun j => M j j
    have hpt_succ : ∀ (M : Matrix (MIdx n) (MIdx n) ℂ) (ℓ : Fin d),
        partialTrace ℓ.succ (fun j₁ j₂ : MIdx (Aux74.extShape n) => M (e j₁) (e j₂)) =
          partialTrace ℓ M := by
      intro M ℓ
      ext a b
      let a' : Fin (n ℓ) := a
      let b' : Fin (n ℓ) := b
      change (∑ j' : MIdx (Aux74.extShape n),
          if j' ℓ.succ = a then M (e j') (e (Function.update j' ℓ.succ b)) else 0) =
        ∑ j : MIdx n, if j ℓ = a' then M j (Function.update j ℓ b') else 0
      rw [← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun j' _ => ?_
      have he_eq : (e j') ℓ = j' ℓ.succ := rfl
      have he_upd : e (Function.update j' ℓ.succ b) = Function.update (e j') ℓ b' := by
        funext m
        change Function.update j' ℓ.succ b m.succ = Function.update (e j') ℓ b' m
        by_cases hm : m = ℓ
        · subst hm
          rw [Function.update_self, Function.update_self]
        · have hne : m.succ ≠ ℓ.succ := mt Fin.succ_inj.mp hm
          rw [Function.update_of_ne hne, Function.update_of_ne hm]
          rfl
      rw [he_upd]
      rfl
    have hρ'_inv : ∀ k : Fin (d + 1), (partialTrace k ρ').det ≠ 0 := by
      intro k
      refine Fin.cases ?_ ?_ k
      · rw [hpt0 ρ, hρ_tr, one_smul, Matrix.det_one]
        exact one_ne_zero
      · intro ℓ
        rw [hpt_succ ρ ℓ]
        exact hρ_inv ℓ
    have h76' := h1 (d + 1) (Aux74.extShape n) (Aux74.extProb η θ) hθ' ρ' hρ'_psd hρ'_tr hρ'_inv
    have hc0 : cfc (fun x : ℝ => x ^ (-(1 * Aux74.extProb η θ 0 / 2))) (partialTrace 0 ρ') = 1 := by
      rw [hpt0 ρ, hρ_tr, one_smul]
      exact Aux74.cfc_rpow_one_mat _
    have hkron_eq : kron (fun k : Fin (d + 1) =>
        cfc (fun x : ℝ => x ^ (-(1 * Aux74.extProb η θ k / 2))) (partialTrace k ρ')) =
        fun j₁ j₂ : MIdx (Aux74.extShape n) =>
          kron (fun ℓ : Fin d => cfc (fun x : ℝ => x ^ (-(η * θ ℓ / 2))) (partialTrace ℓ ρ))
            (e j₁) (e j₂) := by
      ext j₁ j₂
      simp only [kron, Fin.prod_univ_succ]
      have hj0 : j₁ 0 = j₂ 0 := Aux74.extShape_zero_eq _ _
      rw [hc0, hj0, Matrix.one_apply_eq, one_mul]
      refine Finset.prod_congr rfl fun ℓ _ => ?_
      change cfc (fun x : ℝ => x ^ (-(1 * (η * θ ℓ) / 2))) (partialTrace ℓ.succ ρ') (j₁ ℓ.succ) (j₂ ℓ.succ) = _
      rw [one_mul, hpt_succ ρ ℓ]
      rfl
    have hσ'_eq : sigmaOf 1 (Aux74.extProb η θ) ρ' = fun j₁ j₂ => sigmaOf η θ ρ (e j₁) (e j₂) := by
      unfold sigmaOf
      rw [hkron_eq]
      ext j₁ j₂
      simp only [Matrix.mul_apply, ρ']
      rw [← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun k₂ _ => ?_
      congr 1
      rw [← Equiv.sum_comp e]
      rfl
    have htr_σ' : (sigmaOf 1 (Aux74.extProb η θ) ρ').trace = (sigmaOf η θ ρ).trace := by
      rw [hσ'_eq]
      simp only [Matrix.trace, Matrix.diag]
      exact Equiv.sum_comp e fun j => sigmaOf η θ ρ j j
    obtain ⟨_, htr_σ_pos, _⟩ := Aux74.sigmaOf_posSemidef_and_trace_pos η θ hρ_psd hρ_tr hρ_inv
    have htr_σ_ne : (sigmaOf η θ ρ).trace ≠ 0 := by
      intro h0
      rw [h0] at htr_σ_pos
      exact lt_irrefl 0 htr_σ_pos
    unfold EntropyIneq76 at h76' ⊢
    rw [one_mul, htr_σ', Fin.sum_univ_succ] at h76'
    have h0_vn : vnEntropy (((sigmaOf η θ ρ).trace)⁻¹ •
        partialTrace 0 (sigmaOf 1 (Aux74.extProb η θ) ρ')) = 0 := by
      have hptσ0 : partialTrace (0 : Fin (d + 1)) (sigmaOf 1 (Aux74.extProb η θ) ρ') =
          (sigmaOf η θ ρ).trace • (1 : Matrix (Fin (Aux74.extShape n 0)) (Fin (Aux74.extShape n 0)) ℂ) := by
        rw [hσ'_eq]
        exact hpt0 (sigmaOf η θ ρ)
      rw [hptσ0, smul_smul, inv_mul_cancel₀ htr_σ_ne, one_smul]
      exact Aux74.vnEntropy_one_mat
    have hsucc_pt : ∀ ℓ : Fin d, partialTrace ℓ.succ (sigmaOf 1 (Aux74.extProb η θ) ρ') =
        partialTrace ℓ (sigmaOf η θ ρ) := by
      intro ℓ
      rw [hσ'_eq]
      exact hpt_succ (sigmaOf η θ ρ) ℓ
    simp_rw [h0_vn, mul_zero, zero_add, hsucc_pt] at h76'
    simp only [Aux74.extProb, Fin.cases_succ, mul_assoc, ← Finset.mul_sum] at h76'
    exact h76'
  · -- Part (iii): Equivalence at η = 1
    intro d n θ hθ ρ hρ_psd hρ_tr hρ_inv
    obtain ⟨hσ_psd, htr_pos, htr_im⟩ := Aux74.sigmaOf_posSemidef_and_trace_pos 1 θ hρ_psd hρ_tr hρ_inv
    set s : ℝ := (sigmaOf 1 θ ρ).trace.re
    have htr_eq_s : (sigmaOf 1 θ ρ).trace = (s : ℂ) := by
      apply Complex.ext <;> simp [s, htr_im]
    have hinv_eq : ((sigmaOf 1 θ ρ).trace)⁻¹ = ((s⁻¹ : ℝ) : ℂ) := by
      rw [htr_eq_s]; push_cast; rfl
    have hterm : ∀ ℓ : Fin d,
        vnEntropy (((sigmaOf 1 θ ρ).trace)⁻¹ • partialTrace ℓ (sigmaOf 1 θ ρ)) =
          s⁻¹ * vnEntropy (partialTrace ℓ (sigmaOf 1 θ ρ)) + Real.log s := by
      intro ℓ
      have hσℓ_herm := (Aux74.partialTrace_posSemidef ℓ hσ_psd).isHermitian
      have hσℓ_tr : (partialTrace ℓ (sigmaOf 1 θ ρ)).trace.re = s := by
        rw [Aux74.partialTrace_trace]
      rw [hinv_eq, Aux74.vnEntropy_smul_pos hσℓ_herm (inv_pos.mpr htr_pos),
        hσℓ_tr, Real.log_inv, mul_neg, sub_neg_eq_add, inv_mul_cancel₀ (ne_of_gt htr_pos), one_mul]
    unfold EntropyIneq76
    simp_rw [one_mul, hterm, mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hθ.2, one_mul]
    have hsum_pull : ∑ ℓ : Fin d, θ ℓ * (s⁻¹ * vnEntropy (partialTrace ℓ (sigmaOf 1 θ ρ))) =
        s⁻¹ * ∑ ℓ : Fin d, θ ℓ * vnEntropy (partialTrace ℓ (sigmaOf 1 θ ρ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => by ring
    rw [hsum_pull]
    change s⁻¹ * (∑ ℓ : Fin d, θ ℓ * vnEntropy (partialTrace ℓ (sigmaOf 1 θ ρ))) + Real.log s ≥
        Real.log s ↔ _
    constructor
    · intro h
      have h1 : 0 ≤ s⁻¹ * ∑ ℓ : Fin d, θ ℓ * vnEntropy (partialTrace ℓ (sigmaOf 1 θ ρ)) := by
        linarith
      exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr htr_pos)).mp h1
    · intro h
      have h1 : 0 ≤ s⁻¹ * ∑ ℓ : Fin d, θ ℓ * vnEntropy (partialTrace ℓ (sigmaOf 1 θ ρ)) :=
        mul_nonneg (inv_nonneg.mpr (le_of_lt htr_pos)) h
      linarith
