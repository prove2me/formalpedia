-- Prove2me | solution 1 for MomentPolytopes.QuantumFunctionals.theorem_7_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T05:01:35.200046+00:00
-- url     : https://prove2.me/submissions/9eb09809-b7dc-421b-b658-9a53c9c1520e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntanglementPolytope
import Definitions.Def_MomentPolytopes_QuantumFunctionals_QuantumFunctional
import Definitions.Def_MomentPolytopes_QuantumFunctionals_MirrorDescent
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntropicScaling
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Capacity
import Definitions.Def_MomentPolytopes_QuantumFunctionals_GaussianInteger
import Theorems.Thm_MomentPolytopes_QuantumFunctionals_theorem_7_5
import Theorems.Thm_MomentPolytopes_QuantumFunctionals_theorem_6_27
import Theorems.Thm_MomentPolytopes_QuantumFunctionals_theorem_6_28

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


/-! ### 6. Additional helpers for Theorem 7.6 -/

lemma spec_pos_of_posDef {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosDef) (i : Fin m) : 0 < spec A i := by
  unfold spec
  rw [dif_pos hA.isHermitian]
  let e2 : Fin m ≃ Fin (Fintype.card (Fin m)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin m)))).symm
  let k := Fin.cast (Fintype.card_fin m).symm i
  have hk : hA.isHermitian.eigenvalues₀ k = hA.isHermitian.eigenvalues (e2.symm k) := by
    simp [Matrix.IsHermitian.eigenvalues, e2]
  rw [hk]
  exact hA.eigenvalues_pos (e2.symm k)

lemma cfc_unitary_diag_of_continuous {m : ℕ} {B U : Matrix (Fin m) (Fin m) ℂ}
    (hB : B.IsHermitian) (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (μ : Fin m → ℝ)
    (hBU : B = U * Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ)) * Uᴴ)
    {g : ℝ → ℝ} (hg : Continuous g) :
    cfc g B = U * Matrix.diagonal (fun i => ((g (μ i) : ℝ) : ℂ)) * Uᴴ := by
  ext a b
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · exact Fin.elim0 a
  apply eq_of_forall_dist_le
  intro ε hε
  rw [dist_eq_norm]
  set fsum : Fin m → ℝ := fun j => |hB.eigenvalues j| + |μ j|
  set M : ℝ := 1 + ∑ j : Fin m, fsum j
  have heig_mem : ∀ i : Fin m, hB.eigenvalues i ∈ Set.Icc (-M) M := by
    intro i
    have h1 : |hB.eigenvalues i| ≤ fsum i := le_add_of_nonneg_right (abs_nonneg _)
    have h2 : fsum i ≤ ∑ j : Fin m, fsum j :=
      Finset.single_le_sum (f := fsum) (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ i)
    exact abs_le.mp (by linarith)
  have hμ_mem : ∀ i : Fin m, μ i ∈ Set.Icc (-M) M := by
    intro i
    have h1 : |μ i| ≤ fsum i := le_add_of_nonneg_left (abs_nonneg _)
    have h2 : fsum i ≤ ∑ j : Fin m, fsum j :=
      Finset.single_le_sum (f := fsum) (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ i)
    exact abs_le.mp (by linarith)
  have hm_sqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm_pos)
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-M) M g hg.continuousOn
    (ε / (2 * Real.sqrt (m : ℝ))) (by positivity)
  set polyP : Matrix (Fin m) (Fin m) ℂ := ∑ k ∈ P.support, ((P.coeff k : ℝ) : ℂ) • B ^ k
  have h1 : ‖cfc g B a b - polyP a b‖ ≤ ε / 2 := by
    calc
      ‖(cfc g B - polyP) a b‖ ≤ frobNorm (cfc g B - polyP) := norm_entry_le_frobNorm _ a b
      _ = Real.sqrt (∑ i : Fin m, (g (hB.eigenvalues i) - P.eval (hB.eigenvalues i)) ^ 2) :=
        frobNorm_cfc_sub_poly hB g P
      _ ≤ Real.sqrt (∑ _i : Fin m, (ε / (2 * Real.sqrt (m : ℝ))) ^ 2) := by
        apply Real.sqrt_le_sqrt
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sq_abs (g (hB.eigenvalues i) - P.eval (hB.eigenvalues i)), abs_sub_comm, sq, sq]
        exact mul_self_le_mul_self (abs_nonneg _) (le_of_lt (hP _ (heig_mem i)))
      _ = ε / 2 := by
        have hsqn : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
        have hsum : ∑ _i : Fin m, (ε / (2 * Real.sqrt (m : ℝ))) ^ 2 = (ε / 2) ^ 2 := by
          simp [Finset.sum_const]
          field_simp
          rw [hsqn]
        rw [hsum, Real.sqrt_sq (by positivity)]
  have hpolyU : polyP = U * Matrix.diagonal (fun i => ((P.eval (μ i) : ℝ) : ℂ)) * Uᴴ := by
    have hBk : ∀ k : ℕ, ((P.coeff k : ℝ) : ℂ) • B ^ k =
        U * (((P.coeff k : ℝ) : ℂ) • Matrix.diagonal (fun i => (((μ i ^ k : ℝ)) : ℂ))) * Uᴴ := by
      intro k
      have hk0 : B ^ k = U * Matrix.diagonal (fun i => (((μ i ^ k : ℝ)) : ℂ)) * Uᴴ := by
        conv_lhs => rw [hBU]
        simpa using unitary_diag_pow U hU1 hU2 (fun i => ((μ i : ℝ) : ℂ)) k
      rw [hk0, Matrix.mul_smul, Matrix.smul_mul]
    dsimp only [polyP]
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
  set D' := Matrix.diagonal (fun i => (((P.eval (μ i) - g (μ i)) : ℝ) : ℂ))
  have hdiffU : polyP - U * Matrix.diagonal (fun i => ((g (μ i) : ℝ) : ℂ)) * Uᴴ = U * D' * Uᴴ := by
    rw [hpolyU, ← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst hij; simp [D']
    · simp [D', hij]
  have h2 : ‖polyP a b - (U * Matrix.diagonal (fun i => ((g (μ i) : ℝ) : ℂ)) * Uᴴ) a b‖ ≤
      ε / 2 := by
    have hfrobU : frobNorm (U * D' * Uᴴ) =
        Real.sqrt (∑ i : Fin m, (P.eval (μ i) - g (μ i)) ^ 2) := by
      unfold frobNorm
      congr 1
      rw [frobNorm_sq_eq_trace_conjTranspose_mul]
      have hD_herm : D'ᴴ = D' := by
        ext i j; by_cases hij : i = j
        · subst hij; simp [D']
        · simp [D', hij, Ne.symm hij]
      have hprod : (U * D' * Uᴴ)ᴴ * (U * D' * Uᴴ) = U * (D' * D') * Uᴴ := by
        calc
          (U * D' * Uᴴ)ᴴ * (U * D' * Uᴴ) = U * (D' * ((Uᴴ * U) * (D' * Uᴴ))) := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD_herm,
              Matrix.mul_assoc]
          _ = U * (D' * (D' * Uᴴ)) := by rw [hU1, one_mul]
          _ = U * (D' * D') * Uᴴ := by simp only [Matrix.mul_assoc]
      rw [hprod, Matrix.trace_mul_cycle, hU1, one_mul]
      simp [D', Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum, sq]
    calc
      ‖(polyP - U * Matrix.diagonal (fun i => ((g (μ i) : ℝ) : ℂ)) * Uᴴ) a b‖
          ≤ frobNorm (polyP - U * Matrix.diagonal (fun i => ((g (μ i) : ℝ) : ℂ)) * Uᴴ) :=
        norm_entry_le_frobNorm _ a b
      _ = Real.sqrt (∑ i : Fin m, (P.eval (μ i) - g (μ i)) ^ 2) := by rw [hdiffU, hfrobU]
      _ ≤ Real.sqrt (∑ _i : Fin m, (ε / (2 * Real.sqrt (m : ℝ))) ^ 2) := by
        apply Real.sqrt_le_sqrt
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sq_abs (P.eval (μ i) - g (μ i)), sq, sq]
        exact mul_self_le_mul_self (abs_nonneg _) (le_of_lt (hP _ (hμ_mem i)))
      _ = ε / 2 := by
        have hsqn : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
        have hsum : ∑ _i : Fin m, (ε / (2 * Real.sqrt (m : ℝ))) ^ 2 = (ε / 2) ^ 2 := by
          simp [Finset.sum_const]
          field_simp
          rw [hsqn]
        rw [hsum, Real.sqrt_sq (by positivity)]
  calc
    ‖cfc g B a b - (U * Matrix.diagonal (fun i => ((g (μ i) : ℝ) : ℂ)) * Uᴴ) a b‖
        = ‖(cfc g B a b - polyP a b) +
            (polyP a b - (U * Matrix.diagonal (fun i => ((g (μ i) : ℝ) : ℂ)) * Uᴴ) a b)‖ := by
          ring_nf
    _ ≤ ‖cfc g B a b - polyP a b‖ +
          ‖polyP a b - (U * Matrix.diagonal (fun i => ((g (μ i) : ℝ) : ℂ)) * Uᴴ) a b‖ :=
      norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := add_halves ε

lemma hermExp_hsGrad_phiTheta {d : ℕ} {n : Fin d → ℕ} (θ : Fin d → ℝ)
    (X : MatTuple n) (hX : ∀ ℓ, (X ℓ).PosDef) (ℓ : Fin d) :
    hermExp (-(1 / 2)) (hsGrad (phiTheta θ) X ℓ) =
      ((Real.exp (-(1 / 2) * θ ℓ) : ℝ) : ℂ) •
        cfc (fun x : ℝ => x ^ (-(1 * θ ℓ / 2))) (X ℓ) := by
  have hAh := (hX ℓ).isHermitian
  set U : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ :=
    (hAh.eigenvectorUnitary : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ)
  have hU1 : Uᴴ * U = 1 := Unitary.coe_star_mul_self hAh.eigenvectorUnitary
  have hU2 : U * Uᴴ = 1 := Unitary.coe_mul_star_self hAh.eigenvectorUnitary
  set μ : Fin (n ℓ) → ℝ := fun i => θ ℓ * (Real.log (hAh.eigenvalues i) + 1)
  have hgradU : hsGrad (phiTheta θ) X ℓ =
      U * Matrix.diagonal (fun i => ((μ i : ℝ) : ℂ)) * Uᴴ := by
    rw [hsGrad_phiTheta_eq θ X hX ℓ, cfc_eq_unitary_diag hAh Real.log]
    have h1 : (1 : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ) =
        U * Matrix.diagonal (fun _ => (1 : ℂ)) * Uᴴ := by
      simp [Matrix.diagonal_one, hU2]
    conv_lhs =>
      arg 2; arg 2
      rw [h1]
    rw [← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.diagonal_apply_eq, smul_eq_mul, μ]
      push_cast
      ring
    · simp [hij]
  have hB_herm : (hsGrad (phiTheta θ) X ℓ).IsHermitian := by
    rw [hgradU]
    exact isHermitian_unitary_diag U μ
  unfold hermExp
  have hg_cont : Continuous (fun s : ℝ => Real.exp (-(1 / 2) * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  rw [cfc_unitary_diag_of_continuous hB_herm hU1 hU2 μ hgradU hg_cont,
    cfc_eq_unitary_diag hAh (fun x : ℝ => x ^ (-(1 * θ ℓ / 2))),
    ← Matrix.smul_mul, ← Matrix.mul_smul]
  congr 2
  ext i j
  by_cases hij : i = j
  · subst hij
    have hpos_i : 0 < hAh.eigenvalues i := (hX ℓ).eigenvalues_pos i
    have hexp_eq : Real.exp (-(1 / 2) * μ i) =
        Real.exp (-(1 / 2) * θ ℓ) * (hAh.eigenvalues i) ^ (-(1 * θ ℓ / 2)) := by
      have harg : -(1 / 2) * μ i =
          -(1 / 2) * θ ℓ + Real.log (hAh.eigenvalues i) * (-(1 * θ ℓ / 2)) := by
        dsimp only [μ]
        ring
      rw [harg, Real.exp_add, ← Real.rpow_def_of_pos hpos_i]
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
    rw [hexp_eq]
    push_cast
    rfl
  · simp [hij]

noncomputable def mdScalars : ℕ → ℂ
  | 0 => 1
  | _ + 1 => ((Real.exp (1 / 2) : ℝ) : ℂ)

lemma mdScalars_ne_zero (k : ℕ) : mdScalars k ≠ 0 := by
  cases k with
  | zero => exact one_ne_zero
  | succ _ =>
    dsimp [mdScalars]
    exact_mod_cast ne_of_gt (Real.exp_pos _)

lemma mirrorDescentSeq_eq_entropicScalingSeq {d n0 : ℕ} {n : Fin d → ℕ}
    {θ : Fin d → ℝ} (hθ : IsProbVec θ) {T : Ten d n0 n} (hT : T ≠ 0) (hconc : IsConcise T) :
    ∀ k : ℕ, mirrorDescentSeq (phiTheta θ) 1 mdScalars T k = entropicScalingSeq 1 θ T k := by
  intro k
  induction k with
  | zero =>
    simp [mirrorDescentSeq, entropicScalingSeq, mdScalars]
  | succ k ih =>
    simp only [mirrorDescentSeq, entropicScalingSeq, ih, mdScalars]
    obtain ⟨hTk, hconc_k⟩ := entropicScalingSeq_ne_zero_and_concise 1 θ hT hconc k
    set Tk := entropicScalingSeq 1 θ T k
    have hpos_k : ∀ ℓ, (momentMap Tk ℓ).PosDef := fun ℓ =>
      posDef_of_posSemidef_det_ne_zero
        (partialTrace_posSemidef ℓ (densityOp_posSemidef hTk)) (hconc_k ℓ)
    have hgrad_exp : (fun ℓ => hermExp (-(1 / 2)) (hsGrad (phiTheta θ) (momentMap Tk) ℓ)) =
        fun ℓ => ((Real.exp (-(1 / 2) * θ ℓ) : ℝ) : ℂ) •
          cfc (fun x : ℝ => x ^ (-(1 * θ ℓ / 2))) (momentMap Tk ℓ) := by
      funext ℓ
      exact hermExp_hsGrad_phiTheta θ (momentMap Tk) hpos_k ℓ
    rw [hgrad_exp]
    ext ⟨i₀, j⟩
    simp only [Pi.smul_apply, act, kron, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
      Finset.mul_sum]
    have hprod_exp : ∏ ℓ : Fin d, ((Real.exp (-(1 / 2) * θ ℓ) : ℝ) : ℂ) =
        ((Real.exp (-(1 / 2)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum, hθ.2, mul_one]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [hprod_exp]
    have hcancel : ((Real.exp (1 / 2) : ℝ) : ℂ) * ((Real.exp (-(1 / 2)) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
    calc
      ((Real.exp (1 / 2) : ℝ) : ℂ) *
          ((((Real.exp (-(1 / 2)) : ℝ) : ℂ) *
            ∏ x : Fin d, cfc (fun x_1 : ℝ => x_1 ^ (-(1 * θ x / 2))) (momentMap Tk x) (j x) (j' x)) *
            Tk (i₀, j'))
          = (((Real.exp (1 / 2) : ℝ) : ℂ) * ((Real.exp (-(1 / 2)) : ℝ) : ℂ)) *
              ((∏ x : Fin d, cfc (fun x_1 : ℝ => x_1 ^ (-(1 * θ x / 2))) (momentMap Tk x) (j x) (j' x)) *
                Tk (i₀, j')) := by ring
      _ = (∏ x : Fin d, cfc (fun x_1 : ℝ => x_1 ^ (-(1 * θ x / 2))) (momentMap Tk x) (j x) (j' x)) *
            Tk (i₀, j') := by rw [hcancel, one_mul]

lemma entropicScalingSeq_in_orbit {d n0 : ℕ} {n : Fin d → ℕ}
    (η : ℝ) (θ : Fin d → ℝ) {T : Ten d n0 n} (hT : T ≠ 0) (hconc : IsConcise T) :
    ∀ k : ℕ, ∃ g : GTuple n, entropicScalingSeq η θ T k = gact g T := by
  intro k
  induction k with
  | zero =>
    refine ⟨1, ?_⟩
    unfold entropicScalingSeq gact
    exact (act_one T).symm
  | succ k ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨hTk, hconc_k⟩ := entropicScalingSeq_ne_zero_and_concise η θ hT hconc k
    set Tk := entropicScalingSeq η θ T k
    set A : MatTuple n := fun ℓ => cfc (fun x : ℝ => x ^ (-(η * θ ℓ / 2))) (momentMap Tk ℓ)
    have hunit : ∀ ℓ, IsUnit (A ℓ) := by
      intro ℓ
      have hpos := posDef_of_posSemidef_det_ne_zero
        (partialTrace_posSemidef ℓ (densityOp_posSemidef hTk)) (hconc_k ℓ)
      have hdet := posDef_det_ne_zero (posDef_cfc_of_pos hpos.isHermitian
        (fun x : ℝ => x ^ (-(η * θ ℓ / 2))) fun i =>
        Real.rpow_pos_of_pos (hpos.eigenvalues_pos i) _)
      exact (Matrix.isUnit_iff_isUnit_det (A ℓ)).mpr (Ne.isUnit hdet)
    refine ⟨fun ℓ => (hunit ℓ).unit * g ℓ, ?_⟩
    simp only [entropicScalingSeq, gact]
    change act A Tk = _
    rw [hg]
    unfold gact
    rw [act_act]
    congr 1

lemma neg_negMulLog_convex_comb {x y a b : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    -Real.negMulLog (a * x + b * y) ≤ a * (-Real.negMulLog x) + b * (-Real.negMulLog y) := by
  simp only [Real.negMulLog]
  rcases eq_or_lt_of_le (mul_nonneg ha hx) with hax0 | hax_pos
  · rcases mul_eq_zero.mp hax0.symm with rfl | rfl
    · have hb1 : b = 1 := by linarith
      subst hb1; simp
    · simp only [mul_zero, zero_add]
      rcases eq_or_lt_of_le (mul_nonneg hb hy) with hby0 | hby_pos
      · rw [← hby0]
        rcases mul_eq_zero.mp hby0.symm with rfl | rfl <;> simp
      · have hb_pos : 0 < b := pos_of_mul_pos_left hby_pos hy
        have hy_pos : 0 < y := pos_of_mul_pos_right hby_pos hb
        have hb_le1 : b ≤ 1 := by linarith
        have hlogb : Real.log b ≤ 0 := Real.log_nonpos (le_of_lt hb_pos) hb_le1
        rw [Real.log_mul (ne_of_gt hb_pos) (ne_of_gt hy_pos)]
        nlinarith
  · rcases eq_or_lt_of_le (mul_nonneg hb hy) with hby0 | hby_pos
    · rcases mul_eq_zero.mp hby0.symm with rfl | rfl
      · have ha1 : a = 1 := by linarith
        subst ha1; simp
      · simp only [mul_zero, add_zero]
        have ha_pos : 0 < a := pos_of_mul_pos_left hax_pos hx
        have hx_pos : 0 < x := pos_of_mul_pos_right hax_pos ha
        have ha_le1 : a ≤ 1 := by linarith
        have hloga : Real.log a ≤ 0 := Real.log_nonpos (le_of_lt ha_pos) ha_le1
        rw [Real.log_mul (ne_of_gt ha_pos) (ne_of_gt hx_pos)]
        nlinarith
    · have hx_pos : 0 < x := pos_of_mul_pos_right hax_pos ha
      have hy_pos : 0 < y := pos_of_mul_pos_right hby_pos hb
      set s : ℝ := a * x + b * y
      have hs_pos : 0 < s := by dsimp only [s]; linarith
      have h1 := Real.log_le_sub_one_of_pos (div_pos hs_pos hx_pos)
      rw [Real.log_div (ne_of_gt hs_pos) (ne_of_gt hx_pos)] at h1
      have h2 := Real.log_le_sub_one_of_pos (div_pos hs_pos hy_pos)
      rw [Real.log_div (ne_of_gt hs_pos) (ne_of_gt hy_pos)] at h2
      have hm1 := mul_le_mul_of_nonneg_left h1 (le_of_lt hax_pos)
      have hm2 := mul_le_mul_of_nonneg_left h2 (le_of_lt hby_pos)
      have hd1 : a * x * (s / x - 1) = a * s - a * x := by field_simp
      have hd2 : b * y * (s / y - 1) = b * s - b * y := by field_simp
      rw [hd1] at hm1
      rw [hd2] at hm2
      have hsum_ab : a * s + b * s = s := by nlinarith
      have hdef_s : a * x + b * y = s := rfl
      nlinarith

lemma effDom_phiTheta {d : ℕ} {n : Fin d → ℕ} (θ : Fin d → ℝ) :
    effDom (phiTheta θ) = {p : SpecTuple n | ∀ ℓ i, 0 ≤ p ℓ i} := by
  ext p
  change (phiTheta θ p < ⊤) ↔ ∀ ℓ i, 0 ≤ p ℓ i
  unfold phiTheta
  by_cases h : ∀ ℓ i, 0 ≤ p ℓ i
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => EReal.coe_lt_top _⟩
  · rw [if_neg h]
    simp [h]

lemma interior_effDom_phiTheta {d : ℕ} {n : Fin d → ℕ} (θ : Fin d → ℝ) :
    interior (effDom (phiTheta θ)) = {p : SpecTuple n | ∀ ℓ i, 0 < p ℓ i} := by
  rw [effDom_phiTheta]
  set S_nn : Set (SpecTuple n) := {p | ∀ ℓ i, 0 ≤ p ℓ i}
  set S_pos : Set (SpecTuple n) := {p | ∀ ℓ i, 0 < p ℓ i}
  have hopen : IsOpen S_pos := by
    have heq : S_pos = ⋂ ℓ : Fin d, ⋂ i : Fin (n ℓ), (fun p : SpecTuple n => p ℓ i) ⁻¹' Set.Ioi 0 := by
      ext p; simp [S_pos]
    rw [heq]
    exact isOpen_iInter_of_finite fun ℓ => isOpen_iInter_of_finite fun i =>
      isOpen_Ioi.preimage ((continuous_apply i).comp (continuous_apply ℓ))
  apply Set.Subset.antisymm
  · intro p hp ℓ i
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
    set q : SpecTuple n := Function.update p ℓ (Function.update (p ℓ) i (p ℓ i - ε / 2))
    have hq_mem : q ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro m
      rw [dist_pi_lt_iff hε]
      intro j
      by_cases hm : m = ℓ
      · subst hm
        by_cases hj : j = i
        · subst hj
          simp only [q, Function.update_self, Real.dist_eq]
          rw [show p m j - ε / 2 - p m j = -(ε / 2) by ring, abs_neg, abs_of_pos (half_pos hε)]
          linarith
        · simp [q, hj, hε]
      · simp [q, hm, hε]
    have hq_nn := hball hq_mem ℓ i
    simp only [q, Function.update_self] at hq_nn
    linarith
  · exact interior_maximal (fun p hp ℓ i => le_of_lt (hp ℓ i)) hopen

lemma isAdmissibleObjective_phiTheta {d : ℕ} {n : Fin d → ℕ} {θ : Fin d → ℝ}
    (hθ : IsProbVec θ) : IsAdmissibleObjective (phiTheta θ (n := n)) := by
  set S_nn : Set (SpecTuple n) := {p | ∀ ℓ i, 0 ≤ p ℓ i}
  set F : SpecTuple n → ℝ := fun p => -∑ ℓ, θ ℓ * shannonEntropy (p ℓ)
  have hS_closed : IsClosed S_nn := by
    have heq : S_nn = ⋂ ℓ : Fin d, ⋂ i : Fin (n ℓ), (fun p : SpecTuple n => p ℓ i) ⁻¹' Set.Ici 0 := by
      ext p; simp [S_nn]
    rw [heq]
    exact isClosed_iInter fun ℓ => isClosed_iInter fun i =>
      isClosed_Ici.preimage ((continuous_apply i).comp (continuous_apply ℓ))
  have hF_cont : Continuous F := by
    refine Continuous.neg (continuous_finsetSum _ fun ℓ _ => continuous_const.mul ?_)
    exact continuous_finsetSum _ fun i _ =>
      Real.continuous_negMulLog.comp ((continuous_apply i).comp (continuous_apply ℓ))
  refine
    { ne_bot := ?_
      lowerSemicontinuous := ?_
      convex_epigraph := ?_
      symmetric := ?_
      interior_nonempty := ?_
      differentiableOn := ?_ }
  · intro p
    unfold phiTheta
    split_ifs <;> simp
  · rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    induction y using EReal.rec with
    | bot =>
      have hemp : (phiTheta θ ⁻¹' Set.Iic (⊥ : EReal)) = (∅ : Set (SpecTuple n)) := by
        ext p
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, phiTheta]
        split_ifs <;> simp
      rw [hemp]
      exact isClosed_empty
    | top =>
      have huniv : (phiTheta (n := n) θ ⁻¹' Set.Iic (⊤ : EReal)) =
          (Set.univ : Set (SpecTuple n)) := by
        ext p; simp
      rw [huniv]
      exact isClosed_univ
    | coe r =>
      have heq : (phiTheta (n := n) θ ⁻¹' Set.Iic (r : EReal)) = S_nn ∩ {p | F p ≤ r} := by
        ext p
        change (phiTheta θ p ≤ (r : EReal)) ↔ (∀ ℓ i, 0 ≤ p ℓ i) ∧ F p ≤ r
        unfold phiTheta
        by_cases h : ∀ ℓ i, 0 ≤ p ℓ i
        · rw [if_pos h, EReal.coe_le_coe_iff]
          exact ⟨fun hr => ⟨h, hr⟩, fun ⟨_, hr⟩ => hr⟩
        · rw [if_neg h]
          exact ⟨fun htop => absurd htop (not_le_of_gt (EReal.coe_lt_top r)),
            fun ⟨h', _⟩ => absurd h' h⟩
      rw [heq]
      exact hS_closed.inter (isClosed_le hF_cont continuous_const)
  · intro q₁ hq₁ q₂ hq₂ a b ha hb hab
    change phiTheta θ q₁.1 ≤ (q₁.2 : EReal) at hq₁
    change phiTheta θ q₂.1 ≤ (q₂.2 : EReal) at hq₂
    change phiTheta θ (a • q₁ + b • q₂).1 ≤ ((a • q₁ + b • q₂).2 : EReal)
    unfold phiTheta at hq₁ hq₂ ⊢
    have hp₁ : ∀ ℓ i, 0 ≤ q₁.1 ℓ i := by
      by_contra hnot
      rw [if_neg hnot] at hq₁
      exact absurd hq₁ (not_le_of_gt (EReal.coe_lt_top _))
    have hp₂ : ∀ ℓ i, 0 ≤ q₂.1 ℓ i := by
      by_contra hnot
      rw [if_neg hnot] at hq₂
      exact absurd hq₂ (not_le_of_gt (EReal.coe_lt_top _))
    rw [if_pos hp₁, EReal.coe_le_coe_iff] at hq₁
    rw [if_pos hp₂, EReal.coe_le_coe_iff] at hq₂
    have hp_comb : ∀ ℓ i, 0 ≤ (a • q₁ + b • q₂).1 ℓ i := fun ℓ i =>
      add_nonneg (mul_nonneg ha (hp₁ ℓ i)) (mul_nonneg hb (hp₂ ℓ i))
    rw [if_pos hp_comb, EReal.coe_le_coe_iff]
    have hF_comb : F (a • q₁.1 + b • q₂.1) ≤ a * F q₁.1 + b * F q₂.1 := by
      have hterm : ∀ ℓ, -(θ ℓ * shannonEntropy ((a • q₁.1 + b • q₂.1) ℓ)) ≤
          a * (-(θ ℓ * shannonEntropy (q₁.1 ℓ))) + b * (-(θ ℓ * shannonEntropy (q₂.1 ℓ))) := by
        intro ℓ
        have hinner : -shannonEntropy ((a • q₁.1 + b • q₂.1) ℓ) ≤
            a * (-shannonEntropy (q₁.1 ℓ)) + b * (-shannonEntropy (q₂.1 ℓ)) := by
          unfold shannonEntropy
          rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
            Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun i _ =>
            neg_negMulLog_convex_comb (hp₁ ℓ i) (hp₂ ℓ i) ha hb hab
        have hmul := mul_le_mul_of_nonneg_left hinner (hθ.1 ℓ)
        linarith
      have hsum := Finset.sum_le_sum fun ℓ (_ : ℓ ∈ Finset.univ) => hterm ℓ
      simp only [F, ← Finset.sum_neg_distrib] at hsum ⊢
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
      exact hsum
    calc
      F (a • q₁ + b • q₂).1 = F (a • q₁.1 + b • q₂.1) := rfl
      _ ≤ a * F q₁.1 + b * F q₂.1 := hF_comb
      _ ≤ a * q₁.2 + b * q₂.2 := add_le_add (mul_le_mul_of_nonneg_left hq₁ ha)
          (mul_le_mul_of_nonneg_left hq₂ hb)
  · intro σ p
    unfold phiTheta
    have hiff : (∀ ℓ i, 0 ≤ (p ℓ ∘ σ ℓ) i) ↔ ∀ ℓ i, 0 ≤ p ℓ i := by
      constructor
      · intro h ℓ i
        simpa using h ℓ ((σ ℓ).symm i)
      · intro h ℓ i
        exact h ℓ (σ ℓ i)
    have hsh : ∀ ℓ, shannonEntropy (p ℓ ∘ σ ℓ) = shannonEntropy (p ℓ) := fun ℓ =>
      Equiv.sum_comp (σ ℓ) (fun x => Real.negMulLog (p ℓ x))
    by_cases hp : ∀ ℓ i, 0 ≤ p ℓ i
    · rw [if_pos (hiff.mpr hp), if_pos hp]
      simp_rw [hsh]
    · rw [if_neg (mt hiff.mp hp), if_neg hp]
  · rw [interior_effDom_phiTheta]
    exact ⟨fun _ _ => 1, fun _ _ => zero_lt_one⟩
  · intro p hp
    have hp_pos : ∀ ℓ i, 0 < p ℓ i := by
      rwa [interior_effDom_phiTheta] at hp
    have hF_diff : DifferentiableAt ℝ F p := by
      refine DifferentiableAt.neg (DifferentiableAt.fun_sum fun ℓ _ => ?_)
      refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun i _ => ?_) (θ ℓ)
      have hcoord : DifferentiableAt ℝ (fun q : SpecTuple n => q ℓ i) p :=
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n ℓ) => ℝ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun m : Fin d => Fin (n m) → ℝ) ℓ)).differentiableAt
      have heq_nml : (fun q : SpecTuple n => Real.negMulLog (q ℓ i)) =
          fun q => -(q ℓ i * Real.log (q ℓ i)) := by
        ext q; simp [Real.negMulLog]
      rw [heq_nml]
      exact (hcoord.mul ((Real.differentiableAt_log (ne_of_gt (hp_pos ℓ i))).comp p hcoord)).neg
    have hev : (fun q : SpecTuple n => (phiTheta θ q).toReal) =ᶠ[nhds p] F := by
      refine Filter.eventually_of_mem (mem_interior_iff_mem_nhds.mp hp) fun q hq => ?_
      rw [effDom_phiTheta] at hq
      have hq' : ∀ ℓ i, 0 ≤ q ℓ i := hq
      dsimp only
      unfold phiTheta
      rw [if_pos hq', EReal.toReal_coe]
    exact (hF_diff.congr_of_eventuallyEq hev).differentiableWithinAt

lemma entanglementPolytope_nonneg {d n0 : ℕ} {n : Fin d → ℕ} {T : Ten d n0 n} (hT : T ≠ 0) :
    ∀ p ∈ entanglementPolytope T, ∀ ℓ i, 0 ≤ p ℓ i := by
  set S_nn : Set (SpecTuple n) := {p | ∀ ℓ i, 0 ≤ p ℓ i}
  have hclosed : IsClosed S_nn := by
    have heq : S_nn = ⋂ ℓ : Fin d, ⋂ i : Fin (n ℓ), (fun p : SpecTuple n => p ℓ i) ⁻¹' Set.Ici 0 := by
      ext p; simp [S_nn]
    rw [heq]
    exact isClosed_iInter fun ℓ => isClosed_iInter fun i =>
      isClosed_Ici.preimage ((continuous_apply i).comp (continuous_apply ℓ))
  have hsub : {p | ∃ g : GTuple n, p = specTuple (momentMap (gact g T))} ⊆ S_nn := by
    rintro _ ⟨g, rfl⟩ ℓ i
    have hdet : ∀ m, ((g m : Matrix.GeneralLinearGroup (Fin (n m)) ℂ) :
        Matrix (Fin (n m)) (Fin (n m)) ℂ).det ≠ 0 := fun m =>
      ((Matrix.isUnit_iff_isUnit_det _).mp (g m).isUnit).ne_zero
    have hgT : gact g T ≠ 0 := act_ne_zero_of_det_ne_zero hdet hT
    exact spec_nonneg_of_posSemidef (partialTrace_posSemidef ℓ (densityOp_posSemidef hgT)) i
  exact hclosed.closure_subset_iff.mpr hsub

lemma nat_le_two_pow : ∀ m : ℕ, m ≤ 2 ^ m
  | 0 => Nat.zero_le _
  | m + 1 => by
    have ih := nat_le_two_pow m
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
    rw [pow_succ]
    omega

lemma log_tnorm_le_two_bitLength {d n0 : ℕ} {n : Fin d → ℕ} {T : Ten d n0 n}
    (hT : T ≠ 0) (hGI : IsGaussianInteger T) :
    Real.log (tnorm T) ≤ 2 * (bitLength T : ℝ) := by
  set B : ℕ := bitLength T
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hT
  have hterm_ge2 : ∀ x : Fin n0 × MIdx n,
      2 ≤ intBitLength (round (T x).re) + intBitLength (round (T x).im) := by
    intro x
    unfold intBitLength
    omega
  have hB_ge2 : 2 ≤ B :=
    le_trans (hterm_ge2 x₀) (Finset.single_le_sum
      (f := fun x : Fin n0 × MIdx n => intBitLength (round (T x).re) + intBitLength (round (T x).im))
      (fun x _ => Nat.zero_le _) (Finset.mem_univ x₀))
  have hcard_le : Fintype.card (Fin n0 × MIdx n) ≤ B := by
    calc
      Fintype.card (Fin n0 × MIdx n) = ∑ _x : Fin n0 × MIdx n, 1 := by simp
      _ ≤ ∑ x : Fin n0 × MIdx n,
            (intBitLength (round (T x).re) + intBitLength (round (T x).im)) :=
        Finset.sum_le_sum fun x _ => le_trans (by decide : 1 ≤ 2) (hterm_ge2 x)
      _ = B := rfl
  have hentry_bound : ∀ x : Fin n0 × MIdx n, ‖T x‖ ^ 2 ≤ 2 * ((2 : ℝ) ^ B) ^ 2 := by
    intro x
    obtain ⟨a, b, hab⟩ := hGI x
    have hre : (T x).re = (a : ℝ) := by simp [hab]
    have him : (T x).im = (b : ℝ) := by simp [hab]
    have hra : round (T x).re = a := by rw [hre, round_intCast]
    have hrb : round (T x).im = b := by rw [him, round_intCast]
    have hx_le_B : intBitLength a + intBitLength b ≤ B := by
      rw [← hra, ← hrb]
      exact Finset.single_le_sum
        (f := fun y : Fin n0 × MIdx n => intBitLength (round (T y).re) + intBitLength (round (T y).im))
        (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
    have ha_sz : a.natAbs.size ≤ B := by unfold intBitLength at hx_le_B; omega
    have hb_sz : b.natAbs.size ≤ B := by unfold intBitLength at hx_le_B; omega
    have ha_lt : a.natAbs ≤ 2 ^ B :=
      le_trans (le_of_lt (Nat.lt_size_self a.natAbs)) (Nat.pow_le_pow_right (by decide) ha_sz)
    have hb_lt : b.natAbs ≤ 2 ^ B :=
      le_trans (le_of_lt (Nat.lt_size_self b.natAbs)) (Nat.pow_le_pow_right (by decide) hb_sz)
    have ha_sq : (a : ℝ) ^ 2 ≤ ((2 : ℝ) ^ B) ^ 2 := by
      have hsq : (a : ℝ) ^ 2 = (a.natAbs : ℝ) ^ 2 := by
        cases a with
        | ofNat m => simp
        | negSucc m => simp; ring
      have hle : (a.natAbs : ℝ) ≤ (2 : ℝ) ^ B := by exact_mod_cast ha_lt
      rw [hsq, sq, sq]
      exact mul_self_le_mul_self (Nat.cast_nonneg _) hle
    have hb_sq : (b : ℝ) ^ 2 ≤ ((2 : ℝ) ^ B) ^ 2 := by
      have hsq : (b : ℝ) ^ 2 = (b.natAbs : ℝ) ^ 2 := by
        cases b with
        | ofNat m => simp
        | negSucc m => simp; ring
      have hle : (b.natAbs : ℝ) ≤ (2 : ℝ) ^ B := by exact_mod_cast hb_lt
      rw [hsq, sq, sq]
      exact mul_self_le_mul_self (Nat.cast_nonneg _) hle
    have hnsq : ‖T x‖ ^ 2 = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
      ring
    linarith
  have htnorm_sq_le : tnorm T ^ 2 ≤ (2 : ℝ) ^ (3 * B + 1) := by
    rw [tnorm_sq_eq_sum]
    have h1 : ∑ x : Fin n0 × MIdx n, ‖T x‖ ^ 2 ≤
        (Fintype.card (Fin n0 × MIdx n) : ℝ) * (2 * ((2 : ℝ) ^ B) ^ 2) := by
      calc
        ∑ x : Fin n0 × MIdx n, ‖T x‖ ^ 2
            ≤ ∑ _x : Fin n0 × MIdx n, (2 * ((2 : ℝ) ^ B) ^ 2) :=
          Finset.sum_le_sum fun x _ => hentry_bound x
        _ = (Fintype.card (Fin n0 × MIdx n) : ℝ) * (2 * ((2 : ℝ) ^ B) ^ 2) := by
          simp [Finset.sum_const]
    have hcard_pow : (Fintype.card (Fin n0 × MIdx n) : ℝ) ≤ (2 : ℝ) ^ B := by
      have := le_trans hcard_le (nat_le_two_pow B)
      exact_mod_cast this
    have hpow_eq : (2 : ℝ) ^ B * (2 * ((2 : ℝ) ^ B) ^ 2) = (2 : ℝ) ^ (3 * B + 1) := by
      have : 3 * B + 1 = B + (B + B) + 1 := by omega
      rw [this, pow_succ, pow_add, pow_add]
      ring
    calc
      ∑ x : Fin n0 × MIdx n, ‖T x‖ ^ 2
          ≤ (Fintype.card (Fin n0 × MIdx n) : ℝ) * (2 * ((2 : ℝ) ^ B) ^ 2) := h1
      _ ≤ (2 : ℝ) ^ B * (2 * ((2 : ℝ) ^ B) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard_pow (by positivity)
      _ = (2 : ℝ) ^ (3 * B + 1) := hpow_eq
  have htnorm_sq_pos : 0 < tnorm T ^ 2 := tnorm_sq_pos_of_ne_zero hT
  have htnorm_pos : 0 < tnorm T := by
    unfold tnorm
    exact Real.sqrt_pos.mpr (by simpa [tnorm_sq_eq_sum] using htnorm_sq_pos)
  have hlog2_le1 : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp zero_lt_two]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog_sq : Real.log (tnorm T) = (1 / 2 : ℝ) * Real.log (tnorm T ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    ring
  have hlog_le : Real.log (tnorm T ^ 2) ≤ (3 * (B : ℝ) + 1) := by
    calc
      Real.log (tnorm T ^ 2) ≤ Real.log ((2 : ℝ) ^ (3 * B + 1)) :=
        Real.log_le_log htnorm_sq_pos htnorm_sq_le
      _ = ((3 * B + 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (3 * B + 1)
      _ ≤ ((3 * B + 1 : ℕ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog2_le1 (Nat.cast_nonneg _)
      _ = 3 * (B : ℝ) + 1 := by push_cast; ring
  have hB_ge1_real : (1 : ℝ) ≤ (B : ℝ) := by
    have : 1 ≤ B := le_trans (by decide : 1 ≤ 2) hB_ge2
    exact_mod_cast this
  rw [hlog_sq]
  linarith

end Aux74

open MomentPolytopes.QuantumFunctionals

theorem solution :
    (∀ (d n0 : ℕ) (n : Fin d → ℕ) (θ : Fin d → ℝ), IsProbVec θ →
      ∀ T : Ten d n0 n, T ≠ 0 → IsConcise T →
      ∀ pstar ∈ entanglementPolytope T,
        (∀ p ∈ entanglementPolytope T, phiTheta θ pstar ≤ phiTheta θ p) →
      ∀ k : ℕ, 1 ≤ k →
        0 ≤ logQuantumFunctional θ T -
            ∑ ℓ, θ ℓ * vnEntropy (momentMap (entropicScalingSeq 1 θ T k) ℓ) ∧
        (((logQuantumFunctional θ T -
            ∑ ℓ, θ ℓ * vnEntropy (momentMap (entropicScalingSeq 1 θ T k) ℓ) : ℝ)) : EReal) ≤
          ((2 : ℝ) : EReal) * ((Real.log (tnorm T) : EReal) - logCap pstar T) /
            ((k : ℝ) : EReal)) ∧
    (∃ C : ℝ, ∃ c : ℕ, ∀ (d n0 : ℕ) (n : Fin d → ℕ) (θ : Fin d → ℝ), IsProbVec θ →
      ∀ T : Ten d n0 n, T ≠ 0 → IsConcise T → IsGaussianInteger T →
      ∀ pstar ∈ entanglementPolytope T,
        (∀ p ∈ entanglementPolytope T, phiTheta θ pstar ≤ phiTheta θ p) →
      ∀ k : ℕ, 1 ≤ k →
        ((2 : ℝ) : EReal) * ((Real.log (tnorm T) : EReal) - logCap pstar T) /
            ((k : ℝ) : EReal) ≤
          ((C * (1 + d + nmax n + bitLength T : ℝ) ^ c / k : ℝ) : EReal)) := by
  refine ⟨?_, ?_⟩
  · -- Part 1: Convergence rate via Theorem 7.5 and Theorem 6.27
    intro d n0 n θ hθ T hT hconc pstar hpstar hmin k hk
    have hadm : IsAdmissibleObjective (phiTheta θ (n := n)) :=
      Aux74.isAdmissibleObjective_phiTheta hθ
    have hint : ∀ g : GTuple n,
        specTuple (momentMap (gact g T)) ∈ interior (effDom (phiTheta θ)) := by
      intro g
      rw [Aux74.interior_effDom_phiTheta]
      intro ℓ i
      have hdet : ∀ m, ((g m : Matrix.GeneralLinearGroup (Fin (n m)) ℂ) :
          Matrix (Fin (n m)) (Fin (n m)) ℂ).det ≠ 0 := fun m =>
        ((Matrix.isUnit_iff_isUnit_det _).mp (g m).isUnit).ne_zero
      have hgT : gact g T ≠ 0 := Aux74.act_ne_zero_of_det_ne_zero hdet hT
      have hgconc : IsConcise (gact g T) := Aux74.isConcise_act_of_det_ne_zero hdet hT hconc
      have hpos := Aux74.posDef_of_posSemidef_det_ne_zero
        (Aux74.partialTrace_posSemidef ℓ (Aux74.densityOp_posSemidef hgT)) (hgconc ℓ)
      exact Aux74.spec_pos_of_posDef hpos i
    have hseq_eq : mirrorDescentSeq (phiTheta θ) 1 Aux74.mdScalars T = entropicScalingSeq 1 θ T :=
      funext (Aux74.mirrorDescentSeq_eq_entropicScalingSeq hθ hT hconc)
    have hstep_es := theorem_7_5.2 d n0 n θ 1 hθ zero_lt_one le_rfl T hT hconc
    have hstep_md : StepSizeCondition (phiTheta θ) 1
        (mirrorDescentSeq (phiTheta θ) 1 Aux74.mdScalars T) Aux74.mdScalars := by
      intro m
      rw [hseq_eq]
      exact hstep_es m
    have h627 := (theorem_6_27 T hT (phiTheta θ) hadm hint pstar hpstar hmin).1
      1 zero_lt_one Aux74.mdScalars Aux74.mdScalars_ne_zero hstep_md k hk
    rw [hseq_eq, one_mul] at h627
    set Hθ : SpecTuple n → ℝ := fun p => ∑ ℓ, θ ℓ * shannonEntropy (p ℓ)
    have hphi_on_poly : ∀ p ∈ entanglementPolytope T,
        phiTheta θ p = ((-Hθ p : ℝ) : EReal) := by
      intro p hp
      unfold phiTheta
      rw [if_pos (Aux74.entanglementPolytope_nonneg hT p hp)]
    have hH_le_pstar : ∀ p ∈ entanglementPolytope T, Hθ p ≤ Hθ pstar := by
      intro p hp
      have hm := hmin p hp
      rw [hphi_on_poly pstar hpstar, hphi_on_poly p hp, EReal.coe_le_coe_iff] at hm
      linarith
    have hE_eq : logQuantumFunctional θ T = Hθ pstar := by
      unfold logQuantumFunctional
      refine IsGreatest.csSup_eq ⟨⟨pstar, hpstar, rfl⟩, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      exact hH_le_pstar p hp
    have hinf_eq : (⨅ p ∈ entanglementPolytope T, phiTheta θ p) =
        ((-logQuantumFunctional θ T : ℝ) : EReal) := by
      have h1 : (⨅ p ∈ entanglementPolytope T, phiTheta θ p) = phiTheta θ pstar :=
        le_antisymm (iInf₂_le pstar hpstar) (le_iInf₂ hmin)
      rw [h1, hphi_on_poly pstar hpstar, hE_eq]
    obtain ⟨gk, hgk⟩ := Aux74.entropicScalingSeq_in_orbit 1 θ hT hconc k
    set pk : SpecTuple n := specTuple (momentMap (entropicScalingSeq 1 θ T k))
    have hpk_mem : pk ∈ entanglementPolytope T :=
      subset_closure ⟨gk, by simp [pk, hgk]⟩
    have hpk_H : Hθ pk = ∑ ℓ, θ ℓ * vnEntropy (momentMap (entropicScalingSeq 1 θ T k) ℓ) := rfl
    have hnonneg : 0 ≤ logQuantumFunctional θ T -
        ∑ ℓ, θ ℓ * vnEntropy (momentMap (entropicScalingSeq 1 θ T k) ℓ) := by
      rw [hE_eq, ← hpk_H]
      linarith [hH_le_pstar pk hpk_mem]
    refine ⟨hnonneg, ?_⟩
    rw [hphi_on_poly pk hpk_mem, hinf_eq, ← EReal.coe_sub] at h627
    have hsub_eq : -Hθ pk - -logQuantumFunctional θ T =
        logQuantumFunctional θ T -
          ∑ ℓ, θ ℓ * vnEntropy (momentMap (entropicScalingSeq 1 θ T k) ℓ) := by
      rw [hpk_H]; ring
    rw [hsub_eq] at h627
    exact h627
  · -- Part 2: Universal polynomial bound for Gaussian-integer tensors via Theorem 6.28(a)
    obtain ⟨C₁, c₁, h628⟩ := theorem_6_28.1
    set C₀ : ℝ := max C₁ 0
    set c : ℕ := max c₁ 1
    refine ⟨2 * (2 + C₀), c, ?_⟩
    intro d n0 n θ _hθ T hT _hconc hGI pstar hpstar _hmin k hk
    have hcap := h628 d n0 n T hT hGI pstar hpstar
    set X : ℝ := 1 + (d : ℝ) + (nmax n : ℝ) + (bitLength T : ℝ)
    have hX_ge1 : 1 ≤ X := by
      dsimp only [X]
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hn : (0 : ℝ) ≤ nmax n := Nat.cast_nonneg (nmax n)
      have hb : (0 : ℝ) ≤ bitLength T := Nat.cast_nonneg (bitLength T)
      linarith
    have hbase_nn : 0 ≤ 1 + (d : ℝ) + (nmax n : ℝ) := by
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hn : (0 : ℝ) ≤ nmax n := Nat.cast_nonneg (nmax n)
      linarith
    have hbase_le_X : 1 + (d : ℝ) + (nmax n : ℝ) ≤ X := by
      dsimp only [X]
      linarith [Nat.cast_nonneg (α := ℝ) (bitLength T)]
    have hC₀_nn : 0 ≤ C₀ := le_max_right C₁ 0
    have hcap_bound : C₁ * (1 + (d : ℝ) + (nmax n : ℝ)) ^ c₁ ≤ C₀ * X ^ c := by
      calc
        C₁ * (1 + (d : ℝ) + (nmax n : ℝ)) ^ c₁
            ≤ C₀ * (1 + (d : ℝ) + (nmax n : ℝ)) ^ c₁ :=
          mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (pow_nonneg hbase_nn c₁)
        _ ≤ C₀ * X ^ c₁ :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn hbase_le_X c₁) hC₀_nn
        _ ≤ C₀ * X ^ c :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX_ge1 (le_max_left c₁ 1)) hC₀_nn
    have hlog_bound : Real.log (tnorm T) ≤ 2 * X ^ c := by
      have hB_le_X : (bitLength T : ℝ) ≤ X := by
        dsimp only [X]
        linarith
      have hX_le_pow : X ≤ X ^ c := by
        simpa using pow_le_pow_right₀ hX_ge1 (le_max_right c₁ 1)
      calc
        Real.log (tnorm T) ≤ 2 * (bitLength T : ℝ) := Aux74.log_tnorm_le_two_bitLength hT hGI
        _ ≤ 2 * X := by linarith
        _ ≤ 2 * X ^ c := by linarith
    have hk_pos : (0 : ℝ) < (k : ℝ) :=
      Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
    induction hl : logCap pstar T using EReal.rec with
    | bot =>
      rw [hl, EReal.neg_bot] at hcap
      exact absurd hcap (not_le_of_gt (EReal.coe_lt_top _))
    | top =>
      have h1 : (Real.log (tnorm T) : EReal) - ⊤ = ⊥ := by simp [sub_eq_add_neg]
      have h2 : ((2 : ℝ) : EReal) * ⊥ = ⊥ := EReal.coe_mul_bot_of_pos two_pos
      have h3 : (⊥ : EReal) / ((k : ℝ) : EReal) = ⊥ := by
        rw [div_eq_mul_inv, ← EReal.coe_inv]
        exact EReal.bot_mul_coe_of_pos (inv_pos.mpr hk_pos)
      rw [h1, h2, h3]
      exact bot_le
    | coe r =>
      rw [hl] at hcap
      have hr_le : -r ≤ C₀ * X ^ c := by
        have hr0 : -r ≤ C₁ * (1 + (d : ℝ) + (nmax n : ℝ)) ^ c₁ := by
          exact_mod_cast hcap
        exact le_trans hr0 hcap_bound
      rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_div, EReal.coe_le_coe_iff]
      exact div_le_div_of_nonneg_right (by nlinarith) (le_of_lt hk_pos)
