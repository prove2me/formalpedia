-- Prove2me | solution 1 for HryniewiczCriterion.positive_unitary_path_eigenAngleSum_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T09:40:05.131048+00:00
-- url     : https://prove2.me/submissions/0c57cdcc-3a03-4a91-96c2-622543ab8535

import Definitions.Def_HryniewiczCriterion_GraphAngle
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Matrix.PosDef

open HryniewiczCriterion
open scoped ContDiff ComplexOrder
open Module InnerProductSpace

/-!
# Leaf C2, part 1: Weyl's eigenvalue inequality

For symmetric operators `T`, `S` on a finite-dimensional inner product space with
`re ⟪T x, x⟫ ≤ re ⟪S x, x⟫ + ε ‖x‖²` for all `x`, the sorted eigenvalues satisfy
`λⱼ(T) ≤ λⱼ(S) + ε`. Proof by dimension count: the span of the first `j + 1` eigenvectors of `T`
meets the span of the last `m - j` eigenvectors of `S` only in `0`.
-/


namespace LinearMap.IsSymmetric

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E} {m : ℕ}

/-- Rayleigh expansion in an eigenbasis. -/
lemma re_inner_apply_eq_sum (hT : T.IsSymmetric) (hn : finrank 𝕜 E = m) (x : E) :
    RCLike.re (inner 𝕜 (T x) x) =
      ∑ k, hT.eigenvalues hn k * ‖inner 𝕜 (hT.eigenvectorBasis hn k) (x)‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn
  have h : inner 𝕜 (T x) (x) = ∑ k, (hT.eigenvalues hn k : 𝕜) * ((‖inner 𝕜 (b k) (x)‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← b.sum_inner_mul_inner (T x) x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hT (x) (b k), hT.apply_eigenvectorBasis hn k, inner_smul_right, mul_assoc]
    congr 1
    rw [← inner_conj_symm, RCLike.conj_mul]
    norm_cast
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← RCLike.ofReal_mul, RCLike.ofReal_re]

lemma inner_eigenvectorBasis_eq_zero_of_mem_span (hT : T.IsSymmetric) (hn : finrank 𝕜 E = m)
    {K : Set (Fin m)} {x : E} (hx : x ∈ Submodule.span 𝕜 (hT.eigenvectorBasis hn '' K))
    {k : Fin m} (hk : k ∉ K) : inner 𝕜 (hT.eigenvectorBasis hn k) (x) = 0 := by
  set b := hT.eigenvectorBasis hn
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, hi, rfl⟩
    have hki : k ≠ i := fun h => hk (h ▸ hi)
    exact b.orthonormal.2 hki
  · simp
  · intro u v _ _ hu hv; rw [inner_add_right, hu, hv, add_zero]
  · intro c u _ hu; rw [inner_smul_right, hu, mul_zero]

lemma finrank_span_eigenvectorBasis (hT : T.IsSymmetric) (hn : finrank 𝕜 E = m)
    (K : Finset (Fin m)) :
    finrank 𝕜 (Submodule.span 𝕜 (hT.eigenvectorBasis hn '' (K : Set (Fin m)))) = K.card := by
  set b := hT.eigenvectorBasis hn
  have hli : LinearIndependent 𝕜 (fun i : (K : Set (Fin m)) => b i) :=
    b.orthonormal.linearIndependent.comp _ Subtype.val_injective
  have hr : Set.range (fun i : (K : Set (Fin m)) => b i) = b '' (K : Set (Fin m)) := by
    ext y; simp
  rw [← hr, finrank_span_eq_card hli]
  simp

/-- **Weyl's inequality** (sorted eigenvalues, decreasing order). -/
theorem eigenvalues_le_add_of_re_inner_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hn : finrank 𝕜 E = m) (ε : ℝ)
    (h : ∀ x : E, RCLike.re (inner 𝕜 (T x) x) ≤ RCLike.re (inner 𝕜 (S x) x) + ε * ‖x‖ ^ 2) (j : Fin m) :
    hT.eigenvalues hn j ≤ hS.eigenvalues hn j + ε := by
  by_contra hlt
  push_neg at hlt
  set P := Submodule.span 𝕜 (hT.eigenvectorBasis hn '' ((Finset.Iic j : Finset (Fin m)) : Set (Fin m)))
  set R := Submodule.span 𝕜 (hS.eigenvectorBasis hn '' ((Finset.Ici j : Finset (Fin m)) : Set (Fin m)))
  have hPR : P ⊓ R = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxP, hxR⟩
    -- lower Rayleigh bound on `P`
    have h1 : hT.eigenvalues hn j * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (T x) x) := by
      rw [hT.re_inner_apply_eq_sum hn, ← (hT.eigenvectorBasis hn).sum_sq_norm_inner_right x, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      by_cases hk : k ≤ j
      · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hk) (by positivity)
      · have : inner 𝕜 (hT.eigenvectorBasis hn k) (x) = 0 :=
          hT.inner_eigenvectorBasis_eq_zero_of_mem_span hn hxP (by simpa using hk)
        simp [this]
    -- upper Rayleigh bound on `R`
    have h2 : RCLike.re (inner 𝕜 (S x) x) ≤ hS.eigenvalues hn j * ‖x‖ ^ 2 := by
      rw [hS.re_inner_apply_eq_sum hn, ← (hS.eigenvectorBasis hn).sum_sq_norm_inner_right x, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      by_cases hk : j ≤ k
      · exact mul_le_mul_of_nonneg_right (hS.eigenvalues_antitone hn hk) (by positivity)
      · have : inner 𝕜 (hS.eigenvectorBasis hn k) (x) = 0 :=
          hS.inner_eigenvectorBasis_eq_zero_of_mem_span hn hxR (by simpa using hk)
        simp [this]
    have h3 := h x
    have hx2 : ‖x‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp this
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq P R
  rw [hPR, finrank_bot, add_zero, hT.finrank_span_eigenvectorBasis hn,
    hS.finrank_span_eigenvectorBasis hn, Fin.card_Iic, Fin.card_Ici] at hdim
  have hle : finrank 𝕜 ↥(P ⊔ R) ≤ m := hn ▸ Submodule.finrank_le _
  omega

end LinearMap.IsSymmetric

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n 𝕜}

/-- **Weyl's inequality** for Hermitian matrices: if `A ≤ B + ε` as quadratic forms, then
`λⱼ(A) ≤ λⱼ(B) + ε` for the eigenvalues sorted in decreasing order. -/
theorem eigenvalues₀_le_add (hA : A.IsHermitian) (hB : B.IsHermitian) (ε : ℝ)
    (h : ∀ x : n → 𝕜, RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤
      RCLike.re (star x ⬝ᵥ (B *ᵥ x)) + ε * RCLike.re (star x ⬝ᵥ x))
    (j : Fin (Fintype.card n)) : hA.eigenvalues₀ j ≤ hB.eigenvalues₀ j + ε := by
  refine LinearMap.IsSymmetric.eigenvalues_le_add_of_re_inner_le _ _ _ ε (fun x => ?_) j
  have hx := h (WithLp.ofLp x)
  have key : ∀ M : Matrix n n 𝕜, RCLike.re (inner 𝕜 (Matrix.toEuclideanLin M x) x) =
      RCLike.re (star (WithLp.ofLp x) ⬝ᵥ (M *ᵥ WithLp.ofLp x)) := by
    intro M
    rw [← inner_conj_symm, RCLike.conj_re, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm]
    rfl
  have hn : ‖x‖ ^ 2 = RCLike.re (star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x) := by
    rw [@norm_sq_eq_re_inner 𝕜, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [hn]
  erw [key A, key B]
  exact hx

end Matrix.IsHermitian

/-!
# Leaf C2, part 2: the Cayley transform of a unitary matrix

For `a` on the unit circle that is not an eigenvalue of the unitary `V`,
`C = 2 i a (a - V)⁻¹ - i = i (a + V)(a - V)⁻¹` is Hermitian, `(C + i) V = a (C - i)`, and the
eigenvalues of `V` are `a (cₖ - i)/(cₖ + i)` for the eigenvalues `cₖ` of `C`.
-/

namespace HryniewiczCriterion

open Matrix Complex

noncomputable section

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The Cayley transform `2 i a (a - V)⁻¹ - i` of `V` with pole `a`. -/
def cayleyT (a : ℂ) (V : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 * I * a) • (a • (1 : Matrix n n ℂ) - V)⁻¹ - I • (1 : Matrix n n ℂ)

lemma inv_comm_of_sub {a : ℂ} {V : Matrix n n ℂ} :
    (a • (1 : Matrix n n ℂ) - V)⁻¹ * V = V * (a • (1 : Matrix n n ℂ) - V)⁻¹ := by
  set M := a • (1 : Matrix n n ℂ) - V
  by_cases hM : IsUnit M.det
  · have hc : M * V = V * M := by simp [M, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
    calc M⁻¹ * V = M⁻¹ * V * (M * M⁻¹) := by rw [mul_nonsing_inv _ hM, Matrix.mul_one]
      _ = M⁻¹ * (M * V) * M⁻¹ := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = V * M⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.one_mul]
  · simp [nonsing_inv_apply_not_isUnit _ hM]

lemma cayleyT_mul {a : ℂ} {V : Matrix n n ℂ} (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) :
    (cayleyT a V + I • (1 : Matrix n n ℂ)) * V = a • (cayleyT a V - I • (1 : Matrix n n ℂ)) := by
  set M := a • (1 : Matrix n n ℂ) - V
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have h1 : a • M⁻¹ - (1 : Matrix n n ℂ) = V * M⁻¹ := by
    have : a • M⁻¹ - (1 : Matrix n n ℂ) = (a • (1 : Matrix n n ℂ) - M) * M⁻¹ := by
      rw [sub_mul, mul_nonsing_inv _ hM, smul_mul_assoc, Matrix.one_mul]
    rw [this]; simp [M]
  have hL : (cayleyT a V + I • (1 : Matrix n n ℂ)) * V = (2 * I * a) • (V * M⁻¹) := by
    simp only [cayleyT, sub_add_cancel, smul_mul_assoc]
    rw [inv_comm_of_sub]
  have hR : a • (cayleyT a V - I • (1 : Matrix n n ℂ)) = (2 * I * a) • (a • M⁻¹ - 1) := by
    simp only [cayleyT, smul_sub, smul_smul]
    rw [sub_sub, ← add_smul]
    congr 1
    · congr 1; ring
    · rw [show a * I + a * I = 2 * I * a by ring]
  rw [hL, hR, h1]

lemma smul_inv_sub_one {a : ℂ} {V : Matrix n n ℂ} (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) :
    a • (a • (1 : Matrix n n ℂ) - V)⁻¹ - 1 = V * (a • (1 : Matrix n n ℂ) - V)⁻¹ := by
  set M := a • (1 : Matrix n n ℂ) - V
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have : a • M⁻¹ - (1 : Matrix n n ℂ) = (a • (1 : Matrix n n ℂ) - M) * M⁻¹ := by
    rw [sub_mul, mul_nonsing_inv _ hM, smul_mul_assoc, Matrix.one_mul]
  rw [this]; simp [M]

lemma inv_conjTranspose_sub {a : ℂ} {V : Matrix n n ℂ} (hV : star V * V = 1) (ha : star a * a = 1)
    (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) :
    (a • (1 : Matrix n n ℂ) - V)⁻¹ᴴ = (-a) • (V * (a • (1 : Matrix n n ℂ) - V)⁻¹) := by
  set M := a • (1 : Matrix n n ℂ) - V
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  rw [conjTranspose_nonsing_inv]
  apply inv_eq_right_inv
  have hVh : Vᴴ * V = 1 := hV
  have hMh : Mᴴ = star a • (1 : Matrix n n ℂ) - Vᴴ := by
    simp [M, conjTranspose_sub, conjTranspose_smul]
  rw [hMh, sub_mul, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, ← Matrix.mul_assoc, hVh,
    Matrix.one_mul, smul_smul, mul_neg, ha]
  have : M * M⁻¹ = 1 := mul_nonsing_inv _ hM
  rw [← this]
  simp only [M, sub_mul, smul_mul_assoc, Matrix.one_mul, neg_smul, one_smul]
  abel

lemma cayleyT_isHermitian {a : ℂ} {V : Matrix n n ℂ} (hV : star V * V = 1) (ha : star a * a = 1)
    (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) : (cayleyT a V).IsHermitian := by
  set M := a • (1 : Matrix n n ℂ) - V
  have hC : cayleyT a V = (2 * I) • (V * M⁻¹) + I • (1 : Matrix n n ℂ) := by
    rw [← smul_inv_sub_one hdet]
    simp only [cayleyT, smul_sub, smul_smul]
    rw [mul_assoc, sub_add, ← sub_smul]
    congr 2; ring
  unfold Matrix.IsHermitian
  conv_rhs => rw [hC]
  rw [cayleyT, conjTranspose_sub, conjTranspose_smul, conjTranspose_smul,
    inv_conjTranspose_sub hV ha hdet, conjTranspose_one, smul_smul]
  have hs : star (2 * I * a) * -a = (2 * I) * (star a * a) := by
    have : star a * a = a * star a := mul_comm _ _
    simp only [star_mul', star_ofNat, Complex.star_def, Complex.conj_I]; ring
  rw [hs, ha, mul_one, show star I = -I from Complex.conj_I, neg_smul, sub_neg_eq_add]

/-- The eigenvalues of `V`, through the eigenvalues `cₖ` of its Cayley transform. -/
lemma roots_charpoly_eq_cayley {a : ℂ} {V : Matrix n n ℂ}
    (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) (hC : (cayleyT a V).IsHermitian) :
    V.charpoly.roots = Multiset.map
      (fun k => a * (((hC.eigenvalues k : ℝ) : ℂ) - I) / (((hC.eigenvalues k : ℝ) : ℂ) + I))
      Finset.univ.val := by
  set C := cayleyT a V
  set U : Matrix n n ℂ := (hC.eigenvectorUnitary : Matrix n n ℂ)
  set c : n → ℂ := fun k => ((hC.eigenvalues k : ℝ) : ℂ)
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hD : star U * C * U = diagonal c := by
    have := hC.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    have h2 : diagonal c = diagonal (RCLike.ofReal ∘ hC.eigenvalues) := rfl
    rw [h2]
    simpa [U] using this
  set W := star U * V * U
  have key : diagonal (fun k => c k + I) * W = a • diagonal (fun k => c k - I) := by
    have e1 : diagonal (fun k => c k + I) = star U * (C + I • (1 : Matrix n n ℂ)) * U := by
      rw [Matrix.mul_add, Matrix.add_mul, hD, mul_smul_comm, Matrix.mul_one, smul_mul_assoc, hUU]
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
    have e2 : diagonal (fun k => c k - I) = star U * (C - I • (1 : Matrix n n ℂ)) * U := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hD, mul_smul_comm, Matrix.mul_one, smul_mul_assoc, hUU]
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
    rw [e1, e2]
    calc star U * (C + I • 1) * U * W
        = star U * ((C + I • 1) * V) * U := by
          simp only [W, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc U (star U), hUU', Matrix.one_mul]
      _ = a • (star U * (C - I • 1) * U) := by
          rw [cayleyT_mul hdet, mul_smul_comm, smul_mul_assoc]
  have hW : W = diagonal (fun k => a * (c k - I) / (c k + I)) := by
    ext i j
    have hk := congr_fun (congr_fun key i) j
    have hne : c i + I ≠ 0 := by
      intro h; have := congr_arg Complex.im h; simp [c] at this
    simp only [diagonal_mul, Matrix.smul_apply, diagonal_apply, smul_eq_mul] at hk
    rw [diagonal_apply]
    by_cases h : i = j
    · subst h; simp only [if_true] at hk ⊢; rw [eq_div_iff hne, mul_comm]; exact hk
    · simp only [h, if_false, mul_zero] at hk ⊢
      exact (mul_eq_zero.mp hk).resolve_left hne
  have hchar : V.charpoly = W.charpoly := by
    simp only [W, Matrix.mul_assoc]
    rw [charpoly_mul_comm, Matrix.mul_assoc, hUU', Matrix.mul_one]
  rw [hchar, hW, charpoly_diagonal, Polynomial.roots_prod]
  · simp [c]
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

end

end HryniewiczCriterion

/-!
# Leaf C2, part 3: angle bookkeeping

* `exp_eigenAngleSum_mul_I`: `exp (i · eigenAngleSum V) = det V` when `|det V| = 1`.
* `angPos_exp_mul_I_of_mem`: `angPos (e^{iφ}) = φ` for `φ ∈ (0, 2π]`.
* `angPos_cayley`: the normalized angle of `e^{iα}(c - i)/(c + i)` is
  `α + π + 2 arctan c - 2π [c > tan((π - α)/2)]`.
* `eigenAngleSum_eq_sum_cayley`: the eigen-angle sum of `V` through the eigenvalues of its
  Cayley transform with pole `e^{iα}`.
-/

namespace HryniewiczCriterion

open Matrix Complex

noncomputable section

lemma exp_angPos_mul_I {z : ℂ} : exp ((angPos z : ℂ) * I) = exp ((arg z : ℂ) * I) := by
  unfold angPos
  split_ifs
  · rfl
  · push_cast
    rw [add_mul, exp_add, show (2 * (Real.pi : ℂ)) * I = 2 * Real.pi * I by ring, exp_two_pi_mul_I,
      mul_one]

lemma exp_sum_angPos_mul_norm (s : Multiset ℂ) :
    exp (((s.map angPos).sum : ℂ) * I) * (s.map fun z => ((‖z‖ : ℝ) : ℂ)).prod = s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
    push_cast
    rw [add_mul, exp_add, exp_angPos_mul_I]
    calc exp (↑(arg z) * I) * exp (↑(s.map angPos).sum * I) *
          ((‖z‖ : ℂ) * (s.map fun z => ((‖z‖ : ℝ) : ℂ)).prod)
        = ((‖z‖ : ℂ) * exp (↑(arg z) * I)) *
          (exp (↑(s.map angPos).sum * I) * (s.map fun z => ((‖z‖ : ℝ) : ℂ)).prod) := by ring
      _ = z * s.prod := by rw [norm_mul_exp_arg_mul_I, ih]

lemma multiset_prod_norm (s : Multiset ℂ) :
    (s.map fun z => ((‖z‖ : ℝ) : ℂ)).prod = ((‖s.prod‖ : ℝ) : ℂ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih => simp [ih]

/-- `exp (i · eigenAngleSum V) = det V` for `|det V| = 1`. -/
theorem exp_eigenAngleSum_mul_I {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n n ℂ)
    (hV : ‖V.det‖ = 1) : exp ((eigenAngleSum V : ℂ) * I) = V.det := by
  have h := exp_sum_angPos_mul_norm V.charpoly.roots
  rw [multiset_prod_norm, ← det_eq_prod_roots_charpoly, hV] at h
  simpa [eigenAngleSum] using h

lemma angPos_exp_mul_I_of_mem {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ 2 * Real.pi) :
    angPos (exp ((φ : ℂ) * I)) = φ := by
  unfold angPos
  rcases le_or_gt φ Real.pi with hφ | hφ
  · have : arg (exp ((φ : ℂ) * I)) = φ := by
      rw [← cos_add_sin_I]
      exact_mod_cast arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], hφ⟩
    rw [this, if_pos h0]
  · have he : exp ((φ : ℂ) * I) = exp (((φ - 2 * Real.pi : ℝ) : ℂ) * I) := by
      push_cast
      rw [sub_mul, exp_sub, show (2 * (Real.pi : ℂ)) * I = 2 * Real.pi * I by ring,
        exp_two_pi_mul_I, div_one]
    have : arg (exp ((φ : ℂ) * I)) = φ - 2 * Real.pi := by
      rw [he, ← cos_add_sin_I]
      exact_mod_cast arg_cos_add_sin_mul_I ⟨by linarith, by linarith [Real.pi_pos]⟩
    rw [this, if_neg (by linarith)]
    ring

lemma angPos_exp_mul_I_of_mem' {φ : ℝ} (h0 : 2 * Real.pi < φ) (h1 : φ ≤ 4 * Real.pi) :
    angPos (exp ((φ : ℂ) * I)) = φ - 2 * Real.pi := by
  have he : exp ((φ : ℂ) * I) = exp (((φ - 2 * Real.pi : ℝ) : ℂ) * I) := by
    push_cast
    rw [sub_mul, exp_sub, show (2 * (Real.pi : ℂ)) * I = 2 * Real.pi * I by ring,
      exp_two_pi_mul_I, div_one]
  rw [he, angPos_exp_mul_I_of_mem (by linarith) (by linarith)]

/-- `(c - i)/(c + i) = e^{i(π + 2 arctan c)}`. -/
lemma cayley_scalar_eq_exp (c : ℝ) :
    ((c : ℂ) - I) / ((c : ℂ) + I) = exp (((Real.pi + 2 * Real.arctan c : ℝ) : ℂ) * I) := by
  have hs : (0 : ℝ) < √(1 + c ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : (√(1 + c ^ 2)) ^ 2 = 1 + c ^ 2 := Real.sq_sqrt (by positivity)
  have hexp : exp (((Real.arctan c : ℝ) : ℂ) * I) = (1 + c * I) / (√(1 + c ^ 2) : ℝ) := by
    rw [← cos_add_sin_I, ← ofReal_cos, ← ofReal_sin, Real.cos_arctan, Real.sin_arctan]
    push_cast
    ring
  have hne : (c : ℂ) + I ≠ 0 := by
    intro h; have := congr_arg Complex.im h; simp at this
  have hne2 : ((√(1 + c ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hs2c : ((√(1 + c ^ 2) : ℝ) : ℂ) ^ 2 = 1 + (c : ℂ) ^ 2 := by exact_mod_cast hs2
  push_cast
  rw [add_mul, exp_add, exp_pi_mul_I, show 2 * (Real.arctan c : ℂ) * I =
    (Real.arctan c : ℂ) * I + (Real.arctan c : ℂ) * I by ring, exp_add, hexp]
  have h1c : (1 + (c : ℂ) ^ 2) ≠ 0 := by
    rw [← hs2c]; exact pow_ne_zero 2 hne2
  rw [div_mul_div_comm, ← pow_two ((√(1 + c ^ 2) : ℝ) : ℂ), hs2c, neg_one_mul, ← neg_div,
    div_eq_div_iff hne h1c]
  linear_combination (2 * (c : ℂ) + c ^ 3 + c ^ 2 * I) * I_sq

/-- The normalized angle of `e^{iα}(c - i)/(c + i)`, `α ∈ (0, 2π)`. -/
def gAngle (α c : ℝ) : ℝ :=
  α + Real.pi + 2 * Real.arctan c - if Real.tan ((Real.pi - α) / 2) < c then 2 * Real.pi else 0

lemma angPos_cayley {α : ℝ} (hα0 : 0 < α) (hα1 : α < 2 * Real.pi) (c : ℝ) :
    angPos (exp ((α : ℂ) * I) * ((c : ℂ) - I) / ((c : ℂ) + I)) = gAngle α c := by
  have ha1 := Real.neg_pi_div_two_lt_arctan c
  have ha2 := Real.arctan_lt_pi_div_two c
  rw [mul_div_assoc, cayley_scalar_eq_exp, ← exp_add, ← add_mul, ← ofReal_add]
  have hy1 : -(Real.pi / 2) < (Real.pi - α) / 2 := by linarith
  have hy2 : (Real.pi - α) / 2 < Real.pi / 2 := by linarith
  have key : Real.tan ((Real.pi - α) / 2) < c ↔ (Real.pi - α) / 2 < Real.arctan c := by
    rw [← Real.arctan_lt_arctan_iff, Real.arctan_tan hy1 hy2]
  unfold gAngle
  split_ifs with h
  · rw [angPos_exp_mul_I_of_mem' (by linarith [key.mp h]) (by linarith)]
    ring
  · rw [angPos_exp_mul_I_of_mem (by linarith) (by linarith [not_lt.mp (mt key.mpr h)])]
    ring

/-- The eigen-angle sum of `V` through the eigenvalues of its Cayley transform. -/
theorem eigenAngleSum_eq_sum_cayley {n : Type} [Fintype n] [DecidableEq n] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 2 * Real.pi) {V : Matrix n n ℂ}
    (hdet : (exp ((α : ℂ) * I) • (1 : Matrix n n ℂ) - V).det ≠ 0)
    (hC : (cayleyT (exp ((α : ℂ) * I)) V).IsHermitian) :
    eigenAngleSum V = ∑ k, gAngle α (hC.eigenvalues k) := by
  unfold eigenAngleSum
  rw [roots_charpoly_eq_cayley hdet hC, Multiset.map_map]
  simp only [Function.comp_def, angPos_cayley hα0 hα1]
  rfl

end

end HryniewiczCriterion

/-!
# Leaf C2, part 4: one step of the eigen-angle count

If `A ≤ B ≤ A + ε` as Hermitian forms, then `Σ g(λ(B)) ≤ Σ g(λ(A)) + 2nε` for the normalized
Cayley angle `g = gAngle α`: sorted eigenvalues move up by at most `ε` (Weyl), `arctan` is
1-Lipschitz, and the wrap-around term only decreases.
-/

namespace HryniewiczCriterion

open Matrix Complex

noncomputable section

lemma arctan_sub_le {x y : ℝ} (h : x ≤ y) : Real.arctan y - Real.arctan x ≤ y - x := by
  have hm : Monotone fun z => z - Real.arctan z := by
    have hd : ∀ z, HasDerivAt (fun z => z - Real.arctan z) (1 - 1 / (1 + z ^ 2)) z :=
      fun z => (hasDerivAt_id z).sub (Real.hasDerivAt_arctan z)
    refine monotone_of_deriv_nonneg (fun z => (hd z).differentiableAt) fun z => ?_
    rw [(hd z).deriv]
    have : 1 / (1 + z ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg z]
    linarith
  have := hm h
  simp only at this
  linarith

lemma gAngle_sub_le {α x y ε : ℝ} (hxy : x ≤ y) (hyx : y ≤ x + ε) :
    gAngle α y ≤ gAngle α x + 2 * ε := by
  have h := arctan_sub_le hxy
  unfold gAngle
  split_ifs with h1 h2 h2
  · linarith
  · linarith [Real.pi_pos]
  · exact absurd (h2.trans_le hxy) h1
  · linarith

variable {n : Type} [Fintype n] [DecidableEq n]

lemma sum_eigenvalues_eq_sum_eigenvalues₀ {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ∑ k, f (hA.eigenvalues k) = ∑ j, f (hA.eigenvalues₀ j) := by
  unfold IsHermitian.eigenvalues
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm (fun j => f (hA.eigenvalues₀ j))

/-- One step: `A ≤ B ≤ A + ε` gives `Σ g(λ(B)) ≤ Σ g(λ(A)) + 2 n ε`. -/
theorem sum_gAngle_le_of_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (α ε : ℝ)
    (hAB : ∀ x : n → ℂ, (star x ⬝ᵥ (A *ᵥ x)).re ≤ (star x ⬝ᵥ (B *ᵥ x)).re)
    (hBA : ∀ x : n → ℂ, (star x ⬝ᵥ (B *ᵥ x)).re ≤
      (star x ⬝ᵥ (A *ᵥ x)).re + ε * (star x ⬝ᵥ x).re) :
    ∑ k, gAngle α (hB.eigenvalues k) ≤
      ∑ k, gAngle α (hA.eigenvalues k) + 2 * Fintype.card n * ε := by
  rw [sum_eigenvalues_eq_sum_eigenvalues₀ hA, sum_eigenvalues_eq_sum_eigenvalues₀ hB]
  have hle : ∀ j, gAngle α (hB.eigenvalues₀ j) ≤ gAngle α (hA.eigenvalues₀ j) + 2 * ε := by
    intro j
    refine gAngle_sub_le ?_ ?_
    · have := hA.eigenvalues₀_le_add hB 0 (fun x => by simpa using hAB x) j
      linarith
    · exact hB.eigenvalues₀_le_add hA ε (fun x => hBA x) j
  calc ∑ j, gAngle α (hB.eigenvalues₀ j) ≤ ∑ j, (gAngle α (hA.eigenvalues₀ j) + 2 * ε) :=
        Finset.sum_le_sum fun j _ => hle j
    _ = ∑ j, gAngle α (hA.eigenvalues₀ j) + 2 * Fintype.card n * ε := by
        rw [Finset.sum_add_distrib]; simp; ring

lemma re_star_dotProduct_eigenvectorBasis {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : n) :
    (star ⇑(hA.eigenvectorBasis k) ⬝ᵥ ⇑(hA.eigenvectorBasis k)).re = 1 := by
  have h := hA.eigenvectorBasis.orthonormal.1 k
  have : ‖hA.eigenvectorBasis k‖ ^ 2 = (star ⇑(hA.eigenvectorBasis k) ⬝ᵥ ⇑(hA.eigenvectorBasis k)).re := by
    rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  rw [← this, h, one_pow]

/-- Start of the count: if `0 < B ≤ ε`, the angles at the pole `-1 = e^{iπ}` sum to at most
`2 n ε`. -/
theorem sum_gAngle_pi_le {B : Matrix n n ℂ} (hB : B.IsHermitian) (ε : ℝ)
    (hpos : ∀ x : n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (B *ᵥ x)).re)
    (hle : ∀ x : n → ℂ, (star x ⬝ᵥ (B *ᵥ x)).re ≤ ε * (star x ⬝ᵥ x).re) :
    ∑ k, gAngle Real.pi (hB.eigenvalues k) ≤ 2 * Fintype.card n * ε := by
  have hk : ∀ k, gAngle Real.pi (hB.eigenvalues k) ≤ 2 * ε := by
    intro k
    set v := hB.eigenvectorBasis k
    have hv1 := re_star_dotProduct_eigenvectorBasis hB k
    have hv0 : (⇑v : n → ℂ) ≠ 0 := by
      intro h0; rw [h0] at hv1; simp at hv1
    have he : hB.eigenvalues k = (star ⇑v ⬝ᵥ (B *ᵥ ⇑v)).re := hB.eigenvalues_eq k
    have hc0 : 0 < hB.eigenvalues k := he ▸ hpos _ hv0
    have hc1 : hB.eigenvalues k ≤ ε := by
      have := hle ⇑v; rw [hv1, mul_one, ← he] at this; exact this
    have hat := arctan_sub_le hc0.le
    simp only [Real.arctan_zero, sub_zero] at hat
    unfold gAngle
    rw [sub_self, zero_div, Real.tan_zero, if_pos hc0]
    linarith
  calc ∑ k, gAngle Real.pi (hB.eigenvalues k) ≤ ∑ _k : n, 2 * ε := Finset.sum_le_sum fun k _ => hk k
    _ = 2 * Fintype.card n * ε := by simp; ring

end

end HryniewiczCriterion

/-!
# Leaf C2, part 5: the Cayley transform of a positive unitary path is increasing

If `V' = i Q V` with `Q > 0`, then `C(t) = 2 i a (a - V(t))⁻¹ - i` has
`C' = 2 (a - V)⁻¹ Q (a - V)⁻ᴴ > 0`, so `t ↦ re ⟪x, C(t) x⟫` has positive derivative.
-/

namespace HryniewiczCriterion

open Matrix Complex Filter Topology

open scoped ComplexOrder

noncomputable section

variable {n : Type} [Fintype n] [DecidableEq n]

lemma differentiableAt_det_entries {M : ℝ → Matrix n n ℂ} {t : ℝ}
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) :
    DifferentiableAt ℝ (fun s => (M s).det) t := by
  simp only [Matrix.det_apply']
  fun_prop

/-- Entrywise derivative of the inverse of a path of complex matrices. -/
theorem hasDerivAt_inv_entry {M : ℝ → Matrix n n ℂ} {M' : Matrix n n ℂ} {t : ℝ}
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) t) (ht : (M t).det ≠ 0) (i j : n) :
    HasDerivAt (fun s => (M s)⁻¹ i j) ((-((M t)⁻¹ * M' * (M t)⁻¹)) i j) t := by
  have hMd : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t := fun a b => (hM a b).differentiableAt
  have hinv : ∀ a b, DifferentiableAt ℝ (fun s => (M s)⁻¹ a b) t := by
    intro a b
    simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
      Matrix.adjugate_apply]
    refine ((differentiableAt_det_entries hMd).inv ht).mul
      (differentiableAt_det_entries fun r c => ?_)
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact differentiableAt_const _
    · exact hMd r c
  set D : Matrix n n ℂ := Matrix.of fun a b => deriv (fun s => (M s)⁻¹ a b) t with hD
  have hDd : ∀ a b, HasDerivAt (fun s => (M s)⁻¹ a b) (D a b) t := fun a b => (hinv a b).hasDerivAt
  have hev : ∀ᶠ s in 𝓝 t, (M s).det ≠ 0 :=
    (differentiableAt_det_entries hMd).continuousAt.eventually_ne ht
  have hprod : ∀ a b, HasDerivAt (fun s => (M s * (M s)⁻¹) a b) ((M' * (M t)⁻¹ + M t * D) a b) t := by
    intro a b
    simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
    exact HasDerivAt.fun_sum fun k _ => (hM a k).mul (hDd k b)
  have hone : ∀ a b, HasDerivAt (fun s => (M s * (M s)⁻¹) a b) 0 t := by
    intro a b
    refine (hasDerivAt_const t ((1 : Matrix n n ℂ) a b)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs)]
  have heq : M' * (M t)⁻¹ + M t * D = 0 := by
    ext a b; exact (hprod a b).unique (hone a b)
  have hu : IsUnit (M t).det := isUnit_iff_ne_zero.mpr ht
  have key : D = -((M t)⁻¹ * M' * (M t)⁻¹) := by
    have h2 : M t * D = -(M' * (M t)⁻¹) := eq_neg_of_add_eq_zero_right heq
    calc D = (M t)⁻¹ * (M t * D) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = -((M t)⁻¹ * M' * (M t)⁻¹) := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]
  rw [← key]
  exact hDd i j

/-- Derivative of the quadratic form of the Cayley transform along a path. -/
lemma hasDerivAt_quad_cayleyT {a : ℂ} {V : ℝ → Matrix n n ℂ} {V' : Matrix n n ℂ} {u : ℝ}
    (hd : ∀ i j, HasDerivAt (fun s => V s i j) (V' i j) u)
    (hdet : (a • (1 : Matrix n n ℂ) - V u).det ≠ 0) (x : n → ℂ) :
    HasDerivAt (fun s => star x ⬝ᵥ (cayleyT a (V s) *ᵥ x))
      (star x ⬝ᵥ (((2 * I * a) • ((a • (1 : Matrix n n ℂ) - V u)⁻¹ * V' *
        (a • (1 : Matrix n n ℂ) - V u)⁻¹)) *ᵥ x)) u := by
  have hM : ∀ i j, HasDerivAt (fun s => (a • (1 : Matrix n n ℂ) - V s) i j) ((-V') i j) u := by
    intro i j
    exact ((hasDerivAt_const u ((a • (1 : Matrix n n ℂ)) i j)).sub (hd i j)).congr_deriv (by simp)
  have hinv := hasDerivAt_inv_entry hM hdet
  have hC : ∀ i j, HasDerivAt (fun s => cayleyT a (V s) i j)
      (((2 * I * a) • ((a • (1 : Matrix n n ℂ) - V u)⁻¹ * V' *
        (a • (1 : Matrix n n ℂ) - V u)⁻¹)) i j) u := by
    intro i j
    exact (((hinv i j).const_mul (2 * I * a)).sub_const ((I • (1 : Matrix n n ℂ)) i j)).congr_deriv
      (by simp [Matrix.mul_neg, Matrix.neg_mul])
  simp only [dotProduct, mulVec]
  refine HasDerivAt.fun_sum fun i _ => ?_
  refine HasDerivAt.const_mul _ ?_
  exact HasDerivAt.fun_sum fun j _ => (hC i j).mul_const (x j)

/-- `C' = 2 (a - V)⁻¹ Q (a - V)⁻ᴴ` for `V' = i Q V`. -/
lemma cayley_deriv_eq {a : ℂ} {V Q : Matrix n n ℂ} (hV : star V * V = 1) (ha : star a * a = 1)
    (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) :
    (2 * I * a) • ((a • (1 : Matrix n n ℂ) - V)⁻¹ * (I • (Q * V)) * (a • (1 : Matrix n n ℂ) - V)⁻¹)
      = (2 : ℂ) • ((a • (1 : Matrix n n ℂ) - V)⁻¹ * Q * (a • (1 : Matrix n n ℂ) - V)⁻¹ᴴ) := by
  rw [inv_conjTranspose_sub hV ha hdet]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  congr 1
  ring_nf
  rw [I_sq]; ring

lemma re_quad_cayley_deriv_pos {a : ℂ} {V Q : Matrix n n ℂ} (hQ : Q.PosDef)
    (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) {x : n → ℂ} (hx : x ≠ 0) :
    0 < (star x ⬝ᵥ (((2 : ℂ) • ((a • (1 : Matrix n n ℂ) - V)⁻¹ * Q *
      (a • (1 : Matrix n n ℂ) - V)⁻¹ᴴ)) *ᵥ x)).re := by
  set M := a • (1 : Matrix n n ℂ) - V
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  set y := M⁻¹ᴴ *ᵥ x
  have hy : y ≠ 0 := by
    intro h
    have : Mᴴ *ᵥ y = x := by
      simp only [y, mulVec_mulVec]
      rw [← conjTranspose_mul, nonsing_inv_mul _ hM, conjTranspose_one, one_mulVec]
    rw [h, mulVec_zero] at this
    exact hx this.symm
  have he : star x ⬝ᵥ (((2 : ℂ) • (M⁻¹ * Q * M⁻¹ᴴ)) *ᵥ x) = 2 * (star y ⬝ᵥ (Q *ᵥ y)) := by
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    congr 1
    simp only [y, star_mulVec, conjTranspose_conjTranspose, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_vecMul]
  rw [he, show ((2 : ℂ) * (star y ⬝ᵥ (Q *ᵥ y))).re = 2 * (star y ⬝ᵥ (Q *ᵥ y)).re by simp]
  have := hQ.re_dotProduct_pos hy
  simp only [RCLike.re_to_complex] at this
  linarith

end

end HryniewiczCriterion

/-!
# Leaf C2, part 6: auxiliary facts for the assembly

* `abs_re_quad_le`: `|re ⟪x, D x⟫| ≤ (Σᵢⱼ |Dᵢⱼ|) ‖x‖²`.
* `exists_int_sub_eigenAngleSum`: `θ - eigenAngleSum V ∈ 2πℤ` when `e^{iθ} = det V`, `V` unitary.
* `exists_angle_det_ne_zero`: some `e^{iα}`, `α ∈ (0, 2π)`, is not an eigenvalue.
* `monotoneOn_Icc_of_local`: a function that is monotone on a neighbourhood (in `[0, T]`) of
  every point of `[0, T]` is monotone on `[0, T]` (Lebesgue number lemma).
-/

namespace HryniewiczCriterion

open Matrix Complex Filter Topology Set

noncomputable section

variable {n : Type} [Fintype n] [DecidableEq n]

lemma abs_re_quad_le (D : Matrix n n ℂ) (x : n → ℂ) :
    |(star x ⬝ᵥ (D *ᵥ x)).re| ≤ (∑ i, ∑ j, ‖D i j‖) * (star x ⬝ᵥ x).re := by
  have hS : (star x ⬝ᵥ x).re = ∑ k, ‖x k‖ ^ 2 := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  have hpair : ∀ i j, ‖x i‖ * ‖x j‖ ≤ ∑ k, ‖x k‖ ^ 2 := by
    intro i j
    have hi : ‖x i‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
    have hj : ‖x j‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
    nlinarith [sq_nonneg (‖x i‖ - ‖x j‖)]
  rw [hS]
  calc |(star x ⬝ᵥ (D *ᵥ x)).re| ≤ ‖star x ⬝ᵥ (D *ᵥ x)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ∑ j, ‖D i j‖ * (‖x i‖ * ‖x j‖) := by
        simp only [dotProduct, mulVec, Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => le_of_eq ?_)
        rw [norm_mul, norm_mul, Pi.star_apply, norm_star]
        ring
    _ ≤ ∑ i, ∑ j, ‖D i j‖ * ∑ k, ‖x k‖ ^ 2 := by
        gcongr with i _ j _
        exact hpair i j
    _ = (∑ i, ∑ j, ‖D i j‖) * ∑ k, ‖x k‖ ^ 2 := by
        rw [Finset.sum_mul]; simp_rw [Finset.sum_mul]

lemma norm_det_eq_one {V : Matrix n n ℂ} (hV : star V * V = 1) : ‖V.det‖ = 1 := by
  have h := congr_arg Matrix.det hV
  rw [det_mul, star_eq_conjTranspose, det_conjTranspose, det_one, Complex.star_def,
    Complex.conj_mul'] at h
  have h2 : ‖V.det‖ ^ 2 = 1 := by exact_mod_cast h
  have h0 := norm_nonneg V.det
  nlinarith [sq_nonneg (‖V.det‖ - 1)]

lemma exists_int_sub_eigenAngleSum {V : Matrix n n ℂ} (hV : star V * V = 1) {θ : ℝ}
    (hθ : V.det = exp ((θ : ℂ) * I)) :
    ∃ k : ℤ, θ - eigenAngleSum V = 2 * Real.pi * k := by
  have h := exp_eigenAngleSum_mul_I V (norm_det_eq_one hV)
  rw [hθ, exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨-k, ?_⟩
  have := congr_arg Complex.im hk
  simp at this
  push_cast
  linarith

lemma exists_angle_det_ne_zero (W : Matrix n n ℂ) :
    ∃ α ∈ Ioo 0 (2 * Real.pi), (exp ((α : ℂ) * I) • (1 : Matrix n n ℂ) - W).det ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  set f : ℝ → ℂ := fun α => exp ((α : ℂ) * I)
  have hinj : InjOn f (Ioo 0 (2 * Real.pi)) := by
    intro α hα β hβ h
    obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.mp h
    have him := congr_arg Complex.im hk
    simp at him
    have hk0 : k = 0 := by
      have h1 : (k : ℝ) < 1 := by
        by_contra h'; push_neg at h'
        nlinarith [hα.1, hα.2, hβ.1, hβ.2, Real.pi_pos]
      have h2 : (-1 : ℝ) < k := by
        by_contra h'; push_neg at h'
        nlinarith [hα.1, hα.2, hβ.1, hβ.2, Real.pi_pos]
      have : k < 1 := by exact_mod_cast h1
      have : -1 < k := by exact_mod_cast h2
      omega
    rw [hk0] at him; simp at him; linarith
  have hsub : f '' Ioo 0 (2 * Real.pi) ⊆ (W.charpoly.roots.toFinset : Set ℂ) := by
    rintro _ ⟨α, hα, rfl⟩
    have hz := hcon α hα
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots (Matrix.charpoly_monic W).ne_zero, Polynomial.IsRoot,
      eval_charpoly, scalar_apply, ← smul_one_eq_diagonal]
    exact hz
  exact Set.Ioo_infinite (by linarith [Real.pi_pos] : (0 : ℝ) < 2 * Real.pi)
    (Set.Finite.of_finite_image ((Finset.finite_toSet _).subset hsub) hinj)

/-- Local monotonicity on `[0, T]` implies monotonicity (Lebesgue number lemma). -/
theorem monotoneOn_Icc_of_local {E : ℝ → ℝ} {T : ℝ}
    (h : ∀ t0 ∈ Icc 0 T, ∃ δ > 0, ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T →
      |s - t0| < δ → |t - t0| < δ → s ≤ t → E s ≤ E t) :
    MonotoneOn E (Icc 0 T) := by
  choose! δ hδ hloc using h
  obtain ⟨r, hr, hcov⟩ := lebesgue_number_lemma_of_metric (c := fun t0 : Icc (0 : ℝ) T =>
      Metric.ball (t0 : ℝ) (δ t0)) isCompact_Icc (fun _ => Metric.isOpen_ball)
    (fun t ht => Set.mem_iUnion.mpr ⟨⟨t, ht⟩, Metric.mem_ball_self (hδ t ht)⟩)
  have close : ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t → t - s < r → E s ≤ E t := by
    intro s t hs ht hst hlt
    obtain ⟨⟨t0, ht0⟩, hball⟩ := hcov s hs
    have hs' := hball (Metric.mem_ball_self hr)
    have ht' := hball (show t ∈ Metric.ball s r by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    simp only [Metric.mem_ball, Real.dist_eq] at hs' ht'
    exact hloc t0 ht0 s t hs ht hs' ht' hst
  have step : ∀ k : ℕ, ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t → t - s < k * (r / 2) →
      E s ≤ E t := by
    intro k
    induction k with
    | zero => intro s t _ _ hst hlt; simp at hlt; linarith
    | succ k ih =>
      intro s t hs ht hst hlt
      by_cases hc : t - s < r / 2
      · exact close s t hs ht hst (by linarith)
      · push_neg at hc
        have hu : s + r / 2 ∈ Icc 0 T := ⟨by linarith [hs.1], by linarith [ht.2]⟩
        refine (close s (s + r / 2) hs hu (by linarith) (by linarith)).trans
          (ih (s + r / 2) t hu ht (by linarith) ?_)
        push_cast at hlt; linarith
  intro s hs t ht hst
  obtain ⟨k, hk⟩ := exists_nat_gt (T / (r / 2))
  refine step k s t hs ht hst ?_
  have : T < k * (r / 2) := by rwa [div_lt_iff₀ (by linarith)] at hk
  linarith [hs.1, ht.2]

end

end HryniewiczCriterion

/-!
# Leaf C2: eigen-angle sum of a positive unitary path

Near any time, pick a pole `a = e^{iα}` that is not an eigenvalue; the Cayley transform `C(t)` is
Hermitian and increasing, so its sorted eigenvalues increase by at most `ε` over a short step
(Weyl), and `E(t) = θ(t) - eigenAngleSum V(t) ∈ 2πℤ` cannot decrease. At `t = 0⁺` (pole `-1`)
all eigenvalues of `C` are small and positive, so `E = 0` there.
-/

namespace HryniewiczCriterion

open Matrix Complex Filter Topology Set

open scoped ComplexOrder

noncomputable section

variable {n : Type} [Fintype n] [DecidableEq n]

lemma continuousAt_cayleyT_entry {a : ℂ} {V : ℝ → Matrix n n ℂ} {V' : Matrix n n ℂ} {u : ℝ}
    (hd : ∀ i j, HasDerivAt (fun s => V s i j) (V' i j) u)
    (hdet : (a • (1 : Matrix n n ℂ) - V u).det ≠ 0) (i j : n) :
    ContinuousAt (fun s => cayleyT a (V s) i j) u := by
  have hM : ∀ i j, HasDerivAt (fun s => (a • (1 : Matrix n n ℂ) - V s) i j) ((-V') i j) u := by
    intro i j
    exact ((hasDerivAt_const u ((a • (1 : Matrix n n ℂ)) i j)).sub (hd i j)).congr_deriv (by simp)
  exact (((hasDerivAt_inv_entry hM hdet i j).continuousAt.const_mul (2 * I * a)).sub
    continuousAt_const : _)

lemma window_core {V Q : ℝ → Matrix n n ℂ} {T : ℝ}
    (hd : ∀ t ∈ Icc 0 T, ∀ i j : n,
      HasDerivAt (fun s => V s i j) ((Complex.I • (Q t * V t)) i j) t)
    {θ : ℝ → ℝ} (hθc : ContinuousOn θ (Icc 0 T)) {t0 : ℝ} (ht0 : t0 ∈ Icc 0 T) {a : ℂ}
    (hdet0 : (a • (1 : Matrix n n ℂ) - V t0).det ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ u ∈ Icc 0 T, |u - t0| < δ → (a • (1 : Matrix n n ℂ) - V u).det ≠ 0 ∧
      |θ u - θ t0| < η ∧ ∀ i j, ‖cayleyT a (V u) i j - cayleyT a (V t0) i j‖ < η := by
  have hdetc : ContinuousAt (fun s => (a • (1 : Matrix n n ℂ) - V s).det) t0 :=
    (differentiableAt_det_entries fun i j =>
      ((hasDerivAt_const t0 ((a • (1 : Matrix n n ℂ)) i j)).sub
        (hd t0 ht0 i j)).differentiableAt).continuousAt
  have e1 : ∀ᶠ u in 𝓝 t0, (a • (1 : Matrix n n ℂ) - V u).det ≠ 0 := hdetc.eventually_ne hdet0
  have e2 : ∀ᶠ u in 𝓝 t0, ∀ i j, ‖cayleyT a (V u) i j - cayleyT a (V t0) i j‖ < η := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    have := (continuousAt_cayleyT_entry (hd t0 ht0) hdet0 i j).eventually
      (Metric.ball_mem_nhds _ hη)
    filter_upwards [this] with u hu
    simpa [Metric.mem_ball, dist_eq_norm] using hu
  have e3 : ∀ᶠ u in 𝓝[Icc 0 T] t0, |θ u - θ t0| < η := by
    have := (hθc t0 ht0) (Metric.ball_mem_nhds _ hη)
    filter_upwards [this] with u hu
    rwa [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hu
  have e : ∀ᶠ u in 𝓝 t0, u ∈ Icc 0 T →
      ((a • (1 : Matrix n n ℂ) - V u).det ≠ 0 ∧
        ∀ i j, ‖cayleyT a (V u) i j - cayleyT a (V t0) i j‖ < η) ∧ |θ u - θ t0| < η := by
    have := ((e1.and e2).filter_mono nhdsWithin_le_nhds).and e3
    exact eventually_nhdsWithin_iff.mp (this.mono fun u hu => hu)
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.mp e
  refine ⟨δ, hδ, fun u hu hut => ?_⟩
  have := h (by rwa [Real.dist_eq]) hu
  exact ⟨this.1.1, this.2, this.1.2⟩

lemma quad_strictMonoOn {V Q : ℝ → Matrix n n ℂ} {T : ℝ}
    (hU : ∀ t ∈ Icc 0 T, star (V t) * V t = 1)
    (hQ : ∀ t ∈ Icc 0 T, (Q t).PosDef)
    (hd : ∀ t ∈ Icc 0 T, ∀ i j : n,
      HasDerivAt (fun s => V s i j) ((Complex.I • (Q t * V t)) i j) t)
    {a : ℂ} (ha : star a * a = 1) {D : Set ℝ} (hDc : Convex ℝ D) (hDs : D ⊆ Icc 0 T)
    (hDdet : ∀ u ∈ D, (a • (1 : Matrix n n ℂ) - V u).det ≠ 0) {x : n → ℂ} (hx : x ≠ 0) :
    StrictMonoOn (fun u => (star x ⬝ᵥ (cayleyT a (V u) *ᵥ x)).re) D := by
  have hder : ∀ u ∈ D, HasDerivAt (fun u => (star x ⬝ᵥ (cayleyT a (V u) *ᵥ x)).re)
      ((star x ⬝ᵥ (((2 : ℂ) • ((a • (1 : Matrix n n ℂ) - V u)⁻¹ * Q u *
        (a • (1 : Matrix n n ℂ) - V u)⁻¹ᴴ)) *ᵥ x)).re) u := by
    intro u hu
    have h1 := hasDerivAt_quad_cayleyT (hd u (hDs hu)) (hDdet u hu) x
    rw [cayley_deriv_eq (hU u (hDs hu)) ha (hDdet u hu)] at h1
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt u h1
  refine strictMonoOn_of_hasDerivWithinAt_pos hDc
    (fun u hu => (hder u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hder u (interior_subset hu)).hasDerivWithinAt) (fun u hu => ?_)
  exact re_quad_cayley_deriv_pos (hQ u (hDs (interior_subset hu)))
    (hDdet u (interior_subset hu)) hx

lemma int_step {x y : ℝ} {k l : ℤ} (hx : x = 2 * Real.pi * k) (hy : y = 2 * Real.pi * l)
    (h : -(2 * Real.pi) < y - x) : x ≤ y := by
  have hpi := Real.pi_pos
  have h1 : (-1 : ℝ) < (l - k : ℤ) := by
    push_cast
    by_contra h'; push_neg at h'
    nlinarith
  have h2 : (-1 : ℤ) < l - k := by exact_mod_cast h1
  have h3 : (k : ℝ) ≤ l := by exact_mod_cast (show k ≤ l by omega)
  rw [hx, hy]; nlinarith

lemma sum_entries_le {D : Matrix n n ℂ} {c : ℝ} (h : ∀ i j, ‖D i j‖ ≤ c) :
    ∑ i, ∑ j, ‖D i j‖ ≤ (Fintype.card n : ℝ) ^ 2 * c := by
  calc ∑ i, ∑ j, ‖D i j‖ ≤ ∑ _i : n, ∑ _j : n, c := by gcongr with i _ j _; exact h i j
    _ = _ := by simp; ring

/-- Local monotonicity of `θ - eigenAngleSum V` near `t0`, at a pole `e^{iα}` that is not an
eigenvalue of `V t0`. -/
theorem window_monotone {V Q : ℝ → Matrix n n ℂ} {T : ℝ}
    (hU : ∀ t ∈ Icc 0 T, star (V t) * V t = 1)
    (hQ : ∀ t ∈ Icc 0 T, (Q t).PosDef)
    (hd : ∀ t ∈ Icc 0 T, ∀ i j : n,
      HasDerivAt (fun s => V s i j) ((Complex.I • (Q t * V t)) i j) t)
    {θ : ℝ → ℝ} (hθc : ContinuousOn θ (Icc 0 T))
    (hθd : ∀ t ∈ Icc 0 T, (V t).det = Complex.exp ((θ t : ℂ) * Complex.I))
    {t0 : ℝ} (ht0 : t0 ∈ Icc 0 T) {α : ℝ} (hα : α ∈ Ioo 0 (2 * Real.pi))
    (hdet0 : (exp ((α : ℂ) * I) • (1 : Matrix n n ℂ) - V t0).det ≠ 0) :
    ∃ δ > 0, ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T → |s - t0| < δ → |t - t0| < δ → s ≤ t →
      θ s - eigenAngleSum (V s) ≤ θ t - eigenAngleSum (V t) := by
  set a := exp ((α : ℂ) * I)
  have ha : star a * a = 1 := by
    rw [Complex.star_def, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]; simp
  set m : ℝ := (Fintype.card n : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  set η : ℝ := 1 / (2 * m ^ 3 + 2)
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hw⟩ := window_core hd hθc ht0 hdet0 hη
  set D := Icc 0 T ∩ Metric.ball t0 δ
  have hDc : Convex ℝ D := (convex_Icc 0 T).inter (convex_ball t0 δ)
  have hDs : D ⊆ Icc 0 T := inter_subset_left
  have hmemD : ∀ u ∈ Icc 0 T, |u - t0| < δ → u ∈ D := fun u hu h =>
    ⟨hu, by rwa [Metric.mem_ball, Real.dist_eq]⟩
  have hDdet : ∀ u ∈ D, (a • (1 : Matrix n n ℂ) - V u).det ≠ 0 := fun u hu =>
    (hw u hu.1 (by have := hu.2; rwa [Metric.mem_ball, Real.dist_eq] at this)).1
  refine ⟨δ, hδ, fun s t hs ht hs0 ht0' hst => ?_⟩
  obtain ⟨hdets, hθs, hCs0⟩ := hw s hs hs0
  obtain ⟨hdett, hθt, hCt0⟩ := hw t ht ht0'
  have hCs := cayleyT_isHermitian (hU s hs) ha hdets
  have hCt := cayleyT_isHermitian (hU t ht) ha hdett
  set ε : ℝ := m ^ 2 * (2 * η)
  have hAB : ∀ x : n → ℂ, (star x ⬝ᵥ (cayleyT a (V s) *ᵥ x)).re ≤
      (star x ⬝ᵥ (cayleyT a (V t) *ᵥ x)).re := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (quad_strictMonoOn hU hQ hd ha hDc hDs hDdet hx).monotoneOn
        (hmemD s hs hs0) (hmemD t ht ht0') hst
  have hBA : ∀ x : n → ℂ, (star x ⬝ᵥ (cayleyT a (V t) *ᵥ x)).re ≤
      (star x ⬝ᵥ (cayleyT a (V s) *ᵥ x)).re + ε * (star x ⬝ᵥ x).re := by
    intro x
    have hq := abs_re_quad_le (cayleyT a (V t) - cayleyT a (V s)) x
    have hsum : ∑ i, ∑ j, ‖(cayleyT a (V t) - cayleyT a (V s)) i j‖ ≤ ε := by
      refine (sum_entries_le fun i j => ?_).trans le_rfl
      rw [Matrix.sub_apply]
      calc ‖cayleyT a (V t) i j - cayleyT a (V s) i j‖
          ≤ ‖cayleyT a (V t) i j - cayleyT a (V t0) i j‖ +
            ‖cayleyT a (V t0) i j - cayleyT a (V s) i j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 2 * η := by
          rw [norm_sub_rev (cayleyT a (V t0) i j)]
          linarith [hCs0 i j, hCt0 i j]
    have hxx : 0 ≤ (star x ⬝ᵥ x).re := by
      have := (abs_re_quad_le (1 : Matrix n n ℂ) x)
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_nonneg fun k _ => ?_
      rw [Complex.star_def, Complex.conj_mul']; norm_cast; positivity
    rw [sub_mulVec, dotProduct_sub, Complex.sub_re] at hq
    have := (abs_le.mp hq).2
    nlinarith
  have hstep := sum_gAngle_le_of_le hCs hCt α ε hAB hBA
  rw [← eigenAngleSum_eq_sum_cayley hα.1 hα.2 hdets hCs,
    ← eigenAngleSum_eq_sum_cayley hα.1 hα.2 hdett hCt] at hstep
  obtain ⟨k, hk⟩ := exists_int_sub_eigenAngleSum (hU s hs) (hθd s hs)
  obtain ⟨l, hl⟩ := exists_int_sub_eigenAngleSum (hU t ht) (hθd t ht)
  refine int_step hk hl ?_
  have hθst : -(2 * η) < θ t - θ s := by
    rw [abs_lt] at hθs hθt; linarith [hθs.1, hθs.2, hθt.1, hθt.2]
  have hη2 : (2 + 4 * m ^ 3) * η ≤ 2 := by
    rw [show (2 + 4 * m ^ 3) * η = (2 + 4 * m ^ 3) / (2 * m ^ 3 + 2) by simp [η]; ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  have : 2 * m * ε = 4 * m ^ 3 * η := by simp only [ε]; ring
  nlinarith [Real.two_le_pi]

lemma cayleyT_neg_one_one : cayleyT (-1 : ℂ) (1 : Matrix n n ℂ) = 0 := by
  have hinv : ((-1 : ℂ) • (1 : Matrix n n ℂ) - 1)⁻¹ = (-(1 / 2 : ℂ)) • (1 : Matrix n n ℂ) := by
    apply inv_eq_right_inv
    rw [show (-1 : ℂ) • (1 : Matrix n n ℂ) - 1 = (-2 : ℂ) • 1 by
      rw [sub_eq_add_neg, ← neg_one_smul ℂ (1 : Matrix n n ℂ), ← add_smul]; norm_num]
    rw [smul_mul_smul, Matrix.one_mul]; norm_num
  rw [cayleyT, hinv, smul_smul]
  norm_num
  rw [show 2 * I * (1 / 2 : ℂ) = I by ring, sub_self]

/-- Start: `θ - eigenAngleSum V ≥ 0` for small `t > 0`. -/
theorem start_nonneg {V Q : ℝ → Matrix n n ℂ} {T : ℝ} (hT : 0 < T) (h0 : V 0 = 1)
    (hU : ∀ t ∈ Icc 0 T, star (V t) * V t = 1)
    (hQ : ∀ t ∈ Icc 0 T, (Q t).PosDef)
    (hd : ∀ t ∈ Icc 0 T, ∀ i j : n,
      HasDerivAt (fun s => V s i j) ((Complex.I • (Q t * V t)) i j) t)
    {θ : ℝ → ℝ} (hθc : ContinuousOn θ (Icc 0 T)) (hθ0 : θ 0 = 0)
    (hθd : ∀ t ∈ Icc 0 T, (V t).det = Complex.exp ((θ t : ℂ) * Complex.I)) :
    ∃ δ > 0, ∀ t ∈ Icc 0 T, 0 < t → t < δ → 0 ≤ θ t - eigenAngleSum (V t) := by
  set a := exp ((Real.pi : ℂ) * I)
  have ha1 : a = -1 := exp_pi_mul_I
  have ha : star a * a = 1 := by rw [ha1]; simp
  have h00 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hdet0 : (a • (1 : Matrix n n ℂ) - V 0).det ≠ 0 := by
    rw [h0, ha1, show (-1 : ℂ) • (1 : Matrix n n ℂ) - 1 = (-2 : ℂ) • 1 by
      rw [sub_eq_add_neg, ← neg_one_smul ℂ (1 : Matrix n n ℂ), ← add_smul]; norm_num,
      det_smul, det_one, mul_one]
    exact pow_ne_zero _ (by norm_num)
  have hC0 : cayleyT a (V 0) = 0 := by rw [h0, ha1]; exact cayleyT_neg_one_one
  set m : ℝ := (Fintype.card n : ℝ)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  set η : ℝ := 1 / (2 * m ^ 3 + 2)
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hw⟩ := window_core hd hθc h00 hdet0 hη
  set D := Icc 0 T ∩ Metric.ball 0 δ
  have hDc : Convex ℝ D := (convex_Icc 0 T).inter (convex_ball 0 δ)
  have hDs : D ⊆ Icc 0 T := inter_subset_left
  have hDdet : ∀ u ∈ D, (a • (1 : Matrix n n ℂ) - V u).det ≠ 0 := fun u hu =>
    (hw u hu.1 (by have := hu.2; rwa [Metric.mem_ball, Real.dist_eq] at this)).1
  refine ⟨δ, hδ, fun t ht htpos htδ => ?_⟩
  have htδ' : |t - 0| < δ := by rw [sub_zero, abs_of_pos htpos]; exact htδ
  obtain ⟨hdett, hθt, hCt0⟩ := hw t ht htδ'
  have hCt := cayleyT_isHermitian (hU t ht) ha hdett
  have hpos : ∀ x : n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (cayleyT a (V t) *ᵥ x)).re := by
    intro x hx
    have := (quad_strictMonoOn hU hQ hd ha hDc hDs hDdet hx)
      ⟨h00, Metric.mem_ball_self hδ⟩
      ⟨ht, by rwa [Metric.mem_ball, Real.dist_eq]⟩ htpos
    simpa [hC0] using this
  set ε : ℝ := m ^ 2 * η
  have hle : ∀ x : n → ℂ, (star x ⬝ᵥ (cayleyT a (V t) *ᵥ x)).re ≤ ε * (star x ⬝ᵥ x).re := by
    intro x
    have hq := abs_re_quad_le (cayleyT a (V t)) x
    have hsum : ∑ i, ∑ j, ‖cayleyT a (V t) i j‖ ≤ ε :=
      sum_entries_le fun i j => by
        have := hCt0 i j; rw [hC0, Matrix.zero_apply, sub_zero] at this; exact this.le
    have hxx : 0 ≤ (star x ⬝ᵥ x).re := by
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_nonneg fun k _ => ?_
      rw [Complex.star_def, Complex.conj_mul']; norm_cast; positivity
    have := (abs_le.mp hq).2
    nlinarith
  have hS := sum_gAngle_pi_le hCt ε hpos hle
  rw [← eigenAngleSum_eq_sum_cayley (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    hdett hCt] at hS
  obtain ⟨k, hk⟩ := exists_int_sub_eigenAngleSum (hU t ht) (hθd t ht)
  have hk0 : (0 : ℝ) = 2 * Real.pi * (0 : ℤ) := by simp
  refine sub_nonneg.mpr ?_
  have := int_step hk0 hk ?_
  · linarith
  · rw [hθ0, sub_zero, abs_lt] at hθt
    have hη2 : (1 + 2 * m ^ 3) * η ≤ 1 := by
      rw [show (1 + 2 * m ^ 3) * η = (1 + 2 * m ^ 3) / (2 * m ^ 3 + 2) by simp [η]; ring,
        div_le_iff₀ (by positivity)]
      nlinarith
    have : 2 * m * ε = 2 * m ^ 3 * η := by simp only [ε]; ring
    nlinarith [Real.two_le_pi]

theorem positive_unitary_path_eigenAngleSum_le' {n : Type} [Fintype n] [DecidableEq n]
    (V Q : ℝ → Matrix n n ℂ) (T : ℝ) (hT : 0 < T) (h0 : V 0 = 1)
    (hU : ∀ t ∈ Set.Icc 0 T, star (V t) * V t = 1)
    (hQ : ∀ t ∈ Set.Icc 0 T, (Q t).PosDef)
    (hd : ∀ t ∈ Set.Icc 0 T, ∀ i j : n,
      HasDerivAt (fun s => V s i j) ((Complex.I • (Q t * V t)) i j) t)
    (θ : ℝ → ℝ) (hθ : IsDetAngleLift V T θ) :
    eigenAngleSum (V T) ≤ θ T := by
  obtain ⟨hθc, hθ0, hθd⟩ := hθ
  have hmono : MonotoneOn (fun t => θ t - eigenAngleSum (V t)) (Icc 0 T) := by
    refine monotoneOn_Icc_of_local fun t0 ht0 => ?_
    obtain ⟨α, hα, hdet⟩ := exists_angle_det_ne_zero (V t0)
    exact window_monotone hU hQ hd hθc hθd ht0 hα hdet
  obtain ⟨δ, hδ, hstart⟩ := start_nonneg hT h0 hU hQ hd hθc hθ0 hθd
  set t1 := min (δ / 2) T
  have ht1 : t1 ∈ Icc 0 T := ⟨by positivity, min_le_right _ _⟩
  have ht1pos : 0 < t1 := by positivity
  have h1 := hstart t1 ht1 ht1pos (by
    calc t1 ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith)
  have h2 := hmono ht1 ⟨hT.le, le_rfl⟩ (min_le_right _ _)
  simp only at h2
  linarith

end

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution {n : Type} [Fintype n] [DecidableEq n]
    (V Q : ℝ → Matrix n n ℂ) (T : ℝ) (hT : 0 < T) (h0 : V 0 = 1)
    (hU : ∀ t ∈ Set.Icc 0 T, star (V t) * V t = 1)
    (hQ : ∀ t ∈ Set.Icc 0 T, (Q t).PosDef)
    (hd : ∀ t ∈ Set.Icc 0 T, ∀ i j : n,
      HasDerivAt (fun s => V s i j) ((Complex.I • (Q t * V t)) i j) t)
    (θ : ℝ → ℝ) (hθ : IsDetAngleLift V T θ) :
    eigenAngleSum (V T) ≤ θ T :=
  positive_unitary_path_eigenAngleSum_le' V Q T hT h0 hU hQ hd θ hθ
