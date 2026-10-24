-- Prove2me | solution 1 for OAI.Problem315.switch_chain_tv_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:14:08.591024+00:00
-- url     : https://prove2.me/submissions/3f47394c-6400-4489-9dbc-8dc7d990bbc0

import Mathlib
import Definitions.Def_SwitchChain
import Definitions.Def_OAIQWSWC002
import Theorems.Thm_OAI_Problem315_switch_chain_main

section
-- module Solutions.OAIQW_Problem315.FiniteKernelAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiniteKernel

variable {α : Type*} [Fintype α]

theorem weighted_sq_sum_le
    (w f : α → ℝ)
    (hpos : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    (∑ i, w i * f i) ^ 2 ≤ ∑ i, w i * f i ^ 2 := by
  let m := ∑ i, w i * f i
  have hvar : 0 ≤ ∑ i, w i * (f i - m) ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hpos i) (sq_nonneg _))
  have heq : (∑ i, w i * (f i - m) ^ 2) =
      (∑ i, w i * f i ^ 2) - m ^ 2 := by
    calc
      (∑ i, w i * (f i - m) ^ 2) =
          ∑ i, (w i * f i ^ 2 - 2 * m * (w i * f i) + w i * m ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, w i * f i ^ 2) - m ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, hsum]
        change (∑ i, w i * f i ^ 2) - 2 * m * m + 1 * m ^ 2 = _
        ring
  rw [heq] at hvar
  dsimp [m] at hvar
  linarith

theorem sq_sum_apply_le
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hpos : ∀ i j, 0 ≤ K i j)
    (f : α → ℝ) :
    (∑ i, (∑ j, K i j * f j) ^ 2) ≤ ∑ i, f i ^ 2 := by
  have hcol (j : α) : ∑ i, K i j = 1 := by
    simpa only [hsymm] using hrow j
  calc
    (∑ i, (∑ j, K i j * f j) ^ 2) ≤ ∑ i, ∑ j, K i j * f j ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact weighted_sq_sum_le (K i) f (hpos i) (hrow i)
    _ = ∑ i, f i ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul, hcol, one_mul]

theorem lazy_sq_sum_apply_le_inner
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hpos : ∀ i j, 0 ≤ K i j)
    (hlazy : ∀ i, (1 / 2 : ℝ) ≤ K i i)
    (f : α → ℝ) :
    (∑ i, (∑ j, K i j * f j) ^ 2) ≤
      ∑ i, f i * (∑ j, K i j * f j) := by
  classical
  let Q (i j : α) : ℝ := 2 * K i j - if i = j then 1 else 0
  have hQrow (i : α) : ∑ j, Q i j = 1 := by
    norm_num [Q, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow]
  have hQsymm (i j : α) : Q i j = Q j i := by
    simp only [Q, hsymm i j, eq_comm]
  have hQpos (i j : α) : 0 ≤ Q i j := by
    by_cases hij : i = j
    · subst j
      simp only [Q, ite_true]
      linarith [hlazy i]
    · simp only [Q, hij, ite_false, sub_zero]
      exact mul_nonneg (by norm_num) (hpos i j)
  have hQapply (i : α) :
      (∑ j, Q i j * f j) = 2 * (∑ j, K i j * f j) - f i := by
    simp [Q, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  have hc := sq_sum_apply_le Q hQrow hQsymm hQpos f
  simp only [hQapply] at hc
  have hexpand : (∑ i, (2 * (∑ j, K i j * f j) - f i) ^ 2) =
      4 * (∑ i, (∑ j, K i j * f j) ^ 2) -
      4 * (∑ i, f i * (∑ j, K i j * f j)) + ∑ i, f i ^ 2 := by
    calc
      _ = ∑ i, (4 * (∑ j, K i j * f j) ^ 2 -
          4 * (f i * (∑ j, K i j * f j)) + f i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hexpand] at hc
  linarith

theorem lazy_inner_nonneg
    (K : α → α → ℝ)
    (hrow : ∀ i, ∑ j, K i j = 1)
    (hsymm : ∀ i j, K i j = K j i)
    (hpos : ∀ i j, 0 ≤ K i j)
    (hlazy : ∀ i, (1 / 2 : ℝ) ≤ K i i)
    (f : α → ℝ) :
    0 ≤ ∑ i, f i * (∑ j, K i j * f j) :=
  le_trans (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (lazy_sq_sum_apply_le_inner K hrow hsymm hpos hlazy f)

end Problem315.FiniteKernel

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SpectralFromSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315.Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem norm_apply_le_of_inner_bounds
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {r : ℝ} (hr : 0 ≤ r)
    (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
    (hbound : ∀ x : E, ⟪x, T x⟫ ≤ r * ‖x‖ ^ 2)
    (x : E) : ‖T x‖ ≤ r * ‖x‖ := by
  classical
  let b := hT.eigenvectorBasis (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  let ev := hT.eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have hbe (i : Fin (Module.finrank ℝ E)) : T (b i) = ev i • b i :=
    hT.apply_eigenvectorBasis rfl i
  have hunit (i : Fin (Module.finrank ℝ E)) : ⟪b i, b i⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    norm_num
  have hev (i : Fin (Module.finrank ℝ E)) : 0 ≤ ev i ∧ ev i ≤ r := by
    constructor
    · simpa only [hbe, inner_smul_right, hunit, mul_one] using hpos (b i)
    · simpa only [hbe, inner_smul_right, hunit, mul_one, b.orthonormal.1 i,
        one_pow] using hbound (b i)
  have hsq : ‖T x‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    rw [mul_pow, ← b.sum_sq_inner_right (T x), ← b.sum_sq_inner_right x,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hcoord : ⟪b i, T x⟫ = ev i * ⟪b i, x⟫ := by
      rw [← hT (b i) x, hbe, inner_smul_left]
      simp
    rw [hcoord, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (hev i).1 (hev i).2 2
  nlinarith [norm_nonneg (T x), norm_nonneg x, mul_nonneg hr (norm_nonneg x)]

omit [FiniteDimensional ℝ E] in

theorem norm_iterate_le
    (T : E →ₗ[ℝ] E) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ x : E, ‖T x‖ ≤ r * ‖x‖) (t : ℕ) (x : E) :
    ‖(T : E → E)^[t] x‖ ≤ r ^ t * ‖x‖ := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖T ((T : E → E)^[t] x)‖ ≤ r * ‖(T : E → E)^[t] x‖ := hbound _
        _ ≤ r * (r ^ t * ‖x‖) := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (t + 1) * ‖x‖ := by ring

theorem norm_iterate_le_exp_of_inner_bounds
    (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {γ : ℝ} (hγ : γ ≤ 1)
    (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
    (hgap : ∀ x : E, ⟪x, T x⟫ ≤ (1 - γ) * ‖x‖ ^ 2)
    (t : ℕ) (x : E) :
    ‖(T : E → E)^[t] x‖ ≤ Real.exp (-γ * (t : ℝ)) * ‖x‖ := by
  have hr : 0 ≤ 1 - γ := sub_nonneg.mpr hγ
  calc
    ‖(T : E → E)^[t] x‖ ≤ (1 - γ) ^ t * ‖x‖ :=
      norm_iterate_le T hr (norm_apply_le_of_inner_bounds T hT hr hpos hgap) t x
    _ ≤ (Real.exp (-γ)) ^ t * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      exact pow_le_pow_left₀ hr (Real.one_sub_le_exp_neg γ) t
    _ = Real.exp (-γ * (t : ℝ)) * ‖x‖ := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring

end Problem315.Analytic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FiniteKernelTV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace
open WithLp

namespace Problem315.Analytic

variable {α : Type*} [Fintype α]

lemma euclidean_inner_eq_sum (f g : EuclideanSpace ℝ α) :
    ⟪f, g⟫ = ∑ i, f i * g i := by
  simp [PiLp.inner_apply, mul_comm]

lemma euclidean_norm_sq_eq_sum (f : EuclideanSpace ℝ α) :
    ‖f‖ ^ 2 = ∑ i, (f i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, euclidean_inner_eq_sum]
  simp [pow_two]

variable [DecidableEq α]

lemma matrix_preserves_zeroSum (K : Matrix α α ℝ)
    (hcols : ∀ j, ∑ i, K i j = 1) (f : EuclideanSpace ℝ α)
    (hf : f ∈ zeroSumSpace α) : Matrix.toEuclideanLin K f ∈ zeroSumSpace α := by
  change ∑ i, (Matrix.toEuclideanLin K f) i = 0
  simp only [Matrix.toLpLin_apply, ofLp_toLp, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hcols, one_mul]
  exact hf

theorem matrix_centered_norm_decay (K : Matrix α α ℝ)
    (hsymm : K.IsSymm) (hcols : ∀ j, ∑ i, K i j = 1)
    {γ : ℝ} (hγ : γ ≤ 1)
    (hpos : ∀ f : α → ℝ, 0 ≤ ∑ i, f i * ∑ j, K i j * f j)
    (hgap : ∀ f : α → ℝ, (∑ i, f i) = 0 →
      γ * (∑ i, (f i) ^ 2) ≤ ∑ i, f i * (f i - ∑ j, K i j * f j))
    (t : ℕ) (f : EuclideanSpace ℝ α) (hf : ∑ i, f i = 0) :
    ‖(Matrix.toEuclideanLin K : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[t] f‖ ≤
      Real.exp (-γ * (t : ℝ)) * ‖f‖ := by
  let T := Matrix.toEuclideanLin K
  have hinv := matrix_preserves_zeroSum K hcols
  let S := T.restrict hinv
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr hsymm)
  have hS : S.IsSymmetric := hT.restrict_invariant hinv
  have hSpos : ∀ x : zeroSumSpace α, 0 ≤ ⟪x, S x⟫ := by
    intro x
    change 0 ≤ ⟪(x : EuclideanSpace ℝ α), T x⟫
    simpa only [T, euclidean_inner_eq_sum, Matrix.toLpLin_apply, ofLp_toLp,
      Matrix.mulVec, dotProduct] using hpos (fun i => x.val i)
  have hSgap : ∀ x : zeroSumSpace α, ⟪x, S x⟫ ≤ (1 - γ) * ‖x‖ ^ 2 := by
    intro x
    change ⟪(x : EuclideanSpace ℝ α), T x⟫ ≤ (1 - γ) * ‖(x : EuclideanSpace ℝ α)‖ ^ 2
    rw [euclidean_inner_eq_sum, euclidean_norm_sq_eq_sum]
    simp only [T, Matrix.toLpLin_apply, ofLp_toLp, Matrix.mulVec, dotProduct]
    have hh := hgap (fun i => x.val i) x.property
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← pow_two] at hh
    linarith
  have hdec := norm_iterate_le_exp_of_inner_bounds S hS hγ hSpos hSgap t ⟨f, hf⟩
  have hiter (k : ℕ) :
      ((S : zeroSumSpace α → zeroSumSpace α)^[k] ⟨f, hf⟩).val =
        (T : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[k] f := by
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [Function.iterate_succ_apply']
        change T (((S : zeroSumSpace α → zeroSumSpace α)^[k] ⟨f, hf⟩).val) = _
        rw [ih]
  change ‖(((S : zeroSumSpace α → zeroSumSpace α)^[t] ⟨f, hf⟩).val)‖ ≤
    Real.exp (-γ * (t : ℝ)) * ‖f‖ at hdec
  rwa [hiter] at hdec

omit [DecidableEq α] in
lemma sum_abs_le_sqrt_card_mul_norm (f : EuclideanSpace ℝ α) :
    (∑ i, |f i|) ≤ Real.sqrt (Fintype.card α : ℝ) * ‖f‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun _ : α => (1 : ℝ)) (fun i => |f i|)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, sq_abs, ← euclidean_norm_sq_eq_sum, Real.sqrt_sq (norm_nonneg f)] using h

lemma centeredPoint_sum (a : α) : ∑ i, centeredPoint a i = 0 := by
  have : Nonempty α := ⟨a⟩
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [centeredPoint, Finset.sum_sub_distrib, hn]

lemma centeredPoint_norm_sq (a : α) :
    ‖centeredPoint a‖ ^ 2 = 1 - 1 / (Fintype.card α : ℝ) := by
  have : Nonempty α := ⟨a⟩
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [euclidean_norm_sq_eq_sum]
  simp only [centeredPoint, ofLp_toLp, sub_sq, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [ite_pow, one_pow, zero_pow (by omega : (2 : ℕ) ≠ 0), Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

lemma centeredPoint_norm_le_one (a : α) : ‖centeredPoint a‖ ≤ 1 := by
  have h := centeredPoint_norm_sq a
  have hn : 0 ≤ 1 / (Fintype.card α : ℝ) := by positivity
  nlinarith [norm_nonneg (centeredPoint a)]

lemma matrix_pow_row_sum (K : Matrix α α ℝ)
    (hrows : ∀ i, ∑ j, K i j = 1) (t : ℕ) : ∀ i, ∑ j, (K ^ t) i j = 1 := by
  induction t with
  | zero => intro i; simp [Matrix.one_apply]
  | succ t ih =>
      intro i
      simp only [pow_succ, Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hrows, mul_one]
      exact ih i

lemma matrix_iterate_centeredPoint (K : Matrix α α ℝ)
    (hrows : ∀ i, ∑ j, K i j = 1) (t : ℕ) (a i : α) :
    ((Matrix.toEuclideanLin K : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[t]
      (centeredPoint a)) i = (K ^ t) i a - 1 / (Fintype.card α : ℝ) := by
  rw [← Module.End.pow_apply]
  change ((Matrix.toLpLin 2 2 K ^ t) (centeredPoint a)) i = _
  rw [← Matrix.toLpLin_pow, Matrix.toLpLin_apply]
  simp only [ofLp_toLp, Matrix.mulVec, dotProduct, centeredPoint, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, matrix_pow_row_sum K hrows t,
    one_mul]
  simp

theorem matrix_tv_bound_of_gap (K : Matrix α α ℝ)
    (hsymm : K.IsSymm) (hrows : ∀ i, ∑ j, K i j = 1)
    {γ : ℝ} (hγ : γ ≤ 1)
    (hpos : ∀ f : α → ℝ, 0 ≤ ∑ i, f i * ∑ j, K i j * f j)
    (hgap : ∀ f : α → ℝ, (∑ i, f i) = 0 →
      γ * (∑ i, (f i) ^ 2) ≤ ∑ i, f i * (f i - ∑ j, K i j * f j))
    (t : ℕ) (a : α) :
    (1 / 2 : ℝ) * (∑ i, |(K ^ t) a i - 1 / (Fintype.card α : ℝ)|) ≤
      Real.sqrt (Fintype.card α : ℝ) / 2 * Real.exp (-γ * (t : ℝ)) := by
  have hcols : ∀ j, ∑ i, K i j = 1 := by
    intro j
    calc
      ∑ i, K i j = ∑ i, K j i := Finset.sum_congr rfl (fun i _ => hsymm.apply j i)
      _ = 1 := hrows j
  let f := (Matrix.toEuclideanLin K : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[t]
    (centeredPoint a)
  have heq (i : α) : f i = (K ^ t) a i - 1 / (Fintype.card α : ℝ) := by
    dsimp only [f]
    rw [matrix_iterate_centeredPoint K hrows, (hsymm.pow t).apply a i]
  have hnorm : ‖f‖ ≤ Real.exp (-γ * (t : ℝ)) := by
    calc
      ‖f‖ ≤ Real.exp (-γ * (t : ℝ)) * ‖centeredPoint a‖ :=
        matrix_centered_norm_decay K hsymm hcols hγ hpos hgap t
          (centeredPoint a) (centeredPoint_sum a)
      _ ≤ Real.exp (-γ * (t : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left (centeredPoint_norm_le_one a) (Real.exp_nonneg _)
      _ = _ := mul_one _
  calc
    (1 / 2 : ℝ) * (∑ i, |(K ^ t) a i - 1 / (Fintype.card α : ℝ)|) =
        (1 / 2 : ℝ) * ∑ i, |f i| := by simp_rw [heq]
    _ ≤ (1 / 2 : ℝ) * (Real.sqrt (Fintype.card α : ℝ) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (sum_abs_le_sqrt_card_mul_norm f) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (Real.sqrt (Fintype.card α : ℝ) *
        Real.exp (-γ * (t : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
    _ = _ := by ring

end Problem315.Analytic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.MatchingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.MatchingCount

private theorem involution_fin_four_card :
    Fintype.card (FixedPointFreeInvolution (Fin 4)) = 3 := by
  decide

 theorem involution_card_of_card_four {V : Type*} [Fintype V]
    (hV : Fintype.card V = 4) : Nat.card (FixedPointFreeInvolution V) = 3 := by
  classical
  let e : V ≃ Fin 4 := Fintype.equivFinOfCardEq hV
  rw [Nat.card_congr (involutionCongr e), Nat.card_eq_fintype_card]
  exact involution_fin_four_card

variable {n : ℕ} {S : FourSet n}

theorem perfectMatching_card (S : FourSet n) : Nat.card (PerfectMatching S) = 3 := by
  rw [Nat.card_congr (matchingEquivInvolution S)]
  apply involution_card_of_card_four
  simpa only [Fintype.card_coe] using S.property

theorem orderedMatchings_card (S : FourSet n) :
    Nat.card {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2} = 6 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun p : PerfectMatching S × PerfectMatching S => p.1 ≠ p.2) =
      (Finset.univ : Finset (PerfectMatching S)).offDiag := by
    ext p
    simp
  rw [hfilter, Finset.offDiag_card, Finset.card_univ]
  have hcard : Fintype.card (PerfectMatching S) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact perfectMatching_card S
  rw [hcard]

theorem fourSet_card (n : ℕ) : Nat.card (FourSet n) = n.choose 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.univ_filter_card_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem switchProposal_card (n : ℕ) : Nat.card (SwitchProposal n) = 6 * n.choose 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  have hcard (S : FourSet n) :
      Fintype.card {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2} = 6 := by
    rw [← Nat.card_eq_fintype_card]
    exact orderedMatchings_card S
  simp_rw [hcard]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
    fourSet_card, Nat.mul_comm]

theorem allProposals_card (n : ℕ) : (allProposals n).card = 6 * n.choose 4 := by
  classical
  unfold allProposals
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact switchProposal_card n

end Problem315.MatchingCount

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchFoundations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315

theorem validSwitch_of_result_ne {n : Nat} {G : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (h : proposalResult G p ≠ G) : validSwitch G p := by
  classical
  by_contra hn
  exact h (by simp [proposalResult, hn])

theorem proposalResult_eq_reverse_of_ne {n : Nat} {G H : SimpleGraph (Fin n)}
    {p : SwitchProposal n} (hne : G ≠ H) (h : proposalResult G p = H) :
    proposalResult H (reverseProposal p) = G := by
  have hv : validSwitch G p := validSwitch_of_result_ne (by
    rw [h]
    exact Ne.symm hne)
  rw [← h]
  exact proposalResult_reverse hv

theorem switchKernel_symm {n : Nat} {d : Fin n → Nat} (G H : GraphState n d) :
    switchKernel n d G H = switchKernel n d H G := by
  classical
  by_cases hGH : G = H
  · subst H
    rfl
  have hvGH : G.val ≠ H.val := fun h => hGH (Subtype.ext h)
  have hc : ((allProposals n).filter (fun p => proposalResult G.val p = H.val)).card =
      ((allProposals n).filter (fun p => proposalResult H.val p = G.val)).card := by
    apply Finset.card_bij (fun p _ => reverseProposal p)
    · intro p hp
      simp only [Finset.mem_filter, allProposals, Finset.mem_univ, true_and] at hp ⊢
      exact proposalResult_eq_reverse_of_ne hvGH hp
    · intro p hp q hq heq
      have heq' := congrArg reverseProposal heq
      simpa using heq'
    · intro p hp
      refine ⟨reverseProposal p, ?_, reverseProposal_reverse p⟩
      simp only [Finset.mem_filter, allProposals, Finset.mem_univ, true_and] at hp ⊢
      exact proposalResult_eq_reverse_of_ne (Ne.symm hvGH) hp
  simp only [switchKernel, hGH, Ne.symm hGH, ↓reduceIte, zero_add, hc]

theorem switchKernel_nonneg {n : Nat} {d : Fin n → Nat} (G H : GraphState n d) :
    0 ≤ switchKernel n d G H := by
  classical
  unfold switchKernel
  positivity

theorem switchKernel_self_ge_half {n : Nat} {d : Fin n → Nat} (G : GraphState n d) :
    (1 : ℝ) / 2 ≤ switchKernel n d G G := by
  classical
  simp only [switchKernel, ↓reduceIte]
  exact le_add_of_nonneg_right (by positivity)

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.KernelNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315

theorem proposal_fiber_cards_sum {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) :
    (∑ H ∈ allGraphStates n d,
      ((allProposals n).filter (fun p => proposalResult G.val p = H.val)).card) =
      (allProposals n).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (allProposals n) (allGraphStates n d) (proposalState G)
  have hf (H : GraphState n d) :
      ((allProposals n).filter (fun p => proposalState G p = H)) =
      ((allProposals n).filter (fun p => proposalResult G.val p = H.val)) := by
    ext p
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    exact Subtype.ext_iff
  simp_rw [hf] at h
  simpa only [allGraphStates, Finset.mem_univ, Finset.filter_true] using h

theorem switchKernel_row_sum {n : ℕ} {d : Fin n → ℕ}
    (hn : 4 ≤ n) (G : GraphState n d) :
    (∑ H ∈ allGraphStates n d, switchKernel n d G H) = 1 := by
  classical
  have hc : (Nat.choose n 4 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hn))
  unfold switchKernel
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Nat.cast_sum,
    proposal_fiber_cards_sum, MatchingCount.allProposals_card]
  have hdiag : (∑ H ∈ allGraphStates n d, if G = H then (1 : ℝ) / 2 else 0) = 1 / 2 := by
    simp [allGraphStates]
  rw [hdiag]
  push_cast
  field_simp
  ring

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchTV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace Problem315

lemma kernelPow_eq_matrix_pow (n : ℕ) (d : Fin n → ℕ) (t : ℕ) :
    (kernelPow n d t : Matrix (GraphState n d) (GraphState n d) ℝ) =
      (Matrix.of (switchKernel n d)) ^ t := by
  classical
  induction t with
  | zero =>
      funext G H
      change (if G = H then (1 : ℝ) else 0) = (1 : Matrix (GraphState n d) (GraphState n d) ℝ) G H
      simp [Matrix.one_apply]
  | succ t ih =>
      funext G H
      change (∑ K ∈ allGraphStates n d, kernelPow n d t G K * switchKernel n d K H) = _
      rw [ih, pow_succ]
      rfl

theorem switch_tv_bound_of_gap (n : ℕ) (d : Fin n → ℕ)
    (hrows : ∀ G : GraphState n d, ∑ H, switchKernel n d G H = 1)
    {γ : ℝ} (hγ : γ ≤ 1) (hgap : hasSpectralGapAtLeast n d γ)
    (t : ℕ) (G : GraphState n d) :
    tvDistanceFrom n d t G ≤
      Real.sqrt (stateCount n d : ℝ) / 2 * Real.exp (-γ * (t : ℝ)) := by
  classical
  have : Nonempty (GraphState n d) := ⟨G⟩
  have hN : (0 : ℝ) < (Fintype.card (GraphState n d) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsymm : Matrix.IsSymm (Matrix.of (switchKernel n d)) :=
    Matrix.IsSymm.ext (fun G H => switchKernel_symm H G)
  have hpos : ∀ f : GraphState n d → ℝ,
      0 ≤ ∑ G, f G * ∑ H, switchKernel n d G H * f H :=
    FiniteKernel.lazy_inner_nonneg (switchKernel n d) hrows switchKernel_symm
      switchKernel_nonneg switchKernel_self_ge_half
  have hgap' : ∀ f : GraphState n d → ℝ, (∑ G, f G) = 0 →
      γ * (∑ G, (f G) ^ 2) ≤
        ∑ G, f G * (f G - ∑ H, switchKernel n d G H * f H) := by
    intro f hf
    have hh := hgap f
    have havg : uniformAverage n d f = 0 := by
      simp [uniformAverage, allGraphStates, hf]
    unfold uniformVariance at hh
    rw [havg] at hh
    simp only [sub_zero, uniformAverage, stateCount,
      allGraphStates, Finset.card_univ, dirichletEnergy, uniformInner, markovApply] at hh
    rw [← mul_div_assoc] at hh
    exact (div_le_div_iff_of_pos_right hN).mp hh
  have ht := Analytic.matrix_tv_bound_of_gap (Matrix.of (switchKernel n d)) hsymm hrows hγ hpos hgap' t G
  simpa only [tvDistanceFrom, allGraphStates, stateCount, Finset.card_univ,
    kernelPow_eq_matrix_pow] using ht

lemma switch_gap_parameter_le_one (n : ℕ) (hn : 4 ≤ n) :
    (1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ)) ≤ 1 := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hc : (1 : ℝ) ≤ (Nat.choose n 4 : ℝ) := by
    exact_mod_cast (Nat.choose_pos hn)
  have hd : (1 : ℝ) ≤ 24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ) := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hn')) hc
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd

theorem switch_chain_tv_bound_of_stochastic_and_gap (n : ℕ) (d : Fin n → ℕ)
    (hn : 4 ≤ n)
    (hrows : ∀ G : GraphState n d, ∑ H, switchKernel n d G H = 1)
    (hgap : hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))))
    (t : ℕ) (G : GraphState n d) :
    tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
      Real.exp (- (t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  have h := switch_tv_bound_of_gap n d hrows (switch_gap_parameter_le_one n hn) hgap t G
  convert h using 1
  congr 2
  ring

theorem switch_chain_tv_bound_of_spectralGap (n : ℕ) (d : Fin n → ℕ)
    (hn : 4 ≤ n)
    (hgap : hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))))
    (t : ℕ) (G : GraphState n d) :
    tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
      Real.exp (- (t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  apply switch_chain_tv_bound_of_stochastic_and_gap n d hn _ hgap t G
  intro H
  simpa only [allGraphStates] using switchKernel_row_sum hn H

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315

theorem switch_chain_tv_bound_oai :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → 1 < stateCount n d → ∀ (t : Nat) (G : GraphState n d), tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 * Real.exp (- (t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  intro n d hn hd hgraph hmany t G
  exact switch_chain_tv_bound_of_spectralGap n d hn
    ((switch_chain_main n d hn hd hgraph).2.2 hmany) t G

end Problem315

end

end OAI
end

theorem solution : type_of% @OAI.Problem315.switch_chain_tv_bound_oai := @OAI.Problem315.switch_chain_tv_bound_oai
