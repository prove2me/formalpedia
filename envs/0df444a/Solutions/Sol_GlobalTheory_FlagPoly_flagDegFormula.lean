-- Prove2me | solution 1 for GlobalTheory.FlagPoly.flagDegFormula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:41:38.332298+00:00
-- url     : https://prove2.me/submissions/58ad79ba-d48f-4e87-aeb7-39334cfc2dca

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_CurveCl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagDegreeVandermonde
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagDegreeFormula
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_degFl_C_mul
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_degree_permExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Finset Formalism.DegreeFormula
namespace GlobalTheory.FlagPoly
open MvPolynomial Finset in
private theorem coeff_linearForm_pow_eq_factorial_mul_prod {σ : Type} [Fintype σ] [DecidableEq σ] (c : σ → ℝ) (n : ℕ)
    (d : σ →₀ ℕ) (hd : d.degree = n) :
    coeff d ((∑ x, C (c x) * X x) ^ n) =
      (n.factorial : ℝ) * ∏ x, (c x ^ d x / ((d x).factorial : ℝ)) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    ← map_natCast (C : ℝ →+* MvPolynomial σ ℝ), ← mul_assoc, ← map_mul, coeff_C_mul,
    coeff_prod_X_pow]
  have hsum : ∑ i, d i = n := by
    rw [← hd, Finsupp.degree_eq_sum]
  rw [Finset.sum_eq_single (⇑d)]
  · have hind : d = Finsupp.indicator univ (fun i _ => d i) := by
      ext i; simp
    rw [if_pos hind, mul_one]
    have hspec := Nat.multinomial_spec (univ : Finset σ) (⇑d)
    rw [hsum] at hspec
    have hpos : (∏ i, ((d i).factorial : ℝ)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]; intro i _; exact_mod_cast (Nat.factorial_pos _).ne'
    rw [Finset.prod_div_distrib, ← hspec]
    push_cast
    field_simp
  · intro k _ hk
    rw [if_neg, mul_zero]
    intro h
    apply hk
    funext i
    have := congrArg (fun f : σ →₀ ℕ => f i) h
    simpa using this.symm
  · intro h
    exfalso; apply h
    rw [Finset.mem_piAntidiag]
    exact ⟨hsum, fun i _ => Finset.mem_univ i⟩
open MvPolynomial Finset in
private theorem prod_factorial_rev_eq_prod_sub (N : ℕ) :
    ∏ j : Fin N, ((j.rev : ℕ).factorial : ℝ) =
      ∏ i : Fin N, ∏ k ∈ Ioi i, (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by
  cases N with
  | zero => simp
  | succ n =>
    have h1 : ∏ i : Fin (n + 1), ∏ k ∈ Ioi i, (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) =
        (n.superFactorial : ℝ) := by
      rw [← Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) n, Matrix.det_vandermonde]
    rw [h1, ← Nat.prod_range_succ_factorial, Nat.cast_prod,
      ← Fin.prod_univ_eq_prod_range (fun x => ((x.factorial : ℕ) : ℝ)) (n + 1)]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun j => rfl)
open MvPolynomial Finset in
private theorem sum_sign_prod_pow_div_factorial_eq_prod {N : ℕ} (v : Fin N → ℝ) :
    ∑ π : Equiv.Perm (Fin N), ((Equiv.Perm.sign π : ℤ) : ℝ) *
        ∏ i, (v i ^ (N - 1 - (π i : ℕ)) / ((N - 1 - (π i : ℕ)).factorial : ℝ)) =
      ∏ i : Fin N, ∏ k : Fin N,
        if i < k then (v i - v k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1 := by
  have hrev : ∀ j : Fin N, N - 1 - (j : ℕ) = (j.rev : ℕ) := by
    intro j; rw [Fin.val_rev]; omega
  have hterm : ∀ π : Equiv.Perm (Fin N),
      ∏ i, (v i ^ (N - 1 - (π i : ℕ)) / ((N - 1 - (π i : ℕ)).factorial : ℝ)) =
        (∏ i, Matrix.transpose (Matrix.projVandermonde 1 v) (π i) i) *
          ∏ j : Fin N, (((j.rev : ℕ).factorial : ℝ))⁻¹ := by
    intro π
    simp_rw [div_eq_mul_inv, Finset.prod_mul_distrib, hrev]
    congr 1
    · simp [Matrix.projVandermonde_apply]
    · exact Fintype.prod_equiv π _ _ (fun i => rfl)
  simp_rw [hterm, ← mul_assoc, ← Finset.sum_mul, ← Matrix.det_apply', Matrix.det_transpose,
    Matrix.det_projVandermonde, Finset.prod_inv_distrib, prod_factorial_rev_eq_prod_sub,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_div_distrib, div_eq_mul_inv]
  simp only [Pi.one_apply, one_mul]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  congr 1
  ext k
  simp
end GlobalTheory.FlagPoly
end

set_option autoImplicit false
open MvPolynomial Finset Formalism.DegreeFormula
open GlobalTheory GlobalTheory.FlagPoly
open MvPolynomial Finset
namespace GlobalTheory.FlagPoly
namespace _root_.GlobalTheory.FlagPoly
theorem _root_.solution : _root_.Formalism.DegreeFormula.FlagDegFormula := by
  unfold _root_.Formalism.DegreeFormula.FlagDegFormula
  intro ι _ _ N lam
  unfold _root_.Formalism.DegreeFormula.flagDeg _root_.Formalism.DegreeFormula.weylProd _root_.Formalism.DegreeFormula.linRoot
  rw [neg_pow, ← map_one (C : ℝ →+* MvPolynomial (ι × Fin N) ℝ), ← map_neg, ← map_pow, _root_.Formalism.DegreeFormula.PPowSum.degFl_C_mul]
  unfold _root_.Formalism.DegreeFormula.degFl
  simp_rw [coeff_linearForm_pow_eq_factorial_mul_prod _ _ _ (_root_.Formalism.DegreeFormula.PPowSum.degree_permExp _)]
  have hexp : ∀ (σ : ι → Equiv.Perm (Fin N)) (τ : ι) (i : Fin N),
      (_root_.Formalism.DegreeFormula.permExp σ) (τ, i) = N - 1 - ((σ τ) i : ℕ) := by
    intro σ τ i
    unfold _root_.Formalism.DegreeFormula.permExp
    rfl
  simp_rw [Fintype.prod_prod_type, hexp]
  rw [← Finset.prod_congr rfl (fun τ _ => sum_sign_prod_pow_div_factorial_eq_prod (lam τ)),
    Fintype.prod_sum]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.prod_mul_distrib]
  ring
end _root_.GlobalTheory.FlagPoly
end GlobalTheory.FlagPoly
