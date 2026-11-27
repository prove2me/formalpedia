-- Prove2me | solution 1 for GlobalTheory.ThetaWeberProof.thetaWeber_of_tripleProduct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:11.187639+00:00
-- url     : https://prove2.me/submissions/f66c1686-8544-4ea2-a254-69dbac77c0f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaConstEqEtaWeberSqOfTripleProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
namespace GlobalTheory.ThetaWeberProof
open GlobalTheory.ThetaWeberRoad GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma norm_cexp_pi_mul_I_mul_upperHalfPlane_lt_one (τ : ℍ) : ‖cexp (↑Real.pi * I * (τ : ℂ))‖ < 1 := by
  rw [Complex.norm_exp, ← Real.exp_zero, Real.exp_lt_exp]
  have h : (↑Real.pi * I * (τ : ℂ)).re = -(Real.pi * τ.im) := by
    simp [mul_re, mul_im]
  rw [h]
  have := mul_pos Real.pi_pos τ.im_pos
  linarith
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma cexp_eq_cexp_pi_mul_I_mul_pow_of_eq (τ : ℍ) (k : ℕ) (w : ℂ) (hw : w = ↑Real.pi * I * k * τ) :
    cexp w = cexp (↑Real.pi * I * τ) ^ k := by
  rw [← Complex.exp_nat_mul, hw]; ring_nf
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma tpFactor_eq_nome_product (τ : ℍ) (z : ℂ) (n : ℕ) :
    _root_.GlobalTheory.ThetaWeberRoad.tpFactor τ z n =
      (1 - cexp (↑Real.pi * I * τ) ^ (2 * n + 2)) *
        (1 + cexp (↑Real.pi * I * τ) ^ (2 * n + 1) * cexp (2 * ↑Real.pi * I * z)) *
        (1 + cexp (↑Real.pi * I * τ) ^ (2 * n + 1) / cexp (2 * ↑Real.pi * I * z)) := by
  unfold _root_.GlobalTheory.ThetaWeberRoad.tpFactor
  have h1 : cexp (2 * ↑Real.pi * I * (↑n + 1) * τ) = cexp (↑Real.pi * I * τ) ^ (2 * n + 2) :=
    cexp_eq_cexp_pi_mul_I_mul_pow_of_eq τ _ _ (by push_cast; ring)
  have h2 : cexp (↑Real.pi * I * (2 * ↑n + 1) * τ) = cexp (↑Real.pi * I * τ) ^ (2 * n + 1) :=
    cexp_eq_cexp_pi_mul_I_mul_pow_of_eq τ _ _ (by push_cast; ring)
  rw [Complex.exp_add, Complex.exp_sub, h1, h2]
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma hasProd_one_sub_pow_succ_of_norm_lt_one {y : ℂ} (hy : ‖y‖ < 1) :
    HasProd (fun n : ℕ => 1 - y ^ (n + 1)) (∏' n : ℕ, (1 - y ^ (n + 1))) :=
  (ModularForm.multipliable_one_sub_pow hy).hasProd
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma hasProd_one_add_even_mul_one_add_odd_tprod {f : ℕ → ℂ} (he : Summable fun k => f (2 * k))
    (ho : Summable fun k => f (2 * k + 1)) :
    HasProd (fun k => (1 + f (2 * k)) * (1 + f (2 * k + 1))) (∏' n, (1 + f n)) := by
  have hme := (Complex.multipliable_one_add_of_summable he).hasProd
  have hmo := (Complex.multipliable_one_add_of_summable ho).hasProd
  have h := hme.even_mul_odd (f := fun n => 1 + f n) hmo
  rw [h.tprod_eq]
  exact hme.mul hmo
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma summable_pow_mul_add_of_norm_lt_one {y : ℂ} (hy : ‖y‖ < 1) (a b : ℕ) (hb : 0 < b) :
    Summable fun k : ℕ => y ^ (b * k + a) := by
  apply Summable.of_norm
  have hg' : Summable fun k : ℕ => ‖y‖ ^ a * (‖y‖ ^ b) ^ k := by
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (by positivity)
      (pow_lt_one₀ (norm_nonneg y) hy hb.ne')
  refine hg'.congr fun k => ?_
  rw [norm_pow, ← pow_mul, ← pow_add]; ring_nf
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma hasProd_one_sub_pow_odd_mul_one_sub_pow_even {y : ℂ} (hy : ‖y‖ < 1) :
    HasProd (fun k : ℕ => (1 - y ^ (2 * k + 1)) * (1 - y ^ (2 * k + 2)))
      (∏' n : ℕ, (1 - y ^ (n + 1))) := by
  have h := hasProd_one_add_even_mul_one_add_odd_tprod (f := fun n => -y ^ (n + 1))
    ((summable_pow_mul_add_of_norm_lt_one hy 1 2 two_pos).neg)
    ((summable_pow_mul_add_of_norm_lt_one hy 2 2 two_pos).neg)
  simp only [← sub_eq_add_neg] at h
  exact h
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma eta_eq_cexp_div_twentyFour_mul_tprod_one_sub_pow (w : ℂ) :
    ModularForm.eta w = cexp (2 * ↑Real.pi * I * w / 24) *
      ∏' n : ℕ, (1 - cexp (2 * ↑Real.pi * I * w) ^ (n + 1)) := by
  unfold ModularForm.eta
  simp only [Function.Periodic.qParam, ModularForm.eta_q_eq_pow]
  norm_num
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma eta_eq_cexp_mul_tprod_one_sub_nome_sq_pow (τ : ℍ) :
    ModularForm.eta τ = cexp (2 * ↑Real.pi * I * τ / 24) *
      ∏' n : ℕ, (1 - (cexp (↑Real.pi * I * τ) ^ 2) ^ (n + 1)) := by
  rw [eta_eq_cexp_div_twentyFour_mul_tprod_one_sub_pow, cexp_eq_cexp_pi_mul_I_mul_pow_of_eq τ 2 (2 * ↑Real.pi * I * τ) (by push_cast; ring)]
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma mul_inv_mul_mul_inv_eq_mul_inv_mul_mul_inv {Θ A B E c E₂ : ℂ} (hA : A ≠ 0) (hE : E ≠ 0)
    (key : Θ * (E * A) = c ^ 2 * E₂ ^ 2 * B ^ 2) : Θ = E * A * (c * (E₂ * B) / (E * A)) ^ 2 := by
  have h : E * A ≠ 0 := mul_ne_zero hE hA
  rw [div_pow, mul_pow, mul_pow, eq_comm, mul_div_assoc', div_eq_iff (pow_ne_zero 2 h)]
  linear_combination (-(E * A)) * key
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma tprod_one_sub_nome_sq_pow_succ_ne_zero (τ : ℍ) :
    ∏' n : ℕ, (1 - (cexp (↑Real.pi * I * τ) ^ 2) ^ (n + 1)) ≠ 0 := by
  have h := ModularForm.eta_ne_zero (z := (τ : ℂ)) τ.im_pos
  rw [eta_eq_cexp_mul_tprod_one_sub_nome_sq_pow] at h
  exact right_ne_zero_of_mul h
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma thetaConst_zero_zero_eq_eta_mul_weberF_sq (hTP : _root_.GlobalTheory.ThetaWeberRoad.TripleProduct) (τ : ℍ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ = ModularForm.eta τ * _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF τ ^ 2 := by
  set q := cexp (↑Real.pi * I * τ) with hqdef
  have hq : ‖q‖ < 1 := norm_cexp_pi_mul_I_mul_upperHalfPlane_lt_one τ
  have hΘ : HasProd (fun n : ℕ => (1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1)) ^ 2)
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ) := by
    have h := hTP τ 0
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst]
    convert h using 1
    · funext n; rw [tpFactor_eq_nome_product]; simp; ring
    · simp
  have hA := hasProd_one_sub_pow_succ_of_norm_lt_one (y := q ^ 2) (by rw [norm_pow]; nlinarith [norm_nonneg q])
  have hB := hasProd_one_sub_pow_odd_mul_one_sub_pow_even (y := -q) (by rwa [norm_neg])
  have key : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ * (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) =
      (∏' n : ℕ, (1 - (-q) ^ (n + 1))) ^ 2 := by
    refine ((hΘ.mul hA).unique ?_).trans (sq _).symm
    convert hB.mul hB using 1
    funext n
    simp only [Odd.neg_pow (⟨n, rfl⟩ : Odd (2 * n + 1)),
      Even.neg_pow (⟨n + 1, by ring⟩ : Even (2 * n + 2)), ← pow_mul]
    ring
  have e₂ : cexp (2 * ↑Real.pi * I * (((τ : ℂ) + 1) / 2)) = -q := by
    rw [hqdef, show 2 * ↑Real.pi * I * (((τ : ℂ) + 1) / 2) = ↑Real.pi * I * τ + ↑Real.pi * I by ring,
      Complex.exp_add, Complex.exp_pi_mul_I]; ring
  have hexp : cexp (-(↑Real.pi * I / 24)) ^ 2 * cexp (2 * ↑Real.pi * I * (((τ : ℂ) + 1) / 2) / 24) ^ 2 =
      cexp (2 * ↑Real.pi * I * τ / 24) := by
    rw [← mul_pow, ← Complex.exp_add, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF]
  rw [eta_eq_cexp_mul_tprod_one_sub_nome_sq_pow, eta_eq_cexp_div_twentyFour_mul_tprod_one_sub_pow (((τ : ℂ) + 1) / 2), e₂, ← hqdef]
  refine mul_inv_mul_mul_inv_eq_mul_inv_mul_mul_inv (tprod_one_sub_nome_sq_pow_succ_ne_zero τ) (Complex.exp_ne_zero _) ?_
  rw [hexp, ← key]; ring
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma eq_mul_div_sq_of_mul_mul_eq_sq_mul_sq {Θ A B E E₂ : ℂ} (hA : A ≠ 0) (hE : E ≠ 0)
    (key : Θ * (E * A) = E₂ ^ 2 * B ^ 2) : Θ = E * A * ((E₂ * B) / (E * A)) ^ 2 := by
  simpa using mul_inv_mul_mul_inv_eq_mul_inv_mul_mul_inv (c := 1) hA hE (by simpa using key)
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma thetaConst_zero_one_eq_eta_mul_weberF₁_sq (hTP : _root_.GlobalTheory.ThetaWeberRoad.TripleProduct) (τ : ℍ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ = ModularForm.eta τ * _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁ τ ^ 2 := by
  set q := cexp (↑Real.pi * I * τ) with hqdef
  have hq : ‖q‖ < 1 := norm_cexp_pi_mul_I_mul_upperHalfPlane_lt_one τ
  have hm : cexp (2 * ↑Real.pi * I * 2⁻¹) = -1 := by
    rw [show 2 * ↑Real.pi * I * 2⁻¹ = ↑Real.pi * I by ring, Complex.exp_pi_mul_I]
  have hΘ : HasProd (fun n : ℕ => (1 - q ^ (2 * n + 2)) * (1 - q ^ (2 * n + 1)) ^ 2)
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ) := by
    have h := hTP τ 2⁻¹
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst]
    convert h using 1
    · funext n; rw [tpFactor_eq_nome_product, hm]; ring
    · simp
  have hA := hasProd_one_sub_pow_succ_of_norm_lt_one (y := q ^ 2) (by rw [norm_pow]; nlinarith [norm_nonneg q])
  have hB := hasProd_one_sub_pow_odd_mul_one_sub_pow_even hq
  have key : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ * (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) =
      (∏' n : ℕ, (1 - q ^ (n + 1))) ^ 2 := by
    refine ((hΘ.mul hA).unique ?_).trans (sq _).symm
    convert hB.mul hB using 1
    funext n
    simp only [← pow_mul]
    ring
  have e₂ : cexp (2 * ↑Real.pi * I * ((τ : ℂ) / 2)) = q := by
    rw [hqdef]; congr 1; ring
  have hexp : cexp (2 * ↑Real.pi * I * ((τ : ℂ) / 2) / 24) ^ 2 =
      cexp (2 * ↑Real.pi * I * τ / 24) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₁]
  rw [eta_eq_cexp_mul_tprod_one_sub_nome_sq_pow, eta_eq_cexp_div_twentyFour_mul_tprod_one_sub_pow ((τ : ℂ) / 2), e₂, ← hqdef]
  refine eq_mul_div_sq_of_mul_mul_eq_sq_mul_sq (tprod_one_sub_nome_sq_pow_succ_ne_zero τ) (Complex.exp_ne_zero _) ?_
  rw [hexp, ← key]; ring
open Complex in
open UpperHalfPlane hiding I in
open scoped Real in
private lemma thetaConst_one_zero_eq_eta_mul_weberF₂_sq (hTP : _root_.GlobalTheory.ThetaWeberRoad.TripleProduct) (τ : ℍ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ = ModularForm.eta τ * _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂ τ ^ 2 := by
  set q := cexp (↑Real.pi * I * τ) with hqdef
  have hq : ‖q‖ < 1 := norm_cexp_pi_mul_I_mul_upperHalfPlane_lt_one τ
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hz : cexp (2 * ↑Real.pi * I * ((τ : ℂ) / 2)) = q := by
    rw [hqdef]; congr 1; ring
  have hθ : HasProd (fun n : ℕ => (1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 2)) * (1 + q ^ (2 * n)))
      (jacobiTheta₂ ((τ : ℂ) / 2) τ) := by
    convert hTP τ ((τ : ℂ) / 2) using 1
    funext n
    rw [tpFactor_eq_nome_product, hz, ← hqdef, pow_succ q (2 * n), mul_div_cancel_right₀ _ hq0]
    ring
  have hΘ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ =
      cexp (↑Real.pi * I * τ / 4) * jacobiTheta₂ ((τ : ℂ) / 2) τ := by
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst]; push_cast; ring_nf
  have hC := (Complex.multipliable_one_add_of_summable (summable_pow_mul_add_of_norm_lt_one hq 2 2 two_pos)).hasProd
  have hg : HasProd (fun n : ℕ => 1 + q ^ (2 * n))
      (2 * ∏' k : ℕ, (1 + q ^ (2 * k + 2))) := by
    have h := HasProd.zero_mul (f := fun n : ℕ => 1 + q ^ (2 * n)) (by
      convert hC using 2 with n; ring_nf)
    convert h using 1; norm_num
  have hA := hasProd_one_sub_pow_succ_of_norm_lt_one (y := q ^ 2) (by rw [norm_pow]; nlinarith [norm_nonneg q])
  have hD := hasProd_one_sub_pow_succ_of_norm_lt_one (y := q ^ 4) (by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num))
  have h₁ : jacobiTheta₂ ((τ : ℂ) / 2) τ =
      (∏' n : ℕ, (1 - (q ^ 4) ^ (n + 1))) * (2 * ∏' k : ℕ, (1 + q ^ (2 * k + 2))) := by
    refine hθ.unique ?_
    convert hD.mul hg using 1
    funext n
    simp only [← pow_mul]
    ring
  have h₂ : (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) * (∏' k : ℕ, (1 + q ^ (2 * k + 2))) =
      ∏' n : ℕ, (1 - (q ^ 4) ^ (n + 1)) := by
    refine (hA.mul hC).unique ?_
    convert hD using 1
    funext n
    simp only [← pow_mul]
    ring
  have hc : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hx : cexp (2 * ↑Real.pi * I * (2 * (τ : ℂ)) / 24) ^ 2 =
      cexp (↑Real.pi * I * τ / 4) * cexp (2 * ↑Real.pi * I * τ / 24) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
  have e₄ : cexp (2 * ↑Real.pi * I * (2 * (τ : ℂ))) = q ^ 4 :=
    cexp_eq_cexp_pi_mul_I_mul_pow_of_eq τ 4 _ (by push_cast; ring)
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.weberF₂]
  rw [eta_eq_cexp_mul_tprod_one_sub_nome_sq_pow, eta_eq_cexp_div_twentyFour_mul_tprod_one_sub_pow (2 * (τ : ℂ)), e₄, ← hqdef]
  refine mul_inv_mul_mul_inv_eq_mul_inv_mul_mul_inv (tprod_one_sub_nome_sq_pow_succ_ne_zero τ) (Complex.exp_ne_zero _) ?_
  rw [hc, hx, hΘ, h₁, ← h₂]
  ring
end GlobalTheory.ThetaWeberProof
end
end

set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaWeberProof
open GlobalTheory.ThetaWeberRoad GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
open Complex
open UpperHalfPlane hiding I
open scoped Real
namespace GlobalTheory.ThetaWeberProof
namespace _root_.GlobalTheory.ThetaWeberProof
theorem _root_.solution (hTP : _root_.GlobalTheory.ThetaWeberRoad.TripleProduct) (τ : ℍ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ :=
  ⟨thetaConst_zero_zero_eq_eta_mul_weberF_sq hTP τ, thetaConst_zero_one_eq_eta_mul_weberF₁_sq hTP τ, thetaConst_one_zero_eq_eta_mul_weberF₂_sq hTP τ⟩
end _root_.GlobalTheory.ThetaWeberProof
end GlobalTheory.ThetaWeberProof
