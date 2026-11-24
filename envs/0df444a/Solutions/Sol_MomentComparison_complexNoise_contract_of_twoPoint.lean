-- Prove2me | solution 1 for MomentComparison.complexNoise_contract_of_twoPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:12:37.346547+00:00
-- url     : https://prove2.me/submissions/2454e098-49bd-4679-84be-33ab0a6ae61e

module
public import Definitions.Def_MomentComparison_MomentNorm
public import Definitions.Def_MomentComparison_NoisePolynomial
public import Definitions.Def_MomentComparison_TwoPointReduction
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Hypercontractivity
public import Theorems.Thm_MomentComparison_complexMomentNorm_nonneg
public import Theorems.Thm_MomentComparison_complexNoise_cons
public import Theorems.Thm_MomentComparison_complexNoise_zero
public import Theorems.Thm_MomentComparison_cubeAverage_cons
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeAverage_nonneg
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_walsh_empty
attribute [local simp] MomentComparison.cubeAverage_const
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.walsh_empty


section
public section
open scoped BigOperators
namespace MomentComparison
private theorem cubeAverage_congr_le {n : ℕ} {f g : Cube n → ℝ} (h : ∀ x, f x ≤ g x) :
    cubeAverage f ≤ cubeAverage g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)
private theorem cubeAverage_minkowski {n : ℕ} {r : ℝ} (hr : 1 ≤ r)
    (u v : Cube n → ℝ) (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x) :
    (cubeAverage fun x => ((u x + v x) / 2) ^ r) ^ r⁻¹ ≤
      ((cubeAverage fun x => u x ^ r) ^ r⁻¹ + (cubeAverage fun x => v x ^ r) ^ r⁻¹) / 2 := by
  let N := (2 : ℝ) ^ n
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hpos : 0 < r := zero_lt_one.trans_le hr
  have hM := Real.Lp_add_le_of_nonneg (s := Finset.univ) (f := u) (g := v) hr
    (fun x _ => hu x) (fun x _ => hv x)
  simp only [one_div] at hM
  have hscale (f : Cube n → ℝ) (hf : ∀ x, 0 ≤ f x) :
      (cubeAverage fun x => f x ^ r) ^ r⁻¹ = (∑ x, f x ^ r) ^ r⁻¹ / N ^ r⁻¹ :=
    Real.div_rpow (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hf x) _) hN r⁻¹
  have hscaleTwo :
      (cubeAverage fun x => ((u x + v x) / 2) ^ r) ^ r⁻¹ =
        (cubeAverage fun x => (u x + v x) ^ r) ^ r⁻¹ / 2 := by
    have hh (x : Cube n) : ((u x + v x) / 2) ^ r = (u x + v x) ^ r / (2 : ℝ) ^ r :=
      Real.div_rpow (add_nonneg (hu x) (hv x)) (by norm_num : 0 ≤ (2 : ℝ)) r
    unfold cubeAverage
    simp only [hh]
    rw [← Finset.sum_div]
    rw [div_right_comm, Real.div_rpow (div_nonneg (Finset.sum_nonneg fun x _ =>
        Real.rpow_nonneg (add_nonneg (hu x) (hv x)) _) hN) (by positivity),
      ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)), mul_inv_cancel₀ hpos.ne', Real.rpow_one]
  rw [hscaleTwo, hscale _ (fun x => add_nonneg (hu x) (hv x)), hscale u hu, hscale v hv, ← add_div]
  exact div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right hM (Real.rpow_nonneg hN _)) (by norm_num)
private theorem mixedMoment_le {n : ℕ} {p q : ℝ} (hq : 0 < q) (hqp : q ≤ p)
    (f g : Cube n → ℂ) :
    (cubeAverage fun x => (((‖f x‖ ^ q + ‖g x‖ ^ q) / 2) ^ q⁻¹) ^ p) ^ p⁻¹ ≤
      ((complexMomentNorm p f ^ q + complexMomentNorm p g ^ q) / 2) ^ q⁻¹ := by
  have hp : 0 < p := hq.trans_le hqp
  have hr : 1 ≤ p / q := (le_div_iff₀ hq).2 (by simpa using hqp)
  have hM := cubeAverage_minkowski hr (fun x => ‖f x‖ ^ q) (fun x => ‖g x‖ ^ q)
    (fun x => Real.rpow_nonneg (norm_nonneg _) _) (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have hup (t : ℝ) (ht : 0 ≤ t) : (t ^ q) ^ (p / q) = t ^ p := by
    rw [← Real.rpow_mul ht, show q * (p / q) = p by field_simp]
  have hdown (t : ℝ) (ht : 0 ≤ t) : (t ^ q⁻¹) ^ p = t ^ (p / q) := by
    rw [← Real.rpow_mul ht, show q⁻¹ * p = p / q by ring]
  have hroot (t : ℝ) (ht : 0 ≤ t) : (t ^ p⁻¹) ^ q = t ^ (p / q)⁻¹ := by
    rw [← Real.rpow_mul ht, inv_div, div_eq_mul_inv, mul_comm]
  have hnonneg (x : Cube n) : 0 ≤ (‖f x‖ ^ q + ‖g x‖ ^ q) / 2 :=
    div_nonneg (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (norm_nonneg _) _)) (by norm_num)
  apply (Real.rpow_le_rpow_iff
    (Real.rpow_nonneg (cubeAverage_nonneg fun _ => Real.rpow_nonneg
      (Real.rpow_nonneg (hnonneg _) _) _) _)
    (Real.rpow_nonneg (div_nonneg (add_nonneg
      (Real.rpow_nonneg (complexMomentNorm_nonneg p f) _)
      (Real.rpow_nonneg (complexMomentNorm_nonneg p g) _)) (by norm_num)) _) hq).mp
  rw [← Real.rpow_mul (div_nonneg (add_nonneg
      (Real.rpow_nonneg (complexMomentNorm_nonneg p f) _)
      (Real.rpow_nonneg (complexMomentNorm_nonneg p g) _)) (by norm_num)),
    inv_mul_cancel₀ hq.ne', Real.rpow_one]
  unfold complexMomentNorm
  simp only [hdown _ (hnonneg _), hroot _ (cubeAverage_nonneg fun _ =>
    Real.rpow_nonneg (norm_nonneg _) _), hup _ (norm_nonneg _)] at hM ⊢
  rw [hroot _ (cubeAverage_nonneg fun x => Real.rpow_nonneg (hnonneg x) _)]
  exact hM
private theorem cubeAverage_pair {n : ℕ} (u v : Cube n → ℝ) :
    cubeAverage (fun x => (u x + v x) / 2) = (cubeAverage u + cubeAverage v) / 2 := by
  simp only [cubeAverage, ← Finset.sum_div, Finset.sum_add_distrib, ← add_div]
  rw [div_right_comm]
private theorem complexMomentNorm_cons {n : ℕ} {q : ℝ} (hq : 0 < q)
    (f : Cube (n + 1) → ℂ) :
    complexMomentNorm q f =
      ((complexMomentNorm q (fun x => f (Fin.cons true x)) ^ q +
        complexMomentNorm q (fun x => f (Fin.cons false x)) ^ q) / 2) ^ q⁻¹ := by
  unfold complexMomentNorm
  simp only [Real.rpow_inv_rpow (cubeAverage_nonneg fun _ =>
    Real.rpow_nonneg (norm_nonneg _) _) hq.ne']
  rw [cubeAverage_cons]
private theorem complexMomentNorm_zeroCube {p : ℝ} (hp : 0 < p) (f : Cube 0 → ℂ) :
    complexMomentNorm p f = ‖f default‖ := by
  unfold complexMomentNorm cubeAverage
  rw [Fintype.sum_unique, pow_zero, div_one, Real.rpow_rpow_inv (norm_nonneg _) hp.ne']
  exact congrArg (fun x : Cube 0 => ‖f x‖) (Subsingleton.elim _ _)
end MomentComparison
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution {p q : ℝ} {w : ℂ} (hq : 0 < q) (hqp : q ≤ p)
    (htwo : ∀ a b : ℂ,
      ((‖a + w * b‖ ^ p + ‖a - w * b‖ ^ p) / 2) ^ p⁻¹ ≤
        ((‖a + b‖ ^ q + ‖a - b‖ ^ q) / 2) ^ q⁻¹)
    {n : ℕ} (f : Cube n → ℂ) :
    complexMomentNorm p (complexNoise w f) ≤ complexMomentNorm q f := by
  have hp := hq.trans_le hqp
  induction n with
  | zero =>
    simp only [complexMomentNorm_zeroCube hp, complexMomentNorm_zeroCube hq, complexNoise_zero]
    rfl
  | succ n ih =>
    let f₁ (x : Cube n) := f (Fin.cons true x)
    let f₂ (x : Cube n) := f (Fin.cons false x)
    let g₁ := complexNoise w f₁
    let g₂ := complexNoise w f₂
    let T := complexNoise w f
    let H (x : Cube n) := ((‖g₁ x‖ ^ q + ‖g₂ x‖ ^ q) / 2) ^ q⁻¹
    have hpos (x : Cube n) : 0 ≤
        (‖T (Fin.cons true x)‖ ^ p + ‖T (Fin.cons false x)‖ ^ p) / 2 :=
      div_nonneg (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (Real.rpow_nonneg (norm_nonneg _) _)) (by norm_num)
    have hpoint (x : Cube n) :
        (‖T (Fin.cons true x)‖ ^ p + ‖T (Fin.cons false x)‖ ^ p) / 2 ≤ H x ^ p := by
      let a := (g₁ x + g₂ x) / 2
      let b := (g₁ x - g₂ x) / 2
      have h₁ : a + b = g₁ x := by dsimp [a, b]; ring
      have h₂ : a - b = g₂ x := by dsimp [a, b]; ring
      have h₃ : a + w * b = T (Fin.cons true x) := by
        simp only [T, complexNoise_cons, ↓reduceIte, one_mul]
        change a + w * b = a + w * (g₁ x - g₂ x) / 2
        rw [mul_div_assoc]
      have h₄ : a - w * b = T (Fin.cons false x) := by
        simp only [T, complexNoise_cons, Bool.false_eq_true, ↓reduceIte]
        change a - w * b = a + (-1) * w * (g₁ x - g₂ x) / 2
        dsimp [b]
        ring
      have h := htwo a b
      rw [h₁, h₂, h₃, h₄] at h
      have h' := Real.rpow_le_rpow (Real.rpow_nonneg (hpos x) _) h hp.le
      rwa [Real.rpow_inv_rpow (hpos x) hp.ne'] at h'
    calc
      complexMomentNorm p T = (cubeAverage fun x : Cube n =>
          (‖T (Fin.cons true x)‖ ^ p + ‖T (Fin.cons false x)‖ ^ p) / 2) ^ p⁻¹ := by
        unfold complexMomentNorm
        rw [cubeAverage_cons, cubeAverage_pair]
      _ ≤ (cubeAverage fun x => H x ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow (cubeAverage_nonneg hpos) (cubeAverage_congr_le hpoint)
          (inv_nonneg.mpr hp.le)
      _ ≤ ((complexMomentNorm p g₁ ^ q + complexMomentNorm p g₂ ^ q) / 2) ^ q⁻¹ :=
        mixedMoment_le hq hqp g₁ g₂
      _ ≤ ((complexMomentNorm q f₁ ^ q + complexMomentNorm q f₂ ^ q) / 2) ^ q⁻¹ := by
        have h₁ := Real.rpow_le_rpow (complexMomentNorm_nonneg p g₁) (ih f₁) hq.le
        have h₂ := Real.rpow_le_rpow (complexMomentNorm_nonneg p g₂) (ih f₂) hq.le
        exact Real.rpow_le_rpow (div_nonneg (add_nonneg
          (Real.rpow_nonneg (complexMomentNorm_nonneg p g₁) _)
          (Real.rpow_nonneg (complexMomentNorm_nonneg p g₂) _)) (by norm_num))
          (div_le_div_of_nonneg_right (add_le_add h₁ h₂) (by norm_num)) (inv_nonneg.mpr hq.le)
      _ = complexMomentNorm q f := (complexMomentNorm_cons hq f).symm
end MomentComparison
