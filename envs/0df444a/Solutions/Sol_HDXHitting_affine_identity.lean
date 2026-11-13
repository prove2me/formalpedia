-- Prove2me | solution 1 for HDXHitting.affine_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:52.794836+00:00
-- url     : https://prove2.me/submissions/50d1ad4a-1d0b-49eb-85d0-d488da7bcf14

import Mathlib
import Definitions.Def_HDXHitting_cPoly

section
set_option autoImplicit false
namespace HDXHitting.Dev.Aff
open HDXHitting

/-- `cPoly` is affine in the `i`-th coordinate. -/
lemma cpoly_update {ι : Type*} [DecidableEq ι] (S : Finset ι) (i : ι) (hi : i ∈ S) (lam : ℝ)
    (μ : ι → ℝ) (t : ℝ) :
    cPoly S lam (Function.update μ i t) =
      (1 / (S.card : ℝ)) * (((S.card : ℝ) * lam) *
          ∑ k ∈ S.erase i, μ k * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam)) +
      (1 / (S.card : ℝ)) * (∏ j ∈ S.erase i, (μ j + S.card * lam) +
          ∑ k ∈ S.erase i, μ k * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam)) * t := by
  unfold cPoly
  rw [← Finset.add_sum_erase S _ hi]
  have h1 : ∏ j ∈ S.erase i, (Function.update μ i t j + S.card * lam)
      = ∏ j ∈ S.erase i, (μ j + S.card * lam) :=
    Finset.prod_congr rfl (fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  have h2 : ∀ k ∈ S.erase i, Function.update μ i t k *
        ∏ j ∈ S.erase k, (Function.update μ i t j + S.card * lam)
      = (μ k * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam)) * (t + S.card * lam) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have hkS : k ∈ S := Finset.mem_of_mem_erase hk
    have hiek : i ∈ S.erase k := Finset.mem_erase.2 ⟨hki.symm, hi⟩
    rw [Function.update_of_ne hki, ← Finset.mul_prod_erase (S.erase k) _ hiek,
      Function.update_self, Finset.erase_right_comm]
    have : ∏ j ∈ (S.erase i).erase k, (Function.update μ i t j + S.card * lam)
        = ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam) :=
      Finset.prod_congr rfl (fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj))])
    rw [this]; ring
  rw [Finset.sum_congr rfl h2, Function.update_self, h1, ← Finset.sum_mul]
  ring

/-- The slope equals `c_{d-1}(μ_{-i} + λ)`. -/
lemma slope_eq {ι : Type*} [DecidableEq ι] (S : Finset ι) (hS : 2 ≤ S.card) (i : ι)
    (hi : i ∈ S) (lam : ℝ) (μ : ι → ℝ) :
    (1 / (S.card : ℝ)) * (∏ j ∈ S.erase i, (μ j + S.card * lam) +
          ∑ k ∈ S.erase i, μ k * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam)) =
      cPoly (S.erase i) lam (fun j => μ j + lam) := by
  have hc : ((S.erase i).card : ℝ) = (S.card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hi, Nat.cast_sub (by omega)]; simp
  have hd : (S.card : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    linarith
  have hd1 : (S.card : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    linarith
  unfold cPoly
  rw [hc]
  set P := ∏ j ∈ S.erase i, (μ j + S.card * lam) with hP
  have hPk : ∀ k ∈ S.erase i, P = (μ k + S.card * lam) * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam) :=
    fun k hk => (Finset.mul_prod_erase (S.erase i) (fun j => μ j + S.card * lam) hk).symm
  have hinner : ∀ k ∈ S.erase i, (μ k + lam) *
        ∏ j ∈ (S.erase i).erase k, ((μ j + lam) + ((S.card : ℝ) - 1) * lam)
      = (μ k + lam) * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam) := by
    intro k hk
    congr 1
    exact Finset.prod_congr rfl (fun j _ => by ring)
  rw [Finset.sum_congr rfl hinner]
  have hsum : ((S.card : ℝ) - 1) * P =
      ∑ k ∈ S.erase i, (μ k + S.card * lam) * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam) := by
    rw [← hc, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl hPk
  have hkey : (S.card : ℝ) * ∑ k ∈ S.erase i, (μ k + lam) * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam)
      = ((S.card : ℝ) - 1) * (P + ∑ k ∈ S.erase i, μ k * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam)) := by
    have : (S.card : ℝ) * ∑ k ∈ S.erase i, (μ k + lam) * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam)
        = ∑ k ∈ S.erase i, (μ k + S.card * lam) * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam)
          + ((S.card : ℝ) - 1) * ∑ k ∈ S.erase i, μ k * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [this, ← hsum]; ring
  field_simp
  linarith [hkey]
end HDXHitting.Dev.Aff
namespace HDXHitting
open HDXHitting.Dev.Aff in
theorem chk_affine_identity {ι : Type*} [DecidableEq ι] (S : Finset ι) (hS : 2 ≤ S.card) (i : ι)
    (hi : i ∈ S) (lam : ℝ) (μ : ι → ℝ) (h : ℝ) :
    HasDerivAt (fun t => cPoly S lam (Function.update μ i t))
        (cPoly (S.erase i) lam (fun j => μ j + lam)) (μ i) ∧
      cPoly S lam (μ - h • Pi.single i 1) + h * cPoly (S.erase i) lam (fun j => μ j + lam) =
        cPoly S lam μ := by
  have hB := slope_eq S hS i hi lam μ
  have hF := cpoly_update S i hi lam μ
  set A := (1 / (S.card : ℝ)) * (((S.card : ℝ) * lam) *
          ∑ k ∈ S.erase i, μ k * ∏ j ∈ (S.erase i).erase k, (μ j + S.card * lam)) with hA
  set B := cPoly (S.erase i) lam (fun j => μ j + lam) with hBdef
  have hF' : ∀ t, cPoly S lam (Function.update μ i t) = A + B * t := fun t => by
    rw [hF t, ← hB]
  constructor
  · have : (fun t => cPoly S lam (Function.update μ i t)) = fun t => A + B * t := funext hF'
    rw [this]
    exact ((hasDerivAt_id (μ i)).const_mul B).const_add A |>.congr_deriv (by simp)
  · have hμ : μ - h • Pi.single i (1 : ℝ) = Function.update μ i (μ i - h) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj, Pi.single_apply, hj]
    have hμ2 : cPoly S lam μ = A + B * μ i := by
      rw [← hF' (μ i), Function.update_eq_self]
    rw [hμ, hF', hμ2]; ring
end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_affine_identity := @HDXHitting.chk_affine_identity
