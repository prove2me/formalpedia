-- Prove2me | solution 1 for GeneralizedComplex.eq_of_plusIEigenspace_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:30:32.320472+00:00
-- url     : https://prove2.me/submissions/a226f659-e212-46eb-a927-397017d7b143

import Mathlib
import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GCAux
open GeneralizedComplex

noncomputable abbrev Jc {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) : Matrix (GIdx N) (GIdx N) ℂ :=
  J.map (fun x : ℝ => (x : ℂ))

lemma mem_plusI {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (v : GIdx N → ℂ) :
    v ∈ plusIEigenspace J ↔ Jc J *ᵥ v = Complex.I • v := by
  simp [plusIEigenspace, sub_eq_zero]

lemma star_mulVec {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (v : GIdx N → ℂ) :
    star (Jc J *ᵥ v) = Jc J *ᵥ star v := by
  ext i
  simp [mulVec, dotProduct, Matrix.map_apply]

lemma Jc_sq {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (h : J * J = -1) (v : GIdx N → ℂ) :
    Jc J *ᵥ (Jc J *ᵥ v) = -v := by
  rw [mulVec_mulVec]
  have : Jc J * Jc J = -1 := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply] at this ⊢
    rw [← Complex.ofReal_inj] at this
    push_cast at this
    rw [this]; split_ifs <;> simp
  rw [this, neg_mulVec, one_mulVec]

lemma eq_of_eq {N : ℕ} (J₁ J₂ : Matrix (GIdx N) (GIdx N) ℝ)
    (h₁ : IsGenAlmostComplex J₁) (h : plusIEigenspace J₁ = plusIEigenspace J₂) : J₁ = J₂ := by
  have key : ∀ v, Jc J₁ *ᵥ v = Jc J₂ *ᵥ v := by
    intro v
    set a := v - Complex.I • (Jc J₁ *ᵥ v) with ha
    set b := v + Complex.I • (Jc J₁ *ᵥ v) with hb
    have hsq := Jc_sq J₁ h₁.sq_eq_neg_one v
    have hIa : Jc J₁ *ᵥ a = Complex.I • a := by
      rw [ha, mulVec_sub, mulVec_smul, hsq, smul_sub, smul_smul, Complex.I_mul_I]
      ext i; simp; try ring
    have hIb : Jc J₁ *ᵥ b = -(Complex.I • b) := by
      rw [hb, mulVec_add, mulVec_smul, hsq, smul_add, smul_smul, Complex.I_mul_I]
      ext i; simp; try ring
    have ha2 : Jc J₂ *ᵥ a = Complex.I • a := (mem_plusI J₂ a).1 (h ▸ (mem_plusI J₁ a).2 hIa)
    have hsb : Jc J₁ *ᵥ star b = Complex.I • star b := by
      rw [← star_mulVec, hIb, star_neg, star_smul]
      ext i; simp [Complex.conj_I]
    have hsb2 : Jc J₂ *ᵥ star b = Complex.I • star b := (mem_plusI J₂ _).1 (h ▸ (mem_plusI J₁ _).2 hsb)
    have hb2 : Jc J₂ *ᵥ b = -(Complex.I • b) := by
      have := congrArg star hsb2
      rw [star_mulVec, star_star, star_smul, star_star] at this
      rw [this]; ext i; simp
    have hv : v = (1 / 2 : ℂ) • (a + b) := by
      rw [ha, hb]; ext i; simp; ring
    have e1 : Jc J₂ *ᵥ v = (1 / 2 : ℂ) • (Complex.I • a - Complex.I • b) := by
      rw [hv, mulVec_smul, mulVec_add, ha2, hb2, sub_eq_add_neg]
    rw [e1, ha, hb]
    ext i; simp; ring_nf; rw [Complex.I_sq]; ring
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simp [mulVec, dotProduct, Pi.single_apply] at this
  exact_mod_cast this

end GCAux

open GeneralizedComplex GCAux in
theorem solution {N : ℕ} (J₁ J₂ : Matrix (GIdx N) (GIdx N) ℝ)
    (h₁ : IsGenAlmostComplex J₁) (h₂ : IsGenAlmostComplex J₂)
    (h : plusIEigenspace J₁ = plusIEigenspace J₂) : J₁ = J₂ := eq_of_eq J₁ J₂ h₁ h
