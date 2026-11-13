-- Prove2me | solution 1 for MvResultant.isWeightedHomogeneous_block
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T18:57:32.440069+00:00
-- url     : https://prove2.me/submissions/38c3d7f0-6fef-47c6-8402-365ccecd0c5c

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Theorems.Thm_MvResultant_dvd_of_vanishing

open HararySachs.Hyper MvPolynomial Finset

namespace BlockHomAux

variable {n : ℕ} {D : Fin n → ℕ}

/-- weight `1` on the coefficients of the `i`-th form -/
def wt (i : Fin n) : ResVar n D → ℕ := fun v => if v.1 = i then 1 else 0

/-- scale each coefficient by `2 ^ (block-i degree of its monomial)` -/
noncomputable def scale (i : Fin n) (P : MvPolynomial (ResVar n D) ℂ) :
    MvPolynomial (ResVar n D) ℂ :=
  ∑ m ∈ P.support, monomial m ((2 : ℂ) ^ Finsupp.weight (wt i) m * coeff m P)

lemma coeff_scale (i : Fin n) (P : MvPolynomial (ResVar n D) ℂ) (m : ResVar n D →₀ ℕ) :
    coeff m (scale i P) = (2 : ℂ) ^ Finsupp.weight (wt i) m * coeff m P := by
  classical
  unfold scale
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, mul_zero]

lemma support_scale (i : Fin n) (P : MvPolynomial (ResVar n D) ℂ) :
    (scale i P).support = P.support := by
  ext m
  rw [mem_support_iff, mem_support_iff, coeff_scale]
  constructor
  · intro h h0; exact h (by rw [h0, mul_zero])
  · intro h; exact mul_ne_zero (pow_ne_zero _ two_ne_zero) h

lemma aeval_scale (i : Fin n) (P : MvPolynomial (ResVar n D) ℂ) (u : ResVar n D → ℂ) :
    aeval u (scale i P) = aeval (fun v => (if v.1 = i then (2 : ℂ) else 1) * u v) P := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, support_scale]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_scale]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, mul_pow, prod_mul_distrib]
  have hw : ∏ v ∈ m.support, (if v.1 = i then (2 : ℂ) else 1) ^ m v =
      (2 : ℂ) ^ Finsupp.weight (wt i) m := by
    rw [Finsupp.weight_apply, Finsupp.sum, ← prod_pow_eq_pow_sum]
    refine prod_congr rfl fun v _ => ?_
    unfold wt
    split_ifs <;> simp
  rw [hw]
  ring

end BlockHomAux

open BlockHomAux in
theorem solution {n : ℕ} {D : Fin n → ℕ}
    (res : MvPolynomial (ResVar n D) ℤ) (hres : IsResultant n D res) (i : Fin n) :
    ∃ δ : ℕ, res.IsWeightedHomogeneous
      (fun v : ResVar n D => if v.1 = i then 1 else 0) δ := by
  classical
  set P := MvPolynomial.map (Int.castRingHom ℂ) res with hPdef
  by_cases hres0 : res = 0
  · exact ⟨0, by rw [hres0]; exact isWeightedHomogeneous_zero _ _ _⟩
  have hcoeff : ∀ d, coeff d P = ((coeff d res : ℤ) : ℂ) := fun d => by
    rw [hPdef, coeff_map]; rfl
  have hP0 : P ≠ 0 := by
    intro h
    apply hres0
    ext d
    have := hcoeff d
    rw [h, coeff_zero] at this
    simpa using this.symm
  -- the scaled resultant vanishes on every solvable system
  have hQ : ∀ F : Fin n → MvPolynomial (Fin n) ℂ, (∀ j, (F j).IsHomogeneous (D j)) →
      (∃ x : Fin n → ℂ, x ≠ 0 ∧ ∀ j, MvPolynomial.eval x (F j) = 0) →
      aeval (fun v : ResVar n D => coeff v.2.1 (F v.1)) (scale i P) = 0 := by
    intro F hF hx
    rw [aeval_scale]
    set F' : Fin n → MvPolynomial (Fin n) ℂ :=
      fun j => C (if j = i then (2 : ℂ) else 1) * F j with hF'
    have hcF : (fun v : ResVar n D => (if v.1 = i then (2 : ℂ) else 1) * coeff v.2.1 (F v.1)) =
        fun v => coeff v.2.1 (F' v.1) := by
      funext v; simp only [hF', coeff_C_mul]
    rw [hcF]
    have hhom : ∀ j, (F' j).IsHomogeneous (D j) := fun j => by
      have := (isHomogeneous_C (Fin n) (if j = i then (2 : ℂ) else 1)).mul (hF j)
      simpa using this
    apply ((hres.1 F' hhom).mp)
    obtain ⟨x, hx0, hxF⟩ := hx
    exact ⟨x, hx0, fun j => by simp [hF', hxF j]⟩
  obtain ⟨h, hh⟩ := MvResultant.dvd_of_vanishing res hres (scale i P) hQ
  -- the cofactor is a constant
  have hQ0 : scale i P ≠ 0 := by
    intro h0
    apply hP0
    rw [← support_eq_empty, ← support_scale i P, h0, support_zero]
  have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hh; exact hQ0 hh
  have hdeg : (scale i P).totalDegree = P.totalDegree := by
    unfold totalDegree; rw [support_scale]
  have hconst : h.totalDegree = 0 := by
    have := totalDegree_mul_of_isDomain hP0 hh0
    rw [← hh, hdeg] at this
    omega
  rw [totalDegree_eq_zero_iff_eq_C] at hconst
  set μ := coeff 0 h
  -- compare coefficients: `2 ^ weight = μ` on the support
  have hμ : ∀ d, coeff d P ≠ 0 → (2 : ℂ) ^ Finsupp.weight (wt i) d = μ := by
    intro d hd
    have := congrArg (coeff d) hh
    rw [coeff_scale, hconst, mul_comm P, coeff_C_mul] at this
    exact mul_right_cancel₀ hd this
  obtain ⟨m0, hm0⟩ := support_nonempty.mpr hP0
  refine ⟨Finsupp.weight (wt i) m0, fun d hd => ?_⟩
  have hdP : coeff d P ≠ 0 := by rw [hcoeff]; exact_mod_cast hd
  have h1 := (hμ d hdP).trans (hμ m0 (mem_support_iff.mp hm0)).symm
  have h2 : ((2 ^ Finsupp.weight (wt i) d : ℕ) : ℂ) = ((2 ^ Finsupp.weight (wt i) m0 : ℕ) : ℂ) := by
    push_cast; exact h1
  exact Nat.pow_right_injective le_rfl (Nat.cast_injective h2)
