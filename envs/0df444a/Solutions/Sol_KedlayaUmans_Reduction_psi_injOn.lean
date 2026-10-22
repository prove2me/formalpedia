-- Prove2me | solution 1 for KedlayaUmans.Reduction.psi_injOn
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:43:03.911517+00:00
-- url     : https://prove2.me/submissions/98c50f0a-c344-4971-95e2-5970bbc6c254

import Mathlib
import Definitions.Def_KedlayaUmans_Reduction_Psi

set_option autoImplicit false
open MvPolynomial KedlayaUmans.Reduction

lemma kur_digits_sum (h : ℕ) (hh : 2 ≤ h) (ℓ : ℕ) :
    ∀ a : ℕ, a < h ^ ℓ → ∑ j : Fin ℓ, (Nat.digits h a).getD j 0 * h ^ (j : ℕ) = a := by
  induction ℓ with
  | zero =>
    intro a ha
    have : a = 0 := by simpa using ha
    subst this; simp
  | succ ℓ ih =>
    intro a ha
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · simp
    · rw [Fin.sum_univ_succ]
      have hd : Nat.digits h a = (a % h) :: Nat.digits h (a / h) := Nat.digits_def' (by omega) hpos
      have hlt : a / h < h ^ ℓ := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc a < h ^ (ℓ + 1) := ha
          _ = h ^ ℓ * h := pow_succ _ _
      have := ih (a / h) hlt
      simp only [hd, Fin.val_zero, pow_zero, mul_one, Fin.val_succ, List.getD_cons_zero,
        List.getD_cons_succ]
      have h2 : ∑ i : Fin ℓ, (Nat.digits h (a / h)).getD (i : ℕ) 0 * h ^ ((i : ℕ) + 1) =
          h * ∑ i : Fin ℓ, (Nat.digits h (a / h)).getD (i : ℕ) 0 * h ^ (i : ℕ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [h2, this]
      have := Nat.mod_add_div a h
      omega

theorem kur_inverse {R : Type*} [CommRing R] {m : ℕ} (h ℓ : ℕ) (hh : 2 ≤ h)
    (f : MvPolynomial (Fin m) R) (hf : ∀ i, f.degreeOf i ≤ h ^ ℓ - 1) :
    aeval (fun ij : Fin m × Fin ℓ => (X ij.1 : MvPolynomial (Fin m) R) ^ (h ^ (ij.2 : ℕ)))
      (psi h ℓ f) = f := by
  have hpos : 0 < h ^ ℓ := Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
  conv_rhs => rw [f.as_sum]
  unfold psi
  rw [map_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hbound : ∀ i, e i < h ^ ℓ := by
    intro i
    have h1 : e i ≤ f.degreeOf i := by
      rw [MvPolynomial.degreeOf_eq_sup]
      exact Finset.le_sup (f := fun s : Fin m →₀ ℕ => s i) he
    have := hf i
    omega
  rw [aeval_monomial, monomial_eq]
  simp only [algebraMap_eq]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by intro ij; simp)]
  rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : ∀ j : Fin ℓ, ((X i : MvPolynomial (Fin m) R) ^ h ^ (j : ℕ)) ^ (digitExp h ℓ e (i, j)) =
      X i ^ ((Nat.digits h (e i)).getD j 0 * h ^ (j : ℕ)) := by
    intro j
    simp only [digitExp, Finsupp.equivFunOnFinite_symm_apply_apply, ← pow_mul]
    rw [mul_comm]
  simp only [this]
  rw [Finset.prod_pow_eq_pow_sum, kur_digits_sum h hh ℓ (e i) (hbound i)]

theorem solution {R : Type*} [CommRing R] {m : ℕ} (h ℓ : ℕ) (hh : 2 ≤ h) :
    Set.InjOn (psi (R := R) (m := m) h ℓ)
      {f : MvPolynomial (Fin m) R | ∀ i, f.degreeOf i ≤ h ^ ℓ - 1} := by
  intro f hf g hg hfg
  have h1 := kur_inverse h ℓ hh f hf
  have h2 := kur_inverse h ℓ hh g hg
  rw [← h1, ← h2, hfg]
