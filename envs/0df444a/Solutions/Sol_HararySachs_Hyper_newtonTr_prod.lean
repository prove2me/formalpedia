-- Prove2me | solution 1 for HararySachs.Hyper.newtonTr_prod
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T04:38:50.615102+00:00
-- url     : https://prove2.me/submissions/048ee88b-56fb-436e-ab59-37fb8d60aafe

import Mathlib
import Definitions.Def_HararySachs_Hyper_TensorPhi

open HararySachs.Hyper Finset

namespace NewtonProdAux2

variable {R : Type*} [CommRing R]

/-- Newton's identities in the form `n Φ_n = -Σ_{a+b=n} τ_a Φ_b`, valid for all `n`. -/
lemma newton_anti (Φ : Polynomial R) (h0 : Φ.coeff 0 = 1) (n : ℕ) :
    (n : R) * Φ.coeff n = -∑ p ∈ antidiagonal n, newtonTr Φ p.1 * Φ.coeff p.2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => newtonTr Φ a * Φ.coeff b)]
  cases n with
  | zero => simp [newtonTr]
  | succ e =>
    rw [sum_range_succ, Nat.sub_self, h0, mul_one, newtonTr.eq_2,
      ← Fin.sum_univ_eq_sum_range (fun j => newtonTr Φ j * Φ.coeff (e + 1 - j))]
    ring

/-- Newton's recursion determines the traces uniquely. -/
lemma newtonTr_unique (Φ : Polynomial R) (h0 : Φ.coeff 0 = 1) (t : ℕ → R) (ht0 : t 0 = 0)
    (ht : ∀ n : ℕ, (n : R) * Φ.coeff n = -∑ p ∈ antidiagonal n, t p.1 * Φ.coeff p.2) (m : ℕ) :
    newtonTr Φ m = t m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => rw [newtonTr, ht0]
    | succ e =>
      have h := ht (e + 1)
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => t a * Φ.coeff b),
        sum_range_succ, Nat.sub_self, h0, mul_one] at h
      rw [newtonTr.eq_2,
        Fin.sum_univ_eq_sum_range (fun j => newtonTr Φ j * Φ.coeff (e + 1 - j))]
      have hs : ∑ j ∈ range (e + 1), newtonTr Φ j * Φ.coeff (e + 1 - j) =
          ∑ j ∈ range (e + 1), t j * Φ.coeff (e + 1 - j) :=
        sum_congr rfl fun j hj => by rw [ih j (mem_range.mp hj)]
      rw [hs]
      linear_combination -h

/-- the Euler operator `z d/dz` on power series -/
noncomputable def eul (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => (n : R) * PowerSeries.coeff n f

lemma eul_mul (f g : PowerSeries R) : eul (f * g) = eul f * g + f * eul g := by
  ext n
  simp only [eul, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_mul, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp]
  push_cast; ring

/-- the generating series of the Newton traces -/
noncomputable def tser (Φ : Polynomial R) : PowerSeries R := PowerSeries.mk (newtonTr Φ)

lemma eul_eq (Φ : Polynomial R) (h0 : Φ.coeff 0 = 1) :
    eul (Φ : PowerSeries R) = -(tser Φ * Φ) := by
  ext n
  rw [eul, PowerSeries.coeff_mk, map_neg, PowerSeries.coeff_mul, Polynomial.coeff_coe,
    newton_anti Φ h0 n]
  simp only [tser, PowerSeries.coeff_mk, Polynomial.coeff_coe]

lemma newtonTr_mul (Φ Ψ : Polynomial R) (hΦ : Φ.coeff 0 = 1) (hΨ : Ψ.coeff 0 = 1) (m : ℕ) :
    newtonTr (Φ * Ψ) m = newtonTr Φ m + newtonTr Ψ m := by
  have h0 : (Φ * Ψ).coeff 0 = 1 := by rw [Polynomial.mul_coeff_zero, hΦ, hΨ, mul_one]
  refine newtonTr_unique (Φ * Ψ) h0 (fun j => newtonTr Φ j + newtonTr Ψ j)
    (by simp [newtonTr]) (fun n => ?_) m
  have hE : eul ((Φ * Ψ : Polynomial R) : PowerSeries R) =
      -((tser Φ + tser Ψ) * ((Φ * Ψ : Polynomial R) : PowerSeries R)) := by
    rw [Polynomial.coe_mul, eul_mul, eul_eq Φ hΦ, eul_eq Ψ hΨ]
    ring
  have h := congrArg (PowerSeries.coeff n) hE
  rw [eul, PowerSeries.coeff_mk, map_neg, PowerSeries.coeff_mul, Polynomial.coeff_coe] at h
  rw [h]
  simp only [tser, map_add, PowerSeries.coeff_mk, Polynomial.coeff_coe]

end NewtonProdAux2

open NewtonProdAux2 in
theorem solution {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (Φ : ι → Polynomial R) (h : ∀ l ∈ s, (Φ l).coeff 0 = 1) (m : ℕ) :
    newtonTr (∏ l ∈ s, Φ l) m = ∑ l ∈ s, newtonTr (Φ l) m := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [prod_empty, sum_empty]
    refine newtonTr_unique 1 Polynomial.coeff_one_zero (fun _ => 0) rfl (fun n => ?_) m
    simp only [zero_mul, sum_const_zero, neg_zero, Polynomial.coeff_one]
    split_ifs with hn
    · rw [hn, Nat.cast_zero, zero_mul]
    · rw [mul_zero]
  | insert a s ha ih =>
    have hs : ∀ l ∈ s, (Φ l).coeff 0 = 1 := fun l hl => h l (mem_insert_of_mem hl)
    have hp : (∏ l ∈ s, Φ l).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_prod]; exact prod_eq_one hs
    rw [prod_insert ha, sum_insert ha, newtonTr_mul _ _ (h a (mem_insert_self a s)) hp, ih hs]
