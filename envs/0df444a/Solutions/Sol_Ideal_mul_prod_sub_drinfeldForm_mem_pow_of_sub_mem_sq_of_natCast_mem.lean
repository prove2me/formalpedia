-- Prove2me | solution 1 for Ideal.mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8ca59abd-833e-56e7-941a-69b10231d6a9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem

set_option autoImplicit false

open IsLocalRing

section AuxOpen

open Polynomial

namespace DrinformAux

lemma prod_sub_prod_mem_pow {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι] (s : Finset ι) (I : Ideal R)
    (P L : ι → R) (hL : ∀ i ∈ s, L i ∈ I) (hPL : ∀ i ∈ s, P i - L i ∈ I ^ 2) :
    (∏ i ∈ s, P i) - (∏ i ∈ s, L i) ∈ I ^ (s.card + 1) ∧ (∏ i ∈ s, L i) ∈ I ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hL i (Finset.mem_insert_of_mem hi))
      (fun i hi => hPL i (Finset.mem_insert_of_mem hi))
    have hLa : L a ∈ I := hL a (Finset.mem_insert_self a s)
    have hPLa : P a - L a ∈ I ^ 2 := hPL a (Finset.mem_insert_self a s)
    have hPa : P a ∈ I := by
      have h := I.add_mem (Ideal.pow_le_self two_ne_zero hPLa) hLa
      simpa using h
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine ⟨?_, ?_⟩
    · have hsplit : P a * ∏ i ∈ s, P i - L a * ∏ i ∈ s, L i =
          P a * (∏ i ∈ s, P i - ∏ i ∈ s, L i) + (P a - L a) * ∏ i ∈ s, L i := by ring
      rw [hsplit]
      refine Ideal.add_mem _ ?_ ?_
      · have h := Ideal.mul_mem_mul hPa ih1
        rwa [← pow_succ'] at h
      · have h := Ideal.mul_mem_mul hPLa ih2
        rwa [← pow_add, show 2 + s.card = s.card + 1 + 1 by omega] at h
    · have h := Ideal.mul_mem_mul hLa ih2
      rwa [← pow_succ'] at h

section Universal

variable (q : ℕ) [hq : Fact q.Prime]

lemma prod_X_add_C_mul :
    ∏ c : ZMod q, ((X : Polynomial (Polynomial (ZMod q))) + C (C c * X)) =
      X ^ q - C ((X : Polynomial (ZMod q)) ^ (q - 1)) * X := by
  classical
  have hq1 : 1 < q := hq.out.one_lt
  have hq0 : q ≠ 0 := hq.out.ne_zero

  set p : Polynomial (Polynomial (ZMod q)) := X ^ q - C ((X : Polynomial (ZMod q)) ^ (q - 1)) * X with hp
  have hdeg1 : (C ((X : Polynomial (ZMod q)) ^ (q - 1)) * X).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (by simp)
  have hmonic : p.Monic := by
    apply (monic_X_pow q).sub_of_left
    calc degree (C ((X : Polynomial (ZMod q)) ^ (q - 1)) * X) ≤ 1 := by
            exact (degree_le_natDegree).trans (by exact_mod_cast hdeg1)
      _ < degree ((X : Polynomial (Polynomial (ZMod q))) ^ q) := by
            rw [degree_X_pow]; exact_mod_cast hq1
  have hnat : p.natDegree = q := by
    rw [hp, natDegree_sub_eq_left_of_natDegree_lt] <;> simp only [natDegree_X_pow]
    exact lt_of_le_of_lt hdeg1 hq1

  have hroot : ∀ c : ZMod q, p.IsRoot (C c * X) := by
    intro c
    simp only [hp, IsRoot, eval_sub, eval_pow, eval_X, eval_mul, eval_C, mul_pow, ← C_pow, ZMod.pow_card]
    rw [sub_eq_zero, mul_comm (X ^ (q - 1)) (C c * X), mul_assoc, mul_pow_sub_one hq0]
  have hinj : Function.Injective (fun c : ZMod q => C c * (X : Polynomial (ZMod q))) := by
    intro c d h
    have := congrArg (fun f : Polynomial (ZMod q) => f.coeff 1) h
    simpa using this
  set m : Multiset (Polynomial (ZMod q)) := (Finset.univ : Finset (ZMod q)).val.map (fun c => C c * X) with hm
  have hm_nodup : m.Nodup := Multiset.Nodup.map hinj Finset.univ.nodup
  have hm_le : m ≤ p.roots := by
    rw [Multiset.le_iff_subset hm_nodup]
    intro a ha
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp ha
    exact (mem_roots hmonic.ne_zero).mpr (hroot c)
  have hcard : m.card = q := by simp [hm, ZMod.card]
  have hroots : p.roots = m :=
    (Multiset.eq_of_le_of_card_le hm_le (by rw [hcard]; exact (card_roots' p).trans hnat.le)).symm
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic (by rw [hroots, hcard, hnat])
  rw [hroots, hm, Multiset.map_map] at hprod

  calc ∏ c : ZMod q, ((X : Polynomial (Polynomial (ZMod q))) + C (C c * X))
      = ∏ c : ZMod q, ((X : Polynomial (Polynomial (ZMod q))) - C (C (-c) * X)) :=
          Finset.prod_congr rfl (fun c _ => by simp)
    _ = ∏ c : ZMod q, ((X : Polynomial (Polynomial (ZMod q))) - C (C c * X)) :=
          Fintype.prod_equiv (Equiv.neg (ZMod q)) _ _ (fun c => rfl)
    _ = (Multiset.map ((fun a => X - C a) ∘ fun c => C c * X) (Finset.univ : Finset (ZMod q)).val).prod := by
          rw [Finset.prod_eq_multiset_prod]; rfl
    _ = p := hprod

lemma prod_add_mul_eq {B : Type*} [CommRing B] (ψ : ZMod q →+* B) (a b : B) :
    ∏ c : ZMod q, (a + ψ c * b) = a ^ q - b ^ (q - 1) * a := by
  have h := congrArg (eval₂RingHom (eval₂RingHom ψ b) a) (prod_X_add_C_mul q)
  simp only [map_prod, map_add, map_sub, map_mul, map_pow] at h
  simpa [Polynomial.coe_eval₂RingHom, eval₂_X, eval₂_C] using h

end Universal

end DrinformAux

end AuxOpen

namespace SSFGallq

open Polynomial

section DrinP

variable (q : ℕ) [hq : Fact q.Prime]

noncomputable def drinP : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.X 0 * ∏ c : ZMod q, (MvPolynomial.X 1 + MvPolynomial.C (((c.val : ℕ) : ℤ)) * MvPolynomial.X 0) -
    (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1)

theorem drinP_isHomogeneous : (drinP q).IsHomogeneous (q + 1) := by
  have hq0 : q ≠ 0 := hq.out.ne_zero
  have hX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X _ _
  have hX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X _ _
  have hlin : ∀ c : ZMod q,
      (MvPolynomial.X 1 + MvPolynomial.C (((c.val : ℕ) : ℤ)) * MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ).IsHomogeneous 1 := by
    intro c
    refine hX1.add ?_
    have := (MvPolynomial.isHomogeneous_C (Fin 2) (((c.val : ℕ) : ℤ))).mul hX0
    rwa [zero_add] at this
  have hprod : (∏ c : ZMod q, (MvPolynomial.X 1 + MvPolynomial.C (((c.val : ℕ) : ℤ)) * MvPolynomial.X 0 :
      MvPolynomial (Fin 2) ℤ)).IsHomogeneous q := by
    have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (ZMod q)) _ (fun _ => 1) (fun c _ => hlin c)
    rwa [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one] at this
  unfold drinP
  refine MvPolynomial.IsHomogeneous.sub ?_ (MvPolynomial.IsHomogeneous.sub ?_ ?_)
  · have := hX0.mul hprod; rwa [add_comm] at this
  · have := hX0.mul (hX1.pow q); rwa [one_mul, add_comm] at this
  · have := (hX0.pow q).mul hX1; rwa [one_mul] at this

theorem map_drinP_eq_zero : MvPolynomial.map (Int.castRingHom (ZMod q)) (drinP q) = 0 := by
  have hq0 : q ≠ 0 := hq.out.ne_zero
  have key := DrinformAux.prod_add_mul_eq q (algebraMap (ZMod q) (MvPolynomial (Fin 2) (ZMod q)))
    (MvPolynomial.X 1) (MvPolynomial.X 0)
  unfold drinP
  simp only [map_sub, map_mul, map_prod, map_add, map_pow, MvPolynomial.map_X, MvPolynomial.map_C, map_natCast]
  have hC : ∀ c : ZMod q, ((c.val : ℕ) : MvPolynomial (Fin 2) (ZMod q)) =
      algebraMap (ZMod q) (MvPolynomial (Fin 2) (ZMod q)) c := by
    intro c
    rw [← map_natCast (algebraMap (ZMod q) (MvPolynomial (Fin 2) (ZMod q))), ZMod.natCast_zmod_val]
  have hC2 : ∀ c : ZMod q, (MvPolynomial.C ((c.val : ℕ) : ZMod q) : MvPolynomial (Fin 2) (ZMod q)) =
      algebraMap (ZMod q) (MvPolynomial (Fin 2) (ZMod q)) c := by
    intro c; rw [ZMod.natCast_zmod_val]; rfl
  simp only [hC, hC2]
  rw [key, ← pow_sub_one_mul hq0 (MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod q))]
  ring

theorem dvd_coeff_drinP (m : Fin 2 →₀ ℕ) : (q : ℤ) ∣ MvPolynomial.coeff m (drinP q) := by
  have h := congrArg (MvPolynomial.coeff m) (map_drinP_eq_zero q)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h

theorem mul_prod_sub_drinfeldForm_mem_pow
    (R : Type) [CommRing R] (𝔪 : Ideal R) (hqm : ((q : ℕ) : R) ∈ 𝔪)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ 𝔪) (hx₁ : x₁ ∈ 𝔪)
    (P : ZMod q → R) (hP : ∀ c : ZMod q, P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ 𝔪 ^ 2) :
    x₀ * (∏ c : ZMod q, P c) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ 𝔪 ^ (q + 2) := by
  classical

  obtain ⟨h1, -⟩ := DrinformAux.prod_sub_prod_mem_pow (Finset.univ : Finset (ZMod q)) 𝔪 P
    (fun c => x₁ + ((c.val : ℕ) : R) * x₀)
    (fun c _ => 𝔪.add_mem hx₁ (𝔪.mul_mem_left _ hx₀)) (fun c _ => hP c)
  rw [Finset.card_univ, ZMod.card] at h1

  have h3 : x₀ * ∏ c : ZMod q, (x₁ + ((c.val : ℕ) : R) * x₀) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ 𝔪 ^ (q + 2) := by
    have heval : MvPolynomial.eval₂Hom (Int.castRingHom R) (![x₀, x₁] : Fin 2 → R) (drinP q) =
        x₀ * ∏ c : ZMod q, (x₁ + ((c.val : ℕ) : R) * x₀) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) := by
      unfold drinP
      simp only [map_sub, map_mul, map_prod, map_add, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
        map_natCast, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [← heval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
    refine Ideal.sum_mem _ fun m hm => ?_
    obtain ⟨k, hk⟩ := dvd_coeff_drinP q m
    have hdeg : m 0 + m 1 = q + 1 := by
      have hw := drinP_isHomogeneous q (MvPolynomial.mem_support_iff.mp hm)
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hw
    rw [hk, map_mul, map_natCast, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have hmon : x₀ ^ m 0 * x₁ ^ m 1 ∈ 𝔪 ^ (q + 1) := by
      rw [← hdeg, pow_add]; exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx₀ _) (Ideal.pow_mem_pow hx₁ _)
    have : ((q : ℕ) : R) * (Int.castRingHom R k) * (x₀ ^ m 0 * x₁ ^ m 1) ∈ 𝔪 ^ (q + 2) := by
      rw [pow_succ']; exact Ideal.mul_mem_mul (𝔪.mul_mem_right _ hqm) hmon
    simpa [mul_assoc] using this
  have hsplit : x₀ * (∏ c : ZMod q, P c) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) =
      x₀ * ((∏ c : ZMod q, P c) - ∏ c : ZMod q, (x₁ + ((c.val : ℕ) : R) * x₀)) +
        (x₀ * ∏ c : ZMod q, (x₁ + ((c.val : ℕ) : R) * x₀) - (x₀ * x₁ ^ q - x₀ ^ q * x₁)) := by ring
  rw [hsplit]
  refine Ideal.add_mem _ ?_ h3
  have h := Ideal.mul_mem_mul hx₀ h1
  rwa [← pow_succ', show q + 1 + 1 = q + 2 by ring] at h

end DrinP

end SSFGallq

theorem solution
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] (𝔪 : Ideal R) (hq : ((q : ℕ) : R) ∈ 𝔪)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ 𝔪) (hx₁ : x₁ ∈ 𝔪)
    (P : ZMod q → R) (hP : ∀ c : ZMod q, P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ 𝔪 ^ 2) :
    x₀ * (∏ c : ZMod q, P c) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ 𝔪 ^ (q + 2) :=
  SSFGallq.mul_prod_sub_drinfeldForm_mem_pow q R 𝔪 hq x₀ x₁ hx₀ hx₁ P hP

end S_Ideal_mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem
end P2MW
export P2MW.S_Ideal_mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem (solution)
