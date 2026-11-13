-- Prove2me | solution 1 for MvResultant.dvd_of_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T18:59:05.913463+00:00
-- url     : https://prove2.me/submissions/9ff751c0-903f-430b-bfe1-e716ad029a07

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly

open HararySachs.Hyper MvPolynomial Finset

namespace DvdVanAux

instance finite_block (n d : ℕ) : Finite {a : Fin n →₀ ℕ // a.degree = d} := by
  refine Finite.of_injective
    (fun a : {a : Fin n →₀ ℕ // a.degree = d} => fun j : Fin n =>
      (⟨a.1 j, Nat.lt_succ_of_le (by have := Finsupp.le_degree j a.1; rw [a.2] at this; exact this)⟩ : Fin (d + 1))) ?_
  intro a b h
  apply Subtype.ext
  ext j
  have := congrFun h j
  simpa using congrArg Fin.val this

instance finite_resVar (n : ℕ) (D : Fin n → ℕ) : Finite (ResVar n D) := by
  unfold ResVar; infer_instance

/-- the system of forms with prescribed coefficients -/
noncomputable def formsOf {n : ℕ} {D : Fin n → ℕ} (u : ResVar n D → ℂ) (j : Fin n) :
    MvPolynomial (Fin n) ℂ := by
  classical
  haveI := Fintype.ofFinite {a : Fin n →₀ ℕ // a.degree = D j}
  exact ∑ a : {a : Fin n →₀ ℕ // a.degree = D j}, monomial a.1 (u ⟨j, a⟩)

lemma formsOf_homogeneous {n : ℕ} {D : Fin n → ℕ} (u : ResVar n D → ℂ) (j : Fin n) :
    (formsOf u j).IsHomogeneous (D j) := by
  unfold formsOf
  exact IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_monomial _ a.2

lemma coeff_formsOf {n : ℕ} {D : Fin n → ℕ} (u : ResVar n D → ℂ) (v : ResVar n D) :
    coeff v.2.1 (formsOf u v.1) = u v := by
  classical
  obtain ⟨j, a⟩ := v
  unfold formsOf
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [sum_eq_single a]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h; exact hb (Subtype.ext h)
  · simp

end DvdVanAux

open DvdVanAux in
theorem solution {n : ℕ} {D : Fin n → ℕ}
    (res : MvPolynomial (ResVar n D) ℤ) (hres : IsResultant n D res)
    (g : MvPolynomial (ResVar n D) ℂ)
    (hg : ∀ F : Fin n → MvPolynomial (Fin n) ℂ, (∀ i, (F i).IsHomogeneous (D i)) →
      (∃ x : Fin n → ℂ, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (F i) = 0) →
      MvPolynomial.aeval (fun v : ResVar n D => MvPolynomial.coeff v.2.1 (F v.1)) g = 0) :
    MvPolynomial.map (Int.castRingHom ℂ) res ∣ g := by
  classical
  set P := MvPolynomial.map (Int.castRingHom ℂ) res with hP
  have hirr : Irreducible P := hres.2.2
  have hprime : (Ideal.span {P}).IsPrime :=
    (Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime
  have key : g ∈ vanishingIdeal ℂ (zeroLocus ℂ (Ideal.span {P})) := by
    rw [mem_vanishingIdeal_iff]
    intro u hu
    rw [mem_zeroLocus_iff] at hu
    have hPu : aeval u P = 0 := hu P (Ideal.subset_span rfl)
    have hcoef : (fun v : ResVar n D => coeff v.2.1 (formsOf u v.1)) = u :=
      funext fun v => coeff_formsOf u v
    have hsolv := (hres.1 (formsOf u) (formsOf_homogeneous u)).mpr (by rw [hcoef]; exact hPu)
    have := hg (formsOf u) (formsOf_homogeneous u) hsolv
    rwa [hcoef] at this
  rw [IsPrime.vanishingIdeal_zeroLocus] at key
  exact Ideal.mem_span_singleton.mp key
