-- Prove2me | solution 1 for HodgeComputer.Formal.ResidueTransport.injective_of_coordinate_derivations
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:22:15.9258+00:00
-- url     : https://prove2.me/submissions/bab5f6a3-9bf1-4ca9-af08-2ba892ce35c1

import Definitions.Def_HodgeComputerFormal_Algebra
import Mathlib.Algebra.MvPolynomial.Degrees

set_option autoImplicit false

/-! A characteristic-zero coordinate criterion for dominance.
Coordinate derivations force polynomial evaluation to be injective. The proof
uses degree descent on a polynomial relation, so it also applies when the
ambient function field is presented as a quotient. Prepared with OpenAI Codex
assistance for the cycle-three construction. -/
noncomputable section
namespace ResidueCoordinateIndependence
open MvPolynomial
variable {k K σ : Type*} [Field k] [Field K] [CharZero k]
  [Fintype σ] [DecidableEq σ]

omit [CharZero k] [Fintype σ] in
lemma pderiv_degree_lt (p : MvPolynomial σ k) (i : σ) (hp : 0<p.totalDegree) :
    (pderiv i p).totalDegree<p.totalDegree := by
  classical
  rw [totalDegree,Finset.sup_lt_iff hp]
  intro m hm
  have hcoeff : p.coeff (m+Finsupp.single i 1)≠0 := by
    have h := mem_support_iff.mp hm
    rw [coeff_pderiv] at h
    exact (mul_ne_zero_iff.mp h).1
  have hd := le_totalDegree (mem_support_iff.mpr hcoeff)
  have hs : (m+Finsupp.single i 1).sum (fun _ e => e)=m.sum (fun _ e => e)+1 := by
    rw [Finsupp.sum_add_index]
    · simp
    · intros; rfl
    · intros; rfl
  rw [hs] at hd
  omega

lemma constant_of_partials_zero (p : MvPolynomial σ k)
    (h : ∀ i,pderiv i p=0) : p=C (p.coeff 0) := by
  classical
  ext m
  by_cases hm : m=0
  · subst m; simp
  · rw [coeff_C,if_neg (Ne.symm hm)]
    obtain ⟨i,hi⟩ : ∃ i,m i≠0 := by
      by_contra! hn
      exact hm (Finsupp.ext hn)
    have hs : m-Finsupp.single i 1+Finsupp.single i 1=m :=
      Finsupp.sub_add_single_one_cancel hi
    have hc := congrArg (·.coeff (m-Finsupp.single i 1)) (h i)
    rw [coeff_pderiv,hs,MvPolynomial.coeff_zero] at hc
    have hz : (((m-Finsupp.single i 1 : σ →₀ ℕ) i):k)+1≠0 := by
      exact Nat.cast_add_one_ne_zero _
    exact (mul_eq_zero.mp hc).resolve_right hz

theorem injective_of_compatible
    (φ : k →+* K) (ρ : MvPolynomial σ k →+* K)
    (D : σ → Derivation ℤ K K)
    (hC : ∀ c,ρ (C c)=φ c)
    (compatible : ∀ i p,D i (ρ p)=ρ (pderiv i p)) :
    Function.Injective ρ := by
  classical
  have hz : ∀ p : MvPolynomial σ k,ρ p=0 → p=0 := by
    intro p
    induction hn : p.totalDegree using Nat.strong_induction_on generalizing p with
    | h n ih =>
      intro hzero
      have hconst : p=C (p.coeff 0) := by
        by_cases hn0 : n=0
        · exact totalDegree_eq_zero_iff_eq_C.mp (hn.trans hn0)
        · apply constant_of_partials_zero
          intro i
          apply ih (pderiv i p).totalDegree
          · rw [← hn]
            exact pderiv_degree_lt p i (by omega)
          · rfl
          · rw [← compatible,hzero,map_zero]
      rw [hconst,hC] at hzero
      have hc : p.coeff 0=0 := φ.injective (by simpa using hzero)
      rw [hconst,hc,map_zero]
  exact (injective_iff_map_eq_zero ρ).mpr hz

theorem injective_of_coordinate_derivations
    (φ : k →+* K) (x : σ → K) (D : σ → Derivation ℤ K K)
    (hC : ∀ i c,D i (φ c)=0)
    (hx : ∀ i j,D i (x j)=if j=i then 1 else 0) :
    Function.Injective (MvPolynomial.eval₂Hom φ x) := by
  apply injective_of_compatible φ _ D
  · intro c; exact MvPolynomial.eval₂_C φ x c
  · intro i p
    rw [HoldoutConstruction.derivation_eval₂_chain (D i) φ x (hC i) p]
    simp [hx]

end ResidueCoordinateIndependence

end

theorem solution
    {k K σ : Type*} [Field k] [Field K] [CharZero k]
    [Fintype σ] [DecidableEq σ]
    (φ : k →+* K) (x : σ → K) (D : σ → Derivation ℤ K K)
    (hC : ∀ i c, D i (φ c) = 0)
    (hx : ∀ i j, D i (x j) = if j = i then 1 else 0) :
    Function.Injective (MvPolynomial.eval₂Hom φ x) :=
  ResidueCoordinateIndependence.injective_of_coordinate_derivations φ x D hC hx
