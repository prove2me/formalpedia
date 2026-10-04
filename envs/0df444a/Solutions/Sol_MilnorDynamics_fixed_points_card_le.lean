-- Prove2me | solution 1 for MilnorDynamics.fixed_points_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T20:06:21.552691+00:00
-- url     : https://prove2.me/submissions/9c14d604-ee98-43b5-b73c-7712b3b5982c

import Mathlib
import Definitions.Def_MilnorDynamics_PeriodicPoints

open scoped OnePoint Topology
open Filter Set

namespace MilnorDynamics.FixCard81

open Polynomial

lemma toFun_coe (f : RationalMap) (z : ℂ) :
    f.toFun (z : OnePoint ℂ) =
      if f.den.eval z = 0 then ∞ else ((f.num.eval z / f.den.eval z : ℂ) : OnePoint ℂ) := rfl

lemma toFun_infty (f : RationalMap) :
    f.toFun ∞ = if f.den.natDegree < f.num.natDegree then ∞
      else ((f.num.coeff f.den.natDegree / f.den.leadingCoeff : ℂ) : OnePoint ℂ) := rfl

/-- The fixed-point polynomial `num - X * den`. -/
noncomputable def fixPoly (f : RationalMap) : ℂ[X] := f.num - X * f.den

lemma fixPoly_ne_zero (f : RationalMap) (hf : f.toFun ≠ id) : fixPoly f ≠ 0 := by
  intro h
  apply hf
  have hnum : f.num = X * f.den := sub_eq_zero.mp h
  have hu : IsUnit f.den :=
    f.coprime.isUnit_of_dvd' (by rw [hnum]; exact dvd_mul_left _ _) dvd_rfl
  obtain ⟨c, hc, hcd⟩ := Polynomial.isUnit_iff.mp hu
  have hc0 : c ≠ 0 := hc.ne_zero
  have hden : f.den = C c := hcd.symm
  funext x
  induction x using OnePoint.rec with
  | infty =>
    have h1 : f.den.natDegree = 0 := by rw [hden]; simp
    have h2 : f.num.natDegree = 1 := by
      rw [hnum, hden, natDegree_X_mul (by simpa using hc0)]; simp
    rw [toFun_infty, h1, h2, if_pos (by norm_num)]
    rfl
  | coe z =>
    have he : f.den.eval z = c := by rw [hden]; simp
    rw [toFun_coe, he, if_neg hc0]
    rw [hnum, hden]
    simp only [eval_mul, eval_X, eval_C]
    rw [mul_div_assoc, div_self hc0, mul_one]
    rfl

lemma natDegree_fixPoly_le (f : RationalMap) :
    (fixPoly f).natDegree ≤ max f.num.natDegree (f.den.natDegree + 1) := by
  unfold fixPoly
  refine (natDegree_sub_le _ _).trans (max_le_max le_rfl ?_)
  refine (natDegree_mul_le).trans ?_
  have := natDegree_X_le (R := ℂ)
  omega

lemma mem_roots_of_fixed (f : RationalMap) (hP : fixPoly f ≠ 0) (z : ℂ)
    (hz : f.toFun (z : OnePoint ℂ) = (z : OnePoint ℂ)) : z ∈ (fixPoly f).roots := by
  rw [mem_roots hP]
  rw [toFun_coe] at hz
  by_cases h0 : f.den.eval z = 0
  · rw [if_pos h0] at hz
    exact absurd hz.symm (OnePoint.coe_ne_infty z)
  · rw [if_neg h0] at hz
    have hz' : f.num.eval z / f.den.eval z = z := OnePoint.coe_injective hz
    have : f.num.eval z = z * f.den.eval z := by
      field_simp at hz'
      linear_combination hz'
    simp [IsRoot, fixPoly, this]

lemma infty_not_fixed (f : RationalMap) (h : ¬ f.den.natDegree < f.num.natDegree) :
    f.toFun ∞ ≠ ∞ := by
  rw [toFun_infty, if_neg h]
  exact OnePoint.coe_ne_infty _

end MilnorDynamics.FixCard81

open Polynomial in
theorem solution (f : MilnorDynamics.RationalMap) (hf : f.toFun ≠ id) :
    (Function.fixedPoints f.toFun).Finite ∧
      (Function.fixedPoints f.toFun).ncard ≤ f.degree + 1 := by
  classical
  set P := MilnorDynamics.FixCard81.fixPoly f with hPdef
  have hP : P ≠ 0 := MilnorDynamics.FixCard81.fixPoly_ne_zero f hf
  set A : Finset (OnePoint ℂ) := P.roots.toFinset.image (fun z : ℂ => (z : OnePoint ℂ)) with hA
  have hAcard : A.card ≤ P.natDegree :=
    Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P))
  have hsub : Function.fixedPoints f.toFun ⊆ insert (∞ : OnePoint ℂ) (A : Set (OnePoint ℂ)) := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact Set.mem_insert _ _
    | coe z =>
      refine Set.mem_insert_of_mem _ ?_
      have hz : f.toFun (z : OnePoint ℂ) = (z : OnePoint ℂ) := hx
      have := MilnorDynamics.FixCard81.mem_roots_of_fixed f hP z hz
      simp only [hA, Finset.coe_image, Set.mem_image, Finset.mem_coe, Multiset.mem_toFinset]
      exact ⟨z, this, rfl⟩
  have hdeg := MilnorDynamics.FixCard81.natDegree_fixPoly_le f
  have hfin : (Function.fixedPoints f.toFun).Finite :=
    ((A.finite_toSet).insert (∞ : OnePoint ℂ)).subset hsub
  refine ⟨hfin, ?_⟩
  unfold MilnorDynamics.RationalMap.degree
  by_cases hlt : f.den.natDegree < f.num.natDegree
  · have h1 : (Function.fixedPoints f.toFun).ncard ≤ A.card + 1 := by
      calc (Function.fixedPoints f.toFun).ncard
          ≤ (insert (∞ : OnePoint ℂ) (A : Set (OnePoint ℂ))).ncard :=
            Set.ncard_le_ncard hsub ((A.finite_toSet).insert _)
        _ ≤ (A : Set (OnePoint ℂ)).ncard + 1 := Set.ncard_insert_le _ _
        _ = A.card + 1 := by rw [Set.ncard_coe_finset]
    have : max f.num.natDegree (f.den.natDegree + 1) = f.num.natDegree := by omega
    have h2 : P.natDegree ≤ max f.num.natDegree f.den.natDegree := by
      rw [this] at hdeg; exact hdeg.trans (le_max_left _ _)
    omega
  · have hsub' : Function.fixedPoints f.toFun ⊆ (A : Set (OnePoint ℂ)) := by
      intro x hx
      rcases Set.mem_insert_iff.mp (hsub hx) with h | h
      · subst h
        exact absurd hx (MilnorDynamics.FixCard81.infty_not_fixed f hlt)
      · exact h
    have h1 : (Function.fixedPoints f.toFun).ncard ≤ A.card := by
      calc (Function.fixedPoints f.toFun).ncard
          ≤ (A : Set (OnePoint ℂ)).ncard := Set.ncard_le_ncard hsub' A.finite_toSet
        _ = A.card := by rw [Set.ncard_coe_finset]
    have : P.natDegree ≤ max f.num.natDegree f.den.natDegree + 1 := by
      refine hdeg.trans ?_
      omega
    omega
