-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.scaled_product_algebraic_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T18:12:29.874852+00:00
-- url     : https://prove2.me/submissions/86828767-e5b0-45a4-ab46-85d2f3ed4c86

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weightedHomogeneousComponent_rat_eq_real
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaledProduct_family_bounds
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaledProduct_coordinate_generation

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s : Nat) (hs : 0 < s) (D : Real)
    (hD : 0 < D) (r : Rat) (hr : (r : Real) = D)
    (k : Nat) (hk : 0 < k) (n : Nat)
    (f : Fin n → MvPolynomial (Fin d) Complex)
    (hf : ∀ j, f j ∈ I ^ s)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ D)
    (hgen : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈ Ideal.span (Set.range (fun j =>
        MvPolynomial.weightedHomogeneousComponent
          (fun l => (w l : Real)) D (f j)))) :
    0 < k * r ∧
    ∃ n' : Nat, ∃ g : Fin n' → MvPolynomial (Fin d) Complex,
      (∀ j, g j ∈ I ^ (k * s)) ∧
      (∀ j, ∀ a ∈ (g j).support,
        ∑ l, (w l : Real) * (a l : Real) ≤ ((k * r : Rat) : Real)) ∧
      ∀ i : Fin d, ∃ e : Nat,
        MvPolynomial.X i ^ e ∈ Ideal.span (Set.range (fun j =>
          MvPolynomial.weightedHomogeneousComponent (w) (k * r) (g j))) := by
  classical
  have hrpos : 0 < r := by
    have hreal : (0 : Real) < (r : Real) := by rw [hr]; exact hD
    exact_mod_cast hreal
  have hkr : 0 < k * r := mul_pos (Nat.cast_pos.mpr hk) hrpos
  let N := Fintype.card (Fin k → Fin n)
  let eFin : Fin N ≃ (Fin k → Fin n) := (Fintype.equivFin (Fin k → Fin n)).symm
  let g : Fin N → MvPolynomial (Fin d) Complex :=
    fun j => ∏ t : Fin k, f (eFin j t)
  have hfamily := OAI.PiExponent.FormalInterpolation.scaledProduct_family_bounds
    I w s hs D k n N f hf hweight eFin
  have hcoord := OAI.PiExponent.FormalInterpolation.scaledProduct_coordinate_generation
    w D k hk n f hweight hgen N eFin
  refine ⟨hkr, N, g, ?_, ?_, ?_⟩
  · intro j
    exact hfamily.1 j
  · intro j a ha
    have hbound := hfamily.2 j a ha
    have hscale : (k : Real) * D = ((k * r : Rat) : Real) := by
      rw [Rat.cast_mul, Rat.cast_natCast, hr]
    calc
      ∑ l, (w l : Real) * (a l : Real) ≤ (k : Real) * D := hbound
      _ = ((k * r : Rat) : Real) := hscale
  · intro i
    obtain ⟨m, hmpos, hmgen⟩ := hcoord i
    refine ⟨m, ?_⟩
    have hscale : (k : Real) * D = ((k * r : Rat) : Real) := by
      rw [Rat.cast_mul, Rat.cast_natCast, hr]
    have hcomponent (j : Fin N) :
        MvPolynomial.weightedHomogeneousComponent
            (fun l => (w l : Real)) ((k : Real) * D) (g j) =
          MvPolynomial.weightedHomogeneousComponent (w) (k * r) (g j) := by
      rw [hscale]
      exact OAI.PiExponent.FormalInterpolation.weightedHomogeneousComponent_rat_eq_real
        w (k * r) (g j)
    have hspan :
        Ideal.span (Set.range (fun j : Fin N =>
          MvPolynomial.weightedHomogeneousComponent
            (fun l => (w l : Real)) ((k : Real) * D) (g j))) =
        Ideal.span (Set.range (fun j : Fin N =>
          MvPolynomial.weightedHomogeneousComponent (w) (k * r) (g j))) := by
      congr 1
      ext p
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j, (hcomponent j).symm⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j, hcomponent j⟩
    rw [← hspan]
    exact hmgen
