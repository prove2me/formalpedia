-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.weighted_component_span_pow_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:00:49.068143+00:00
-- url     : https://prove2.me/submissions/507c2d01-898f-4b65-8d63-639b97ea0d95

import Mathlib
open scoped BigOperators
open MvPolynomial

namespace S35P

variable {d : Nat}

def B (w : Fin d → ℚ) (α : ℚ) (f : MvPolynomial (Fin d) ℂ) : Prop :=
  ∀ a ∈ f.support, Finsupp.weight w a ≤ α

theorem weight_real (w : Fin d → ℚ) (a : Fin d →₀ ℕ) :
    ((Finsupp.weight w a : ℚ) : ℝ) = ∑ j, (w j : ℝ) * (a j : ℝ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nsmul_eq_mul]; push_cast; ring

theorem B_mul (w : Fin d → ℚ) (α β : ℚ) (f g : MvPolynomial (Fin d) ℂ) (hf : B w α f) (hg : B w β g) :
    B w (α + β) (f * g) := by
  intro c hc
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hc)
  rw [map_add]; exact add_le_add (hf x hx) (hg y hy)

theorem comp_mul (w : Fin d → ℚ) (α β : ℚ) (f g : MvPolynomial (Fin d) ℂ) (hf : B w α f) (hg : B w β g) :
    weightedHomogeneousComponent w (α + β) (f * g) =
      weightedHomogeneousComponent w α f * weightedHomogeneousComponent w β g := by
  classical
  ext c
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hc
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
    by_cases h1 : coeff p.1 f = 0
    · simp [h1]
    by_cases h2 : coeff p.2 g = 0
    · simp [h2]
    have e1 := hf p.1 (mem_support_iff.mpr h1)
    have e2 := hg p.2 (mem_support_iff.mpr h2)
    have : Finsupp.weight w p.1 + Finsupp.weight w p.2 = α + β := by rw [← map_add, hp, hc]
    rw [if_pos (by linarith), if_pos (by linarith)]
  · have hh := ((weightedHomogeneousComponent_isWeightedHomogeneous (R := ℂ) (w := w) α f).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous β g))
    by_contra hne
    exact hc (hh (Ne.symm hne))

theorem prod_aux (w : Fin d → ℚ) (q : ℚ) : ∀ (m : ℕ) (u : Fin m → MvPolynomial (Fin d) ℂ),
    (∀ i, B w q (u i)) →
    B w (m * q) (∏ i, u i) ∧
      weightedHomogeneousComponent w (m * q) (∏ i, u i) = ∏ i, weightedHomogeneousComponent w q (u i)
  | 0, u, _ => by
    refine ⟨fun a ha => ?_, ?_⟩
    · simp only [Finset.univ_eq_empty, Finset.prod_empty] at ha
      rw [MvPolynomial.support_one, Finset.mem_singleton] at ha
      subst ha; simp
    · simp only [Finset.univ_eq_empty, Finset.prod_empty, Nat.cast_zero, zero_mul]
      exact (isWeightedHomogeneous_one ℂ w).weightedHomogeneousComponent_same
  | m + 1, u, hu => by
    obtain ⟨h1, h2⟩ := prod_aux w q m (fun i => u i.succ) (fun i => hu _)
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    have e : ((m + 1 : ℕ) : ℚ) * q = q + m * q := by push_cast; ring
    rw [e]
    exact ⟨B_mul w q _ _ _ (hu 0) h1, by rw [comp_mul w q _ _ _ (hu 0) h1, h2]⟩

end S35P

theorem solution {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex)) (w : Fin d → Rat) (s m : Nat) (q D : Rat) (hs : 0 < s) (hD : q * (m : Rat) = D) (u : Fin m → {g : MvPolynomial (Fin d) Complex // g ∈ I ^ s ∧ ∀ a ∈ g.support, ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) : (∏ i, MvPolynomial.weightedHomogeneousComponent (fun j => (w j : ℚ)) q (u i).1) ∈ Ideal.span {h : MvPolynomial (Fin d) Complex | ∃ g : MvPolynomial (Fin d) Complex, g ∈ I ^ (s * m) ∧ (∀ a ∈ g.support, ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧ h = MvPolynomial.weightedHomogeneousComponent (fun k => (w k : ℚ)) D g} := by
  have hB : ∀ i, S35P.B w q (u i).1 := by
    intro i a ha
    have := (u i).2.2 a ha
    rw [← S35P.weight_real] at this
    exact_mod_cast this
  obtain ⟨h1, h2⟩ := S35P.prod_aux w q m (fun i => (u i).1) hB
  have hDm : (m : ℚ) * q = D := by rw [← hD, mul_comm]
  rw [hDm] at h1 h2
  apply Ideal.subset_span
  refine ⟨∏ i, (u i).1, ?_, ?_, h2.symm⟩
  · have := Ideal.prod_mem_prod (s := Finset.univ) (I := fun _ : Fin m => I ^ s) (x := fun i => (u i).1)
      (fun i _ => (u i).2.1)
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul] at this
  · intro a ha
    rw [← S35P.weight_real]
    exact_mod_cast h1 a ha
