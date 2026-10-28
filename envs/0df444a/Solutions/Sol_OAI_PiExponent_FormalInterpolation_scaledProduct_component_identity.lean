-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.scaledProduct_component_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:24:39.975793+00:00
-- url     : https://prove2.me/submissions/f9a5cd05-327e-400d-87ca-98a62cce4be7

import Mathlib
open scoped BigOperators
open MvPolynomial

namespace A3S44

variable {d : Nat}

def B (w : Fin d → ℝ) (α : ℝ) (f : MvPolynomial (Fin d) ℂ) : Prop :=
  ∀ a ∈ f.support, Finsupp.weight w a ≤ α

theorem weight_real (w : Fin d → ℚ) (a : Fin d →₀ ℕ) :
    Finsupp.weight (fun l => (w l : ℝ)) a = ∑ l, (w l : ℝ) * (a l : ℝ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nsmul_eq_mul]; ring

theorem B_iff (w : Fin d → ℚ) (α : ℝ) (f : MvPolynomial (Fin d) ℂ) :
    B (fun l => (w l : ℝ)) α f ↔ ∀ a ∈ f.support, ∑ l, (w l : ℝ) * (a l : ℝ) ≤ α := by
  simp only [B, weight_real]

theorem B_mul (w : Fin d → ℝ) (α β : ℝ) (f g : MvPolynomial (Fin d) ℂ) (hf : B w α f) (hg : B w β g) :
    B w (α + β) (f * g) := by
  intro c hc
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hc)
  rw [map_add]; exact add_le_add (hf x hx) (hg y hy)

theorem B_one (w : Fin d → ℝ) : B w 0 (1 : MvPolynomial (Fin d) ℂ) := by
  intro a ha
  rw [MvPolynomial.support_one, Finset.mem_singleton] at ha
  subst ha; simp

theorem B_prod {ι : Type} (w : Fin d → ℝ) (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ)
    (Bd : ι → ℝ) (h : ∀ i ∈ s, B w (Bd i) (f i)) : B w (∑ i ∈ s, Bd i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using B_one w
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact B_mul w _ _ _ _ (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem comp_mul (w : Fin d → ℝ) (α β : ℝ) (f g : MvPolynomial (Fin d) ℂ) (hf : B w α f) (hg : B w β g) :
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

theorem prod_aux (w : Fin d → ℝ) (q : ℝ) : ∀ (m : ℕ) (u : Fin m → MvPolynomial (Fin d) ℂ),
    (∀ i, B w q (u i)) →
    B w (m * q) (∏ i, u i) ∧
      weightedHomogeneousComponent w (m * q) (∏ i, u i) = ∏ i, weightedHomogeneousComponent w q (u i)
  | 0, u, _ => by
    refine ⟨by simpa using B_one w, ?_⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Nat.cast_zero, zero_mul]
    exact (isWeightedHomogeneous_one ℂ w).weightedHomogeneousComponent_same
  | m + 1, u, hu => by
    obtain ⟨h1, h2⟩ := prod_aux w q m (fun i => u i.succ) (fun i => hu _)
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    have e : ((m + 1 : ℕ) : ℝ) * q = q + m * q := by push_cast; ring
    rw [e]
    exact ⟨B_mul w q _ _ _ (hu 0) h1, by rw [comp_mul w q _ _ _ (hu 0) h1, h2]⟩

theorem prod_mem_pow {R ι : Type*} [CommRing R] [Fintype ι] (I : Ideal R) (s : ℕ) (f : ι → R)
    (hf : ∀ i, f i ∈ I ^ s) : (∏ i, f i) ∈ I ^ (Fintype.card ι * s) := by
  classical
  have := Ideal.prod_mem_prod (s := Finset.univ) (I := fun _ => I ^ s) (x := f) (fun i _ => hf i)
  rwa [Finset.prod_const, Finset.card_univ, ← pow_mul, mul_comm] at this

theorem pow_mem_span_prod {R : Type*} [CommRing R] {n N : ℕ} (g : Fin n → R) (p : Fin N → R)
    (e k : ℕ) (x : R) (hx : x ^ e ∈ Ideal.span (Set.range g))
    (eFin : Fin N ≃ (Fin k → Fin n)) (hprod : ∀ j, p j = ∏ t : Fin k, g (eFin j t)) :
    x ^ (e * k) ∈ Ideal.span (Set.range p) := by
  have h1 : x ^ (e * k) ∈ Ideal.span (Set.range g) ^ k := by
    rw [pow_mul]; exact Ideal.pow_mem_pow hx k
  have h2 : Ideal.span (Set.range g) ^ k ≤ Ideal.span (Set.range p) := by
    rw [Ideal.span, Submodule.span_pow]
    refine Submodule.span_le.mpr fun y hy => ?_
    rw [Set.mem_pow] at hy
    obtain ⟨φ, rfl⟩ := hy
    have hc : ∀ t, ∃ m, g m = (φ t : R) := fun t => (φ t).2
    choose ψ hψ using hc
    refine Ideal.subset_span ⟨eFin.symm ψ, ?_⟩
    rw [hprod, Equiv.apply_symm_apply, List.prod_ofFn]
    exact Finset.prod_congr rfl fun t _ => hψ t
  exact h2 h1

end A3S44

theorem solution
    {d : Nat} (w : Fin d → Rat) (D : Real) (k : Nat)
    (n : Nat) (f : Fin n → MvPolynomial (Fin d) Complex)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ l, (w l : Real) * (a l : Real) ≤ D)
    (N : Nat) (eFin : Fin N ≃ (Fin k → Fin n)) (j : Fin N) :
    MvPolynomial.weightedHomogeneousComponent
      (fun l => (w l : Real)) ((k : Real) * D)
      (∏ t : Fin k, f (eFin j t)) =
      ∏ t : Fin k, MvPolynomial.weightedHomogeneousComponent
        (fun l => (w l : Real)) D (f (eFin j t)) :=
  (A3S44.prod_aux _ D k (fun t => f (eFin j t)) fun t => (A3S44.B_iff w _ _).mpr (hweight _)).2
