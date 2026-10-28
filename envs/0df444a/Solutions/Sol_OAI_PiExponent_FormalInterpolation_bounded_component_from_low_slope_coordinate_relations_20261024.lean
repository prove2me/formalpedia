-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_component_from_low_slope_coordinate_relations_20261024
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:17:48.573232+00:00
-- url     : https://prove2.me/submissions/e7642124-8406-4cbe-b39b-b8d0e6ff1b90

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

open scoped BigOperators
open MvPolynomial

namespace S156A

variable {d : ℕ} (w : Fin d → ℚ)

def Sle (c : ℚ) : Set (MvPolynomial (Fin d) ℂ) :=
  {p | ∀ a ∈ p.support, Finsupp.weight w a ≤ c}
def Slt (c : ℚ) : Set (MvPolynomial (Fin d) ℂ) :=
  {p | ∀ a ∈ p.support, Finsupp.weight w a < c}

variable {w}

lemma lt_le {p : MvPolynomial (Fin d) ℂ} {c : ℚ} (h : p ∈ Slt w c) : p ∈ Sle w c :=
  fun a ha => (h a ha).le

lemma mul_le_le {p r : MvPolynomial (Fin d) ℂ} {b c : ℚ} (hp : p ∈ Sle w b) (hr : r ∈ Sle w c) :
    p * r ∈ Sle w (b + c) := by
  classical
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (support_mul p r ha)
  rw [map_add]; exact add_le_add (hp x hx) (hr y hy)

lemma mul_le_lt {p r : MvPolynomial (Fin d) ℂ} {b c : ℚ} (hp : p ∈ Sle w b) (hr : r ∈ Slt w c) :
    p * r ∈ Slt w (b + c) := by
  classical
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (support_mul p r ha)
  rw [map_add]; exact add_lt_add_of_le_of_lt (hp x hx) (hr y hy)

lemma mul_lt_le {p r : MvPolynomial (Fin d) ℂ} {b c : ℚ} (hp : p ∈ Slt w b) (hr : r ∈ Sle w c) :
    p * r ∈ Slt w (b + c) := by
  classical
  intro a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (support_mul p r ha)
  rw [map_add]; exact add_lt_add_of_lt_of_le (hp x hx) (hr y hy)

lemma add_lt {p r : MvPolynomial (Fin d) ℂ} {c : ℚ} (hp : p ∈ Slt w c) (hr : r ∈ Slt w c) :
    p + r ∈ Slt w c := by
  classical
  intro a ha
  rcases Finset.mem_union.mp (support_add ha) with h | h
  exacts [hp a h, hr a h]

lemma sub_lt {p r : MvPolynomial (Fin d) ℂ} {c : ℚ} (hp : p ∈ Slt w c) (hr : r ∈ Slt w c) :
    p - r ∈ Slt w c := by
  classical
  intro a ha
  rcases Finset.mem_union.mp (support_sub _ p r ha) with h | h
  exacts [hp a h, hr a h]

lemma add_le {p r : MvPolynomial (Fin d) ℂ} {c : ℚ} (hp : p ∈ Sle w c) (hr : r ∈ Sle w c) :
    p + r ∈ Sle w c := by
  classical
  intro a ha
  rcases Finset.mem_union.mp (support_add ha) with h | h
  exacts [hp a h, hr a h]

lemma weight_cast (a : Fin d →₀ ℕ) :
    ((Finsupp.weight w a : ℚ) : ℝ) = ∑ j, (w j : ℝ) * (a j : ℝ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  push_cast
  simp [nsmul_eq_mul, mul_comm]

lemma X_pow_le (i : Fin d) (m : ℕ) : (X i ^ m : MvPolynomial (Fin d) ℂ) ∈ Sle w (m * w i) := by
  classical
  intro a ha
  rw [X_pow_eq_monomial] at ha
  have := support_monomial_subset ha
  rw [Finset.mem_singleton] at this
  subst this
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

lemma X_pow_hom (i : Fin d) (m : ℕ) :
    (X i ^ m : MvPolynomial (Fin d) ℂ).IsWeightedHomogeneous w (m * w i) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

lemma quot_finite (J : Ideal (MvPolynomial (Fin d) ℂ)) (m : Fin d → ℕ)
    (hm : ∀ i, X i ^ m i ∈ J) : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ J) := by
  have hint : Algebra.IsIntegral ℂ (MvPolynomial (Fin d) ℂ ⧸ J) := by
    constructor
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C a =>
      have : Ideal.Quotient.mk J (C a) = algebraMap ℂ _ a := rfl
      rw [this]; exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p i hp =>
      rw [map_mul]
      refine hp.mul ⟨Polynomial.X ^ m i, Polynomial.monic_X_pow _, ?_⟩
      simp only [Polynomial.eval₂_X_pow]
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hm i
  exact Algebra.IsIntegral.finite

theorem main
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (s₀ : Nat) (hs₀ : 0 < s₀) (q₀ : Rat) (hq₀ : 0 < q₀)
    (hgap : (q₀ : Real) < (s₀ : Real) * ((rho : Real) + eps))
    (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (hdegree : ∀ i, (n i : Rat) * w i = q₀)
    (f : Fin d → MvPolynomial (Fin d) Complex)
    (hrelation : ∀ i, MvPolynomial.X i ^ n i - f i ∈ I ^ s₀)
    (hsupport : ∀ i a, a ∈ (f i).support →
      ∑ j, (w j : Real) * (a j : Real) < (q₀ : Real)) :
    ∃ s : Nat, 0 < s ∧ ∃ q : Rat, 0 < q ∧
      (q : Real) + 1 < (s : Real) * ((rho : Real) + eps) ∧
      Module.Finite Complex
        (MvPolynomial (Fin d) Complex ⧸ Ideal.span (Set.range (fun (p :
          {g : MvPolynomial (Fin d) Complex //
            g ∈ I ^ s ∧ ∀ a ∈ g.support,
              ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : ℚ)) q p.1))) := by
  set δ : ℝ := (s₀ : ℝ) * ((rho : ℝ) + eps) - q₀ with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / δ)
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := lt_trans (by positivity) hk
    exact_mod_cast this
  have hkδ : 1 < (k : ℝ) * δ := by
    rw [div_lt_iff₀ hδpos] at hk; linarith
  refine ⟨k * s₀, Nat.mul_pos hkpos hs₀, k * q₀, by positivity, ?_, ?_⟩
  · push_cast; nlinarith
  -- f i has low weight
  have hf : ∀ i, f i ∈ Slt w q₀ := by
    intro i a ha
    have := hsupport i a ha
    rw [← weight_cast] at this
    exact_mod_cast this
  have hP : ∀ i, (X i ^ n i : MvPolynomial (Fin d) ℂ) ∈ Sle w q₀ := by
    intro i; have := X_pow_le (w := w) i (n i); rwa [hdegree i] at this
  have key : ∀ i (j : ℕ), ∃ R ∈ Slt w (j * q₀),
      (X i ^ n i - f i) ^ j = X i ^ (n i * j) + R := by
    intro i j
    induction j with
    | zero => exact ⟨0, fun a ha => by simp at ha, by simp⟩
    | succ j ih =>
      obtain ⟨R, hR, hEq⟩ := ih
      have hPj : (X i ^ (n i * j) : MvPolynomial (Fin d) ℂ) ∈ Sle w (j * q₀) := by
        have := X_pow_le (w := w) i (n i * j)
        convert this using 1; rw [← hdegree i]; push_cast; ring
      refine ⟨R * X i ^ n i - X i ^ (n i * j) * f i - R * f i, ?_, ?_⟩
      · have e : ((j + 1 : ℕ) : ℚ) * q₀ = j * q₀ + q₀ := by push_cast; ring
        rw [e]
        refine sub_lt (sub_lt (mul_lt_le hR (hP i)) (mul_le_lt hPj (hf i))) ?_
        exact mul_lt_le hR (lt_le (hf i))
      · rw [pow_succ, hEq, Nat.mul_succ, pow_add]; ring
  have hm : ∀ i, (X i ^ (n i * k) : MvPolynomial (Fin d) ℂ) ∈ Ideal.span (Set.range (fun (p :
          {g : MvPolynomial (Fin d) Complex //
            g ∈ I ^ (k * s₀) ∧ ∀ a ∈ g.support,
              ∑ j, (w j : Real) * (a j : Real) ≤ (((k * q₀ : ℚ)) : Real)}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : ℚ)) (k * q₀) p.1)) := by
    intro i
    obtain ⟨R, hR, hEq⟩ := key i k
    have hPk : (X i ^ (n i * k) : MvPolynomial (Fin d) ℂ) ∈ Sle w (k * q₀) := by
      have := X_pow_le (w := w) i (n i * k)
      convert this using 1; rw [← hdegree i]; push_cast; ring
    have hmem : (X i ^ n i - f i) ^ k ∈ I ^ (k * s₀) := by
      rw [mul_comm, pow_mul]; exact Ideal.pow_mem_pow (hrelation i) k
    have hle : ∀ a ∈ ((X i ^ n i - f i) ^ k).support,
        ∑ j, (w j : Real) * (a j : Real) ≤ (((k * q₀ : ℚ)) : Real) := by
      intro a ha
      rw [hEq] at ha
      rw [← weight_cast]; exact_mod_cast add_le hPk (lt_le hR) a ha
    refine Ideal.subset_span ⟨⟨_, hmem, hle⟩, ?_⟩
    show weightedHomogeneousComponent (fun j => (w j : ℚ)) (k * q₀) ((X i ^ n i - f i) ^ k) = _
    rw [hEq, map_add, weightedHomogeneousComponent_eq_self, weightedHomogeneousComponent_eq_zero',
      add_zero]
    · intro a ha; exact (hR a ha).ne
    · convert X_pow_hom (w := w) i (n i * k) using 1; rw [← hdegree i]; push_cast; ring
  exact quot_finite _ _ hm

end S156A

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (s₀ : Nat) (hs₀ : 0 < s₀) (q₀ : Rat) (hq₀ : 0 < q₀)
    (hgap : (q₀ : Real) < (s₀ : Real) * ((rho : Real) + eps))
    (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (hdegree : ∀ i, (n i : Rat) * w i = q₀)
    (f : Fin d → MvPolynomial (Fin d) Complex)
    (hrelation : ∀ i, MvPolynomial.X i ^ n i - f i ∈ I ^ s₀)
    (hsupport : ∀ i a, a ∈ (f i).support →
      ∑ j, (w j : Real) * (a j : Real) < (q₀ : Real)) :
    ∃ s : Nat, 0 < s ∧ ∃ q : Rat, 0 < q ∧
      (q : Real) + 1 < (s : Real) * ((rho : Real) + eps) ∧
      Module.Finite Complex
        (MvPolynomial (Fin d) Complex ⧸ Ideal.span (Set.range (fun (p :
          {g : MvPolynomial (Fin d) Complex //
            g ∈ I ^ s ∧ ∀ a ∈ g.support,
              ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : ℚ)) q p.1))) :=
  S156A.main I w rho eps s₀ hs₀ q₀ hq₀ hgap n hn hdegree f hrelation hsupport
