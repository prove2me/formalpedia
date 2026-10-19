-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.power_representatives_of_finite_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:00:41.071383+00:00
-- url     : https://prove2.me/submissions/855d82da-3e9f-4f32-9e5f-c16d376c2ac1

import Mathlib
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
def h41WB {v : ℕ} (w : Fin v → ℝ) (c : ℝ) (p : MvPolynomial (Fin v) ℂ) : Prop :=
  ∀ a ∈ p.support, ∑ i, w i * (a i : ℝ) ≤ c

theorem h41WB_mono {v : ℕ} {w : Fin v → ℝ} {c c' : ℝ} {p : MvPolynomial (Fin v) ℂ}
    (h : h41WB w c p) (hc : c ≤ c') : h41WB w c' p := fun a ha => (h a ha).trans hc

theorem h41WB_add {v : ℕ} {w : Fin v → ℝ} {c : ℝ} {p q : MvPolynomial (Fin v) ℂ}
    (hp : h41WB w c p) (hq : h41WB w c q) : h41WB w c (p + q) := by
  classical
  intro a ha
  rcases Finset.mem_union.1 (MvPolynomial.support_add ha) with h | h
  · exact hp a h
  · exact hq a h

theorem h41WB_zero {v : ℕ} {w : Fin v → ℝ} {c : ℝ} : h41WB w c (0 : MvPolynomial (Fin v) ℂ) := by
  intro a ha; simp at ha

theorem h41WB_sum {v : ℕ} {w : Fin v → ℝ} {c : ℝ} {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (Fin v) ℂ) (h : ∀ i ∈ s, h41WB w c (p i)) : h41WB w c (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h41WB_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact h41WB_add (h j (Finset.mem_insert_self _ _)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem h41WB_mul {v : ℕ} {w : Fin v → ℝ} {c c' : ℝ} {p q : MvPolynomial (Fin v) ℂ}
    (hp : h41WB w c p) (hq : h41WB w c' q) : h41WB w (c + c') (p * q) := by
  classical
  intro a ha
  obtain ⟨b, hb, b', hb', rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul p q ha)
  have := hp b hb; have := hq b' hb'
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  linarith

theorem h41WB_one {v : ℕ} {w : Fin v → ℝ} : h41WB w 0 (1 : MvPolynomial (Fin v) ℂ) := by
  intro a ha
  rw [MvPolynomial.support_one] at ha
  simp only [Finset.mem_singleton] at ha
  subst ha; simp

theorem h41WB_C_mul {v : ℕ} {w : Fin v → ℝ} {c : ℝ} (z : ℂ) {p : MvPolynomial (Fin v) ℂ}
    (hp : h41WB w c p) : h41WB w c (MvPolynomial.C z * p) := by
  classical
  intro a ha
  rw [MvPolynomial.C_mul'] at ha
  exact hp a (MvPolynomial.support_smul ha)

theorem h41WB_pow {v : ℕ} {w : Fin v → ℝ} {c : ℝ} {p : MvPolynomial (Fin v) ℂ}
    (hp : h41WB w c p) (n : ℕ) : h41WB w (n * c) (p ^ n) := by
  induction n with
  | zero => simpa using h41WB_one
  | succ n ih =>
    rw [pow_succ]
    have := h41WB_mul ih hp
    convert this using 1; push_cast; ring

theorem h41WB_prod {v : ℕ} {w : Fin v → ℝ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (p : ι → MvPolynomial (Fin v) ℂ) (h : ∀ i ∈ s, h41WB w (c i) (p i)) :
    h41WB w (∑ i ∈ s, c i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h41WB_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact h41WB_mul (h j (Finset.mem_insert_self _ _)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem solution
    {v k : Nat} (w : Fin v → Real)
    (I : Ideal (MvPolynomial (Fin v) Complex))
    (s : Nat) (hs : 0 < s) (D : Real) (hD : 0 ≤ D)
    (f : Fin k → MvPolynomial (Fin v) Complex)
    (hmem : ∀ j, f j ∈ I ^ s)
    (hweight : ∀ j, ∀ a ∈ (f j).support,
      ∑ i, w i * (a i : Real) ≤ D)
    (hfinite : Module.Finite (Algebra.adjoin Complex (Set.range f))
      (MvPolynomial (Fin v) Complex)) :
    ∃ B : Real, 0 ≤ B ∧
      ∀ n : Nat, ∀ P : MvPolynomial (Fin v) Complex,
        ∃ Q : MvPolynomial (Fin v) Complex,
          P - Q ∈ I ^ n ∧
          ∀ a ∈ Q.support,
            ∑ i, w i * (a i : Real) ≤
              (n : Real) * (D / (s : Real)) + B := by
  classical
  set A := Algebra.adjoin ℂ (Set.range f)
  obtain ⟨S, hS⟩ := hfinite.fg_top
  set B : ℝ := ∑ g ∈ S, ∑ a ∈ g.support, |∑ i, w i * (a i : ℝ)|
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun g _ => Finset.sum_nonneg (fun a _ => abs_nonneg _))
  have hgB : ∀ g ∈ S, h41WB w B g := by
    intro g hg a ha
    calc ∑ i, w i * (a i : ℝ) ≤ |∑ i, w i * (a i : ℝ)| := le_abs_self _
      _ ≤ ∑ a ∈ g.support, |∑ i, w i * (a i : ℝ)| :=
          Finset.single_le_sum (f := fun a => |∑ i, w i * (a i : ℝ)|) (fun _ _ => abs_nonneg _) ha
      _ ≤ B := Finset.single_le_sum (f := fun g : MvPolynomial (Fin v) ℂ =>
            ∑ a ∈ g.support, |∑ i, w i * (a i : ℝ)|) (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hg
  refine ⟨B, hB0, fun n P => ?_⟩
  have hP : P ∈ Submodule.span A (S : Set (MvPolynomial (Fin v) ℂ)) := by rw [hS]; trivial
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hP
  have hcA : ∀ g, ∃ p : MvPolynomial (Fin k) ℂ, MvPolynomial.aeval f p = (c g : MvPolynomial (Fin v) ℂ) := by
    intro g
    have : (c g : MvPolynomial (Fin v) ℂ) ∈ (MvPolynomial.aeval (R := ℂ) f).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval ℂ f]; exact (c g).2
    exact this
  choose p hp using hcA
  let deg : (Fin k →₀ ℕ) → ℕ := fun α => ∑ j, α j
  let term : MvPolynomial (Fin v) ℂ → (Fin k →₀ ℕ) → MvPolynomial (Fin v) ℂ := fun g α =>
    MvPolynomial.C ((p g).coeff α) * (∏ j, f j ^ α j) * g
  have hPexp : P = ∑ g ∈ S, ∑ α ∈ (p g).support, term g α := by
    rw [← hc]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Subalgebra.smul_def, ← hp g, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', smul_eq_mul, Finset.sum_mul]
    rfl
  refine ⟨∑ g ∈ S, ∑ α ∈ (p g).support.filter (fun α => s * deg α < n), term g α, ?_, ?_⟩
  · have : P - ∑ g ∈ S, ∑ α ∈ (p g).support.filter (fun α => s * deg α < n), term g α =
        ∑ g ∈ S, ∑ α ∈ (p g).support.filter (fun α => ¬ s * deg α < n), term g α := by
      rw [hPexp, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [← Finset.sum_filter_add_sum_filter_not (p g).support (fun α => s * deg α < n)]
      ring
    rw [this]
    apply Ideal.sum_mem; intro g _
    apply Ideal.sum_mem; intro α hα
    have hα' : n ≤ s * deg α := by
      have := (Finset.mem_filter.1 hα).2; omega
    simp only [term]
    rw [mul_comm (MvPolynomial.C _) _, mul_assoc]
    apply Ideal.mul_mem_right
    apply Ideal.pow_le_pow_right hα'
    rw [pow_mul, ← Finset.prod_pow_eq_pow_sum]
    apply Ideal.prod_mem_prod
    intro j _
    exact Ideal.pow_mem_pow (hmem j) _
  · apply h41WB_sum; intro g hg
    apply h41WB_sum; intro α hα
    have hlt := (Finset.mem_filter.1 hα).2
    have hdeg : (deg α : ℝ) * D ≤ (n : ℝ) * (D / (s : ℝ)) := by
      have hsr : (0:ℝ) < s := by exact_mod_cast hs
      have : (s : ℝ) * deg α ≤ n := by exact_mod_cast hlt.le
      rw [mul_div_assoc', le_div_iff₀ hsr]
      nlinarith
    have h1 : h41WB w (∑ j, (α j : ℝ) * D) (∏ j, f j ^ α j) :=
      h41WB_prod _ _ _ (fun j _ => h41WB_pow (hweight j) _)
    have h2 := h41WB_mul (h41WB_C_mul ((p g).coeff α) h1) (hgB g hg)
    simp only [term]
    refine h41WB_mono h2 ?_
    have : ∑ j, (α j : ℝ) * D = (deg α : ℝ) * D := by
      simp only [deg]; push_cast; rw [Finset.sum_mul]
    linarith

