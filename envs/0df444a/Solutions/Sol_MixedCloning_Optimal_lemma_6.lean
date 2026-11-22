-- Prove2me | solution 1 for MixedCloning.Optimal.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-21T19:29:05.705574+00:00
-- url     : https://prove2.me/submissions/740641ff-d507-497b-bf6f-c9e2041a6f45

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open MixedCloning.Optimal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- `d[m+1] (m+1) = d[m] (m+d)` for `d = e+1`. -/
lemma lemma6_symDimension_succ (e m : ℕ) :
    (symDimension (e+1) (m+1) : ℝ) * ((m : ℝ) + 1) =
      (symDimension (e+1) m : ℝ) * ((m : ℝ) + e + 1) := by
  have h := Nat.add_one_mul_choose_eq (m+e) m
  have h1 : m + 1 + (e + 1) - 1 = m + e + 1 := by omega
  have h2 : m + (e + 1) - 1 = m + e := by omega
  simp only [symDimension, h1, h2]
  have h' : ((m + e + 1).choose (m + 1) : ℝ) * ((m : ℝ) + 1) =
      ((m + e).choose m : ℝ) * ((m : ℝ) + e + 1) := by
    have := congrArg (fun t : ℕ => (t : ℝ)) h
    push_cast at this
    linarith
  exact h'

lemma lemma6_symDimension_pos (e m : ℕ) : (0 : ℝ) < symDimension (e+1) m := by
  simp only [symDimension]
  exact_mod_cast Nat.choose_pos (by omega)

theorem solution (n d k : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    1 - (k : ℝ)*d/n ≤ (symDimension d n : ℝ) / symDimension d (n+k) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hD0 := lemma6_symDimension_pos e n
  induction k with
  | zero => simp [hD0.ne']
  | succ k ih =>
    have hD := lemma6_symDimension_pos e (n+k)
    have hrec := lemma6_symDimension_succ e (n+k)
    have hidx : n + (k + 1) = n + k + 1 := by omega
    rw [hidx]
    set x := (symDimension (e+1) n : ℝ) / symDimension (e+1) (n+k) with hx
    have hpos : (0 : ℝ) < (n : ℝ) + k + e + 1 := by positivity
    have key : (symDimension (e+1) n : ℝ) / symDimension (e+1) (n+k+1) =
        x * (((n : ℝ) + k + 1) / ((n : ℝ) + k + e + 1)) := by
      have hD1 := lemma6_symDimension_pos e (n+k+1)
      push_cast at hrec
      rw [hx, div_mul_div_comm, div_eq_div_iff hD1.ne' (by positivity)]
      rw [mul_assoc, ← hrec]
      ring
    rw [key]
    have hf0 : (0 : ℝ) ≤ ((n : ℝ) + k + 1) / ((n : ℝ) + k + e + 1) := by positivity
    have step1 : (1 - (k : ℝ) * ((e + 1 : ℕ) : ℝ) / n) *
        (((n : ℝ) + k + 1) / ((n : ℝ) + k + e + 1)) ≤
        x * (((n : ℝ) + k + 1) / ((n : ℝ) + k + e + 1)) :=
      mul_le_mul_of_nonneg_right ih hf0
    refine le_trans ?_ step1
    push_cast
    simp only [div_eq_mul_inv]
    rw [← sub_nonneg]
    have expand : (1 - (k : ℝ) * (e + 1) * (n : ℝ)⁻¹) * (((n : ℝ) + k + 1) * ((n : ℝ) + k + e + 1)⁻¹) -
        (1 - ((k : ℝ) + 1) * (e + 1) * (n : ℝ)⁻¹) =
        ((n : ℝ) + ((e : ℝ) + 1) * ((k : ℝ) + 1 + e) + (k : ℝ) * e * (e + 1)) *
          ((n : ℝ)⁻¹ * ((n : ℝ) + k + e + 1)⁻¹) := by
      field_simp
      ring
    rw [expand]
    positivity
