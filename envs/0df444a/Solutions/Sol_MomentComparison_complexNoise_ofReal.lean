-- Prove2me | solution 1 for MomentComparison.complexNoise_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:21:53.752413+00:00
-- url     : https://prove2.me/submissions/f2513034-6fb4-4f08-b751-40c2eef9290a

module
public import Definitions.Def_MomentComparison_Walsh
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_NoisePolynomial
public import Theorems.Thm_MomentComparison_complexNoise_cons
public import Theorems.Thm_MomentComparison_complexNoise_walsh
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_walshExpansion
public import Theorems.Thm_MomentComparison_walsh_empty
attribute [local simp] MomentComparison.cubeAverage_const
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.walsh_empty


section
public section
open scoped BigOperators
namespace MomentComparison
open Finset
private theorem complexNoise_zero_function {n : ℕ} (w : ℂ) (x : Cube n) :
    complexNoise w (fun _ => 0) x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Fin.cons_self_tail x, complexNoise_cons]
    simp [ih]
private theorem complexNoise_add {n : ℕ} (w : ℂ) (f g : Cube n → ℂ) (x : Cube n) :
    complexNoise w (fun y => f y + g y) x = complexNoise w f x + complexNoise w g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Fin.cons_self_tail x]
    simp only [complexNoise_cons, ih]
    ring
private theorem complexNoise_const_mul {n : ℕ} (w c : ℂ) (f : Cube n → ℂ) (x : Cube n) :
    complexNoise w (fun y => c * f y) x = c * complexNoise w f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Fin.cons_self_tail x]
    simp only [complexNoise_cons, ih]
    ring
private theorem complexNoise_sum {n : ℕ} {ι : Type*} (w : ℂ) (u : Finset ι)
    (f : ι → Cube n → ℂ) (x : Cube n) :
    complexNoise w (fun y => ∑ i ∈ u, f i y) x =
      ∑ i ∈ u, complexNoise w (f i) x := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [complexNoise_zero_function]
  | insert i u hi ih =>
    simp_rw [sum_insert hi, complexNoise_add, ih]
end MomentComparison
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n : ℕ} (w : ℂ) (f : Cube n → ℝ) (x : Cube n) :
    complexNoise w (fun y => (f y : ℂ)) x =
      ∑ s : Finset (Fin n), (cubeAverage (fun y => f y * walsh s y) : ℂ) *
        (w ^ s.card * (walsh s x : ℂ)) := by
  have hf : (fun y => (f y : ℂ)) = fun y => ∑ s : Finset (Fin n),
      (cubeAverage (fun z => f z * walsh s z) : ℂ) * (walsh s y : ℂ) := by
    funext y
    exact_mod_cast (walshExpansion f y).symm
  rw [hf, complexNoise_sum]
  simp_rw [complexNoise_const_mul, complexNoise_walsh]
end MomentComparison
