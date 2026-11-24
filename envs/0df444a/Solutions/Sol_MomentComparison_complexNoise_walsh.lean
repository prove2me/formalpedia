-- Prove2me | solution 1 for MomentComparison.complexNoise_walsh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:09:02.938035+00:00
-- url     : https://prove2.me/submissions/46737e1b-5797-4412-bdf4-c74dcd13983f

module
public import Definitions.Def_MomentComparison_Walsh
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_NoisePolynomial
public import Theorems.Thm_MomentComparison_complexNoise_zero
public import Theorems.Thm_MomentComparison_complexNoise_cons
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_walsh_empty
attribute [local simp] MomentComparison.cubeAverage_const
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.walsh_empty


section
public section
open scoped BigOperators
namespace MomentComparison
open Finset
private theorem complexNoise_const_mul {n : ℕ} (w c : ℂ) (f : Cube n → ℂ) (x : Cube n) :
    complexNoise w (fun y => c * f y) x = c * complexNoise w f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Fin.cons_self_tail x]
    simp only [complexNoise_cons, ih]
    ring
private theorem map_tailSet {n : ℕ} (s : Finset (Fin (n + 1))) :
    (tailSet s).map (Fin.succEmb n) = s.erase 0 := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [tailSet]
  · simp [tailSet]
private theorem walsh_tail {n : ℕ} (s : Finset (Fin (n + 1))) (b : Bool) (x : Cube n) :
    walsh (s.erase 0) (Fin.cons b x) = walsh (tailSet s) x := by
  rw [← map_tailSet s]
  simp only [walsh, prod_map]
  apply prod_congr rfl
  intro i _
  rfl
private theorem walsh_cons_of_mem {n : ℕ} (s : Finset (Fin (n + 1))) (h : 0 ∈ s)
    (b : Bool) (x : Cube n) :
    walsh s (Fin.cons b x) = walsh (tailSet s) x * (if b then 1 else -1) := by
  unfold walsh at *
  rw [← prod_erase_mul s _ h]
  change walsh (s.erase 0) (Fin.cons b x) * _ = _
  rw [walsh_tail]
  rfl
private theorem walsh_cons_of_notMem {n : ℕ} (s : Finset (Fin (n + 1))) (h : 0 ∉ s)
    (b : Bool) (x : Cube n) : walsh s (Fin.cons b x) = walsh (tailSet s) x := by
  simpa only [erase_eq_of_notMem h] using walsh_tail s b x
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
theorem _root_.solution {n : ℕ} (w : ℂ) (s : Finset (Fin n)) (x : Cube n) :
    complexNoise w (fun y => (walsh s y : ℂ)) x = w ^ s.card * (walsh s x : ℂ) := by
  induction n with
  | zero =>
    have hs : s = ∅ := eq_empty_of_forall_notMem fun i _ => Fin.elim0 i
    simp [hs, complexNoise_zero]
  | succ n ih =>
    rw [← Fin.cons_self_tail x]
    let b := x 0
    let y := Fin.tail x
    change complexNoise w (fun z => (walsh s z : ℂ)) (Fin.cons b y) =
      w ^ s.card * (walsh s (Fin.cons b y) : ℂ)
    have hcard : (tailSet s).card = (s.erase 0).card := by
      rw [← map_tailSet, card_map]
    rw [complexNoise_cons]
    by_cases h : 0 ∈ s
    · have hc : s.card = (tailSet s).card + 1 := by
        rw [hcard, card_erase_add_one h]
      simp only [walsh_cons_of_mem s h, Bool.false_eq_true, ↓reduceIte, mul_neg, mul_one,
        Complex.ofReal_neg]
      have hn : complexNoise w (fun z => -(walsh (tailSet s) z : ℂ)) y =
          - complexNoise w (fun z => (walsh (tailSet s) z : ℂ)) y := by
        simpa only [neg_one_mul] using
          complexNoise_const_mul w (-1) (fun z => (walsh (tailSet s) z : ℂ)) y
      rw [hn, ih, hc, pow_succ]
      cases b <;> simp <;> ring
    · have hc : s.card = (tailSet s).card := by rw [hcard, erase_eq_of_notMem h]
      simp only [walsh_cons_of_notMem s h, ih, hc]
      ring
end MomentComparison
