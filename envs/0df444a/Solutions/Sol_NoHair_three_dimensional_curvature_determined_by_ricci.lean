-- Prove2me | solution 1 for NoHair.three_dimensional_curvature_determined_by_ricci
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:41:52.092806+00:00
-- url     : https://prove2.me/submissions/1fadb372-b2cc-48b1-8ab2-340d6ee1c095

import Mathlib

open Matrix

noncomputable section

open scoped Matrix
private abbrev I := Fin 3
private abbrev M := Matrix I I ℝ
private def u : I → I := ![1,2,0]
private def v : I → I := ![2,0,1]
private def skew (f : I → ℝ) : M := !![0,f 2,-f 1; -f 2,0,f 0; f 1,-f 0,0]

private lemma skew_entries (s : I → I → ℝ) (alt : ∀ a b, s a b = -s b a) (i j : I) :
    s i j = skew (fun k => s (u k) (v k)) i j := by
  fin_cases i <;> fin_cases j
  · change s 0 0 = 0
    linarith only [alt 0 0]
  · rfl
  · exact alt 0 2
  · exact alt 1 0
  · change s 1 1 = 0
    linarith only [alt 1 1]
  · rfl
  · rfl
  · exact alt 2 1
  · change s 2 2 = 0
    linarith only [alt 2 2]

private def inflate (A : M) (a b i j : I) : ℝ :=
  skew (fun p => skew (A p) i j) a b
private def contraction (B A : M) (b j : I) : ℝ :=
  ∑ a : I, ∑ i : I, B a i * inflate A a b i j

set_option maxHeartbeats 1600000 in
private lemma inverse_contraction (B A : M) (hs : B.IsSymm) (p q : I) :
    2*B.det*A p q =
      B q p * (∑ i : I, ∑ j : I, B i j * contraction B A j i) -
      2 * (∑ i : I, ∑ j : I, B q i * contraction B A i j * B j p) := by
  have s10 : B 1 0 = B 0 1 := hs.apply 0 1
  have s20 : B 2 0 = B 0 2 := hs.apply 0 2
  have s21 : B 2 1 = B 1 2 := hs.apply 1 2
  fin_cases p <;> fin_cases q <;>
    simp [contraction,inflate,skew,Fin.sum_univ_three,Matrix.det_fin_three,s10,s20,s21] <;> ring

theorem solution (B : Matrix (Fin 3) (Fin 3) ℝ) (symm : B.IsSymm) (nonsing : B.det ≠ 0)
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (first : ∀ a b i j, R a b i j = -R b a i j)
    (last : ∀ a b i j, R a b i j = -R a b j i)
    (ric : ∀ b j, (∑ a : Fin 3, ∑ i : Fin 3, B a i * R a b i j) = 0) :
    ∀ a b i j, R a b i j = 0 := by
  let A : M := fun p q => R (u p) (v p) (u q) (v q)
  have rep (a b i j : I) : R a b i j = inflate A a b i j := by
    have e := skew_entries (fun a b => R a b i j) (fun a b => first a b i j) a b
    rw [e]
    unfold inflate
    apply congrArg (fun f => skew f a b)
    funext p
    exact skew_entries (R (u p) (v p)) (last (u p) (v p)) i j
  have zero (i j : I) : contraction B A i j = 0 := by
    simpa only [contraction,←rep] using ric i j
  have az (p q : I) : A p q = 0 := by
    have z := inverse_contraction B A symm p q
    simp only [zero,mul_zero,zero_mul,Finset.sum_const_zero,sub_zero] at z
    exact (mul_eq_zero.mp z).resolve_left (mul_ne_zero (by norm_num) nonsing)
  intro a b i j
  rw [rep]
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;> simp [inflate,skew,az]
