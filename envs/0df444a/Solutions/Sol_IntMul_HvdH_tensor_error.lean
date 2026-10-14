-- Prove2me | solution 1 for IntMul.HvdH.tensor_error
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T23:04:08.732808+00:00
-- url     : https://prove2.me/submissions/c31b813a-83fb-47c9-9b90-bc8865e73cd0

import Definitions.Def_IntMul_HvdH_SliceTensor

namespace IntMul.HvdH.TensorPf
open IntMul.HvdH

variable {ι : Type*}

/-- Arrays in the closed unit ball for the max-norm. -/
def InBall (x : ι → ℂ) : Prop := ∀ k, ‖x k‖ ≤ 1

/-- Nonexpansive for the max-norm. -/
def NonExp {κ : Type*} (A : (ι → ℂ) → (κ → ℂ)) : Prop :=
  ∀ (x y : ι → ℂ) (δ : ℝ), (∀ k, ‖x k - y k‖ ≤ δ) → ∀ j, ‖A x j - A y j‖ ≤ δ

lemma sliceMap_ball {d : ℕ} (i : Fin d) (A : (ℕ → ℂ) → (ℕ → ℂ))
    (hA : ∀ x, InBall x → InBall (A x)) (x : (Fin d → ℕ) → ℂ) (hx : InBall x) :
    InBall (sliceMap i A x) := fun j => hA _ (fun k => hx _) _

lemma sliceMap_nonexp {d : ℕ} (i : Fin d) (A : (ℕ → ℂ) → (ℕ → ℂ)) (hA : NonExp A) :
    NonExp (sliceMap i A) := fun x y δ h j => hA _ _ δ (fun k => h _) _

lemma sliceMap_err {d : ℕ} (i : Fin d) (A Aa : (ℕ → ℂ) → (ℕ → ℂ)) (e : ℝ)
    (h : ∀ x, InBall x → ∀ j, ‖Aa x j - A x j‖ ≤ e) (x : (Fin d → ℕ) → ℂ) (hx : InBall x) :
    ∀ j, ‖sliceMap i Aa x j - sliceMap i A x j‖ ≤ e := fun j => h _ (fun k => hx _) _

lemma sliceComp_ball {d : ℕ} (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ))
    (hA : ∀ i x, InBall x → InBall (A i x)) (l : List (Fin d)) :
    ∀ x, InBall x → InBall (sliceComp A l x) := by
  induction l with
  | nil => intro x hx; exact hx
  | cons i l ih => intro x hx; exact ih _ (sliceMap_ball i (A i) (hA i) x hx)

lemma sliceComp_nonexp {d : ℕ} (A : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (hA : ∀ i, NonExp (A i))
    (l : List (Fin d)) : NonExp (sliceComp A l) := by
  induction l with
  | nil => intro x y δ h; exact h
  | cons i l ih =>
    intro x y δ h
    exact ih _ _ δ (sliceMap_nonexp i (A i) (hA i) x y δ h)

lemma sliceComp_err {d : ℕ} (A Aa : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (e : Fin d → ℝ)
    (hA : ∀ i, NonExp (A i)) (hAa : ∀ i x, InBall x → InBall (Aa i x))
    (herr : ∀ i x, InBall x → ∀ j, ‖Aa i x j - A i x j‖ ≤ e i) (l : List (Fin d)) :
    ∀ x, InBall x → ∀ j, ‖sliceComp Aa l x j - sliceComp A l x j‖ ≤ (l.map e).sum := by
  induction l with
  | nil => intro x _ j; simp [sliceComp]
  | cons i l ih =>
    intro x hx j
    simp only [sliceComp, Function.comp_apply, List.map_cons, List.sum_cons]
    set xa := sliceMap i (Aa i) x
    set xe := sliceMap i (A i) x
    have hxa : InBall xa := sliceMap_ball i (Aa i) (hAa i) x hx
    have h1 := ih xa hxa j
    have h2 := sliceComp_nonexp A hA l xa xe (e i) (sliceMap_err i (A i) (Aa i) (e i) (herr i) x hx) j
    calc ‖sliceComp Aa l xa j - sliceComp A l xe j‖
        ≤ ‖sliceComp Aa l xa j - sliceComp A l xa j‖ + ‖sliceComp A l xa j - sliceComp A l xe j‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (l.map e).sum + e i := add_le_add h1 h2
      _ = e i + (l.map e).sum := add_comm _ _

/-- Lemma 2.11 (error part): approximating each factor with error `eᵢ` approximates the tensor
product with error `∑ eᵢ`. -/
theorem tensor_error {d : ℕ} (A Aa : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (e : Fin d → ℝ)
    (hA : ∀ i, ∀ (x y : ℕ → ℂ) (δ : ℝ), (∀ k, ‖x k - y k‖ ≤ δ) → ∀ j, ‖A i x j - A i y j‖ ≤ δ)
    (hAa : ∀ i (x : ℕ → ℂ), (∀ k, ‖x k‖ ≤ 1) → ∀ j, ‖Aa i x j‖ ≤ 1)
    (herr : ∀ i (x : ℕ → ℂ), (∀ k, ‖x k‖ ≤ 1) → ∀ j, ‖Aa i x j - A i x j‖ ≤ e i)
    (x : (Fin d → ℕ) → ℂ) (hx : ∀ j, ‖x j‖ ≤ 1) (j : Fin d → ℕ) :
    ‖tensorMap Aa x j - tensorMap A x j‖ ≤ ∑ i, e i := by
  have h := sliceComp_err A Aa e hA hAa herr (List.finRange d) x hx j
  unfold tensorMap
  refine h.trans (le_of_eq ?_)
  rw [Fin.sum_univ_def]

end IntMul.HvdH.TensorPf

open IntMul.HvdH in
theorem solution {d : ℕ} (A Aa : Fin d → (ℕ → ℂ) → (ℕ → ℂ)) (e : Fin d → ℝ)
    (hA : ∀ i, ∀ (x y : ℕ → ℂ) (δ : ℝ), (∀ k, ‖x k - y k‖ ≤ δ) → ∀ j, ‖A i x j - A i y j‖ ≤ δ)
    (hAa : ∀ i (x : ℕ → ℂ), (∀ k, ‖x k‖ ≤ 1) → ∀ j, ‖Aa i x j‖ ≤ 1)
    (herr : ∀ i (x : ℕ → ℂ), (∀ k, ‖x k‖ ≤ 1) → ∀ j, ‖Aa i x j - A i x j‖ ≤ e i)
    (x : (Fin d → ℕ) → ℂ) (hx : ∀ j, ‖x j‖ ≤ 1) (j : Fin d → ℕ) :
    ‖tensorMap Aa x j - tensorMap A x j‖ ≤ ∑ i, e i :=
  IntMul.HvdH.TensorPf.tensor_error A Aa e hA hAa herr x hx j
