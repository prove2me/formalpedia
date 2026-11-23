-- Prove2me | solution 1 for Kyprianou.Ch01.firstPairIndepOfEveryFiniteShiftedTailCylinder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:26:48.846802+00:00
-- url     : https://prove2.me/submissions/7a527ff6-c2bd-4517-a6ff-4ca9eb27fa2d

import Mathlib
open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (arrival marks : ℕ → Ω → ℝ)
    (hArrival : ∀ n : ℕ, Measurable (arrival n))
    (hMarks : ∀ n : ℕ, Measurable (marks n))
    (hFinite : ∀ I : Finset (ℕ ⊕ ℕ),
      IndepFun
        (fun w => (arrival 0 w, marks 0 w))
        (fun w (i : I) => match i.val with
          | Sum.inl n => arrival (n + 1) w
          | Sum.inr n => marks (n + 1) w) Q) :
    IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q := by
  let Y : (ℕ ⊕ ℕ) → Ω → ℝ := fun i w =>
    match i with
    | Sum.inl n => arrival (n + 1) w
    | Sum.inr n => marks (n + 1) w
  have hYMeas (i : ℕ ⊕ ℕ) : Measurable (Y i) := by
    cases i with
    | inl n => exact hArrival (n + 1)
    | inr n => exact hMarks (n + 1)
  have hHeadMeas : Measurable
      (fun w => (arrival 0 w, marks 0 w)) :=
    (hArrival 0).prodMk (hMarks 0)
  have hTagged : IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w i => Y i w) Q :=
    ProbabilityTheory.IndepFun.indepFun_process
      hHeadMeas hYMeas (by
        intro I
        simpa only [Y] using hFinite I)
  let unpack : ((ℕ ⊕ ℕ) → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun g => (fun n => g (Sum.inl n), fun n => g (Sum.inr n))
  have hUnpack : Measurable unpack := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda
        (fun g : (ℕ ⊕ ℕ) → ℝ => fun n : ℕ => g (Sum.inl n))
        (fun n => measurable_pi_apply (Sum.inl n))
    · exact measurable_pi_lambda
        (fun g : (ℕ ⊕ ℕ) → ℝ => fun n : ℕ => g (Sum.inr n))
        (fun n => measurable_pi_apply (Sum.inr n))
  have hComp :=
    ProbabilityTheory.IndepFun.comp hTagged measurable_id hUnpack
  have hTail :
      (unpack ∘ (fun w i => Y i w)) =
        (fun w => ((fun n : ℕ => arrival (n + 1) w),
                   (fun n : ℕ => marks (n + 1) w))) := by
    funext w
    apply Prod.ext
    · funext n
      rfl
    · funext n
      rfl
  rw [hTail] at hComp
  have hHead :
      (id ∘ fun w => (arrival 0 w, marks 0 w)) =
        (fun w => (arrival 0 w, marks 0 w)) := rfl
  rw [hHead] at hComp
  exact hComp
