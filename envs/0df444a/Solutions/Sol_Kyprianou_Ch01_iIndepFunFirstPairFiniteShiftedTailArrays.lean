-- Prove2me | solution 1 for Kyprianou.Ch01.iIndepFunFirstPairFiniteShiftedTailArrays
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:09:04.050327+00:00
-- url     : https://prove2.me/submissions/514a011b-6eab-4c3a-9326-a82b5b1ddbdd

import Mathlib
open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω)
    (f : (ℕ ⊕ ℕ) → Ω → ℝ)
    (hIndep : iIndepFun f Q)
    (hMeas : ∀ i : ℕ ⊕ ℕ, Measurable (f i))
    (I S T : Finset (ℕ ⊕ ℕ))
    (hS : S = {Sum.inl 0, Sum.inr 0})
    (hT : T = I.image (Sum.map Nat.succ Nat.succ)) :
    IndepFun
      (fun w (i : S) => f i.val w)
      (fun w (i : T) => f i.val w) Q := by
  classical
  subst S
  subst T
  have hDisj :
      Disjoint ({Sum.inl 0, Sum.inr 0} : Finset (ℕ ⊕ ℕ))
        (I.image (Sum.map Nat.succ Nat.succ)) := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiT
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hiT
    subst i
    cases j <;> simp at hiS
  exact ProbabilityTheory.iIndepFun.indepFun_finset
    _ _ hDisj hIndep hMeas
