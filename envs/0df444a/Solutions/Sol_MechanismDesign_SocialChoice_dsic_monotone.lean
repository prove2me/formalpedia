-- Prove2me | solution 1 for MechanismDesign.SocialChoice.dsic_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:17:10.720043+00:00
-- url     : https://prove2.me/submissions/ea5a312f-3c3f-418c-922f-97655a08c072

import Mathlib
import Definitions.Def_MechanismDesign_SocialChoice_Model

set_option autoImplicit false
open MechanismDesign.SocialChoice

theorem solution {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]
    (f : DirectMechanism ι A) (hf : IsDSIC f) : IsMonotone f := by
  intro R R' a hfa hab
  -- interpolating profiles: R' on `s`, R elsewhere
  let Rs : Finset ι → (ι → LinPref A) := fun s i => if i ∈ s then R' i else R i
  have key : ∀ s : Finset ι, f (Rs s) = a := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : Rs ∅ = R := by funext i; simp [Rs]
      rw [this, hfa]
    | insert j s hj ih =>
      have e1 : Rs (insert j s) = Function.update (Rs s) j (R' j) := by
        funext i
        by_cases h : i = j
        · subst h; simp [Rs]
        · simp [Rs, h]
      have e2 : Function.update (Rs (insert j s)) j (R j) = Rs s := by
        funext i
        by_cases h : i = j
        · subst h; simp [Rs, hj]
        · simp [Rs, h]
      have h1 := hf j (Rs s) (R' j)
      have h2 := hf j (Rs (insert j s)) (R j)
      rw [← e1, ih] at h1
      rw [e2, ih] at h2
      have hj0 : Rs s j = R j := by simp [Rs, hj]
      rw [hj0] at h1
      have h3 : (R' j).rel a (f (Rs (insert j s))) := hab j _ h1
      have e3 : Rs (insert j s) j = R' j := by simp [Rs]
      rw [e3] at h2
      exact (R' j).antisymm _ _ h2 h3
  have : Rs Finset.univ = R' := by funext i; simp [Rs]
  rw [← this]
  exact key _
