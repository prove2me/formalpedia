-- Prove2me | solution 1 for InterimTesting.NotProficient.lemma_A1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:39:48.257831+00:00
-- url     : https://prove2.me/submissions/214c404f-0db5-41ee-93a6-453829840899

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

open InterimTesting.NotProficient

theorem solution (θ : Params) (hθ : θ.Standing) (zI : Bool) (S0 : Prof) (e0 : ℝ)
    (he0 : e0 ∈ Set.Icc (0 : ℝ) 1) :
    obsProb θ zI S0 e0 .P =
        (acc θ zI).1 * toP θ S0 e0 + (acc θ zI).2 * (1 - toP θ S0 e0) ∧
      post θ zI S0 e0 .P = (acc θ zI).1 * toP θ S0 e0 /
        ((acc θ zI).1 * toP θ S0 e0 + (acc θ zI).2 * (1 - toP θ S0 e0)) ∧
      post θ zI S0 e0 .N = (1 - (acc θ zI).1) * toP θ S0 e0 /
        ((1 - (acc θ zI).1) * toP θ S0 e0 + (1 - (acc θ zI).2) * (1 - toP θ S0 e0)) ∧
      ∀ (x : Prof) (e1 : ℝ), obsProb θ zI S0 e0 x ≠ 0 →
        (joint θ zI S0 e0 .P x * toP θ .P e1 + joint θ zI S0 e0 .N x * toP θ .N e1) /
            obsProb θ zI S0 e0 x = finalP θ (post θ zI S0 e0 x) e1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [obsProb, joint, sig]; ring
  · simp only [post, obsProb, joint, sig]; ring
  · simp only [post, obsProb, joint, sig]; ring
  · intro x e1 hx
    unfold finalP post
    unfold obsProb at hx ⊢
    generalize joint θ zI S0 e0 .P x = a at hx ⊢
    generalize joint θ zI S0 e0 .N x = b at hx ⊢
    field_simp
    ring
