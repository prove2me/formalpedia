-- Prove2me | solution 1 for MasulloRH.lifted_rank_one_sum_eq_convolution_projection_iff
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:18:55.863844+00:00
-- url     : https://prove2.me/submissions/30e27705-e763-49c2-9ec4-45ebe53e5a77

import Mathlib

open InnerProductSpace

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A P T : H →L[ℂ] H) (v η : ℕ → H)
    (hbi : ∀ i j, inner ℂ (η i) (v j) = if i = j then 1 else 0)
    (hk : ∀ i (u : H), P u = 0 → inner ℂ (η i) u = 0)
    (hd : Dense (Submodule.span ℂ (Set.range v ∪ (P.ker : Set H)) : Set H))
    (hT : HasSum (fun i => rankOne ℂ (A (v i)) (η i)) T) :
    T = A.comp P ↔ ∀ j, A (v j) = A (P (v j)) := by
  classical
  have hv (j : ℕ) : T (v j) = A (v j) := by
    have h := (ContinuousLinearMap.apply ℂ H (v j)).hasSum hT
    change HasSum (fun i => inner ℂ (η i) (v j) • A (v i)) (T (v j)) at h
    rw [← h.tsum_eq, tsum_eq_single j]
    · simp [hbi]
    · intro i hij
      simp [hbi, hij]
  constructor
  · intro h j
    rw [← hv, h]
    rfl
  · intro h
    apply ContinuousLinearMap.ext_on hd
    intro u hu
    rcases hu with ⟨j, rfl⟩ | hu
    · exact (hv j).trans (h j)
    · have hPu : P u = 0 := hu
      have he := (ContinuousLinearMap.apply ℂ H u).hasSum hT
      change HasSum (fun i => inner ℂ (η i) u • A (v i)) (T u) at he
      change T u = A (P u)
      simp [← he.tsum_eq, fun i => hk i u hPu, hPu]
