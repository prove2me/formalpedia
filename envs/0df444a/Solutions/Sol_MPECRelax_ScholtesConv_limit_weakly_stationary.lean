-- Prove2me | solution 1 for MPECRelax.ScholtesConv.limit_weakly_stationary
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T19:48:37.898828+00:00
-- url     : https://prove2.me/submissions/4a2f301a-ef23-46ec-a919-e34ebbe9b36b

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Scholtes
import Theorems.Thm_MPECRelax_ScholtesConv_theorem_3_1

open Filter Topology

open MPECRelax.ScholtesConv in
theorem solution {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (t : ℕ → ℝ) (ht_pos : ∀ k, 0 < t k) (ht_anti : Antitone t)
    (ht_lim : Tendsto t atTop (𝓝 0))
    (x : ℕ → E n) (hx : ∀ k, (P.RS (t k)).IsKKTPoint (x k))
    (xs : E n) (hxs : Tendsto x atTop (𝓝 xs)) (hCQ : P.MPEC_MFCQ xs) :
    P.IsWeaklyStationary xs := by
  obtain ⟨hfeas, lam, mu, γ, ν, hw, -⟩ :=
    theorem_3_1 P hP t ht_pos ht_anti ht_lim x hx xs hxs hCQ
  exact ⟨hfeas, lam, mu, γ, ν, hw⟩
