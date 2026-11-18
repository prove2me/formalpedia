-- Prove2me | solution 1 for Kyprianou.Ch01.finitePrefixIndependentOfNext
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T03:05:47.251799+00:00
-- url     : https://prove2.me/submissions/9625b8e9-02c9-4707-a259-fe1948778e45

import Mathlib.Probability.Independence.Basic
open MeasureTheory ProbabilityTheory Set Finset
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (increment : ℕ → Ω → ℝ)
    (hmeas : ∀ n : ℕ, Measurable (increment n))
    (hindep : iIndepFun increment P) (n : ℕ) :
    IndepFun (fun ω (i : Finset.range n) => increment i.1 ω)
      (increment n) P := by
  have h := hindep.indepFun_finset (Finset.range n) {n}
    (by simp) hmeas
  exact h.comp measurable_id (measurable_pi_apply (⟨n, Finset.mem_singleton_self n⟩ : ({n} : Finset ℕ)))
