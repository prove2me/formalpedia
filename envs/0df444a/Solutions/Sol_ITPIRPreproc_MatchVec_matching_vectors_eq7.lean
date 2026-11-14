-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.matching_vectors_eq7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T17:23:20.891918+00:00
-- url     : https://prove2.me/submissions/d8a08513-6cb4-416b-a8f8-866fd6aa5851
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ITPIRPreproc_MatchVec_polynomial_matching_vectors
import Theorems.Thm_ITPIRPreproc_MatchVec_polynomial_parameter_bounds
import Theorems.Thm_ITPIRPreproc_MatchVec_polynomial_indexed_computability
set_option backward.isDefEq.respectTransparency false
open ITPIRPreproc.MatchVec ITPIRPreproc.MatchVec.PolynomialConstruction

theorem solution :
    ∃ (dim : ℕ → ℕ) (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
      (C C₀ : ℝ) (c₀ : ℕ) (vecProg tableProg : WordRAM.Program),
      (∀ h : ℕ, 3 ≤ h →
        IsMVFamily (2 ^ h) (dim h) (u h) (v h) ∧
        (dim h : ℝ) ≤ 2 ^ (C * Real.sqrt (h * Real.log h))) ∧
      MVComputable dim u v C₀ c₀ vecProg tableProg  := by
  obtain ⟨dim, rows, coords, C₀, c₀, vecProg, tableProg, hcomp⟩ :=
    polynomial_indexed_computability
  refine ⟨dim,
    (fun h r j => leftVector (coefficient (wordLength h) (exponent2 h) (exponent3 h))
      (rows h r) (coords h j)),
    (fun h r j => rightVector (rows h r) (coords h j)),
    1000, C₀, c₀, vecProg, tableProg, ?_, hcomp⟩
  intro h hh
  have hp := polynomial_parameter_bounds h (dim h) hh (coords h)
  exact ⟨(polynomial_matching_vectors (wordLength h) (exponent2 h) (exponent3 h)
    (2^h) (dim h) hp.2.1 hp.2.2.1 (rows h) (coords h)).1, hp.2.2.2⟩
