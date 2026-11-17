-- Prove2me | solution 1 for N25.Endgame.adjoin_pair_eq_top_of_coprime_finrank
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:45.786243+00:00
-- url     : https://prove2.me/submissions/4e53410e-d13d-4990-85d2-5b30b06b25b6

import Mathlib

set_option autoImplicit false

noncomputable section

namespace N25.Endgame

/-- Coprime simple-subfield degrees force a pair to generate the ambient field. -/
theorem _root_.solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u v : F)
    [FiniteDimensional (IntermediateField.adjoin K ({u} : Set F)) F]
    [FiniteDimensional (IntermediateField.adjoin K ({v} : Set F)) F]
    (hcop :
      Nat.Coprime
        (Module.finrank (IntermediateField.adjoin K ({u} : Set F)) F)
        (Module.finrank (IntermediateField.adjoin K ({v} : Set F)) F)) :
    IntermediateField.adjoin K ({u, v} : Set F) = ⊤ := by
  apply IntermediateField.finrank_eq_one_iff_eq_top.mp
  apply Nat.eq_one_of_dvd_coprimes hcop
  · apply IntermediateField.finrank_dvd_of_le_left
    exact IntermediateField.adjoin.mono _ _ _ (by simp)
  · apply IntermediateField.finrank_dvd_of_le_left
    exact IntermediateField.adjoin.mono _ _ _ (by simp)

end N25.Endgame
