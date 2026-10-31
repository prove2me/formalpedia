-- Prove2me | solution 1 for HuangN13.N13ConstructedRationalPointTheorem.exists_separated_compatibleReduction
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:54:08.725167+00:00
-- url     : https://prove2.me/submissions/dcb62618-5944-4d73-8185-796c6d45ec98

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_CompatibleReductionCore
import Theorems.Thm_HuangN13_N13ConstructedRationalPointTheorem_quotient_kernel_separated

set_option autoImplicit false

theorem solution : ∃ D : MazurProof.N13RationalPointEndgame.CompatibleReduction,
    MazurProof.N18RouteC.Separated.NSeparated D.classifier.red.ker 2 :=
  ⟨MazurProof.N13ConstructedReductionClassifier.compatibleReduction,
    HuangN13.N13ConstructedRationalPointTheorem.quotient_kernel_separated⟩
