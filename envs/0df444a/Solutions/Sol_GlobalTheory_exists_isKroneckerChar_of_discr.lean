-- Prove2me | solution 1 for GlobalTheory.exists_isKroneckerChar_of_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:54:22.931036+00:00
-- url     : https://prove2.me/submissions/29e50384-fa02-4a5e-a6b1-f78fa18af869

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Theorems.Thm_GlobalTheory_QuadraticZeta_discr_mod_four
import Theorems.Thm_GlobalTheory_exists_isKroneckerChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution (h2 : finrank ℚ K = 2) (hD : discr K = -d) :
    ∃ χ : DirichletCharacter ℂ d, IsKroneckerChar χ := by
  have := discr_mod_four h2
  have := discr_ne_zero K
  exact exists_isKroneckerChar (by omega) (by omega)
end GlobalTheory
