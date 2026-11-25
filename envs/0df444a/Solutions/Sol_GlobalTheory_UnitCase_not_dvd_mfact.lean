-- Prove2me | solution 1 for GlobalTheory.UnitCase.not_dvd_mfact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:15.3008+00:00
-- url     : https://prove2.me/submissions/029588f1-2e20-4245-8589-a6ab9fa9f044

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_mfact_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution [Fintype κ] {l : ℕ} (hl : l.Prime) (β : κ →₀ ℕ) (h : ∀ j, β j < l) :
    ¬ l ∣ mfact β := by
  rw [mfact_eq, Prime.dvd_finset_prod_iff hl.prime]
  rintro ⟨j, -, hj⟩
  exact absurd (hl.dvd_factorial.1 hj) (not_le.2 (h j))
end GlobalTheory.UnitCase
