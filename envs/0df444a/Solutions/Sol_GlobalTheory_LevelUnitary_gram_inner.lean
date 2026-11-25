-- Prove2me | solution 1 for GlobalTheory.LevelUnitary.gram_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:53:21.943464+00:00
-- url     : https://prove2.me/submissions/2717a834-e4a9-4177-9886-fa3a8eb87a5f

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramRight
import Theorems.Thm_GlobalTheory_LevelUnitary_mul_incl
import Theorems.Thm_GlobalTheory_LevelUnitary_inclH_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory GlobalTheory.LevelUnitary
variable (k i r' : ℕ)
namespace GlobalTheory.LevelUnitary
theorem _root_.solution : (incl k i r')ᴴ * Hpk k (i + r') * incl k i r' = Hpk k r' := by
  ext a b
  rw [mul_incl, inclH_mul]
  have ha := a.isLt
  have hb := b.isLt
  have hva : (levPos k i r' a).val = a.val + i := rfl
  have hvb : (levPos k i r' b).val = b.val + i := rfl
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
end GlobalTheory.LevelUnitary
