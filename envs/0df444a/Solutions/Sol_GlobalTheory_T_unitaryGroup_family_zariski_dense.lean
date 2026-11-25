-- Prove2me | solution 1 for GlobalTheory.T.unitaryGroup_family_zariski_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:39.247124+00:00
-- url     : https://prove2.me/submissions/786946d2-4102-4da0-bcd9-3072eba3faf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDenseStatement
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_unitary_zariski_dense


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} [Fintype ι] {a : ℕ} (Q : MvPolynomial (ι × Fin a × Fin a) ℂ), (∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ, MvPolynomial.eval (fun v : ι × Fin a × Fin a => (g v.1 : Matrix (Fin a) (Fin a) ℂ) v.2.1 v.2.2) Q = 0) → Q = 0 := by
  first | exact @GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense | exact GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense | (intros; apply GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense <;> assumption)
end _root_.GlobalTheory.T
