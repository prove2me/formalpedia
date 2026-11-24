-- Prove2me | solution 1 for GlobalTheory.UnitaryZariskiDense.eval_cay_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:07:20.137629+00:00
-- url     : https://prove2.me/submissions/b389d3db-2b98-4afa-ac5a-9de03094365e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
import Theorems.Thm_GlobalTheory_UnitaryZariskiDense_mapMatrix_varMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
namespace GlobalTheory.UnitaryZariskiDense
theorem _root_.solution (x : ι × Fin a × Fin a → ℂ) (τ : ι) (i j : Fin a) :
    eval x (((1 - varMat (a := a) τ) * (1 + varMat τ).adjugate :
      Matrix (Fin a) (Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ)) i j) =
      ((1 - famOf x τ) * (1 + famOf x τ).adjugate) i j := by
  have e : ∀ M : Matrix (Fin a) (Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ),
      eval x (M i j) = ((eval x).mapMatrix M) i j := fun _ => rfl
  rw [e, map_mul, map_sub, map_one, RingHom.map_adjugate, map_add, map_one, mapMatrix_varMat]
end GlobalTheory.UnitaryZariskiDense
