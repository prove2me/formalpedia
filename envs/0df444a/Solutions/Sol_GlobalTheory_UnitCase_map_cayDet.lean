-- Prove2me | solution 1 for GlobalTheory.UnitCase.map_cayDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:29.068162+00:00
-- url     : https://prove2.me/submissions/ec727401-462d-4aee-a1e7-b84991a5a699

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow

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
theorem _root_.solution (n : ℕ) : MvPolynomial.map (Int.castRingHom C) (cayDet n ℤ) = cayDet n C := by
  rw [cayDet, cayDet, RingHom.map_det]
  congr 1
  ext1 i j
  simp [Matrix.mvPolynomialX]
end GlobalTheory.UnitCase
