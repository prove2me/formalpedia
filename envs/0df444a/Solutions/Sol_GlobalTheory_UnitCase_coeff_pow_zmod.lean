-- Prove2me | solution 1 for GlobalTheory.UnitCase.coeff_pow_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:00.554931+00:00
-- url     : https://prove2.me/submissions/64f6e3f5-cb25-4a4d-96a5-e352f27e84a4

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
theorem _root_.solution {l : ℕ} (hl : l.Prime) (q : MvPolynomial κ ℤ) (A : κ →₀ ℕ) :
    ((MvPolynomial.coeff A (q ^ l) : ℤ) : ZMod l) =
      MvPolynomial.coeff A (MvPolynomial.expand l (MvPolynomial.map (Int.castRingHom (ZMod l)) q)) := by
  haveI := Fact.mk hl
  rw [MvPolynomial.expand_zmod, ← map_pow, MvPolynomial.coeff_map]
  rfl
end GlobalTheory.UnitCase
