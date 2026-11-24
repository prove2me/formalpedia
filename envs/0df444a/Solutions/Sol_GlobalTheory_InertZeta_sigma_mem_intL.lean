-- Prove2me | solution 1 for GlobalTheory.InertZeta.sigma_mem_intL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:47:52.230972+00:00
-- url     : https://prove2.me/submissions/c60c5870-d47b-48a3-a752-d0ed1a5f18bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallCornerOfHeisenbergDuality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution {x : L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (h : x ∈ intL L) : σ x ∈ intL L := by
  change Valued.v (σ x) ≤ 1
  rw [hσ]
  exact h
end GlobalTheory.InertZeta
