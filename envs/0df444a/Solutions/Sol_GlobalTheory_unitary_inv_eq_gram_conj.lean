-- Prove2me | solution 1 for GlobalTheory.unitary_inv_eq_gram_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:16.706905+00:00
-- url     : https://prove2.me/submissions/e039b86e-f40f-4a01-a5e1-dbebe67b09f5

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BesselJUnitaryEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryConjEntryAndInvEntryLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  refine Matrix.inv_eq_left_inv ?_
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [mul_assoc, mul_assoc, ← mul_assoc gᴴ, h, BesselUnitary.gram_sq]
end GlobalTheory
