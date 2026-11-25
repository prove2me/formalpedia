-- Prove2me | solution 1 for GlobalTheory.sandwich_entry_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:52:55.579816+00:00
-- url     : https://prove2.me/submissions/a1614121-9151-42b2-ad56-42e003e7b234

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
theorem _root_.solution {n : Type*} [Fintype n] (A M B : Matrix n n ℂ) (i j : n) :
    (A * M * B) i j = ∑ a, ∑ b, A i a * B b j * M a b := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
end GlobalTheory
