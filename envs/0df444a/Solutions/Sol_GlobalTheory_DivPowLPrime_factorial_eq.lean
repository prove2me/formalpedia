-- Prove2me | solution 1 for GlobalTheory.DivPowLPrime.factorial_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:51.466866+00:00
-- url     : https://prove2.me/submissions/31257b23-a20e-4743-8e53-3f086ff4f151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DivPowLPrime
namespace GlobalTheory.DivPowLPrime
theorem _root_.solution {l : ℕ} (hl : l.Prime) (m : ℕ) :
    m.factorial = l ^ padicValNat l m.factorial * factPrimePart l m := by
  rw [factPrimePart, ← Nat.factorization_def _ hl]
  exact (Nat.ordProj_mul_ordCompl_eq_self _ _).symm
end GlobalTheory.DivPowLPrime
