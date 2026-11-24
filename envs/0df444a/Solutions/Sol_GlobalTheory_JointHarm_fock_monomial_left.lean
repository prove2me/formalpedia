-- Prove2me | solution 1 for GlobalTheory.JointHarm.fock_monomial_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:29:16.533001+00:00
-- url     : https://prove2.me/submissions/8b28ab84-e847-496a-b60b-85ba372f613f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LowerUnipotentMinors
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JointHarmonicOfHookNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JointHarm
open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionPolynomials
variable {n p q : ℕ}
open Formalism.E
namespace GlobalTheory.JointHarm
theorem _root_.solution {σ : Type} (α : σ →₀ ℕ) (c : ℂ) (Q : MvPolynomial σ ℂ) :
    fock (monomial α c) Q = c * star (Q.coeff α) * (Formalism.A.mfact α : ℂ) := by
  classical
  unfold fock
  rw [support_monomial]
  split_ifs with hc
  · simp [hc]
  · simp
end GlobalTheory.JointHarm
