-- Prove2me | solution 1 for GlobalTheory.UnitLemma.exists_invAlg_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:10:27.318703+00:00
-- url     : https://prove2.me/submissions/54704fc0-6091-4f47-9df6-4d3d2863e17f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSelfReciprocalInvAlgWithPoly
import Theorems.Thm_GlobalTheory_UnitLemma_InertUnit_charpoly_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma
noncomputable section
open InertUnit
namespace GlobalTheory.UnitLemma
theorem _root_.solution : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic →
    C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse →
    ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by
  intro K P hP hr
  refine ⟨invAlg hP hr, ?_, charpoly_root hP hr⟩
  show AdjoinRoot.root P * sig hP hr (AdjoinRoot.root P) = 1
  rw [sig_root]
  exact root_mul_rootInv hP hr
end GlobalTheory.UnitLemma
