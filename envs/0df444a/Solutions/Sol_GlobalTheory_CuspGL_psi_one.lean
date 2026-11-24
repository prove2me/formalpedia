-- Prove2me | solution 1 for GlobalTheory.CuspGL.psi_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:40.824561+00:00
-- url     : https://prove2.me/submissions/2896e7f5-190d-4faf-8f0e-62ef7d09c550

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumGaussianMulProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBasesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIco
import Theorems.Thm_GlobalTheory_CuspGL_psi_one_eq_oneValue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (s : F[X] → ℂ) (hs : ∀ j : ℕ, s ((X - C 1) ^ j) = j) (h : 0 < Module.finrank F V) :
    psi s V 1 = ∏ i ∈ Finset.Ico 1 (Module.finrank F V), (1 - (Nat.card F : ℂ) ^ i) := by
  rw [psi_one_eq_oneValue F s hs _ V rfl, oneValue, if_neg h.ne']
end GlobalTheory.CuspGL
