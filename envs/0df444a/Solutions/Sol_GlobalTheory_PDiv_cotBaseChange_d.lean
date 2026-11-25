-- Prove2me | solution 1 for GlobalTheory.PDiv.cotBaseChange_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:01:12.899676+00:00
-- url     : https://prove2.me/submissions/73fbb57f-a99e-41dd-b6e5-50ca9f548b13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveSemilinearLiftBaseChangeBijective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d



set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.PDiv
variable {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A]
  [Module.Projective R A] [IsCocomm R A] [CommRing R'] [Algebra R R']
namespace GlobalTheory.PDiv
theorem _root_.solution (φ : CartierDual R A) :
    cotBaseChange R' (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) =
      (1 : R') ⊗ₜ dUnit R φ := by
  rw [cotBaseChange, LinearEquiv.symm_apply_eq, LinearEquiv.trans_apply,
    AugCot.baseChangeEquiv_tmul_d, one_smul, AugCot.congr_d]
  rfl
end GlobalTheory.PDiv
