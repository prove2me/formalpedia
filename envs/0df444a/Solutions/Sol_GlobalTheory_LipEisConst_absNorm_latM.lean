-- Prove2me | solution 1 for GlobalTheory.LipEisConst.absNorm_latM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:45:04.748778+00:00
-- url     : https://prove2.me/submissions/6d26b70e-3cf2-4dc1-bd68-fc58d051b455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzConstantInverseDifferentEisenstein

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LipEisConst
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
namespace GlobalTheory.LipEisConst
theorem _root_.solution {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) :
    ((FractionalIdeal.absNorm (latM 𝔞) : ℚ) : ℝ) = (dF F * nrm 𝔞)⁻¹ := by
  rw [latM, map_mul, map_inv₀, Units.val_inv_eq_inv_val, map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    absNorm_differentIdeal F (𝓞 F), dF, nrm]
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs, mul_inv]
end GlobalTheory.LipEisConst
