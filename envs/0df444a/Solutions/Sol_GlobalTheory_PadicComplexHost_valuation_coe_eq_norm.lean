-- Prove2me | solution 1 for GlobalTheory.PadicComplexHost.valuation_coe_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:16.218558+00:00
-- url     : https://prove2.me/submissions/bac5f301-9b66-4e07-bf10-46a59fefaa04

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Ideal
open GlobalTheory GlobalTheory.PadicComplexHost
variable (p : ℕ) [hp : Fact p.Prime]
namespace GlobalTheory.PadicComplexHost
theorem _root_.solution (x : ℂ_[p]) : ((Valued.v x : NNReal) : ℝ) = ‖x‖ := by
  rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
    Valuation.embedding_restrict]
end GlobalTheory.PadicComplexHost
