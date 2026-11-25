-- Prove2me | solution 1 for GlobalTheory.PDiv.rankAtStalk_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:08.575837+00:00
-- url     : https://prove2.me/submissions/9fe8d62f-c3f5-4434-8583-687885ccfca6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerCounitAlgHomBaseChangeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_fibreDim_dual
import Theorems.Thm_GlobalTheory_AugCot_rankAtStalk_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory GlobalTheory.PDiv
variable {O : Type} [CommRing O]
variable {M N P : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
  [AddCommGroup P] [Module O P]
variable [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]
namespace GlobalTheory.PDiv
theorem _root_.solution (q : PrimeSpectrum O) :
    rankAtStalk (CartierDual O M) q = rankAtStalk M q := by
  rw [rankAtStalk_eq, rankAtStalk_eq]
  exact fibreDim_dual q
end GlobalTheory.PDiv
