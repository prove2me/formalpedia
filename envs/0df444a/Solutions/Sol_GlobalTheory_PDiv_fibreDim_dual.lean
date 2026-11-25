-- Prove2me | solution 1 for GlobalTheory.PDiv.fibreDim_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:45.596293+00:00
-- url     : https://prove2.me/submissions/7a6278aa-407a-4dfc-b159-c1a3e5ce7f67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerCounitAlgHomBaseChangeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Theorems.Thm_GlobalTheory_PDiv_fibreDim_congr
import Theorems.Thm_GlobalTheory_DualFibreRank_finrank_dual_and_range_dualMap_baseChange


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
theorem _root_.solution (q : PrimeSpectrum O) : fibreDim (CartierDual O M) q = fibreDim M q :=
  (fibreDim_congr (CartierDual.toDual O M) q).trans (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M M _ LinearMap.id).1
end GlobalTheory.PDiv
