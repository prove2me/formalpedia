-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.stdH_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:52.811745+00:00
-- url     : https://prove2.me/submissions/55161e8d-fe3a-47d4-9152-037d1a726ac4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_periodLatticeSesquilinearForm_isHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_stdH_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.ThetaVec
open Formalism.L2.Th1 Formalism.L2.Th1.H Complex GlobalTheory.ThetaInter
open scoped BigOperators ComplexConjugate Real
variable (L : PeriodPair)
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution : IsHerm (stdH L n) := fun x y => by
  simp only [stdH_apply, map_sum, ← periodLatticeSesquilinearForm_isHerm L _ _]
end GlobalTheory.Mem.Col2.ThetaVec
