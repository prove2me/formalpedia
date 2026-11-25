-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.thetaZero_periodLattice_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:54:29.938795+00:00
-- url     : https://prove2.me/submissions/aec834d5-b43d-4913-bbcc-30e52998502a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_sgStar_eq
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_opU_eq

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
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution (t z : ℂ) :
    F.th0 L t z = opU (form1 L) t (canonicalSigma L) z / opU (form1 L) t (canonicalSigma L) 0 := by
  rw [F.th0, opU_eq, sgStar_eq]
end GlobalTheory.Mem.Col2.ThetaVec
