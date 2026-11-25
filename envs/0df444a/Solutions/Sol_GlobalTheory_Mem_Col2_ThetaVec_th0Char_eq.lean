-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.th0Char_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:57.408637+00:00
-- url     : https://prove2.me/submissions/6ce4cfe3-4894-4bfb-bf69-1e6811263dce

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_herm_eq
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_semiChar_eq

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
theorem _root_.solution (ω₀ ω : ℂ) :
    F.thetaZeroCharacter L ω₀ ω = sigmaSign L ω * cexp (π * I * (altE (form1 L) ω ω₀ : ℂ)) := by
  rw [F.thetaZeroCharacter, semiChar_eq, F.altE, herm_eq]; rfl
end GlobalTheory.Mem.Col2.ThetaVec
