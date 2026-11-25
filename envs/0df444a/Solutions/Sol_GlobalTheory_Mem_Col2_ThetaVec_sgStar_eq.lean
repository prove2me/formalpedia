-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.sgStar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:58.901478+00:00
-- url     : https://prove2.me/submissions/77fa0827-6c4e-4a1c-a458-3e07fc0443db

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_quasiPeriodConst_eq

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
theorem _root_.solution : F.sgStar L = canonicalSigma L := by
  funext z
  have : ∀ l : ℂ, F.wFactor l z = sigmaFactor l z := by
    intro l
    rw [sigmaFactor_eq, F.wFactor, primaryFactor, div_pow, div_div, mul_comm (l ^ 2)]
  rw [F.sgStar, canonicalSigma, F.wSigma, weierstrassSigma, sigmaProd, quasiPeriodConst_eq]
  simp only [this]
  congr 2
  ring
end GlobalTheory.Mem.Col2.ThetaVec
