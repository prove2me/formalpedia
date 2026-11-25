-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.differentiable_evenTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:21.338329+00:00
-- url     : https://prove2.me/submissions/9043c00e-0b17-469b-b7fc-80295b4898f7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_thetaZero_periodLattice_eq
import Theorems.Thm_GlobalTheory_ThetaInter_differentiable_opU


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
theorem _root_.solution (t : ℂ) : Differentiable ℂ (F.th0 L t) := by
  have : F.th0 L t = fun z => opU (form1 L) t (canonicalSigma L) z / opU (form1 L) t (canonicalSigma L) 0 :=
    funext (thetaZero_periodLattice_eq L t)
  rw [this]
  exact (differentiable_opU (differentiable_canonicalSigma L) t).div_const _
end GlobalTheory.Mem.Col2.ThetaVec
