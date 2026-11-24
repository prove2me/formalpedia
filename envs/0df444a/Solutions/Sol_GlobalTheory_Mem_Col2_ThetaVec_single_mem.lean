-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.single_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:36.357815+00:00
-- url     : https://prove2.me/submissions/1967d2cf-bc1d-4af6-baf7-0c060b1b5fc5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_mem_stdLat

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
omit [Fintype n]
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution (i : n) {w : ℂ} (hw : w ∈ L.lattice) : (Pi.single i w : n → ℂ) ∈ stdLat L n :=
  (mem_stdLat L).2 fun j => by
    by_cases h : j = i
    · subst h; simpa using hw
    · simp [Pi.single_eq_of_ne h]
end GlobalTheory.Mem.Col2.ThetaVec
