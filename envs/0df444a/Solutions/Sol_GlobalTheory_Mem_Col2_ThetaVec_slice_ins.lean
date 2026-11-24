-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.slice_ins
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:34:43.896477+00:00
-- url     : https://prove2.me/submissions/be3ea9c6-9dd5-4668-a243-d40a29be25c0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm

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
variable {n : Type} [Fintype n]
omit [Fintype n]
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution (z : Fin 4 × n → ℂ) (x : n → ℂ) (a : Fin 4) :
    slice a (ins z x) = if a = 0 then x else slice a z := by
  funext i
  by_cases h : a = 0 <;> simp [slice, ins, h]
end GlobalTheory.Mem.Col2.ThetaVec
