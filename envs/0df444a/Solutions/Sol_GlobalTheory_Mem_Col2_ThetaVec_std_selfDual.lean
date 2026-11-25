-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.std_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:54:25.724804+00:00
-- url     : https://prove2.me/submissions/36ae8243-dc88-4d6f-a099-2d22dae05941

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_mem_of_int
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_altE_stdH
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_stdH_single
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_mem_stdLat
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_single_mem
import Theorems.Thm_GlobalTheory_exists_int_im_latticeForm


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
theorem _root_.solution : IsSelfDual (stdH L n) (stdLat L n) := by
  ext x
  constructor
  · intro h
    refine (mem_stdLat L).2 fun i => mem_of_int L fun y hy => ?_
    have := h _ (single_mem L i hy)
    rwa [altE, stdH_single] at this
  · intro h y hy
    choose k hk using fun i => exists_int_im_latticeForm L ((mem_stdLat L).1 h i) ((mem_stdLat L).1 hy i)
    refine ⟨∑ i, k i, ?_⟩
    rw [altE_stdH]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hk i
end GlobalTheory.Mem.Col2.ThetaVec
