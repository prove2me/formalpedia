-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.quasiPeriodConst_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:41:32.251852+00:00
-- url     : https://prove2.me/submissions/4beeb664-c0d0-4a30-91d5-7003624b677f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_wEta_eq

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
theorem _root_.solution : F.s2 L = sTwo L := by
  have h : L.ω₁ * conj L.ω₂ - L.ω₂ * conj L.ω₁ ≠ 0 := by
    intro h0
    have h1 := latticeArea_pos L
    rw [latticeArea_eq] at h1
    have h2 := congrArg Complex.im h0
    simp at h1 h2
    apply h1
    linarith
  rw [F.s2, wEta_eq, quasiPeriod_eq, quasiPeriod_eq, div_eq_iff h]
  ring
end GlobalTheory.Mem.Col2.ThetaVec
