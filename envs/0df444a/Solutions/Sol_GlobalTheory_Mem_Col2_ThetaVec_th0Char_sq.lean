-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.th0Char_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:54:27.232606+00:00
-- url     : https://prove2.me/submissions/9985102e-300b-4c78-8f97-9150038cddf7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_th0Char_eq
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_sigmaSign_sq
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_exp_int_sign
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
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution {ω₀ ω : ℂ} (h0 : ω₀ ∈ L.lattice) (h : ω ∈ L.lattice) :
    F.thetaZeroCharacter L ω₀ ω * F.thetaZeroCharacter L ω₀ ω = 1 := by
  obtain ⟨k, hk⟩ := exists_int_im_latticeForm L h h0
  have : altE (form1 L) ω ω₀ = k := hk
  rw [th0Char_eq, this, mul_mul_mul_comm, sigmaSign_sq]
  rcases exp_int_sign k with h | h <;> rw [h] <;> norm_num
end GlobalTheory.Mem.Col2.ThetaVec
