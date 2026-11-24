-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.exp_int_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:44.811185+00:00
-- url     : https://prove2.me/submissions/1a0ba4c3-6399-419a-9b41-2c1b26265bc4

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
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution (k : ℤ) : cexp (π * I * ((k : ℝ) : ℂ)) = 1 ∨ cexp (π * I * ((k : ℝ) : ℂ)) = -1 := by
  rw [mul_comm, Complex.ofReal_intCast, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rcases Int.even_or_odd k with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow
end GlobalTheory.Mem.Col2.ThetaVec
