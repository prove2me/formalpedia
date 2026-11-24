-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.chi_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:35:31.883004+00:00
-- url     : https://prove2.me/submissions/3023a4e0-2d60-411e-a9ad-7781bfa203c1

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
theorem _root_.solution (ω ω₀ : ℂ) :
    cexp (π * I * (altE (form1 L) ω ω₀ : ℂ)) * chi (form1 L) ω (ω₀ / 2) = 1 := by
  have : altE (form1 L) ω ω₀ = 2 * altE (form1 L) ω (ω₀ / 2) := by
    conv_lhs => rw [← add_halves ω₀]
    simp only [altE, map_add, add_im]; ring
  rw [chi, ← Complex.exp_add, this, ← Complex.exp_zero]
  congr 1; push_cast; ring
end GlobalTheory.Mem.Col2.ThetaVec
