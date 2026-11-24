-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.law_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:41:31.862219+00:00
-- url     : https://prove2.me/submissions/c04f2a98-13c8-4d7e-b314-b9f09e321131

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_periodLatticeSesquilinearForm_apply
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_sigmaSign_sq

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
theorem _root_.solution (G : ℂ → ℂ) (w z : ℂ) :
    sigmaSign L w * opU (form1 L) w G z = G z ↔
      G (z + w) = sigmaSign L w * cexp (π * latticeForm L z w + π * latticeForm L w w / 2) * G z := by
  have he : cexp (-(π : ℂ) * form1 L z w - π * form1 L w w / 2) *
      cexp (π * latticeForm L z w + π * latticeForm L w w / 2) = 1 := by
    rw [← Complex.exp_add, periodLatticeSesquilinearForm_apply, periodLatticeSesquilinearForm_apply, ← Complex.exp_zero]; congr 1; ring
  have hs := sigmaSign_sq L w
  rw [opU]
  constructor
  · intro h
    rw [← h]
    linear_combination (-G (z + w)) * he - (G (z + w) * cexp (-(π : ℂ) * form1 L z w - π * form1 L w w / 2) *
      cexp (π * latticeForm L z w + π * latticeForm L w w / 2)) * hs
  · intro h
    rw [h]
    linear_combination (G z) * he + (G z * cexp (-(π : ℂ) * form1 L z w - π * form1 L w w / 2) *
      cexp (π * latticeForm L z w + π * latticeForm L w w / 2)) * hs
end GlobalTheory.Mem.Col2.ThetaVec
