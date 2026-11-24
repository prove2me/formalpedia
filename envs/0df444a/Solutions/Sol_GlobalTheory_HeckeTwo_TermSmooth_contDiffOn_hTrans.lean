-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermSmooth.contDiffOn_hTrans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:58.792802+00:00
-- url     : https://prove2.me/submissions/ee32b9c1-aa11-4308-bd18-be72d046c234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_contDiffOn_intT
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_hTrans_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermSmooth
namespace GlobalTheory.HeckeTwo.TermSmooth
theorem _root_.solution (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) :
    ContDiffOn ℝ ∞ (hTrans σ ν) {y | y ≠ 0} := by
  refine (contDiffOn_infty.2 fun n => contDiffOn_intT σ hσ ν n 2 0 0 (by norm_num)).congr fun y hy => ?_
  exact hTrans_eq σ ν hy
end GlobalTheory.HeckeTwo.TermSmooth
