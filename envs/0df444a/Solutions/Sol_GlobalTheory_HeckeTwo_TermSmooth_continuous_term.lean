-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermSmooth.continuous_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:41.455882+00:00
-- url     : https://prove2.me/submissions/b4320c62-92bb-466c-81ba-fd7eb7da4312

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_u_ne

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
theorem _root_.solution (σ : ℂ) (ν : ℝ) (a b m : ℕ) {y : ℝ} (hy : y ≠ 0) : Continuous (term σ ν a b m y) := by
  unfold term
  have h1 : Continuous fun t : ℝ => ((t : ℂ) + (y : ℂ) * I)⁻¹ ^ a :=
    ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) + (y : ℂ) * I).inv₀ (u_ne hy)).pow a
  have h2 : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) :=
    (by fun_prop : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))).cpow continuous_const
      fun t => Complex.ofReal_mem_slitPlane.2 (by positivity)
  exact ((h1.mul h2).mul continuous_const).mul (by fun_prop)
end GlobalTheory.HeckeTwo.TermSmooth
