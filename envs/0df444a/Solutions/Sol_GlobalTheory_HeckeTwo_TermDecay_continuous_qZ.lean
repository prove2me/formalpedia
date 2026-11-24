-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermDecay.continuous_qZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:23:12.369295+00:00
-- url     : https://prove2.me/submissions/83fd8a80-85d0-43c0-9ddc-cc409c8a05a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableHeckeTermDecayIntegrand
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
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
namespace GlobalTheory.HeckeTwo.TermDecay
theorem _root_.solution (σ : ℂ) (a : ℤ) (b m : ℕ) {y : ℝ} (hy : y ≠ 0) : Continuous (qZ σ a b m y) := by
  unfold qZ
  have h1 : Continuous fun t : ℝ => ((t : ℂ) + (y : ℂ) * I) ^ (-a) :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + (y : ℂ) * I).zpow₀ (-a)
      fun t => Or.inl (GlobalTheory.HeckeTwo.TermSmooth.u_ne hy t)
  have h2 : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) :=
    (by fun_prop : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))).cpow continuous_const
      fun t => Complex.ofReal_mem_slitPlane.2 (by positivity)
  exact (h1.mul h2).mul continuous_const
end GlobalTheory.HeckeTwo.TermDecay
