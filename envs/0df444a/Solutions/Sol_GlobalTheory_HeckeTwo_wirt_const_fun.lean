-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.wirt_const_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:23:07.555151+00:00
-- url     : https://prove2.me/submissions/a9ec7526-a483-424a-9c18-d281c111e876

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyOfSigmaOnly

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
open GlobalTheory GlobalTheory.HeckeTwo
namespace GlobalTheory.HeckeTwo
theorem _root_.solution {Φ : Type} [Fintype Φ] (τ : Φ) (bar : Bool) (d : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirt τ bar (fun _ : Φ → ℂ => d) = fun _ => 0 := by
  funext z
  simp [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirt]
end GlobalTheory.HeckeTwo
