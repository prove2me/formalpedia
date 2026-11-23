-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.GoodAdd.wirt_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:23.101251+00:00
-- url     : https://prove2.me/submissions/50634b85-b9e2-4021-9a3d-8022638906d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd

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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.GoodAdd
variable {Φ : Type} [Fintype Φ]
namespace GlobalTheory.HeckeTwo.GoodAdd
theorem _root_.solution {U : Set (Φ → ℂ)} (hU : IsOpen U) {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U)
    (τ : Φ) (b : Bool) : Set.EqOn (wirt τ b f) (wirt τ b g) U := by
  intro z hz
  have he : f =ᶠ[nhds z] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h
  simp only [wirt, he.fderiv_eq]
end GlobalTheory.HeckeTwo.GoodAdd
