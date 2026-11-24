-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.SumGood.goodFam_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:24:56.558958+00:00
-- url     : https://prove2.me/submissions/e4754502-3633-4ae0-8fae-6d4a66b63624

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum

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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.SumGood
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] {ι : Type}
namespace GlobalTheory.HeckeTwo.SumGood
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set V} (hU : IsOpen U) {f : ι → V → E} (hf : GoodFam U f) :
    GoodFam U (fun i => fderiv ℝ (f i)) := by
  refine ⟨fun i => (hf.1 i).fderiv_of_isOpen hU (by simp), fun L hL hLU k => ?_⟩
  obtain ⟨u, hu, hb⟩ := hf.2 L hL hLU (k + 1)
  exact ⟨u, hu, fun i z hz => by rw [norm_iteratedFDeriv_fderiv]; exact hb i z hz⟩
end GlobalTheory.HeckeTwo.SumGood
