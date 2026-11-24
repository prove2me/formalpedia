-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.SumGood.goodFam_wirtWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:14:19.522902+00:00
-- url     : https://prove2.me/submissions/c3f6a142-8a6e-4659-9a3d-7a4ef8afb43a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum
import Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_norm_iteratedFDeriv_wirtWord
import Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_wirtWord_contDiffOn


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
variable {Φ : Type} [Fintype Φ] {ι : Type}
namespace GlobalTheory.HeckeTwo.SumGood
theorem _root_.solution {U : Set (Φ → ℂ)} (hU : IsOpen U) {f : ι → (Φ → ℂ) → ℂ}
    (hf : GoodFam U f) (w : List (Φ × Bool)) : GoodFam U (fun i => wirtWord w (f i)) := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_wirtWord hU w
  refine ⟨fun i => GoodAdd.wirtWord_contDiffOn hU w (hf.1 i), fun L hL hLU k => ?_⟩
  obtain ⟨u, hu, hb⟩ := hf.2 L hL hLU (k + w.length)
  refine ⟨fun i => C * u i, hu.mul_left C, fun i z hz => ?_⟩
  exact (hC (f i) (hf.1 i) k z (hLU hz)).trans (mul_le_mul_of_nonneg_left (hb i z hz) hC0)
end GlobalTheory.HeckeTwo.SumGood
