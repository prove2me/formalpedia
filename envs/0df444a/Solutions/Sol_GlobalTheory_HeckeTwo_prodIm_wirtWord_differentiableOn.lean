-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.prodIm_wirtWord_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:58:21.139601+00:00
-- url     : https://prove2.me/submissions/944fbb9c-2967-4a54-9029-add823be46b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdImIteratedWirtingerDerivWordDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwo_ProdImWirt_wirtWord_mono
import Theorems.Thm_GlobalTheory_HeckeTwo_ProdImWirt_mono_differentiable
import Theorems.Thm_GlobalTheory_HeckeTwo_ProdImWirt_wirtWord_congr
import Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_upperHalf_isOpen


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
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (w : List (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F × Bool)) (z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F → DifferentiableOn ℂ (fun σ : ℂ => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord w (fun z : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)) z) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  intro F _ _ w z hz
  have hU := GoodAdd.upperHalf_isOpen F
  obtain ⟨c', a', hc', ha', h⟩ := ProdImWirt.wirtWord_mono (upperHalf F) hU (fun z hz => hz) w (fun _ => 1)
    (fun σ _ => -1 - 2 * σ) (differentiable_const _)
    (fun _ => (differentiable_const _).sub ((differentiable_const _).mul differentiable_id))
  have hw : ∀ σ, Set.EqOn (wirtWord w (fun z : Emb F → ℂ => ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ)))
      (wirtWord w (ProdImWirt.mono (fun _ => 1) (fun σ _ => -1 - 2 * σ) σ)) (upperHalf F) := by
    intro σ
    have h0 : Set.EqOn (fun z : Emb F → ℂ => ∏ τ : Emb F, (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))
        (ProdImWirt.mono (fun _ => 1) (fun σ _ => -1 - 2 * σ) σ) (upperHalf F) := by
      intro y hy
      simp only [ProdImWirt.mono, one_mul, Complex.exp_sum]
      refine Finset.prod_congr rfl fun τ _ => ?_
      have hpos : 0 < (y τ).im := hy τ
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, mul_comm]
    exact ProdImWirt.wirtWord_congr hU h0 w
  refine ((ProdImWirt.mono_differentiable hc' ha' z).differentiableOn).congr fun σ _ => ?_
  rw [hw σ hz, h σ hz]
end GlobalTheory.HeckeTwo
