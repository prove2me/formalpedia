-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.SumGood.wirtWord_tsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:46.678276+00:00
-- url     : https://prove2.me/submissions/dd61fb17-f08c-46de-b8b0-1f97a6a59f49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum
import Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_hasFDerivAt_tsum
import Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_wirt_eq_clm
import Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_goodFam_wirtWord
import Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_wirt_congr
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_wirtWord_cons


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
    (hf : GoodFam U f) (w : List (Φ × Bool)) :
    Set.EqOn (wirtWord w (fun y => ∑' i, f i y)) (fun y => ∑' i, wirtWord w (f i) y) U := by
  induction w with
  | nil => intro z _; rfl
  | cons a w ih =>
    intro z hz
    obtain ⟨Λ, hΛ⟩ := wirt_eq_clm a.1 a.2
    have hg := goodFam_wirtWord hU hf w
    have hsum : Summable (fun i => fderiv ℝ (wirtWord w (f i)) z) := by
      obtain ⟨u, hu, hb⟩ := hg.2 {z} isCompact_singleton (Set.singleton_subset_iff.2 hz) 1
      exact Summable.of_norm_bounded hu fun i => by
        simpa [norm_iteratedFDeriv_one] using hb i z (Set.mem_singleton z)
    rw [wirtWord_cons, GoodAdd.wirt_congr hU ih a.1 a.2 hz, hΛ, (hasFDerivAt_tsum hU hg hz).fderiv,
      Λ.map_tsum hsum]
    simp only [wirtWord_cons, hΛ]
end GlobalTheory.HeckeTwo.SumGood
