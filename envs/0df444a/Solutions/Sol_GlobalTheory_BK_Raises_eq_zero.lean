-- Prove2me | solution 1 for GlobalTheory.BK.Raises.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:34:46.517548+00:00
-- url     : https://prove2.me/submissions/bfb9b876-1ef3-4b2d-b5a8-e860206d6615

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Theorems.Thm_GlobalTheory_BK_eq_zero_of_mem_uPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.BK.PhiMod
namespace _root_.GlobalTheory.BK.Raises
theorem _root_.solution {T : Module.End K (Vec K a ι)} (hT : Raises T) {α : Type}
    {σ : α → α} (hσ : Function.Surjective σ) {δ : α → Vec K a ι} (h1 : ∀ x, δ x ∈ uPow K a ι 1)
    (h : ∀ x, δ (σ x) = T (δ x)) (x : α) : δ x = 0 := by
  refine eq_zero_of_mem_uPow fun m => ?_
  induction m generalizing x with
  | zero => exact h1 x
  | succ m ih =>
    obtain ⟨y, rfl⟩ := hσ x
    rw [h]
    exact hT m _ (ih y)
end _root_.GlobalTheory.BK.Raises
end GlobalTheory.BK.PhiMod
