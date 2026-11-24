-- Prove2me | solution 1 for GlobalTheory.SplitFlip.FourierDepth.hasDepth_fourierSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:54:53.410887+00:00
-- url     : https://prove2.me/submissions/6da3ae88-e7e8-4fe9-8b79-5c4a75963bc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_setCols_add
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_pairCols_add
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_mem_matLat_smul_stdLat
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_mem_matLat_blockLat
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_mem_matLat_smul_blockLat
import Theorems.Thm_GlobalTheory_SplitFlip_fourierSum_apply
import Theorems.Thm_GlobalTheory_SplitFlip_liftRes_mem
import Theorems.Thm_GlobalTheory_SplitFlip_mem_matLat_stdLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.FourierDepth
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type*} [DecidableEq D]
variable [Fintype A] [DecidableEq A]
namespace GlobalTheory.SplitFlip.FourierDepth
theorem _root_.solution {ψ : AddChar k Circle} {ϖ : kˣ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) {Φ : Matrix A D k → ℂ} (hΦ : IsNatDatum ϖ e Φ) :
    HasDepth ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ) := by
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy => (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have hc : ((ϖ ^ e : kˣ) : k) ∈ 𝒪[k] := by
    rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem e
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · rw [fourierSum_apply]
    split_ifs with h
    · rw [Finset.sum_eq_zero, mul_zero]
      intro T _
      rw [hΦ.1, zero_mul]
      intro H
      refine hY (mem_matLat_blockLat.2 ⟨h, fun i j hj => ?_⟩)
      simpa [setCols, hj] using mem_matLat_stdLat.1 H i j
    · rfl
  · obtain ⟨h1, h2⟩ := mem_matLat_smul_blockLat.1 hZ
    rw [fourierSum_apply, fourierSum_apply]
    refine if_congr (forall_congr' fun i => forall₂_congr fun j hj => ?_) ?_ rfl
    · rw [Matrix.add_apply, mul_add, add_mem_cancel_right (mul_mem hc (h1 i j hj))]
    · congr 1
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [setCols_add, pairCols_add, hΦ.2, AddChar.map_add_eq_mul, triv (pairCols P Z _), mul_one]
      · exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => mul_mem (liftRes_mem T i j) (h1 i j j.2)
      · refine mem_matLat_smul_stdLat.2 fun i j => ?_
        by_cases hj : j ∈ P
        · simp [setCols, hj]
        · simpa only [setCols, of_apply, dif_neg hj] using h2 i j hj
end GlobalTheory.SplitFlip.FourierDepth
