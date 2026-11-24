-- Prove2me | solution 1 for GlobalTheory.SplitFlip.FourierDepth.isNatDatum_invFourierSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:54:54.128115+00:00
-- url     : https://prove2.me/submissions/3add1247-1853-4d47-a632-7510039aa804

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_setCols_add
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_pairCols_add
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_mem_matLat_smul_stdLat
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_mem_matLat_blockLat
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_mem_matLat_smul_blockLat
import Theorems.Thm_GlobalTheory_SplitFlip_invFourierSum_apply
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
    (P : Finset D) {Ψ : Matrix A D k → ℂ} (hΨ : HasDepth ϖ e (blockLat ϖ e P) Ψ) :
    IsNatDatum ϖ e (invFourierSum ψ ϖ e P Ψ) := by
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy => (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have hc : ((ϖ ^ e : kˣ) : k) ∈ 𝒪[k] := by
    rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem e
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  refine ⟨fun Y hY => ?_, fun Y Z hZ => ?_⟩
  · rw [invFourierSum_apply]
    split_ifs with h
    · refine Finset.sum_eq_zero fun S _ => ?_
      rw [hΨ.1, zero_mul]
      intro H
      refine hY (mem_matLat_stdLat.2 fun i j => ?_)
      by_cases hj : j ∈ P
      · exact h i j hj
      · simpa only [setCols, of_apply, dif_neg hj] using (mem_matLat_blockLat.1 H).2 i j hj
    · rfl
  · have h1 := mem_matLat_smul_stdLat.1 hZ
    rw [invFourierSum_apply, invFourierSum_apply]
    refine if_congr (forall_congr' fun i => forall₂_congr fun j _ => ?_) ?_ rfl
    · rw [Matrix.add_apply, add_mem_cancel_right (show Z i j ∈ 𝒪[k] from (Valuation.mem_integer_iff _ _).2
        ((h1 i j).trans ((Valuation.mem_integer_iff _ _).1 hc)))]
    · refine Finset.sum_congr rfl fun S _ => ?_
      rw [setCols_add, pairCols_add, hΨ.2, neg_add, AddChar.map_add_eq_mul, triv (-pairCols P Z _), mul_one]
      · refine neg_mem (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_)
        have h2 : (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j ∈ 𝒪[k] := by
          rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]
          exact h1 i j
        convert mul_mem (liftRes_mem S i j) h2 using 1
        simp only [Matrix.smul_apply, Units.smul_def, smul_eq_mul]
        ring
      · refine mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
        · simp [setCols, hj]
        · simpa only [setCols, of_apply, dif_neg hj] using h1 i j
end GlobalTheory.SplitFlip.FourierDepth
