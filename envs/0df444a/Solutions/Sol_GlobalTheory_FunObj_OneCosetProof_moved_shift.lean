-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.moved_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:29:17.998987+00:00
-- url     : https://prove2.me/submissions/9222586c-31c2-4748-baba-8e6d109f1d87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_frame_mul
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_stepPt_shift
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_moveArgs_theta
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_moveArgs_add
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_downMap_eq
import Theorems.Thm_GlobalTheory_FunObj_fill_theta
import Theorems.Thm_GlobalTheory_FunObj_moved_false
import Theorems.Thm_GlobalTheory_SplitFlip_mem_matLat
import Theorems.Thm_GlobalTheory_SplitFlip_mem_smul_lat
import Theorems.Thm_GlobalTheory_SplitFlip_mem_stdLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
namespace GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
private theorem inv_smul_mem_integers_of_valuation_le (u : kˣ) (q : k) (hq : valuation k q ≤ valuation k (u : k)) :
    u⁻¹ • q ∈ 𝒪[k] := by
  rw [Units.smul_def, smul_eq_mul, Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  have hu : valuation k (u : k) ≠ 0 := by simp
  calc (valuation k (u : k))⁻¹ * valuation k q ≤ (valuation k (u : k))⁻¹ * valuation k (u : k) :=
        by first | exact mul_le_mul_left hq _ | exact mul_le_mul_of_nonneg_left hq (zero_le _) | gcongr
    _ = 1 := inv_mul_cancel₀ hu
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k}
end GlobalTheory.FunObj.OneCosetProof
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip
end GlobalTheory.FunObj
end
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution (hs : 1 ≤ G.s) (hT : G.IsTensor ϖ e (oppositePath G.m) T) (g : G.VertexGroup) (x : ColArgs G)
    (y : RowArgs G) (v : Vars G) (Y : Shift G)
    (hY : ∀ j r s, ¬ Free ((G.m - 2 - j.val) / 2 + 1) (r, s) → Y j r s = 0)
    (hL : ∀ (j : Fin (G.m - 1)) r s, valuation k ((((frameGL (tgt_eq hs j) (g (G.m, j + 1)))⁻¹).val * Y j *
      (frameGL (src_eq hs j) (g (G.m, j))).val) r s) ≤ valuation k ((ϖ ^ e : kˣ) : k)) :
    moved G false g T (fill hs x y (v + Y.vars)) = moved G false g T (fill hs x y v) := by
  have hfill : fill hs x y (v + Y.vars) = fill hs x y v + (fill hs x y (v + Y.vars) - fill hs x y v) := by
    abel
  rw [moved_false, moved_false, hfill, moveArgs_add, hT.2.2]
  intro b
  cases b with
  | ex i j' =>
    have h0 : (fill hs x y (v + Y.vars) - fill hs x y v) (.ex i j') = 0 := by
      simp [fill]
    simp only [Grid.moveArgs, h0, Matrix.mul_zero, Matrix.zero_mul]
    exact zero_mem _
  | theta i j' =>
    by_cases hi : i = G.m
    · subst hi
      by_cases hj : j' < G.m - 1
      · obtain ⟨jj, rfl⟩ : ∃ jj : Fin (G.m - 1), (jj : ℕ) = j' := ⟨⟨j', hj⟩, rfl⟩
        have hD : (fill hs x y (v + Y.vars) - fill hs x y v) (.theta G.m jj) =
            ((Y jj).reindex (frame (tgt_eq hs jj)) (frame (src_eq hs jj)))ᵀ := by
          rw [Pi.sub_apply, fill_theta, fill_theta, downMap_eq hs, downMap_eq hs, stepPt_shift x v Y hY jj]
          ext a b
          simp [Matrix.reindex_apply, Matrix.submatrix_apply]
        rw [moveArgs_theta, hD, Matrix.transpose_transpose, frame_mul, mem_matLat]
        intro a
        rw [mem_smul_lat, mem_stdLat]
        intro b
        have hv := hL jj ((frame (tgt_eq hs jj)).symm b) ((frame (src_eq hs jj)).symm a)
        exact inv_smul_mem_integers_of_valuation_le _ _ hv
      · have h0 : (fill hs x y (v + Y.vars) - fill hs x y v) (.theta G.m j') = 0 := by
          rw [Pi.sub_apply, fill_theta, fill_theta]
          simp only [downMap, dif_neg hj, sub_self]
        simp only [Grid.moveArgs, h0, Matrix.mul_zero, Matrix.zero_mul]
        exact zero_mem _
    · have h0 : (fill hs x y (v + Y.vars) - fill hs x y v) (.theta i j') = 0 := by
        simp [fill, hi]
      simp only [Grid.moveArgs, h0, Matrix.mul_zero, Matrix.zero_mul]
      exact zero_mem _
end GlobalTheory.FunObj.OneCosetProof
