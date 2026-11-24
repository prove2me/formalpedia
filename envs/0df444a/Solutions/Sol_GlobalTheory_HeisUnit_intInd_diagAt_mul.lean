-- Prove2me | solution 1 for GlobalTheory.HeisUnit.intInd_diagAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:43:43.11629+00:00
-- url     : https://prove2.me/submissions/d3d7f41e-8a42-4874-bdd9-99c312ff3856

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCharacterUnitEqOneHeisenberg
import Theorems.Thm_GlobalTheory_HeisUnit_mul_mem_integer_iff_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_HeisUnit_diagAt_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.HeisUnit
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.HeisUnit
theorem _root_.solution {n d : ℕ} {u : kˣ} (hu : valuation k (u : k) = 1) (i0 : Fin n)
    (Y : Matrix (Fin n) (Fin d) k) : intInd k n d ((diagAt u i0).valᵀ * Y) = intInd k n d Y := by
  have e : ∀ i j, ((diagAt u i0).valᵀ * Y) i j ∈ 𝒪[k] ↔ Y i j ∈ 𝒪[k] := by
    intro i j
    rw [diagAt_val, diagonal_transpose, diagonal_mul]
    by_cases hi : i = i0
    · rw [if_pos hi]; exact mul_mem_integer_iff_of_valuation_eq_one hu _
    · rw [if_neg hi, one_mul]
  have hs : ((diagAt u i0).valᵀ * Y) ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} ↔
      Y ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := by
    simp only [Set.mem_setOf_eq]
    exact forall_congr' fun i => forall_congr' fun j => e i j
  unfold intInd
  by_cases h : Y ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hs.mpr h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hs.mp h)]
end GlobalTheory.HeisUnit
