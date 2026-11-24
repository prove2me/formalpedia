-- Prove2me | solution 1 for GlobalTheory.SplitFlip.FourierDepth.mem_matLat_smul_blockLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:15.860009+00:00
-- url     : https://prove2.me/submissions/59d9f9a8-c768-4690-b6b6-07928bd6bfa8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_mem_matLat_diagLat
import Theorems.Thm_GlobalTheory_SplitFlip_smul_diagLat


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
namespace GlobalTheory.SplitFlip.FourierDepth
theorem _root_.solution {ϖ : kˣ} {e : ℕ} {P : Finset D} {X : Matrix A D k} :
    X ∈ matLat A (ϖ ^ e • blockLat ϖ e P) ↔
      (∀ i, ∀ j ∈ P, X i j ∈ 𝒪[k]) ∧ ∀ i, ∀ j ∉ P, valuation k (X i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  rw [blockLat, smul_diagLat, mem_matLat_diagLat]
  constructor
  · intro h
    exact ⟨fun i j hj => by simpa [blockUnits, hj, Valuation.mem_integer_iff] using h i j,
      fun i j hj => by simpa only [blockUnits, if_neg hj, mul_one] using h i j⟩
  · rintro ⟨h, h'⟩ i j
    by_cases hj : j ∈ P
    · simpa [blockUnits, hj, Valuation.mem_integer_iff] using h i j hj
    · simpa only [blockUnits, if_neg hj, mul_one] using h' i j hj
end GlobalTheory.SplitFlip.FourierDepth
