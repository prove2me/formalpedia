-- Prove2me | solution 1 for GlobalTheory.SplitFlip.FourierDepth.mem_matLat_blockLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:15.707396+00:00
-- url     : https://prove2.me/submissions/8fad3b9b-8220-4785-812f-3d4fe3346009

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
import Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_mem_matLat_diagLat

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
    X ∈ matLat A (blockLat ϖ e P) ↔
      (∀ i, ∀ j ∈ P, ((ϖ ^ e : kˣ) : k) * X i j ∈ 𝒪[k]) ∧ ∀ i, ∀ j ∉ P, X i j ∈ 𝒪[k] := by
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  have h1 : ∀ x : k, ((ϖ ^ e : kˣ) : k) * x ∈ 𝒪[k] ↔
      valuation k x ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k) := fun x => by
    rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, mul_comm, ← le_mul_inv_iff₀ h0, one_mul]
  rw [blockLat, mem_matLat_diagLat]
  simp only [h1]
  constructor
  · intro h
    exact ⟨fun i j hj => by simpa only [blockUnits, if_pos hj] using h i j,
      fun i j hj => by simpa [blockUnits, hj, Valuation.mem_integer_iff] using h i j⟩
  · rintro ⟨h, h'⟩ i j
    by_cases hj : j ∈ P
    · simpa only [blockUnits, if_pos hj] using h i j hj
    · simpa [blockUnits, hj, Valuation.mem_integer_iff] using h' i j hj
end GlobalTheory.SplitFlip.FourierDepth
