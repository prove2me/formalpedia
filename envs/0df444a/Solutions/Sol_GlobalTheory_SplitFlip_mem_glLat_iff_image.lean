-- Prove2me | solution 1 for GlobalTheory.SplitFlip.mem_glLat_iff_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:13:17.437919+00:00
-- url     : https://prove2.me/submissions/6b63ca67-c6a6-40c5-a5c7-6a552f354a02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type*}
variable [Fintype D]
variable [DecidableEq D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution {Λ : Submodule 𝒪[k] (D → k)} {h : GL D k} :
    h ∈ glLat Λ ↔ (fun x => x ᵥ* h.val) '' Λ = Λ := by
  constructor
  · intro hh
    ext y
    exact ⟨by rintro ⟨x, hx, rfl⟩; exact (hh x).2 hx, fun hy => ⟨y ᵥ* (h⁻¹).val, ((glLat Λ).inv_mem hh y).2 hy, by
      simp only [vecMul_vecMul, Units.inv_mul, vecMul_one]⟩⟩
  · intro hh x
    refine ⟨fun hx => ?_, fun hx => hh.le ⟨x, hx, rfl⟩⟩
    obtain ⟨y, hy, hxy⟩ := hh.ge hx
    have := congrArg (· ᵥ* (h⁻¹).val) hxy
    simp only [vecMul_vecMul, Units.mul_inv, vecMul_one] at this
    exact this ▸ hy
end GlobalTheory.SplitFlip
