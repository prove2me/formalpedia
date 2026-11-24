-- Prove2me | solution 1 for GlobalTheory.SplitFlip.glLat_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:54:59.340462+00:00
-- url     : https://prove2.me/submissions/a82fcc32-947d-4954-a24e-8941b3d278ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_mem_stdLat

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
theorem _root_.solution : glLat (stdLat k D) = KO k D := by
  have key : ∀ h : GL D k, (∀ x ∈ stdLat k D, x ᵥ* h.val ∈ stdLat k D) ↔ ∀ i j, h.val i j ∈ 𝒪[k] := fun h => by
    constructor
    · intro hh i j
      simpa using mem_stdLat.1 (hh (Pi.single i 1) (mem_stdLat.2 fun l => by
        by_cases h : l = i
        · subst h; simp
        · simp [h])) j
    · intro hh x hx
      exact mem_stdLat.2 fun j => Subring.sum_mem _ fun i _ => mul_mem (mem_stdLat.1 hx i) (hh i j)
  ext h
  rw [mem_KO_iff, ← key, ← key]
  refine ⟨fun hh => ⟨fun x hx => (hh x).2 hx, fun x hx => ((glLat _).inv_mem hh x).2 hx⟩, fun hh x => ⟨fun hx => ?_, hh.1 x⟩⟩
  simpa only [vecMul_vecMul, Units.mul_inv, vecMul_one] using hh.2 _ hx
end GlobalTheory.SplitFlip
