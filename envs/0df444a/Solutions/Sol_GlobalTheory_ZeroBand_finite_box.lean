-- Prove2me | solution 1 for GlobalTheory.ZeroBand.finite_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:43.974921+00:00
-- url     : https://prove2.me/submissions/a862a29a-5992-4f7a-89a8-20ba3c66ab65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinsumMemLeOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ZeroBand
namespace GlobalTheory.ZeroBand
theorem _root_.solution (f : ℂ → ℂ)
    (hW : ∀ t : ℝ, {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}.Finite) (T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ f ρ = 0}.Finite := by
  refine Set.Finite.subset
    ((Finset.Icc ⌊-T⌋ ⌊T⌋).finite_toSet.biUnion fun k _ => hW (k : ℝ)) ?_
  rintro ρ ⟨h0, h1, h2, h3⟩
  rw [abs_lt] at h2
  refine Set.mem_iUnion₂.2 ⟨⌊ρ.im⌋, ?_, h0, h1, ?_, h3⟩
  · rw [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨Int.floor_mono h2.1.le, Int.floor_mono h2.2.le⟩
  · rw [abs_le]
    constructor <;> linarith [Int.floor_le ρ.im, Int.lt_floor_add_one ρ.im]
end GlobalTheory.ZeroBand
