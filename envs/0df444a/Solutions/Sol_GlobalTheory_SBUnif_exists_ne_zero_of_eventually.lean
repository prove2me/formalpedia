-- Prove2me | solution 1 for GlobalTheory.SBUnif.exists_ne_zero_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:13.235625+00:00
-- url     : https://prove2.me/submissions/893abbaf-fa66-4a1c-8e55-32bdb701ff50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.SBUnif
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SBUnif
theorem _root_.solution {P : k → Prop} (h : ∀ᶠ s in nhds (0 : k), P s) :
    ∃ c : k, c ≠ 0 ∧ P c := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 h
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  obtain ⟨w, hw0, hw1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [map_zero] at ha
    exact γ.ne_zero ha.symm
  refine ⟨a * w, mul_ne_zero ha0 hw0, hγ ?_⟩
  show valuation k (a * w) < γ
  rw [map_mul, ha]
  calc (γ : ValueGroupWithZero k) * valuation k w < γ * 1 :=
        mul_lt_mul_of_pos_left hw1 (zero_lt_iff.mpr γ.ne_zero)
    _ = γ := mul_one _
end GlobalTheory.SBUnif
