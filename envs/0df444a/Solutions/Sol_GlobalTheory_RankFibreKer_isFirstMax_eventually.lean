-- Prove2me | solution 1 for GlobalTheory.RankFibreKer.isFirstMax_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:42.843574+00:00
-- url     : https://prove2.me/submissions/764fafd6-2d14-45a2-ba70-0ce58a3e6605

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FirstMaximalMinorLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open GlobalTheory GlobalTheory.RankFibreKer
namespace GlobalTheory.RankFibreKer
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d) :
    IsFirstMax Y J → ∀ᶠ Y' in nhds Y, IsFirstMax Y' J := by
  rintro ⟨h0, hle⟩
  have hm : valuation k (minor Y J) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hc : ∀ J' : Fin a ↪ Fin d, Continuous fun Y' : Matrix (Fin a) (Fin d) k => minor Y' J' := fun J' =>
    (continuous_id.matrix_submatrix id J').matrix_det
  have key : ∀ J' : Fin a ↪ Fin d, ∀ᶠ Y' in nhds Y,
      valuation k (minor Y' J') = valuation k (minor Y J') ∨
        (minor Y J' = 0 ∧ valuation k (minor Y' J') < valuation k (minor Y J)) := by
    intro J'
    by_cases hz : minor Y J' = 0
    · have hn : {x : k | valuation k x < ((Units.mk0 _ hm : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)}
          ∈ nhds (0 : k) := (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hm, subset_rfl⟩
      have hca := (hc J').continuousAt (x := Y)
      rw [ContinuousAt, hz] at hca
      filter_upwards [hca hn] with Y' hY'
      exact Or.inr ⟨hz, hY'⟩
    · have hne : valuation k (minor Y J') ≠ 0 := (Valuation.ne_zero_iff _).2 hz
      filter_upwards [(hc J').continuousAt (x := Y) ((valuation k).locally_const hne)] with Y' hY'
      exact Or.inl hY'
  have hall := Filter.eventually_all.2 key
  filter_upwards [hall] with Y' hY'
  have hJ : valuation k (minor Y' J) = valuation k (minor Y J) := by
    rcases hY' J with h | ⟨h, -⟩
    · exact h
    · exact absurd h h0
  refine ⟨(Valuation.ne_zero_iff _).1 (hJ ▸ hm), fun J' => ?_⟩
  rw [hJ]
  rcases hY' J' with h | ⟨-, h⟩
  · rw [h]; exact hle J'
  · exact ⟨h.le, fun _ => h⟩
end GlobalTheory.RankFibreKer
