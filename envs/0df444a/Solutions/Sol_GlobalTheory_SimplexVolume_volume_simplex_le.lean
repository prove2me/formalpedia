-- Prove2me | solution 1 for GlobalTheory.SimplexVolume.volume_simplex_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:54:35.373434+00:00
-- url     : https://prove2.me/submissions/74aa0de6-edd8-460c-9cbe-228882c9469b

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_VolumePosSimplexLe
import Theorems.Thm_GlobalTheory_SimplexVolume_volume_pos_simplex_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField Finset
open GlobalTheory GlobalTheory.SimplexVolume
namespace GlobalTheory.SimplexVolume
theorem _root_.solution (ι : Type) [Fintype ι] (a : ι → ℝ) (L : ℝ) (hL : 0 ≤ L) :
    volume {t : ι → ℝ | (∀ i, a i ≤ t i) ∧ ∑ i, (t i - a i) ≤ L} ≤
      ENNReal.ofReal (L ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine le_trans (measure_mono (Set.subset_univ _)) ?_
    simp [volume_pi]
  · have hsub : {t : ι → ℝ | (∀ i, a i ≤ t i) ∧ ∑ i, (t i - a i) ≤ L} ⊆
        ((fun t => t - a) ⁻¹' {x : ι → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i ≤ L}) ∪
          ⋃ i, {t : ι → ℝ | t i = a i} := by
      intro t ht
      by_cases h : ∃ i, t i = a i
      · exact Or.inr (Set.mem_iUnion.2 h)
      · push Not at h
        refine Or.inl ⟨fun i => ?_, ht.2⟩
        exact sub_pos.2 (lt_of_le_of_ne (ht.1 i) (h i).symm)
    have hnull : volume (⋃ i, {t : ι → ℝ | t i = a i}) = 0 :=
      measure_iUnion_null fun i => Measure.pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) i (a i)
    refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
    rw [hnull, add_zero]
    simp only [sub_eq_add_neg]
    rw [measure_preimage_add_right]
    exact volume_pos_simplex_le ι L hL
end GlobalTheory.SimplexVolume
