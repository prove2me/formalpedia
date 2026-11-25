-- Prove2me | solution 1 for GlobalTheory.SimplexVolume.volume_pos_simplex_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:38.564863+00:00
-- url     : https://prove2.me/submissions/bdd7d58d-aa3d-42fb-a3ef-25f92ea3c68f

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_VolumePosSimplexLe
import Theorems.Thm_GlobalTheory_SimplexVolume_volume_l1_ball

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
theorem _root_.solution (ι : Type) [Fintype ι] [Nonempty ι] (L : ℝ) (hL : 0 ≤ L) :
    volume {x : ι → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i ≤ L} ≤
      ENNReal.ofReal (L ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  classical
  set S : Set (ι → ℝ) := {x : ι → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i ≤ L} with hS
  have hSm : MeasurableSet S := by
    rw [hS]
    measurability
  let f : (ι → Bool) → ι → ℝ → ℝ := fun e i y => if e i then y else -y
  have hf : ∀ e i, MeasurePreserving (f e i) volume volume := by
    intro e i
    by_cases h : e i
    · simp only [f, h, if_true]
      exact MeasurePreserving.id (volume : Measure ℝ)
    · simpa [f, h] using Measure.measurePreserving_neg (volume : Measure ℝ)
  let R : (ι → Bool) → (ι → ℝ) → (ι → ℝ) := fun e x i => f e i (x i)
  have hR : ∀ e, MeasurePreserving (R e) volume volume := fun e =>
    volume_preserving_pi (fun i => hf e i)
  have hdisj : Pairwise (Function.onFun Disjoint fun e => R e ⁻¹' S) := by
    intro e e' hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    apply hne
    funext i
    have h1 := hx.1 i
    have h2 := hx'.1 i
    simp only [R, f] at h1 h2
    cases he : e i <;> cases he' : e' i <;> simp [he, he'] at h1 h2 ⊢ <;> linarith
  have hsub : (⋃ e, R e ⁻¹' S) ⊆ {x : ι → ℝ | ∑ i, |x i| ≤ L} := by
    intro x hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.1 hx
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) he.2
    have h1 := he.1 i
    rw [← abs_of_pos h1]
    simp only [R, f]
    split_ifs <;> simp
  have hU : volume (⋃ e, R e ⁻¹' S) = 2 ^ Fintype.card ι * volume S := by
    rw [measure_iUnion hdisj (fun e => (hR e).measurable hSm)]
    simp only [fun e => (hR e).measure_preimage hSm.nullMeasurableSet]
    simp [tsum_fintype]
  have hle := measure_mono (μ := volume) hsub
  rw [hU, volume_l1_ball ι L hL] at hle
  exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 hle
end GlobalTheory.SimplexVolume
