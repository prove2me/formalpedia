-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_orthogonal_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:08.868806+00:00
-- url     : https://prove2.me/submissions/e691f516-92a3-4213-a1ad-af79dfa77fbe

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
import Theorems.Thm_GroundTheory_PAdicHodge_exists_orthogonal_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {k E : Type*} [NontriviallyNormedField k] [IsUltrametricDist k]
  [NormedAddCommGroup E] [NormedSpace k E] [IsUltrametricDist E]
variable [CompleteSpace k]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : LinearIndependent k v) {t : ℝ} (ht : t < 1) :
    ∃ w : ι → E, LinearIndependent k w ∧ (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
      ∀ (c : ι → k) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖ := by
  set τ := max t (1 / 2) with hτ
  have hτ0 : 0 < τ := lt_max_of_lt_right (by norm_num)
  have hτ1 : τ < 1 := max_lt ht (by norm_num)
  let e := Fintype.equivFin ι
  obtain ⟨w, hw0, hwmem, hw⟩ := exists_orthogonal_fin (Fintype.card ι) (v ∘ e.symm)
    (hv.comp _ e.symm.injective) hτ0 hτ1
  have hsum : ∀ c : ι → k, ∑ j, c j • w (e j) = ∑ j, (c ∘ e.symm) j • w j := by
    intro c
    have := e.sum_comp (fun j => (c ∘ e.symm) j • w j)
    simpa using this
  have horth : ∀ (c : ι → k) (i : ι), τ * ‖c i • w (e i)‖ ≤ ‖∑ j, c j • w (e j)‖ := by
    intro c i
    rw [hsum]
    simpa using hw (c ∘ e.symm) (e i)
  refine ⟨fun i => w (e i), ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := horth g i
    rw [hg, norm_zero] at h
    have h0 : ‖g i • w (e i)‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (g i • w (e i))]) (norm_nonneg _)
    rw [norm_eq_zero, smul_eq_zero] at h0
    exact h0.resolve_right (hw0 (e i))
  · intro i
    have := hwmem (e i)
    rwa [e.symm.surjective.range_comp v] at this
  · intro c i
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans (horth c i)
end GroundTheory.PAdicHodge
