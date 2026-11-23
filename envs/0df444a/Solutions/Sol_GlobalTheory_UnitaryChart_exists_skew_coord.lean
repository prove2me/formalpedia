-- Prove2me | solution 1 for GlobalTheory.UnitaryChart.exists_skew_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:25.471291+00:00
-- url     : https://prove2.me/submissions/05b49750-77cd-414d-bd79-a1671eef464a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnitaryChart
open Topology Filter
namespace GlobalTheory.UnitaryChart
theorem _root_.solution {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E]
    (σ : E →ₗ[ℝ] E) {N : ℕ} (e : Fin N → E) (hσ : ∀ a, σ (σ a) = a)
    (hli : LinearIndependent ℝ e) (he : ∀ i, σ (e i) = -e i)
    (hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) :
    ∃ P : E →L[ℝ] (Fin N → ℝ), (∀ t : Fin N → ℝ, P (∑ i, t i • e i) = t) ∧
      (∀ m, σ m = m → P m = 0) ∧ ∀ u v, P u = P v → u - σ u = v - σ v := by
  let T : (Fin N → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ e
  have hT : LinearMap.ker T = ⊥ :=
    LinearMap.ker_eq_bot.mpr hli.fintypeLinearCombination_injective
  obtain ⟨Q, hQ⟩ := T.exists_leftInverse_of_injective hT
  have hQT : ∀ t, Q (∑ i, t i • e i) = t := fun t => by
    have := LinearMap.congr_fun hQ t
    simpa [T, Fintype.linearCombination_apply] using this
  let π : E →ₗ[ℝ] E := (1 / 2 : ℝ) • (LinearMap.id - σ)
  have hπ : ∀ m, π m = (1 / 2 : ℝ) • (m - σ m) := fun m => rfl
  refine ⟨LinearMap.toContinuousLinearMap (Q ∘ₗ π), fun t => ?_, fun m hm => ?_, fun u v h => ?_⟩
  · have : σ (∑ i, t i • e i) = -∑ i, t i • e i := by
      simp [map_sum, he]
    change Q (π _) = t
    rw [hπ, this, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
    norm_num
    simpa using hQT t
  · change Q (π _) = 0
    rw [hπ, hm, sub_self, smul_zero, map_zero]
  · change Q (π u) = Q (π v) at h
    have h2 : Q (π (u - v)) = 0 := by rw [map_sub, map_sub, h, sub_self]
    have h3 : σ (π (u - v)) = -π (u - v) := by
      rw [hπ, map_smul, map_sub, hσ, ← smul_neg, neg_sub]
    obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hsp _ h3)
    rw [← hy, hQT] at h2
    have h4 : π (u - v) = 0 := by rw [← hy, h2]; simp
    rw [hπ, smul_eq_zero] at h4
    rcases h4 with h4 | h4
    · norm_num at h4
    · rw [map_sub] at h4
      exact sub_eq_sub_iff_sub_eq_sub.mp (sub_eq_zero.mp h4)
end GlobalTheory.UnitaryChart
