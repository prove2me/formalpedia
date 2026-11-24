-- Prove2me | solution 1 for GlobalTheory.AffinePoints.isProperMap_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:12:21.034973+00:00
-- url     : https://prove2.me/submissions/f4bc7157-313b-45e3-b714-2fb2e4a1e4ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Theorems.Thm_GlobalTheory_AffinePoints_norm_le_of_isRoot_monic
import Theorems.Thm_GlobalTheory_AffinePoints_isClosedEmbedding_coe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set Polynomial
variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
namespace GlobalTheory.AffinePoints
theorem _root_.solution (φ : A →ₐ[ℂ] B) (hφ : φ.toRingHom.IsIntegral) :
    IsProperMap (comap φ : (B →ₐ[ℂ] ℂ) → (A →ₐ[ℂ] ℂ)) := by
  refine isProperMap_iff_ultrafilter_of_t2.2 ⟨continuous_comap φ, fun 𝒰 p hp => ?_⟩
  have hlim : ∀ b : B, ∃ t : ℂ, Tendsto (fun q : B →ₐ[ℂ] ℂ => q b) 𝒰 (𝓝 t) := by
    intro b
    obtain ⟨h, hm, hb⟩ := hφ b
    let M : (A →ₐ[ℂ] ℂ) → ℝ := fun r => ∑ i ∈ Finset.range h.natDegree, ‖r (h.coeff i)‖ + 1
    have hM : Continuous M :=
      (continuous_finset_sum _ fun i _ => (continuous_eval _).norm).add continuous_const
    have hbd : ∀ q : B →ₐ[ℂ] ℂ, ‖q b‖ ≤ M (comap φ q) := by
      intro q
      have hr : (h.map (comap φ q).toRingHom).IsRoot (q b) := by
        have : (comap φ q).toRingHom = q.toRingHom.comp φ.toRingHom := rfl
        rw [IsRoot, eval_map, this]
        change eval₂ _ (q.toRingHom b) h = 0
        rw [← hom_eval₂, hb, map_zero]
      have := norm_le_of_isRoot_monic (hm.map _) hr
      simpa [hm.natDegree_map, M] using this
    have hev : ∀ᶠ q in (𝒰 : Filter (B →ₐ[ℂ] ℂ)), q b ∈ Metric.closedBall (0 : ℂ) (M p + 1) := by
      filter_upwards [((hM.tendsto p).comp hp).eventually (gt_mem_nhds (lt_add_one (M p)))]
        with q hq
      exact mem_closedBall_zero_iff.2 ((hbd q).trans hq.le)
    obtain ⟨t, -, ht⟩ := (isCompact_closedBall (0 : ℂ) (M p + 1)).ultrafilter_le_nhds
      (𝒰.map fun q : B →ₐ[ℂ] ℂ => q b) (le_principal_iff.2 hev)
    exact ⟨t, ht⟩
  choose u hu using hlim
  have hu' : Tendsto (fun q : B →ₐ[ℂ] ℂ => (q : B → ℂ)) 𝒰 (𝓝 u) := tendsto_pi_nhds.2 hu
  obtain ⟨q, hq⟩ := (isClosedEmbedding_coe (R := ℂ) (A := B) (C := ℂ)).isClosed_range.mem_of_tendsto
    hu' (Eventually.of_forall fun q => ⟨q, rfl⟩)
  refine ⟨q, ?_⟩
  rw [← tendsto_id', tendsto_nhds_iff]
  intro b
  rw [show q b = u b from congrFun hq b]
  exact hu b
end GlobalTheory.AffinePoints
