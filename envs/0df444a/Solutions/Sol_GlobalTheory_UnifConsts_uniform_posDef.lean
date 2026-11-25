-- Prove2me | solution 1 for GlobalTheory.UnifConsts.uniform_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:54:28.765322+00:00
-- url     : https://prove2.me/submissions/4fe15b3d-d658-483c-a31f-123a4e55dd06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydisc
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
open GlobalTheory GlobalTheory.UnifConsts
namespace GlobalTheory.UnifConsts
theorem _root_.solution {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] {K : Set X}
    (hK : IsCompact K) (F : X → Matrix ι ι ℝ) (hF : ∀ j k, ContinuousOn (fun z => F z j k) K)
    (hP : ∀ z ∈ K, (F z).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, ∀ y : ι → ℝ, c * (y ⬝ᵥ y) ≤ y ⬝ᵥ F z *ᵥ y := by
  set S : Set (X × (ι → ℝ)) := K ×ˢ Metric.sphere 0 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hq : ContinuousOn (fun p : X × (ι → ℝ) => p.2 ⬝ᵥ F p.1 *ᵥ p.2) S := by
    simp only [dotProduct, mulVec]
    refine continuousOn_finset_sum _ fun j _ => ?_
    refine ContinuousOn.mul (continuous_apply j |>.comp continuous_snd).continuousOn ?_
    refine continuousOn_finset_sum _ fun k _ => ?_
    refine ContinuousOn.mul ?_ (continuous_apply k |>.comp continuous_snd).continuousOn
    exact (hF j k).comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hyy : ∀ y : ι → ℝ, y ⬝ᵥ y ≤ Fintype.card ι * ‖y‖ ^ 2 := by
    intro y
    simp only [dotProduct]
    calc ∑ i, y i * y i ≤ ∑ _i : ι, ‖y‖ ^ 2 := by
          gcongr with i
          have := norm_le_pi_norm y i
          rw [Real.norm_eq_abs] at this
          nlinarith [abs_nonneg (y i), sq_abs (y i)]
      _ = _ := by simp

  have hscale : ∀ z y, y ≠ 0 →
      (‖y‖⁻¹ • y) ⬝ᵥ F z *ᵥ (‖y‖⁻¹ • y) = (‖y‖ ^ 2)⁻¹ * (y ⬝ᵥ F z *ᵥ y) := by
    intro z y _
    simp [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hmem : ∀ z ∈ K, ∀ y : ι → ℝ, y ≠ 0 → (z, ‖y‖⁻¹ • y) ∈ S := by
    intro z hz y hy
    refine ⟨hz, ?_⟩
    simp [norm_smul, norm_ne_zero_iff.2 hy]
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne hq
    have hp2 : p.2 ≠ 0 := by
      intro h0
      have := hp.2
      simp [h0] at this
    have hm : 0 < p.2 ⬝ᵥ F p.1 *ᵥ p.2 := by
      simpa using (hP p.1 hp.1).dotProduct_mulVec_pos hp2
    have hcard : 0 < (Fintype.card ι : ℝ) := by
      have : Nonempty ι := by
        by_contra hι
        rw [not_nonempty_iff] at hι
        exact hp2 (Subsingleton.elim _ _)
      exact_mod_cast Fintype.card_pos
    refine ⟨(p.2 ⬝ᵥ F p.1 *ᵥ p.2) / Fintype.card ι, div_pos hm hcard, fun z hz y => ?_⟩
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have h1 := hmin (hmem z hz y hy)
    simp only [Set.mem_setOf_eq] at h1
    rw [hscale z y hy] at h1
    have hn : 0 < ‖y‖ ^ 2 := by positivity
    have h2 : (p.2 ⬝ᵥ F p.1 *ᵥ p.2) * ‖y‖ ^ 2 ≤ y ⬝ᵥ F z *ᵥ y := by
      rwa [le_inv_mul_iff₀ hn, mul_comm] at h1
    calc (p.2 ⬝ᵥ F p.1 *ᵥ p.2) / Fintype.card ι * (y ⬝ᵥ y)
        ≤ (p.2 ⬝ᵥ F p.1 *ᵥ p.2) / Fintype.card ι * (Fintype.card ι * ‖y‖ ^ 2) := by
          gcongr; exact hyy y
      _ = (p.2 ⬝ᵥ F p.1 *ᵥ p.2) * ‖y‖ ^ 2 := by field_simp
      _ ≤ _ := h2
  · refine ⟨1, one_pos, fun z hz y => ?_⟩
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    exact absurd ⟨_, hmem z hz y hy⟩ hne
end GlobalTheory.UnifConsts
