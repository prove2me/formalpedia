-- Prove2me | solution 1 for GlobalTheory.exists_smooth_homogeneous_hasSum_unit_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:56:24.056984+00:00
-- url     : https://prove2.me/submissions/124b94c8-e7ee-463c-ae0d-59a0a94ed0a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothCompactSupportHasSumLatticeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
import Theorems.Thm_GlobalTheory_UnitPartition_hasSum_quot
import Theorems.Thm_GlobalTheory_UnitPartition_contDiffAt_logMap
import Theorems.Thm_GlobalTheory_UnitPartition_log_le
import Theorems.Thm_GlobalTheory_exists_smooth_compactSupport_hasSum_lattice_translates


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open UnitPartition NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K], ∃ h : mixedSpace K → ℝ, ContDiffOn ℝ ∞ h {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ (t : ℝ) x, 0 < t → h (t • x) = h x) ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → HasSum (fun u : (𝓞 K)ˣ => h (u • x)) 1) ∧ (∀ a b : ℝ, 0 < a → ∃ C : Set (mixedSpace K), IsCompact C ∧ (∀ x ∈ C, mixedEmbedding.norm x ≠ 0) ∧ ∀ x, h x ≠ 0 → a ≤ mixedEmbedding.norm x → mixedEmbedding.norm x ≤ b → x ∈ C) := by
  intro K _ _
  obtain ⟨η, hη, hηc, hηs⟩ := exists_smooth_compactSupport_hasSum_lattice_translates
    ({w : InfinitePlace K // w ≠ w₀} → ℝ) (unitLattice K)
  refine ⟨fun x => if mixedEmbedding.norm x = 0 then 0 else
    η (logMap x) / (Nat.card (torsion K) : ℝ), ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : mixedEmbedding.norm x ≠ 0 := hx
    have hopen : IsOpen {y : mixedSpace K | mixedEmbedding.norm y ≠ 0} :=
      isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const
    refine ContDiffAt.contDiffWithinAt ?_
    have hev : (fun y : mixedSpace K => if mixedEmbedding.norm y = 0 then 0 else
        η (logMap y) / (Nat.card (torsion K) : ℝ)) =ᶠ[nhds x]
        fun y => η (logMap y) / (Nat.card (torsion K) : ℝ) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      rw [if_neg hy]
    exact ((hη.contDiffAt.comp x (contDiffAt_logMap x hx')).div_const _).congr_of_eventuallyEq hev
  · intro t x ht
    have ht0 : t ≠ 0 := ht.ne'
    simp only [mixedEmbedding.norm_smul]
    by_cases hx : mixedEmbedding.norm x = 0
    · simp [hx]
    · have hne : |t| ^ Module.finrank ℚ K * mixedEmbedding.norm x ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (abs_ne_zero.2 ht0)) hx
      rw [if_neg hne, if_neg hx, logMap_real_smul hx ht0]
  · intro x hx
    let e : ((𝓞 K)ˣ ⧸ torsion K) ≃ unitLattice K :=
      Additive.ofMul.trans (logEmbeddingEquiv K).toEquiv
    have hq : HasSum ((fun l : unitLattice K => η (logMap x + l)) ∘ e) 1 :=
      e.hasSum_iff.2 (hηs (logMap x))
    have hu := hasSum_quot (torsion K) _ 1 hq
    convert hu using 2 with u
    have hux : mixedEmbedding.norm (u • x) ≠ 0 := by rwa [norm_unit_smul]
    dsimp only
    rw [if_neg hux, logMap_unit_smul u hx, add_comm]
    simp only [Function.comp_apply, e, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
      logEmbeddingEquiv_apply]
  · intro a b ha
    obtain ⟨R, hR⟩ := hηc.isCompact.isBounded.exists_norm_le
    refine ⟨Metric.closedBall 0 (Real.exp (Fintype.card (InfinitePlace K) * R +
        Real.log b * (Module.finrank ℚ K : ℝ)⁻¹)) ∩ {x | a ≤ mixedEmbedding.norm x},
      (isCompact_closedBall _ _).inter_right
        (isClosed_le continuous_const (mixedEmbedding.continuous_norm K)),
      fun x hx => (ha.trans_le hx.2).ne', fun x hx hax hxb => ⟨?_, hax⟩⟩
    have hx0 : mixedEmbedding.norm x ≠ 0 := (ha.trans_le hax).ne'
    dsimp only at hx
    rw [if_neg hx0] at hx
    have hηx : η (logMap x) ≠ 0 := fun h0 => hx (by rw [h0, zero_div])
    have hlog : ‖logMap x‖ ≤ R := hR _ (subset_tsupport _ hηx)
    rw [mem_closedBall_zero_iff, norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun w _ => ?_
    have hNw : 0 < normAtPlace w x :=
      lt_of_le_of_ne (normAtPlace_nonneg w x) (mixedEmbedding.norm_ne_zero_iff.1 hx0 w).symm
    rw [← Real.exp_log hNw]
    refine Real.exp_le_exp.2 ((log_le x hx0 w).trans (add_le_add
      (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)) ?_))
    exact mul_le_mul_of_nonneg_right (Real.log_le_log (ha.trans_le hax) hxb) (by positivity)
end GlobalTheory
