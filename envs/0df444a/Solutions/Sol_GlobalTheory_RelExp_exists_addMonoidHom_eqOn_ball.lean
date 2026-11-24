-- Prove2me | solution 1 for GlobalTheory.RelExp.exists_addMonoidHom_eqOn_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:55:18.990266+00:00
-- url     : https://prove2.me/submissions/8f6c6bea-3a91-405d-87fe-7c7ca333917e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Theorems.Thm_GlobalTheory_RelExp_HolAt_eventually
import Theorems.Thm_GlobalTheory_RelExp_HolAt_congr
import Theorems.Thm_GlobalTheory_exists_addMonoidHom_eventuallyEq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.RelExp
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {Z Y : Scheme.{0}}
variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup A]
namespace GlobalTheory.RelExp
theorem _root_.solution {g : V → A} {r : ℝ} (hr : 0 < r)
    (hg : ∀ x ∈ Metric.ball (0 : V) r, ∀ x' ∈ Metric.ball (0 : V) r, g (x + x') = g x + g x') :
    ∃ e : V →+ A, ∀ x ∈ Metric.ball (0 : V) r, e x = g x := by
  obtain ⟨e, he⟩ := exists_addMonoidHom_eventuallyEq (g := g) (by
    filter_upwards [prod_mem_nhds (Metric.ball_mem_nhds (0 : V) hr) (Metric.ball_mem_nhds (0 : V) hr)] with p hp
    exact hg _ hp.1 _ hp.2)
  refine ⟨e, fun x hx => ?_⟩
  have hball : ∀ k : ℕ, (2⁻¹ : ℝ) ^ k • x ∈ Metric.ball (0 : V) r := fun k => by
    rw [mem_ball_zero_iff] at hx ⊢
    rw [norm_smul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (by norm_num))).trans_lt hx
  have hstep : ∀ k : ℕ, e ((2⁻¹ : ℝ) ^ k • x) = g ((2⁻¹ : ℝ) ^ k • x) → e x = g x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro h
      apply ih
      have : (2⁻¹ : ℝ) ^ k • x = (2⁻¹ : ℝ) ^ (k + 1) • x + (2⁻¹ : ℝ) ^ (k + 1) • x := by
        rw [← add_smul, pow_succ]; congr 1; ring
      rw [this, map_add, hg _ (hball _) _ (hball _), h]
  have ht : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) ^ j • x) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
      (by norm_num)).smul_const x
  obtain ⟨k, hk⟩ := (ht.eventually he).exists
  exact hstep k hk
end GlobalTheory.RelExp
