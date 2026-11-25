-- Prove2me | solution 1 for GlobalTheory.exists_mem_thetaLevelChar_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:25:42.101449+00:00
-- url     : https://prove2.me/submissions/352d77e5-6b11-4ea0-8615-137c1d868a0d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMemThetaLevelCharApplyNeZero
import Theorems.Thm_GlobalTheory_SCV_eqOn_of_eqOn_open
import Theorems.Thm_GlobalTheory_prod_translate_mem_thetaLevelChar
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_GlobalTheory_theta_mem_thetaLevelChar_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply


section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℝ}
private lemma exists_mem_open_ne_zero_of_differentiable {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (hf0 : f ≠ 0)
    {V : Set (Fin g → ℂ)} (hV : IsOpen V) (hVne : V.Nonempty) : ∃ z ∈ V, f z ≠ 0 := by
  by_contra h
  push Not at h
  have := SCV.eqOn_of_eqOn_open (f := f) (g := fun _ => 0) isOpen_univ isPreconnected_univ
    hf.differentiableOn (differentiable_const _).differentiableOn hV hVne (Set.subset_univ _) h
  exact hf0 (funext fun z => this (Set.mem_univ z))
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℝ}
namespace GlobalTheory
theorem _root_.solution (hτ : τ ∈ SiegelH (Fin g)) (a b : Fin g → ℝ)
    {k : ℕ} (hk : k ≠ 0) (z₀ : Fin g → ℂ) : ∃ F ∈ thetaLevelChar a b (k + 1) τ, F z₀ ≠ 0 := by
  set θ : (Fin g → ℂ) → ℂ := fun z => theta a b z τ with hθ
  have hθd : Differentiable ℂ θ := differentiable_theta hτ a b
  have hθ0 : θ ≠ 0 := theta_ne_zero hτ a b
  obtain ⟨q, hq⟩ : ∃ q, θ q ≠ 0 := by
    by_contra h
    push Not at h
    exact hθ0 (funext h)
  have hk' : (-(k : ℂ)) ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hk)
  have hV : IsOpen {w : Fin g → ℂ | θ (z₀ + w) ≠ 0} :=
    isOpen_ne_fun (hθd.continuous.comp (continuous_const.add continuous_id)) continuous_const
  have hVne : ({w : Fin g → ℂ | θ (z₀ + w) ≠ 0}).Nonempty :=
    ⟨q - z₀, by simpa only [Set.mem_ofPred_eq, add_sub_cancel] using hq⟩
  have hhd : Differentiable ℂ (fun w : Fin g → ℂ => θ (z₀ + (-(k : ℂ)) • w)) :=
    hθd.comp (by fun_prop)
  have hh0 : (fun w : Fin g → ℂ => θ (z₀ + (-(k : ℂ)) • w)) ≠ 0 := by
    intro h0
    apply hq
    have := congrFun h0 ((-(k : ℂ))⁻¹ • (q - z₀))
    simpa only [smul_smul, mul_inv_cancel₀ hk', one_smul, add_sub_cancel, Pi.zero_apply] using this
  obtain ⟨w, hw1, hw2⟩ := exists_mem_open_ne_zero_of_differentiable hhd hh0 hV hVne
  refine ⟨fun z => ∏ i : Fin (k + 1), θ (z + if i = 0 then (-(k : ℂ)) • w else w), ?_, ?_⟩
  · have hsum : ∑ i ∈ (Finset.univ : Finset (Fin (k + 1))), ((fun _ => 1 : Fin (k + 1) → ℕ) i : ℂ) •
        (fun i : Fin (k + 1) => if i = 0 then (-(k : ℂ)) • w else w) i = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [Nat.cast_one, one_smul, if_pos, Fin.succ_ne_zero, if_false, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℂ, neg_smul, neg_add_cancel]
    have := prod_translate_mem_thetaLevelChar (a := a) (b := b) (τ := τ)
      (Finset.univ : Finset (Fin (k + 1))) (d := fun _ => 1) (F := fun _ => θ)
      (fun _ _ => theta_mem_thetaLevelChar_one hτ) _ hsum
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, _root_.mul_one] using this
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    split_ifs
    · exact hw2
    · exact hw1
end GlobalTheory
