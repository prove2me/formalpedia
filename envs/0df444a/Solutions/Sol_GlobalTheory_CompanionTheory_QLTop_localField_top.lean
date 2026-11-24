-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QLTop.localField_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:16:27.1856+00:00
-- url     : https://prove2.me/submissions/59cc6e38-5f3c-4426-9ed3-33a8470619a2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBalls
import Theorems.Thm_GlobalTheory_CompanionTheory_QLTop_isOpen_integers
import Theorems.Thm_GlobalTheory_CompanionTheory_QLTop_nrm_le_one_iff
import Theorems.Thm_GlobalTheory_SgLoc_Top_localField_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLTop
namespace GlobalTheory.CompanionTheory.QLTop
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → IsOpen (O : Set F) ∧ IsCompact (O : Set F) ∧ SecondCountableTopology F ∧ Continuous (fun x : F => nrm x) ∧ (∀ e : ℤ, IsOpen {x : F | nrm x ≤ (q : ℝ) ^ e}) ∧ (∀ s ∈ nhds (0 : F), ∃ e : ℤ, {x : F | nrm x ≤ (q : ℝ) ^ e} ⊆ s) := by
  intro F _ _ _ _ O ϖ nrm q h
  obtain ⟨hq, hle⟩ := nrm_le_one_iff h
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := lt_trans one_pos hq1
  have hO : IsOpen (O : Set F) := by rw [h.O_eq]; exact isOpen_integers F
  have hball : ∀ (e : ℤ) (x : F), nrm x ≤ (q : ℝ) ^ e ↔ x * ϖ ^ e ∈ O := by
    intro e x
    rw [← hle, map_mul, map_zpow₀, h.nrm_pi, _root_.inv_zpow, ← div_eq_mul_inv, div_le_one (zpow_pos hq0 e)]
  have hopen : ∀ e : ℤ, IsOpen {x : F | nrm x ≤ (q : ℝ) ^ e} := by
    intro e
    have : {x : F | nrm x ≤ (q : ℝ) ^ e} = (fun x => x * ϖ ^ e) ⁻¹' (O : Set F) := by
      ext x; exact hball e x
    rw [this]
    exact hO.preimage (continuous_id.mul continuous_const)
  refine ⟨hO, ?_, GlobalTheory.SgLoc.Top.localField_secondCountable F, ?_, hopen, ?_⟩
  · rw [h.O_eq]
    exact IsNonarchimedeanLocalField.isCompact_closedBall F 1
  · rw [continuous_iff_continuousAt]
    intro x₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq1)
    have hU : IsOpen ((fun x => x - x₀) ⁻¹' {x : F | nrm x ≤ (q : ℝ) ^ (-(n : ℤ))}) :=
      (hopen _).preimage (continuous_id.sub continuous_const)
    have hm : x₀ ∈ ((fun x => x - x₀) ⁻¹' {x : F | nrm x ≤ (q : ℝ) ^ (-(n : ℤ))}) := by
      show nrm (x₀ - x₀) ≤ _
      rw [sub_self, map_zero]; exact (zpow_pos hq0 _).le
    filter_upwards [hU.mem_nhds hm] with x hx
    have hx' : nrm (x - x₀) ≤ (q : ℝ) ^ (-(n : ℤ)) := hx
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow] at hx'
    rw [Real.dist_eq]
    exact lt_of_le_of_lt ((nrm.abs_abv_sub_le_abv_sub x x₀).trans hx') hn
  · intro s hs
    obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.mp hs
    have hv : ValuativeRel.valuation F ϖ < 1 := (h.lt_one ϖ).mpr ⟨1, O.one_mem, (mul_one _).symm⟩
    haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero F) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hv (Units.mk0 γ hγ)
    refine ⟨-(n : ℤ), fun x hx => hs ?_⟩
    have hx' := (hball _ x).mp hx
    rw [h.O_eq, Valuation.mem_integer_iff] at hx'
    have : x = (x * ϖ ^ (-(n : ℤ))) * ϖ ^ n := by
      rw [_root_.zpow_neg, zpow_natCast, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h.ne), mul_one]
    show ValuativeRel.valuation F x < γ
    rw [this, map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx') hn
end GlobalTheory.CompanionTheory.QLTop
