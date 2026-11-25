-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocInv.tendsto_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:49.136423+00:00
-- url     : https://prove2.me/submissions/069ec980-e73d-4db5-acdc-0efb144796a7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExists
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInv_measureReal_dual_mul
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocInv
open GroundTheory.LocalField ValuativeRel MeasureTheory Topology Filter
open scoped NNReal ENNReal
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
namespace GlobalTheory.CompanionTheory.SW.LocInv
theorem _root_.solution (ψ : AddChar K Circle) {Φ : K → ℂ} (hΦ : Continuous Φ) (z : K) :
    Tendsto (fun k : ℕ =>
      (((selfDualMeasure ψ).real (valBall K (addCharConductor ψ - (k : ℤ))) : ℝ) : ℂ) *
        ∫ x in valBall K (k : ℤ), Φ (x - z) ∂(selfDualMeasure ψ)) atTop (𝓝 (Φ (-z))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcont : ContinuousAt (fun h : K => Φ (h - z)) 0 :=
    (hΦ.comp (continuous_id.sub continuous_const)).continuousAt
  have hnh : {h : K | dist (Φ (h - z)) (Φ (-z)) < ε / 2} ∈ 𝓝 (0 : K) := by
    have := hcont.preimage_mem_nhds (Metric.ball_mem_nhds (Φ (0 - z)) (half_pos hε))
    simpa [Metric.ball, zero_sub] using this
  obtain ⟨m, -, hm⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp hnh
  refine ⟨m.toNat, fun k hk => ?_⟩
  have hkm : m ≤ (k : ℤ) := by omega
  have hsub : (valBall K (k : ℤ) : Set K) ⊆ valBall K m := valBall_antitone hkm
  have hmul := measureReal_dual_mul ψ (k : ℤ)
  set c : ℝ := (selfDualMeasure ψ).real (valBall K (addCharConductor ψ - (k : ℤ))) with hcdef
  set v : ℝ := (selfDualMeasure ψ).real (valBall K (k : ℤ)) with hvdef
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hfin : (selfDualMeasure ψ) (valBall K (k : ℤ) : Set K) < ∞ :=
    (isCompact_valBall _).measure_lt_top
  have hint : IntegrableOn (fun x => Φ (x - z)) (valBall K (k : ℤ)) (selfDualMeasure ψ) :=
    (hΦ.comp (continuous_id.sub continuous_const)).continuousOn.integrableOn_compact
      (isCompact_valBall _)
  have hintc : IntegrableOn (fun _ : K => Φ (-z)) (valBall K (k : ℤ)) (selfDualMeasure ψ) :=
    integrableOn_const hfin.ne
  have hdiff : (c : ℂ) * (∫ x in valBall K (k : ℤ), Φ (x - z) ∂(selfDualMeasure ψ)) - Φ (-z) =
      (c : ℂ) * ∫ x in valBall K (k : ℤ), (Φ (x - z) - Φ (-z)) ∂(selfDualMeasure ψ) := by
    rw [integral_sub hint hintc, setIntegral_const, Complex.real_smul, mul_sub, ← mul_assoc,
      ← hvdef]
    have : (c : ℂ) * (v : ℂ) = 1 := by exact_mod_cast hmul
    rw [this, one_mul]
  have hbound : ‖∫ x in valBall K (k : ℤ), (Φ (x - z) - Φ (-z)) ∂(selfDualMeasure ψ)‖ ≤
      ε / 2 * v := by
    refine norm_setIntegral_le_of_norm_le_const hfin fun x hx => ?_
    have := hm (hsub hx)
    rw [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  rw [dist_eq_norm, hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
  calc c * ‖∫ x in valBall K (k : ℤ), (Φ (x - z) - Φ (-z)) ∂(selfDualMeasure ψ)‖
      ≤ c * (ε / 2 * v) := mul_le_mul_of_nonneg_left hbound hc0
    _ = ε / 2 := by
        rw [show c * (ε / 2 * v) = ε / 2 * (c * v) by ring, hmul, mul_one]
    _ < ε := half_lt_self hε
end GlobalTheory.CompanionTheory.SW.LocInv
