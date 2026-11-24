-- Prove2me | solution 1 for GlobalTheory.IdealChain.integral_scale_change_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:33.211621+00:00
-- url     : https://prove2.me/submissions/cfca7c26-a7b3-419a-a16f-b74ce0bf1831

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMeasurePiChangeConstant
import Theorems.Thm_GlobalTheory_IdealChain_pi_nnreal_smul
import Theorems.Thm_GlobalTheory_IdealChain_isHalfPow_inv
import Theorems.Thm_GlobalTheory_IdealChain_isHalfPow_mul
import Theorems.Thm_GlobalTheory_IdealChain_isHalfPow_nabs
import Theorems.Thm_GlobalTheory_IdealChain_isHalfPow_pow
import Theorems.Thm_GlobalTheory_IdealChain_resCard_pos
import Theorems.Thm_GlobalTheory_SplitWeil_integral_comp_mulVec_eq_smul
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_P2M_GlobalTheory_SplitWeil_nabs_pos__162ed63212bf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
open GlobalTheory GlobalTheory.IdealChain
namespace GlobalTheory.IdealChain
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι] (ν νs : Measure k) (d : ι → kˣ), ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ F : (ι → k) → ℂ, ∫ e, F e ∂(Measure.pi fun _ => ν) = C * ∫ e, F (fun i => (d i : k) * e i) ∂(Measure.pi fun _ => νs) := by
  intro k _ _ _ _ _ _ ι _ ν νs d hν hνs
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨a, ha0, ha⟩ : ∃ a : NNReal, 0 < a ∧ ν = a • νs :=
    ⟨_, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν νs, Measure.isAddLeftInvariant_eq_smul ν νs⟩
  let g : GL ι k := ⟨Matrix.diagonal fun i => (d i : k), Matrix.diagonal fun i => ((d i)⁻¹ : kˣ),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩
  have hpos := nabs_pos' (Matrix.GeneralLinearGroup.det g)
  refine ⟨(a : ℝ) ^ Fintype.card ι * nabs k (Matrix.GeneralLinearGroup.det g),
    ⟨mul_pos (pow_pos ha0 _) hpos, fun h1 h2 => isHalfPow_mul (isHalfPow_pow ?_ _) (isHalfPow_nabs _)⟩, fun F => ?_⟩
  · have h3 : (νs (𝒪[k] : Set k)).toReal ≠ 0 := by
      obtain ⟨e, he⟩ := h2
      rw [he]
      exact (Real.rpow_pos_of_pos resCard_pos _).ne'
    have h4 : (a : ℝ) = (ν (𝒪[k] : Set k)).toReal * ((νs (𝒪[k] : Set k)).toReal)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ h3, ha, Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul, ENNReal.coe_toReal]
    rw [h4]
    exact isHalfPow_mul h1 (isHalfPow_inv h2)
  · have h := integral_comp_mulVec_eq_smul νs g F
    have h2 : ∀ x : ι → k, g.val.mulVec x = fun i => (d i : k) * x i := by
      intro x; funext i; simp [g, Matrix.mulVec_diagonal]
    simp only [h2] at h
    have h5 : (Measure.pi fun _ : ι => ν) = (a ^ Fintype.card ι) • Measure.pi fun _ : ι => νs := by
      rw [← pi_nnreal_smul, ← ha]
    rw [h, h5, integral_smul_nnreal_measure]
    have : (nabs k (Matrix.GeneralLinearGroup.det g) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [Complex.real_smul, NNReal.smul_def, Complex.real_smul]
    push_cast
    field_simp
end GlobalTheory.IdealChain
