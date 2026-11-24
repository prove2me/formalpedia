-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelRows.rowInt_of_kerBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:40:48.116372+00:00
-- url     : https://prove2.me/submissions/4b6f3ebc-f189-4532-85a6-209d99ed3318

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RowIntOfKerBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelRows
open PositivityTheory.Rg.BcB.E1
namespace GlobalTheory.CompanionTheory.KernelRows
theorem _root_.solution : KerBasic → RowInt := by
  intro hK X φ hφ
  haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have hc : Continuous φ := hφ.1
  have hcs : HasCompactSupport φ := hφ.2
  have hc' : Continuous fun z : X.G => φ z⁻¹ := hc.comp continuous_inv
  have hcs' : HasCompactSupport fun z : X.G => φ z⁻¹ :=
    hcs.comp_homeomorph (Homeomorph.inv X.G)
  have hfin1 : ∫⁻ z, ‖φ z‖ₑ ∂X.μ ≠ ⊤ :=
    (hc.integrable_of_hasCompactSupport (μ := X.μ) hcs).2.ne
  have hfin2 : ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ ≠ ⊤ :=
    (hc'.integrable_of_hasCompactSupport (μ := X.μ) hcs').2.ne
  have hb := (hK X φ hφ).2.2.2.2.2
  have hν : X.ν = X.μ.restrict X.F := rfl
  refine ⟨∫⁻ z, ‖φ z‖ₑ ∂X.μ + ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ, ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩, ?_, ?_⟩
  · intro x
    calc ∫⁻ y, ‖ker X.Γ φ x y‖ₑ ∂X.ν
        ≤ ∫⁻ y, ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ ∂X.ν := lintegral_mono (hb x)
      _ = ∑' γ : X.Γ, ∫⁻ y in X.F, ‖φ (x⁻¹ * (γ • y))‖ₑ ∂X.μ := by
          rw [hν, lintegral_tsum]
          · refine tsum_congr fun γ => lintegral_congr fun y => ?_
            rw [Subgroup.smul_def, smul_eq_mul, mul_assoc]
          · intro γ
            exact (hc.comp (by fun_prop)).enorm.aemeasurable
      _ = ∫⁻ y, ‖φ (x⁻¹ * y)‖ₑ ∂X.μ :=
          (X.fd.lintegral_eq_tsum'' (fun y => ‖φ (x⁻¹ * y)‖ₑ)).symm
      _ = ∫⁻ y, ‖φ y‖ₑ ∂X.μ := lintegral_mul_left_eq_self (fun y => ‖φ y‖ₑ) x⁻¹
      _ ≤ _ := le_self_add
  · intro y
    calc ∫⁻ x, ‖ker X.Γ φ x y‖ₑ ∂X.ν
        ≤ ∫⁻ x, ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ ∂X.ν :=
          lintegral_mono fun x => hb x y
      _ = ∑' γ : X.Γ, ∫⁻ x in X.F, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ ∂X.μ := by
          rw [hν, lintegral_tsum]
          intro γ
          exact (hc.comp (by fun_prop)).enorm.aemeasurable
      _ = ∑' γ : X.Γ, ∫⁻ x in X.F, ‖φ ((γ • x)⁻¹ * y)‖ₑ ∂X.μ := by
          rw [← (Equiv.inv X.Γ).tsum_eq]
          refine tsum_congr fun γ => lintegral_congr fun x => ?_
          simp [Subgroup.smul_def, smul_eq_mul, mul_inv_rev]
      _ = ∫⁻ x, ‖φ (x⁻¹ * y)‖ₑ ∂X.μ :=
          (X.fd.lintegral_eq_tsum'' (fun x => ‖φ (x⁻¹ * y)‖ₑ)).symm
      _ = ∫⁻ z, ‖φ z⁻¹‖ₑ ∂X.μ := by
          rw [← lintegral_mul_left_eq_self (fun x => ‖φ (x⁻¹ * y)‖ₑ) y]
          refine lintegral_congr fun z => ?_
          simp [mul_inv_rev]
      _ ≤ _ := le_add_self
end GlobalTheory.CompanionTheory.KernelRows
