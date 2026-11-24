-- Prove2me | solution 1 for GlobalTheory.HeisUnit.norm_char_unit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:59:49.109329+00:00
-- url     : https://prove2.me/submissions/3aebecb5-4742-466c-ba00-7ea68df7f980

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCharacterUnitEqOneHeisenberg
import Theorems.Thm_GlobalTheory_HeisUnit_intInd_diagAt_mul
import Theorems.Thm_GlobalTheory_HeisUnit_det_diagAt
import Theorems.Thm_GlobalTheory_WeilM_norm_eq_one_of_lintegral_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.HeisUnit
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.HeisUnit
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ 0 ∧ ∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ ≠ ⊤) →
    ∀ (_i0 : Fin n) (u : kˣ), valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1 := by
  intro k _ _ _ _ n d ι hinj S hS hiso χ hι φ0 hφ0 hι0 hfin i0 u hu
  set g := diagAt u i0 with hg
  have hmem : (χ u : ℂ) • φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) := Submodule.smul_mem _ _ hφ0
  have heq : S g φ0 = (χ u : ℂ) • φ0 := by
    refine hinj (hS g φ0 hφ0) hmem ?_
    rw [hι g φ0 hφ0, map_smul, hι0, det_diagAt]
    funext Y
    rw [intInd_diagAt_mul hu i0 Y]
    rfl
  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  have hμ : Measure.IsAddHaarMeasure (Measure.addHaar : Measure (Fin n × Fin d → k)) := inferInstance
  have h := hiso g φ0 hφ0 Measure.addHaar hμ
  rw [heq] at h
  exact GlobalTheory.WeilM.norm_eq_one_of_lintegral_eq h (hfin _ hμ).1 (hfin _ hμ).2
end GlobalTheory.HeisUnit
