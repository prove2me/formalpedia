-- Prove2me | solution 1 for GlobalTheory.HeisUnit.inner_eq_mul_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:25:06.103005+00:00
-- url     : https://prove2.me/submissions/76b9f32f-8aaf-40b6-b8d9-b51dcf4f0386

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryAndSeparates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergCosetRepTranslatesOrthogonal

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
namespace GlobalTheory.HeisUnit
theorem _root_.solution (ψ0 : AddChar k ℂ)
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (l : Matrix (Fin n) (Fin d) k →ₗ[k] k) (f f' : (Fin n × Fin d → k) → ℂ)
    (hf : f ∈ GlobalTheory.WeilM.SB _) (hf' : f' ∈ GlobalTheory.WeilM.SB _) (a b : ℂ) (ha : Mu l f = a • f) (hb : Mu l f' = b • f') :
    ∫ y, f y * (starRingEnd ℂ) (f' y) ∂μ = a * (starRingEnd ℂ) b * ∫ y, f y * (starRingEnd ℂ) (f' y) ∂μ := by
  rw [← integral_const_mul, ← hMuI μ hμ l f hf f' hf', ha, hb]
  congr 1; funext y
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
end GlobalTheory.HeisUnit
