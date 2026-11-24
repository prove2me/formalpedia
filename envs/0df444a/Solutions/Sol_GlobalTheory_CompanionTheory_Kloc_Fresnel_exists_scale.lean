-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.exists_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:40:52.066728+00:00
-- url     : https://prove2.me/submissions/6408f5d2-5a72-47df-9816-256cb4cfcb2c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {m n : ℕ}
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
theorem _root_.solution (m n : ℕ) : ∃ κ : ℝ, 0 < κ ∧ ∀ F : EuclideanSpace ℂ (Fin m × Fin n) → ℂ,
    ∫ u : Fin m → Fin n → ℂ, F (matEquiv m n u) = κ * ∫ y, F y := by
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI hH : (Measure.map (matEquiv m n) (volume : Measure (Fin m → Fin n → ℂ))).IsAddHaarMeasure :=
    (matEquiv m n).isAddHaarMeasure_map _
  have he := Measure.isAddLeftInvariant_eq_smul
    (Measure.map (matEquiv m n) (volume : Measure (Fin m → Fin n → ℂ)))
    (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (Measure.map (matEquiv m n) (volume : Measure (Fin m → Fin n → ℂ)))
    (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n))) : NNReal), ?_, fun F => ?_⟩
  · exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  · have h := (matEquiv m n).toHomeomorph.measurableEmbedding.integral_map
      (μ := (volume : Measure (Fin m → Fin n → ℂ))) F
    have h' : ∫ u : Fin m → Fin n → ℂ, F (matEquiv m n u) =
        ∫ y, F y ∂(Measure.map (matEquiv m n) (volume : Measure (Fin m → Fin n → ℂ))) := h.symm
    rw [h']
    conv_lhs => rw [he]
    rw [integral_smul_nnreal_measure]
    rfl
end GlobalTheory.CompanionTheory.Kloc.Fresnel
