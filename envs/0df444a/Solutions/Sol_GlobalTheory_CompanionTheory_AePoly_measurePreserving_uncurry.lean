-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AePoly.measurePreserving_uncurry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:23.825794+00:00
-- url     : https://prove2.me/submissions/55de35bd-82a1-460a-b0b9-d49492ed34aa

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AePolynomialNonvanishing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AePoly
namespace GlobalTheory.CompanionTheory.AePoly
theorem _root_.solution (M n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm
      (volume : Measure (Fin M → Fin n → ℂ)) (volume : Measure (Fin M × Fin n → ℂ)) := by
  refine ⟨(MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm.measurable, ?_⟩
  refine (Measure.pi_eq (μ := fun _ : Fin M × Fin n => (volume : Measure ℂ)) fun s hs => ?_).symm
  rw [MeasurableEquiv.map_apply]
  have h : (MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun a => Set.univ.pi fun k => s (a, k) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]
    rfl
  rw [h, volume_pi, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [← Fintype.prod_prod_type']
end GlobalTheory.CompanionTheory.AePoly
