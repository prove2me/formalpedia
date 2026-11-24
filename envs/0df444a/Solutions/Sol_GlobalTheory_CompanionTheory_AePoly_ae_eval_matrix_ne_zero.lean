-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AePoly.ae_eval_matrix_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:31:34.381971+00:00
-- url     : https://prove2.me/submissions/e1cc68b4-7c37-42aa-97b9-741d7368d3ba

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AePolynomialNonvanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_AePoly_ae_eval_ne_zero_fin
import Theorems.Thm_GlobalTheory_CompanionTheory_AePoly_measurePreserving_uncurry

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
theorem _root_.solution : ∀ (M n : ℕ) (Q : MvPolynomial (Fin M × Fin n) ℂ), Q ≠ 0 →
    ∀ᵐ C ∂(volume : Measure (Fin M → Fin n → ℂ)), MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 := by
  intro M n Q hQ
  have hQ' : MvPolynomial.rename (finProdFinEquiv : Fin M × Fin n ≃ Fin (M * n)) Q ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.rename_injective _ finProdFinEquiv.injective)).2 hQ
  have h1 := ae_eval_ne_zero_fin _ _ hQ'
  have h2 := (volume_measurePreserving_piCongrLeft (fun _ : Fin (M * n) => ℂ)
    (finProdFinEquiv : Fin M × Fin n ≃ Fin (M * n))).quasiMeasurePreserving.ae h1
  have h3 := (measurePreserving_uncurry M n).quasiMeasurePreserving.ae h2
  filter_upwards [h3] with C hC
  rw [MvPolynomial.eval_rename] at hC
  have hfun : (MeasurableEquiv.piCongrLeft (fun _ : Fin (M * n) => ℂ)
      (finProdFinEquiv : Fin M × Fin n ≃ Fin (M * n))
      ((MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm C)) ∘ finProdFinEquiv =
      fun p => C p.1 p.2 := by
    funext p
    simp only [Function.comp]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl
  rwa [hfun] at hC
end GlobalTheory.CompanionTheory.AePoly
