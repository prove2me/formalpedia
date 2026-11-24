-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.opE_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:37:15.475954+00:00
-- url     : https://prove2.me/submissions/fbfb829a-c574-41bd-8339-932e44fef071

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Kloc_Fresnel_pairing_eq

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
theorem _root_.solution (C s : ℂ) (hs : s ≠ 0) (hω : ‖s / ‖s‖‖ = 1) (κ : ℝ)
    (hκ : ∀ F : EuclideanSpace ℂ (Fin m × Fin n) → ℂ,
      ∫ u : Fin m → Fin n → ℂ, F (matEquiv m n u) = κ * ∫ y, F y)
    (g : EuclideanSpace ℂ (Fin m × Fin n) → ℂ) :
    opE C s (g ∘ matEquiv m n) =
      kerOp (C * κ) ‖s‖ (unitMul _ (s / ‖s‖) hω) g ∘ matEquiv m n := by
  funext u
  simp only [opE, Function.comp, kerOp, pairing_eq s hs hω]
  rw [hκ (fun y => cexp (2 * Real.pi * I * ((‖s‖ * inner ℝ (matEquiv m n u)
    (unitMul _ (s / ‖s‖) hω y) : ℝ) : ℂ)) * g y)]
  ring
end GlobalTheory.CompanionTheory.Kloc.Fresnel
