-- Prove2me | solution 2 for GlobalTheory.tensorContent_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:27.190356+00:00
-- url     : https://prove2.me/submissions/55c05851-a99a-4299-aba5-471cd47b6ea0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
import Theorems.Thm_GlobalTheory_polyContent_le_iff
import Theorems.Thm_GlobalTheory_tensorContent_eq_polyContent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial Module
variable {O R S Γ₀ ι κ σ : Type*} [CommRing O] [CommRing R] [Algebra O R] [CommRing S]
  [Algebra O S] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
  {M : Type*} [AddCommGroup M] [Module O M] (b : Basis ι O M)
namespace GlobalTheory
theorem _root_.solution {x : MvPolynomial σ R ⊗[O] M} {γ : Γ₀} :
    tensorContent v b x ≤ γ ↔ ∀ m, basisVal v (b.baseChange R) (tensorCoeffs x m) ≤ γ := by
  rw [tensorContent_eq_polyContent, polyContent_le_iff]
end GlobalTheory
