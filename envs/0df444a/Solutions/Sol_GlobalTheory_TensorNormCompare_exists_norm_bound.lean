-- Prove2me | solution 1 for GlobalTheory.TensorNormCompare.exists_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:27:44.027906+00:00
-- url     : https://prove2.me/submissions/f8ae90cc-f0f7-456e-88fb-06f6db811869

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorPlaceNorm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorNormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TensorNormLeIffTensorNormBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.TensorNormCompare
open Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke
variable {ι : Type} [Fintype ι] {n n' : ℕ}
namespace GlobalTheory.TensorNormCompare
theorem _root_.solution {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (S : Submodule ℂ E) [FiniteDimensional ℂ S] (A : S →ₗ[ℂ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : S, (inner ℂ (A f) (A f)).re ≤ C * (inner ℂ f.1 f.1).re := by
  let B := LinearMap.toContinuousLinearMap A
  refine ⟨‖B‖ ^ 2, by positivity, fun f => ?_⟩
  have h1 : (inner ℂ (A f) (A f)).re = ‖A f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (A f)
  have h2 : (inner ℂ f.1 f.1).re = ‖f.1‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f.1
  have h3 : ‖A f‖ ≤ ‖B‖ * ‖f.1‖ := B.le_opNorm f
  rw [h1, h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2
end GlobalTheory.TensorNormCompare
