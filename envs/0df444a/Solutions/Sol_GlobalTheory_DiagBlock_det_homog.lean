-- Prove2me | solution 1 for GlobalTheory.DiagBlock.det_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:10.204318+00:00
-- url     : https://prove2.me/submissions/8a12c9a7-397c-46d7-8d17-631e8dcea553

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution {C : Type} [Field C] {σ : Type} {n : ℕ} (w : σ → ℕ) (f : Fin n → Fin n → σ)
    (r : Fin n → ℕ) (h : ∀ b c, w (f b c) = r b) :
    (Matrix.of fun b c : Fin n =>
      (MvPolynomial.X (f b c) : MvPolynomial σ C)).det.IsWeightedHomogeneous w (∑ b, r b) := by
  rw [Matrix.det_apply, ← MvPolynomial.mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun τ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun i => (Matrix.of fun b c : Fin n => (MvPolynomial.X (f b c) : MvPolynomial σ C)) (τ i) i)
    (fun i => r (τ i)) (w := w) (fun i _ => by
      simpa [Matrix.of_apply, h] using MvPolynomial.isWeightedHomogeneous_X C w (f (τ i) i))
  rwa [Equiv.sum_comp τ r] at hprod
end GlobalTheory.DiagBlock
