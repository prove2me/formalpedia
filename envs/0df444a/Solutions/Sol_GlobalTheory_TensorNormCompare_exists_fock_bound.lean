-- Prove2me | solution 1 for GlobalTheory.TensorNormCompare.exists_fock_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:25:29.164999+00:00
-- url     : https://prove2.me/submissions/815c2955-838b-4419-8661-db73dea3c5e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorPlaceNorm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorNormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TensorNormLeIffTensorNormBound
import Theorems.Thm_GlobalTheory_TensorNormCompare_exists_norm_bound

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
theorem _root_.solution {σ σ' : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ S]
    (A : S →ₗ[ℂ] MvPolynomial σ' ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : S, (fockS (A f) (A f)).re ≤ C * (fockS f.1 f.1).re := by
  exact @exists_norm_bound _ _ (fockCore σ).toNormedAddCommGroup (InnerProductSpace.ofCore (fockCore σ).toCore)
    (fockCore σ').toNormedAddCommGroup (InnerProductSpace.ofCore (fockCore σ').toCore) S ‹_› A
end GlobalTheory.TensorNormCompare
