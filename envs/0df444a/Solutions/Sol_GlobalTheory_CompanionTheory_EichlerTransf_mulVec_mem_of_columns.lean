-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EichlerTransf.mulVec_mem_of_columns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:00:07.137993+00:00
-- url     : https://prove2.me/submissions/738ea1ff-f6e1-4d76-a32b-241547256c90

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExtendByZeroApplyOfNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EichlerTransf
open scoped ComplexOrder
variable {n m : ℕ}
namespace GlobalTheory.CompanionTheory.EichlerTransf
theorem _root_.solution {p q : ℕ} (G : Submodule ℂ (Fin p → ℂ))
    (M : Matrix (Fin p) (Fin q) ℂ) (h : ∀ i, (fun j => M j i) ∈ G) (z : Fin q → ℂ) :
    M *ᵥ z ∈ G := by
  have e : M *ᵥ z = ∑ i, z i • (fun j => M j i) := by
    ext k; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [e]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (h i))
end GlobalTheory.CompanionTheory.EichlerTransf
