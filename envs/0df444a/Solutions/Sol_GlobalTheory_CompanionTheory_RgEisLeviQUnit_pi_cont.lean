-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.pi_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:37.048197+00:00
-- url     : https://prove2.me/submissions/c28482a1-fd95-4c09-ae90-13175a6a9ca5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ)
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (hσ : ∀ x, A.σ (A.σ x) = x) : Continuous (piQ (s := s) A ε hσ) := by
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_submatrix _ _
  · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_submatrix _ _
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
