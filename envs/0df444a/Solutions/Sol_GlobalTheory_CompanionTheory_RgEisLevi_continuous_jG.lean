-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.continuous_jG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:10:47.554481+00:00
-- url     : https://prove2.me/submissions/d5fb5a84-086a-4c12-ac6e-dbfa72e01903

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (σ : R →+* R) (hσ : Continuous σ) : Continuous (jG σ : GL ι R → GL (ι ⊕ ι) R) := by
  have hm : Continuous fun m : GL ι R => (m : Matrix ι ι R) := Units.continuous_val
  have hi : Continuous fun m : GL ι R => ((m⁻¹ : GL ι R) : Matrix ι ι R) := Units.continuous_val.comp continuous_inv
  rw [Units.continuous_iff]
  exact ⟨hm.matrix_fromBlocks continuous_const continuous_const (hi.matrix_transpose.matrix_map hσ),
    hi.matrix_fromBlocks continuous_const continuous_const (hm.matrix_transpose.matrix_map hσ)⟩
end GlobalTheory.CompanionTheory.RgEisLevi
