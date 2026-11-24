-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:14.634898+00:00
-- url     : https://prove2.me/submissions/4fec7045-ce69-4480-b133-da7f1485822c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_block_unit

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
variable {R : Type} [CommRing R]
open Classical
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution {α : Type} [Fintype α] [DecidableEq α] (S : Set α) (g : GL α R) (hg : g ∈ stab R S) :
    ((bdet S g : Rˣ) : R) = ((g : Matrix α α R).submatrix (Subtype.val : S → α) Subtype.val).det := by
  unfold bdet
  rw [dif_pos (block_unit g hg)]
  rfl
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
