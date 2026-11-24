-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.jM_off_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:32.548815+00:00
-- url     : https://prove2.me/submissions/5ab55b37-9e22-4cb9-9886-01178e86fd5d

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
variable {α κ β : Type} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (e : κ → α) (m : Matrix κ κ R) (a b : α) (h : a ∉ Set.range e) :
    jM e m a b = (1 : Matrix α α R) a b := by
  have h0 : ∀ y, Pm R e a y = 0 := fun y => by
    have : a ≠ e y := fun hh => h ⟨y, hh.symm⟩
    simp [Pm_apply, this]
  unfold jM
  rw [Matrix.add_apply, Matrix.mul_assoc, Matrix.mul_apply, Dm_apply, Matrix.one_apply]
  simp [h0, h]
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
