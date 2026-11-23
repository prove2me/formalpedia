-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.mem_hermC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:09.605686+00:00
-- url     : https://prove2.me/submissions/c169dc49-bcc1-428c-ad2e-8f4e5a36c74c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
open MeasureTheory
open scoped Matrix ComplexConjugate
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
theorem _root_.solution {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} : b ∈ hermC n ↔ b.IsHermitian := by
  unfold hermC
  rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
  exact Iff.rfl
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
