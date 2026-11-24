-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.exists_trace_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:51:56.576701+00:00
-- url     : https://prove2.me/submissions/0f8d4cd9-1701-4d7e-87ca-3e6231d0e5c1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSpaceAnisotropicUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
namespace GlobalTheory.CompanionTheory.UnrDens
theorem _root_.solution {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
    (hE : ResAlg E τ q ε) {a : E} (ha : a ≠ 0) : ∃ c : E, c * a + τ (c * a) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨u, hu, -⟩ := hE.basis
  have h1 := hcon 1
  have h2 := hcon u
  simp only [one_mul, map_mul] at h1 h2
  have hta : τ a = -a := by linear_combination h1
  rw [hta] at h2
  obtain ⟨w', hw'⟩ := hu.exists_left_inv
  apply ha
  linear_combination w' * h2 - a * hw'
end GlobalTheory.CompanionTheory.UnrDens
