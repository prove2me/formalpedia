-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Pairing.sum_perfect_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:55:20.130137+00:00
-- url     : https://prove2.me/submissions/bbee2c1e-696b-4089-bd31-3687c3f5358e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SumPerfectApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Pairing
namespace GlobalTheory.CompanionTheory.Pairing
theorem _root_.solution {R : Type} [CommRing R] {ι : Type} [Fintype ι] {X Y : ι → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] [∀ i, AddCommGroup (Y i)]
    [∀ i, Module R (Y i)] (B : ∀ i, Y i →ₗ[R] X i →ₗ[R] R)
    (y : ∀ i, Y i) (x : ∀ i, X i) :
    (∑ i, (B i).compl₁₂ (LinearMap.proj i : (∀ i, Y i) →ₗ[R] Y i)
      (LinearMap.proj i : (∀ i, X i) →ₗ[R] X i)) y x = ∑ i, B i (y i) (x i) := by
  simp [LinearMap.sum_apply]
end GlobalTheory.CompanionTheory.Pairing
