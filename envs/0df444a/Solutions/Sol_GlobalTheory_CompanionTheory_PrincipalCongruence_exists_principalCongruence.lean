-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrincipalCongruence.exists_principalCongruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:42.242907+00:00
-- url     : https://prove2.me/submissions/d8f5c4b0-e004-4f1f-9f28-704796c514d6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrincipalCongruence
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CompanionTheory.PrincipalCongruence
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (t : k), t ≠ 0 → ValuativeRel.valuation k (t) < 1 →
      ∃ H : Subgroup (GL (Fin N) k), (H : Set (GL (Fin N) k)) =
        {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
          ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
            ValuativeRel.valuation k (t)} := by
  intro k _ _ _ _ N t _ ht
  exact ⟨principalCongruence (ValuativeRel.valuation k) _ ht, rfl⟩
end GlobalTheory.CompanionTheory.PrincipalCongruence
