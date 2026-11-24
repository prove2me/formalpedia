-- Prove2me | solution 1 for GlobalTheory.existsUnique_of_compatible_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:13.344887+00:00
-- url     : https://prove2.me/submissions/0926b779-580a-4e54-ad37-0c48c3e6aae4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct
variable {R : Type*} [CommRing R] (I : Ideal R)
namespace GlobalTheory
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module R M]
    [IsAdicComplete I M] {C : ℕ → Type*} (π : ∀ n, M → C n)
    (hπ : ∀ n, Function.Surjective (π n))
    (hker : ∀ n x y, π n x = π n y ↔ x - y ∈ (I ^ n • ⊤ : Submodule R M))
    (t : ∀ n, C (n + 1) → C n) (ht : ∀ n x, t n (π (n + 1) x) = π n x)
    (c : ∀ n, C n) (hc : ∀ n, t n (c (n + 1)) = c n) : ∃! x : M, ∀ n, π n x = c n := by
  choose x hx using fun n ↦ hπ n (c n)
  have hcauchy : ∀ {m n}, m ≤ n → x m ≡ x n [SMOD (I ^ m • ⊤ : Submodule R M)] := by
    refine (AdicCompletion.isAdicCauchy_iff I M x).2 fun n ↦ ?_
    rw [SModEq.sub_mem, ← hker, hx, ← ht, hx, hc]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) x hcauchy
  have hLc : ∀ n, π n L = c n := fun n ↦ by
    rw [← hx, hker, ← SModEq.sub_mem]
    exact (hL n).symm
  refine ⟨L, hLc, fun y hy ↦ sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun n ↦ ?_)⟩
  rw [SModEq.zero, ← hker, hy, hLc]
end GlobalTheory
