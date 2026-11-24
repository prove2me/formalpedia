-- Prove2me | solution 1 for GlobalTheory.card_hom_vanishing_of_diag_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:24:45.921+00:00
-- url     : https://prove2.me/submissions/512fc40a-a912-48a5-95fc-c2b1e2b19a53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CardHomVanishingOfDiagBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {M A ι : Type} [AddCommGroup M] [AddCommGroup A]
    [Fintype ι] (N : Submodule ℤ M) (b : Basis ι ℤ M) (c : Basis ι ℤ N) (a : ι → ℤ)
    (h : ∀ i, (c i : M) = a i • b i) :
    Nat.card {f : M →ₗ[ℤ] A // ∀ x ∈ N, f x = 0} = ∏ i, Nat.card {y : A // a i • y = 0} := by
  rw [← Nat.card_pi, ← Nat.card_congr (Equiv.subtypePiEquivPi (p := fun i (y : A) => a i • y = 0))]
  symm
  refine Nat.card_congr ((b.constr ℤ).toEquiv.subtypeEquiv fun y => ?_)
  constructor
  · intro hy x hx
    have : (b.constr ℤ y) ∘ₗ N.subtype = 0 := c.ext fun i => by
      simp [h, hy, -Basis.constr_apply_fintype]
    exact LinearMap.congr_fun this ⟨x, hx⟩
  · intro hy i
    have := hy _ (c i).2
    simpa [h, -Basis.constr_apply_fintype] using this
end GlobalTheory
