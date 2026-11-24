-- Prove2me | solution 1 for GlobalTheory.exists_forall_eq_pow_of_finite_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:25.676846+00:00
-- url     : https://prove2.me/submissions/95b999e0-e54b-4ab0-b7f3-01c3aaeddc5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusPowerEmbeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F]
    (k : Type) [Field k] [CharP k p] (a b : F →+* k) : ∃ n : ℕ, ∀ x, b x = a x ^ p ^ n := by
  have : CharP F p := RingHom.charP a a.injective p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let : Algebra F k := a.toAlgebra
  have : IsScalarTower (ZMod p) F k :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let b' : F →ₐ[ZMod p] k :=
    { b with
      commutes' := fun r => RingHom.congr_fun
        (Subsingleton.elim (b.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) k)) r }
  obtain ⟨n, hn⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod p) p F (b'.restrictNormal' F)
  refine ⟨n, fun x => ?_⟩
  have h := AlgHom.restrictNormal_commutes b' F x
  have h2 : b'.restrictNormal F x = x ^ p ^ n := by
    have := hn x
    rw [Nat.card_zmod] at this
    exact this
  rw [h2, map_pow] at h
  exact h.symm
end GlobalTheory
