-- Prove2me | solution 1 for GlobalTheory.T.stabilizer_relIndex_ne_zero_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:31.774605+00:00
-- url     : https://prove2.me/submissions/bba090e3-ad3b-4d1f-aaf3-871d1f66a9d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StabilizerRelIndexNeZeroParabolic
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StabilizerRelIndexNeZeroParabolicStatement
import Theorems.Thm_GlobalTheory_stab_relIndex_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ TM : Subgroup M, (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ (q : M) (X : N), (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) ≠ 0 := by
  first | exact @GlobalTheory.stab_relIndex_ne_zero | exact GlobalTheory.stab_relIndex_ne_zero | (intros; apply GlobalTheory.stab_relIndex_ne_zero <;> assumption)
end _root_.GlobalTheory.T
