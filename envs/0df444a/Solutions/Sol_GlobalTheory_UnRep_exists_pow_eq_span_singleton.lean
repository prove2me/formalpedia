-- Prove2me | solution 1 for GlobalTheory.UnRep.exists_pow_eq_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:45:04.668028+00:00
-- url     : https://prove2.me/submissions/a737cb3a-095f-41eb-8532-4bcca8b62f4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep
namespace GlobalTheory.UnRep
theorem _root_.solution (E : Type) [Field E] [NumberField E] (a : Ideal (𝓞 E))
    (ha : a ≠ ⊥) : ∃ (h : ℕ) (s : 𝓞 E), h ≠ 0 ∧ a ^ h = Ideal.span {s} := by
  have ha0 : a ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero ha
  have hone : ClassGroup.mk0 ⟨a, ha0⟩ ^ Fintype.card (ClassGroup (𝓞 E)) = 1 := pow_card_eq_one
  rw [← map_pow, SubmonoidClass.mk_pow] at hone
  have hprin : (a ^ Fintype.card (ClassGroup (𝓞 E))).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff _).mp hone
  exact ⟨Fintype.card (ClassGroup (𝓞 E)), Submodule.IsPrincipal.generator _, Fintype.card_ne_zero,
    (Ideal.span_singleton_generator _).symm⟩
end GlobalTheory.UnRep
