-- Prove2me | solution 1 for IntermediateField.finrank_adjoin_rootsOfUnity_eq_card_rootSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ad2c4b34-6e5e-5168-bfba-61d4cd359cfd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_finrank_adjoin_rootsOfUnity_eq_card_rootSet

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField
open Polynomial

theorem solution {F E : Type} [Field F] [Field E] [Algebra F E] [IsAlgClosed E] [CharZero F] (m : ℕ) (hm : 0 < m) (ζ₀ : E)
    (hζ₀ : IsPrimitiveRoot ζ₀ m) :
    Module.finrank F (IntermediateField.adjoin F {ζ : E | ζ ^ m = 1})
      = Fintype.card ((minpoly F ζ₀).rootSet E) := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  have hint : IsIntegral F ζ₀ := IsIntegral.of_pow hm (by rw [hζ₀.pow_eq_one]; exact isIntegral_one)
  have h1 : IntermediateField.adjoin F {ζ : E | ζ ^ m = 1} = F⟮ζ₀⟯ := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro ζ hζ
      obtain ⟨i, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
      exact pow_mem (IntermediateField.mem_adjoin_simple_self F ζ₀) i
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin F _ hζ₀.pow_eq_one
  rw [LinearEquiv.finrank_eq (IntermediateField.equivOfEq h1).toLinearEquiv, IntermediateField.adjoin.finrank hint,
    Polynomial.card_rootSet_eq_natDegree (minpoly.irreducible hint).separable (IsAlgClosed.splits _)]

end S_IntermediateField_finrank_adjoin_rootsOfUnity_eq_card_rootSet
end P2MW
export P2MW.S_IntermediateField_finrank_adjoin_rootsOfUnity_eq_card_rootSet (solution)
