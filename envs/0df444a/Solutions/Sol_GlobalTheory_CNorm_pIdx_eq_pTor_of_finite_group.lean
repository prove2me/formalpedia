-- Prove2me | solution 1 for GlobalTheory.CNorm.pIdx_eq_pTor_of_finite_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:56.905345+00:00
-- url     : https://prove2.me/submissions/8d48f0a2-c9b4-49dd-a60d-413b499ea2a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowImageUnitsCongruentOneModOfIsAdicCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexOneUnitsMulEqCardQuotientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowRelIndexUnitsOfIsAdicComplete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution (p : ℕ) {G : Type} [CommGroup G] [Finite G]
    (U : Subgroup G) : pTor p U ≠ 0 ∧ pIdx p U = pTor p U := by
  have h1 : pTor p U = Nat.card (powMonoidHom p : U →* U).ker := by
    unfold pTor
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
        invFun := fun y => ⟨y.1.1, y.1.2, congrArg Subtype.val y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h2 : pIdx p U = (powMonoidHom p : U →* U).range.index := by
    unfold pIdx pows Subgroup.relIndex
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext h⟩
    · rintro ⟨y, h⟩
      exact ⟨y.1, y.2, congrArg Subtype.val h⟩
  have h3 := (powMonoidHom p : U →* U).range.card_mul_index
  have h4 := (powMonoidHom p : U →* U).ker.card_mul_index
  rw [Subgroup.index_ker] at h4
  have h5 : Nat.card (powMonoidHom p : U →* U).range ≠ 0 := Nat.card_pos.ne'
  refine ⟨h1 ▸ Nat.card_pos.ne', ?_⟩
  rw [h1, h2]
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h5)
  rw [h3, ← h4, mul_comm]
end GlobalTheory.CNorm
