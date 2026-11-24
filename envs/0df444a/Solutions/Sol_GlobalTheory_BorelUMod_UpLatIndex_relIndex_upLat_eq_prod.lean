-- Prove2me | solution 1 for GlobalTheory.BorelUMod.UpLatIndex.relIndex_upLat_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:49.912709+00:00
-- url     : https://prove2.me/submissions/1a08eb97-921e-42b5-97b1-d93337b0ce06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Theorems.Thm_GlobalTheory_BorelUMod_mem_upLat
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.UpLatIndex
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.BorelUMod.UpLatIndex
theorem _root_.solution {n : ℕ} (c C : Fin n → Fin n → ℤ) :
    (upLat L C).relIndex (upLat L c) =
      ∏ p : {p : Fin n × Fin n // p.1 < p.2}, (ordBall L (C p.1.1 p.1.2)).relIndex (ordBall L (c p.1.1 p.1.2)) := by
  let f : upLat L c →+ (∀ p : {p : Fin n × Fin n // p.1 < p.2}, ordBall L (c p.1.1 p.1.2) ⧸
      (ordBall L (C p.1.1 p.1.2)).addSubgroupOf (ordBall L (c p.1.1 p.1.2))) :=
    { toFun := fun x p => QuotientAddGroup.mk ⟨x.1 p.1.1 p.1.2, x.2.2 _ _ p.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y => by
    refine ⟨⟨fun i j => if h : i < j then ((y ⟨(i, j), h⟩).out : L) else 0, fun i j h => dif_neg (not_lt.2 h),
      fun i j h => ?_⟩, funext fun p => ?_⟩
    · simp only [dif_pos h]
      exact (y ⟨(i, j), h⟩).out.2
    · refine Eq.trans ?_ (y p).out_eq
      exact congrArg QuotientAddGroup.mk (Subtype.ext (dif_pos p.2))
  have hc : (upLat L C).addSubgroupOf (upLat L c) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, mem_upLat]
    constructor
    · intro h p
      exact (QuotientAddGroup.eq_zero_iff _).2 (h.2 _ _ p.2)
    · intro h
      exact ⟨x.2.1, fun i j e => (QuotientAddGroup.eq_zero_iff _).1 (h ⟨(i, j), e⟩)⟩
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl
end GlobalTheory.BorelUMod.UpLatIndex
