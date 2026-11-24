-- Prove2me | solution 1 for GlobalTheory.BorelUMod.relIndex_upLat_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:34:31.924361+00:00
-- url     : https://prove2.me/submissions/447cfee4-979a-4fd4-92d2-11b538e243b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
import Theorems.Thm_GlobalTheory_BorelUMod_relIndex_prod_prod
import Theorems.Thm_GlobalTheory_BorelUMod_skewPair_injective
import Theorems.Thm_GlobalTheory_BorelUMod_map_skewPair_upLat
import Theorems.Thm_GlobalTheory_BorelUMod_exists_trace_one
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
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
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] {n : ℕ}
variable [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.BorelUMod
theorem _root_.solution : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ (c C : Fin n → Fin n → ℤ), (∀ i j, c j.rev i.rev = c i j) →
    (∀ i j, C j.rev i.rev = C i j) → (∀ i j, i < j → c i j ≤ C i j) →
    (upLat L C).relIndex (upLat L c) = ((upLat L C ⊓ skewJ σ n).relIndex (upLat L c ⊓ skewJ σ n)) ^ 2 := by
  intro L _ _ ϖ σ q n h c C hc hC _
  obtain ⟨⟨θ, hθ, hθ1⟩, d, hd, hd1⟩ := exists_trace_one h
  have hd0 : d ≠ 0 := fun e => by simp [e] at hd
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (skewPair_injective σ θ hd0),
    map_skewPair_upLat h.1 h.2.1 hθ hθ1 hd hd1 hc, map_skewPair_upLat h.1 h.2.1 hθ hθ1 hd hd1 hC,
    relIndex_prod_prod, sq]
end GlobalTheory.BorelUMod
