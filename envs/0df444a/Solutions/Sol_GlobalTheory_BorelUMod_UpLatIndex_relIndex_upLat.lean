-- Prove2me | solution 1 for GlobalTheory.BorelUMod.UpLatIndex.relIndex_upLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:52:41.17737+00:00
-- url     : https://prove2.me/submissions/7b921ae5-454e-4ede-b191-ca367f63e9f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Theorems.Thm_GlobalTheory_BorelUMod_UpLatIndex_relIndex_ordBall
import Theorems.Thm_GlobalTheory_BorelUMod_UpLatIndex_relIndex_upLat_eq_prod
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
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.UpLatIndex
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.BorelUMod.UpLatIndex
theorem _root_.solution : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ (c C : Fin n → Fin n → ℤ), (∀ i j, i < j → c i j ≤ C i j) →
    (upLat L C).relIndex (upLat L c) = ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (q ^ 2) ^ (C p.1 p.2 - c p.1 p.2).toNat := by
  intro L _ _ ϖ σ q n h c C hc
  rw [relIndex_upLat_eq_prod, Finset.prod_subtype (p := fun p : Fin n × Fin n => p.1 < p.2) _ (by simp)]
  exact Finset.prod_congr rfl fun p _ => relIndex_ordBall h (hc _ _ p.2)
end GlobalTheory.BorelUMod.UpLatIndex
