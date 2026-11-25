-- Prove2me | solution 1 for GlobalTheory.BorelUMod.sum_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:30:24.530209+00:00
-- url     : https://prove2.me/submissions/0de7da51-e740-468f-ad86-f5e32a478413

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealWeight
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
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.BorelUMod
theorem _root_.solution (a : Fin n → ℤ) (ha : ∀ i, a i.rev = -a i) :
    ∑ i, a i * ((n : ℤ) - 1 - 2 * i.val) =
      2 * ∑ i : Fin (n / 2), a (Fin.castLE (Nat.div_le_self n 2) i) * ((n : ℤ) - 1 - 2 * i.val) := by
  have h1 : ∑ i : Fin (n / 2), a (Fin.castLE (Nat.div_le_self n 2) i) * ((n : ℤ) - 1 - 2 * i.val) =
      ∑ i : Fin n, if i.val < n / 2 then a i * ((n : ℤ) - 1 - 2 * i.val) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun i _ => Fin.castLE (Nat.div_le_self n 2) i) (fun i _ => by simp)
      (fun i _ j _ e => Fin.castLE_injective _ e) (fun j hj => ⟨⟨j.val, by simpa using hj⟩, by simp, rfl⟩)
      fun i _ => rfl
  rw [two_mul]
  nth_rewrite 2 [h1]
  rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin n => if i.val < n / 2 then a i * ((n : ℤ) - 1 - 2 * i.val) else 0),
    h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.2
  have hr : ((i.rev.val : ℕ) : ℤ) = n - 1 - i.val := by rw [Fin.val_rev]; omega
  simp only [Fin.revPerm_apply, ha, hr]
  split_ifs with h1 h2 h2
  · omega
  · ring
  · ring
  · have : (n : ℤ) - 1 - 2 * i.val = 0 := by omega
    simp [this]
end GlobalTheory.BorelUMod
