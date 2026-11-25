-- Prove2me | solution 1 for GlobalTheory.BorelUMod.zpow_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:30:35.193659+00:00
-- url     : https://prove2.me/submissions/d783f844-8e8f-4b78-9124-6f028284b960

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
import Theorems.Thm_GlobalTheory_AbelianSumIdentityFirst_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.BorelUMod
theorem _root_.solution {ι : Type} {z : ℂ} (hz : z ≠ 0) (s : Finset ι) (a : ι → ℤ) :
    z ^ ∑ i ∈ s, a i = ∏ i ∈ s, z ^ a i := by
  first
  | exact @_root_.GlobalTheory.AbelianSumIdentityFirst.main
  | exact _root_.GlobalTheory.AbelianSumIdentityFirst.main
  | (apply _root_.GlobalTheory.AbelianSumIdentityFirst.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AbelianSumIdentityFirst.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AbelianSumIdentityFirst.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AbelianSumIdentityFirst.main ..)
end GlobalTheory.BorelUMod
