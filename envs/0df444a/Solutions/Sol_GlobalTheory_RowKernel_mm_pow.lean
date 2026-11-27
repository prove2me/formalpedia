-- Prove2me | solution 1 for GlobalTheory.RowKernel.mm_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:31:30.902643+00:00
-- url     : https://prove2.me/submissions/3deb6685-e75a-454d-956e-224038ab786d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSaturatedGoodVectorsSmallCorankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodCurvesPairingMemMaxIdealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupKernelSmallOfSecond
import Theorems.Thm_GlobalTheory_RowKernel_mm_int_mul
import Theorems.Thm_GlobalTheory_RowKernel_mm_ge
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowKernel
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.RowKernel
theorem _root_.solution {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.MM a) : V.MM (a ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]
  exact mm_int_mul ((mm_ge h).pow m) h
end GlobalTheory.RowKernel
