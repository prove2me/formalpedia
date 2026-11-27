-- Prove2me | solution 1 for GlobalTheory.IdemRange.uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:58:24.857963+00:00
-- url     : https://prove2.me/submissions/a1db7fc7-d889-4161-a683-f2a341ba4b65

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEmbeddingCongrIntegralCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RingHomEqOfCongruentIntegralUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenvectorOfGeneralizedEigenUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCharacterGeneralizedEigenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LimitIdempotentRangeLeSumEigenspaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.IdemRange
variable {C : Type} [Field C] {V : VF C}
variable {κ : Type} [Fintype κ] [DecidableEq κ]
omit [DecidableEq κ]
namespace GlobalTheory.IdemRange
theorem _root_.solution {P : κ → ℕ → Prop} (h : ∀ i, ∃ n0 : ℕ, ∀ n ≥ n0, P i n) :
    ∃ n0 : ℕ, ∀ n ≥ n0, ∀ i, P i n := by
  choose b hb using h
  refine ⟨∑ i, b i, fun n hn i => hb i n (le_trans ?_ hn)⟩
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
end GlobalTheory.IdemRange
