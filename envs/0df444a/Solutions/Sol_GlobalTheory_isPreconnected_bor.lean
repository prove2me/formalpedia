-- Prove2me | solution 1 for GlobalTheory.isPreconnected_bor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:52:16.263852+00:00
-- url     : https://prove2.me/submissions/2bc97871-df05-4c3b-9002-58bc07bfe116

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OmFConnPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousRmulPair
import Theorems.Thm_GlobalTheory_bor_eq_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) (r : ℕ) : IsPreconnected (Bor Ψ r) := by
  rw [bor_eq_pi]
  refine isPreconnected_univ_pi fun _ => isPreconnected_univ_pi fun a =>
    isPreconnected_univ_pi fun c => ?_
  split_ifs
  · exact isPreconnected_singleton
  · refine (isConnected_compl_singleton_of_one_lt_rank ?_ (0 : ℂ)).isPreconnected
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  · exact isPreconnected_univ
end GlobalTheory
