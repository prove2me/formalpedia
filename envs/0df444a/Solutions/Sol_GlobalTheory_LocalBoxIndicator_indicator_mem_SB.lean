-- Prove2me | solution 1 for GlobalTheory.LocalBoxIndicator.indicator_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:01.173865+00:00
-- url     : https://prove2.me/submissions/13a14e0c-d1be-4064-aa51-818a870a5ea9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslateOpenSubgroupsFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.LocalBoxIndicator
namespace GlobalTheory.LocalBoxIndicator
theorem _root_.solution {X : Type} [TopologicalSpace X] {S : Set X} (hcl : IsClopen S) (hco : IsCompact S) :
    Set.indicator S (1 : X → ℂ) ∈ GlobalTheory.WeilM.SB X := by
  classical
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)
end GlobalTheory.LocalBoxIndicator
