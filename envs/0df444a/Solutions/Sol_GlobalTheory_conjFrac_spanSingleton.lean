-- Prove2me | solution 1 for GlobalTheory.conjFrac_spanSingleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:43.536253+00:00
-- url     : https://prove2.me/submissions/e39372cf-4b60-464f-bb3a-bb3cfcf35c5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul



set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open scoped nonZeroDivisors
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory
theorem _root_.solution (x : E) :
    conjFrac (FractionalIdeal.spanSingleton (𝓞 E)⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (cc x) := by
  ext y
  rw [mem_conjFrac, FractionalIdeal.mem_spanSingleton, FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨IsCMField.ringOfIntegersComplexConj E z, ?_⟩
    rw [← cc_cc y, ← hz, Algebra.smul_def, Algebra.smul_def, cc_mul]; rfl
  · rintro ⟨z, hz⟩
    refine ⟨IsCMField.ringOfIntegersComplexConj E z, ?_⟩
    rw [← hz, Algebra.smul_def, Algebra.smul_def, cc_mul, cc_cc]; rfl
end GlobalTheory
