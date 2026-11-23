-- Prove2me | solution 1 for GlobalTheory.SW.Base.ccT_mem_DH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:41.369344+00:00
-- url     : https://prove2.me/submissions/a0193a60-8b8e-4719-b643-9878521f8191

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Theorems.Thm_GlobalTheory_SW_Base_isIntegral_cc
import Theorems.Thm_GlobalTheory_SW_Base_ccT_ccT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open GlobalTheory.SW.Base
namespace GlobalTheory.SW.Base
theorem _root_.solution {M : ℕ} {h : Matrix (Fin n) (Fin n) E} (hh : h ∈ DH E n M) :
    ccT h ∈ DH E n M := by
  obtain ⟨hu, s, hs, hsM, y, hy, e⟩ := hh
  refine ⟨by rw [ccT_ccT]; exact mul_eq_one_comm.1 hu, s, hs, hsM, ccT y,
    fun i j => isIntegral_cc (hy j i), ?_⟩
  ext i j
  have := congrArg cc (congrFun (congrFun e j) i)
  by_cases hij : i = j
  · subst hij; simpa [ccT, cc] using this
  · simpa [ccT, cc, Matrix.one_apply, hij, Ne.symm hij] using this
end GlobalTheory.SW.Base
