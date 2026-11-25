-- Prove2me | solution 1 for GlobalTheory.LevelTupleSum.Gen.of_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:38.662049+00:00
-- url     : https://prove2.me/submissions/7264c5a0-67f0-4232-a124-fb28497c42ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelTupleSumEqRational
import Theorems.Thm_GlobalTheory_LevelTupleSum_coe_smul_mem
import Theorems.Thm_GlobalTheory_LevelTupleSum_nat_smul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.LevelTupleSum
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [IsCMField E]
namespace GlobalTheory.LevelTupleSum
namespace Gen
theorem _root_.solution {Λ : Submodule (𝓞 E) (Fin r → E)} {t t' : Fin r → Fin r → E} (h : Gen Λ t)
    (hs : ∀ j, t j - t' j ∈ Λ) : Gen Λ t' := by
  refine ⟨fun j => ?_, fun u hu => ?_⟩
  · have h1 : (25 : E) • (t j - t' j) ∈ Λ := by simpa using nat_smul_mem Λ 25 (hs j)
    have : (25 : E) • t' j = (25 : E) • t j - (25 : E) • (t j - t' j) := by module
    rw [this]
    exact Λ.sub_mem (h.1 j) h1
  · obtain ⟨c, y, hy, rfl⟩ := h.2 u hu
    refine ⟨c, y + ∑ j, (c j : E) • ((5 : E) • (t j - t' j)), Λ.add_mem hy (Λ.sum_mem fun j _ =>
      coe_smul_mem Λ _ (by simpa using nat_smul_mem Λ 5 (hs j))), ?_⟩
    rw [smul_add, Finset.smul_sum, add_comm ((5 : E) • y), ← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    module
end Gen
end GlobalTheory.LevelTupleSum
