-- Prove2me | solution 1 for GlobalTheory.finsum_neg_one_pow_hdim_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:13:17.570606+00:00
-- url     : https://prove2.me/submissions/05e38542-df2c-49af-890f-900d6b6e5e1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_cohOn___map_6ba3242e7e5e
import Theorems.Thm_P2M_GlobalTheory_cohOn_map___8dd9b9fe2c60
import Theorems.Thm_GlobalTheory_SheafLES_map_id
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_hom
import Theorems.Thm_GlobalTheory_SheafLES_res_id
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_map_hom
import Theorems.Thm_GlobalTheory_SheafLES_toAbSheaf_obj_obj
import Theorems.Thm_GlobalTheory_hdim_eq_zero_of_subsingleton
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
import Theorems.Thm_P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SheafLES.map_id
attribute [local simp] GlobalTheory.SheafLES.map_zero_hom
attribute [local simp] GlobalTheory.SheafLES.res_id
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_map_hom
attribute [local simp] GlobalTheory.SheafLES.toAbSheaf_obj_obj
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply
attribute [local simp] P2M_GlobalTheory_SheafLES___map_026ec4bafb10
attribute [local simp] P2M_GlobalTheory_SheafLES_map___ee3a67e9aebf


attribute [local simp] GlobalTheory.cohOn.δ_map
attribute [local simp] GlobalTheory.cohOn.map_δ

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS
omit hS
namespace GlobalTheory
theorem _root_.solution (F : X.Modules) (N : ℕ)
    (hN : ∀ i, N ≤ i → Subsingleton (coh F i)) :
    ∑ᶠ i, (-1 : ℤ) ^ i * hdim k F i = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k F i := by
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  by_contra h
  have := hN i (by simpa using h)
  exact hi (by simp [hdim_eq_zero_of_subsingleton])
end GlobalTheory
