-- Prove2me | solution 1 for GroundTheory.LocalField.unitsEquivIntProd_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:40.770797+00:00
-- url     : https://prove2.me/submissions/09e8a756-c7d8-4474-9d9c-b91dbcad48e7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_eq_exp_ord
import Theorems.Thm_GroundTheory_LocalField_unitsEquivIntProd_symm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (x : Kˣ) :
    (unitsEquivIntProd hϖ x).1 = Multiplicative.ofAdd (ord (x : K)) := by
  set p := unitsEquivIntProd hϖ x
  have hx : x = unitsOfIntProd hϖ p := by
    rw [← unitsEquivIntProd_symm_apply, MulEquiv.symm_apply_apply]
  have hv := normalizedValuation_eq_exp_ord x.ne_zero
  rw [hx, normalizedValuation_unitsOfIntProd, WithZero.exp_inj, neg_inj] at hv
  simp only [← hx] at hv
  rw [← hv]
  rfl
end GroundTheory.LocalField
