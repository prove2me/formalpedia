-- Prove2me | solution 1 for GlobalTheory.PeriodTate.rt_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:52.078888+00:00
-- url     : https://prove2.me/submissions/194a8dbf-b059-4787-8272-18ec490b3259

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsTateIsoOfPeriods
import Theorems.Thm_GlobalTheory_PeriodTate_rt_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.PeriodTate
namespace GlobalTheory.PeriodTate
theorem _root_.solution {n : ℕ} (hn : 0 < n) {x y : ℤ} (h : (n : ℤ) ∣ x - y) : rt n x = rt n y := by
  obtain ⟨c, hc⟩ := h
  apply Units.ext
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [rt_val, rt_val, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-c, ?_⟩
  rw [sub_eq_iff_eq_add.1 hc]
  push_cast
  field_simp
  ring
end GlobalTheory.PeriodTate
