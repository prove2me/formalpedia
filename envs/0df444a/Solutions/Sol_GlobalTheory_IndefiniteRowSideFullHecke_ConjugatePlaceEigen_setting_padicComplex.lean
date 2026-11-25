-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.setting_padicComplex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:45.256933+00:00
-- url     : https://prove2.me/submissions/3a7adde9-b13b-4db0-8315-047c66286d24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ConjugatePlaceEigen
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ConjugatePlaceEigen_valuation_coe_eq_norm
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ConjugatePlaceEigen_norm_p
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ConjugatePlaceEigen_inv_p_lt_one
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ConjugatePlaceEigen_isAdicComplete

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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out
open Ideal
variable (p : ℕ) [hp : Fact p.Prime]
namespace GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen
theorem _root_.solution : HidaSetting p (PadicComplex.valued p).v 𝓞_ℂ_[p] where
  prime := hp.out
  algClosed := inferInstance
  charZero := inferInstance
  integers := PadicComplexInt.integers p
  p_lt := by
    have h := valuation_coe_eq_norm p ((p : ℕ) : ℂ_[p])
    rw [norm_p] at h
    have h1 := inv_p_lt_one p
    rw [← h] at h1
    exact_mod_cast h1
  complete := isAdicComplete p
end GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen
