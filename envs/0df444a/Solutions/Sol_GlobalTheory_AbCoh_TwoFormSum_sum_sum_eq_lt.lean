-- Prove2me | solution 1 for GlobalTheory.AbCoh.TwoFormSum.sum_sum_eq_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:11:16.115558+00:00
-- url     : https://prove2.me/submissions/a7a4d295-c083-4c2d-b70a-a902f7f19058

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalTwoFormEqSumWedgeGlobalOneForms
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.TwoFormSum
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
namespace GlobalTheory.AbCoh.TwoFormSum
theorem _root_.solution {M : Type} [AddCommGroup M] {n : ℕ} (g : Fin n → Fin n → M) (hg : ∀ i, g i i = 0) :
    ∑ i, ∑ j, g i j = ∑ i, ∑ j, (if i < j then g i j + g j i else 0) := by
  calc ∑ i, ∑ j, g i j
      = ∑ i, ∑ j, ((if i < j then g i j else 0) + (if j < i then g i j else 0)) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rcases lt_trichotomy i j with h | h | h
        · simp [h, not_lt.2 h.le]
        · subst h; simp [hg]
        · simp [h, not_lt.2 h.le]
    _ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if j < i then g i j else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_add_distrib
    _ = ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if i < j then g j i else 0) := by
        rw [Finset.sum_comm (f := fun i j ↦ if j < i then g i j else 0)]
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> simp
end GlobalTheory.AbCoh.TwoFormSum
