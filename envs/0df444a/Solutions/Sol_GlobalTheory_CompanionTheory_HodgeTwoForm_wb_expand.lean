-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeTwoForm.wb_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:53.296454+00:00
-- url     : https://prove2.me/submissions/800825a2-67b5-455a-8332-4edb24f387b7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_sum_pairs
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wb_self
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wb_swap
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeTwoForm
variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}
namespace GlobalTheory.CompanionTheory.HodgeTwoForm
theorem _root_.solution (e : Fin n → M) (L : Fin n → Module.Dual A M) (h : ∀ x, x = ∑ i, L i x • e i)
    (a b : M) :
    wb (A := A) a b = ∑ i, ∑ j ∈ Finset.Ioi i, (L i a * L j b - L j a * L i b) • wb (A := A) (e i) (e j) := by
  have h1 : wb (A := A) a b = ∑ i, ∑ j, (L i a * L j b) • wb (A := A) (e i) (e j) := by
    conv_lhs => rw [h a, h b]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_smul,
      Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_comm]
  rw [h1, sum_pairs _ (fun i ↦ by rw [wb_self, smul_zero])]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [wb_swap (e i) (e j), sub_smul, smul_neg, sub_eq_add_neg]
end GlobalTheory.CompanionTheory.HodgeTwoForm
