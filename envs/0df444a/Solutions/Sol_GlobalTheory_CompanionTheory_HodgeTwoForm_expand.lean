-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeTwoForm.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:56:25.124964+00:00
-- url     : https://prove2.me/submissions/6b702141-103d-4e8b-a985-3176426bfc6a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeFunctionalTwoFormNaturality
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wedge_functional_iota_multi
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wb_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_eq_two
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeTwoForm_wb_expand
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Cris_Thick_Hom_mem
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
    (z : ⋀[A]^2 M) :
    z = ∑ i, ∑ j ∈ Finset.Ioi i, L2 L i j z • wb (A := A) (e i) (e j) := by
  have hz : z ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have e1 : exteriorPower.ιMulti A 2 v = wb (A := A) (v 0) (v 1) := by rw [wb_apply, ← eq_two]
    rw [e1]
    conv_lhs => rw [wb_expand e L h]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [wb_apply (v 0), wedge_functional_iota_multi]
  | zero => simp
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add, add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    conv_lhs => rw [hx]
    simp only [map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]
end GlobalTheory.CompanionTheory.HodgeTwoForm
