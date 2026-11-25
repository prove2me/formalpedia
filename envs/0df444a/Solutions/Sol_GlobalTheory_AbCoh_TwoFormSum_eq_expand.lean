-- Prove2me | solution 1 for GlobalTheory.AbCoh.TwoFormSum.eq_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:53:00.699033+00:00
-- url     : https://prove2.me/submissions/a185c6e1-c324-4a15-bd63-949e7a4aa530

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalTwoFormEqSumWedgeGlobalOneForms
import Theorems.Thm_GlobalTheory_AbCoh_TwoFormSum_coordPair_wedge
import Theorems.Thm_P2M_GlobalTheory_AbCoh_TwoFormSum__Multi_two_bb841c234bcc
import Theorems.Thm_GlobalTheory_AbCoh_TwoFormSum_sum_sum_eq_lt
import Theorems.Thm_GlobalTheory_AbCoh_TwoFormSum_expand_apply
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_wedge_swap
import Theorems.Thm_GlobalTheory_Cris_Thick_Hom_mem
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
theorem _root_.solution {n : ℕ} (w : Fin n → Ω[B⁄R]) (δ : Fin n → Module.Dual B Ω[B⁄R])
    (hs : ∀ ω, ω = ∑ i, δ i ω • w i) (x : Om R B 2) :
    x = ∑ i, ∑ j, (if i < j then coordPair (δ i) (δ j) x else 0) • wedge R B (w i) (w j) := by
  rw [← expand_apply]
  have hx : x ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B 2 (M := Ω[B⁄R]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    have hL : wedge R B (v 0) (v 1) = ∑ i, ∑ j, (δ i (v 0) * δ j (v 1)) • wedge R B (w i) (w j) := by
      conv_lhs => rw [hs (v 0), hs (v 1)]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_comm]
    rw [ιMulti_two, expand_apply]
    conv_lhs => rw [hL,
      sum_sum_eq_lt (fun i j ↦ (δ i (v 0) * δ j (v 1)) • wedge R B (w i) (w j)) (fun i ↦ by simp)]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · rw [coordPair_wedge, wedge_swap (w j) (w i), smul_neg, sub_smul]; abel
    · simp
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, ← hy, ← hz]
  | smul c y _ hy => rw [map_smul, ← hy]
end GlobalTheory.AbCoh.TwoFormSum
