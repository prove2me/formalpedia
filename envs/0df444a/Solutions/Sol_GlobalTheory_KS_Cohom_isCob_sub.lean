-- Prove2me | solution 1 for GlobalTheory.KS.Cohom.isCob_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:45:05.543539+00:00
-- url     : https://prove2.me/submissions/6b6ba7b7-13a1-4525-952d-37f0b2c5086b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Theorems.Thm_GlobalTheory_KS_rsT_add
import Theorems.Thm_GlobalTheory_KS_rsT_sub
import Theorems.Thm_GlobalTheory_KS_pbT_sub
import Theorems.Thm_GlobalTheory_KS_rsT_rsT
import Theorems.Thm_GlobalTheory_KS_rsT_pbT
import Theorems.Thm_GlobalTheory_KS_pbT_rsT
import Theorems.Thm_GlobalTheory_KS_eq_of_rsT_eq
import Theorems.Thm_GlobalTheory_KS_exists_rsT_eq
import Theorems.Thm_GlobalTheory_KS_le_iSup_inf_preimage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS
variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens}
namespace GlobalTheory.KS
namespace Cohom
theorem _root_.solution (f : Y ⟶ Y) (hU : ⨆ i, U i = ⊤) {c c₁ c' c₁' : C1 U} (h : Cohom f U c c')
    (h₁ : Cohom f U c₁ c₁') (hc : IsCob U (c' - c₁')) : IsCob U (c - c₁) := by
  obtain ⟨b, hb, hb'⟩ := h
  obtain ⟨b₁, hb₁, hb₁'⟩ := h₁
  obtain ⟨β, hβ⟩ := hc
  have glue : ∀ i, ∃ t : Γ(Y, U i), ∀ k, rsT t (U i ⊓ f ⁻¹ᵁ U k) =
      b i k - b₁ i k + pbT f (β k) (U i ⊓ f ⁻¹ᵁ U k) := by
    intro i
    refine exists_rsT_eq (fun k => U i ⊓ f ⁻¹ᵁ U k) (fun k => inf_le_left)
      (le_iSup_inf_preimage f U hU _) _ fun k l => ?_
    have e : (U i ⊓ f ⁻¹ᵁ U k) ⊓ (U i ⊓ f ⁻¹ᵁ U l) ≤ U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l :=
      fun y hy => ⟨hy.1, hy.2.2⟩
    have e₁ : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l ≤ f ⁻¹ᵁ (U k ⊓ U l) := fun y hy => ⟨hy.1.2, hy.2⟩
    have e₂ : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l ≤ U i ⊓ f ⁻¹ᵁ U l := fun y hy => ⟨hy.1.1, hy.2⟩
    rw [← rsT_rsT inf_le_left e, ← rsT_rsT e₂ e]
    congr 1
    have k₀ := congrArg (fun s => pbT f s (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l)) (hβ k l)
    simp only [Pi.sub_apply, pbT_sub] at k₀
    rw [pbT_rsT f inf_le_right e₁, pbT_rsT f inf_le_left e₁, ← hb', ← hb₁'] at k₀
    simp only [rsT_add, rsT_sub]
    rw [rsT_pbT f inf_le_right inf_le_left, rsT_pbT f inf_le_right e₂]
    linear_combination k₀
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun k => U i ⊓ U j ⊓ f ⁻¹ᵁ U k) (fun k => inf_le_left)
    (le_iSup_inf_preimage f U hU _) _ _ fun k => ?_
  have e₁ : U i ⊓ U j ⊓ f ⁻¹ᵁ U k ≤ U i ⊓ f ⁻¹ᵁ U k := inf_le_inf_right _ inf_le_left
  have e₂ : U i ⊓ U j ⊓ f ⁻¹ᵁ U k ≤ U j ⊓ f ⁻¹ᵁ U k := inf_le_inf_right _ inf_le_right
  simp only [Pi.sub_apply, rsT_sub]
  rw [rsT_rsT inf_le_right inf_le_left, rsT_rsT inf_le_left inf_le_left,
    ← rsT_rsT inf_le_left e₂ (t j), ← rsT_rsT inf_le_left e₁ (t i), ht, ht, ← hb, ← hb₁]
  simp only [rsT_add, rsT_sub]
  rw [rsT_pbT f inf_le_right e₁, rsT_pbT f inf_le_right e₂]
  ring
end Cohom
end GlobalTheory.KS
