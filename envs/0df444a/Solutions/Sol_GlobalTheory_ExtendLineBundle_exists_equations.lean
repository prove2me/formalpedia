-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.exists_equations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:26.691263+00:00
-- url     : https://prove2.me/submissions/2f678d6a-359e-409e-9355-2afeeb5fa3aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_imageVal_res
import Theorems.Thm_GlobalTheory_ExtendLineBundle_mem_image_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
variable (j : Y ⟶ X) [IsOpenImmersion j]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution (L : LB Y) (hL : L.IsLB) : ∃ f : L.ι → X.functionFieldˣ,
    ∀ i k, genericPoint X ∈ j ''ᵁ L.U i → genericPoint X ∈ j ''ᵁ L.U k →
      imageVal j _ (L.g i k) = f i / f k := by
  by_cases h : ∃ i₀, genericPoint X ∈ j ''ᵁ L.U i₀
  · obtain ⟨i₀, h₀⟩ := h
    refine ⟨fun i => imageVal j _ (L.g i i₀), fun i k hi hk => ?_⟩
    have hη := mem_image_inf j (mem_image_inf j hi hk) h₀
    have e := congrArg (imageVal j _) (hL.cocycle i k i₀)
    rw [map_mul, imageVal_res j _ hη, imageVal_res j _ hη, imageVal_res j _ hη] at e
    exact eq_div_iff_mul_eq'.2 e
  · exact ⟨1, fun i _ hi => (h ⟨i, hi⟩).elim⟩
end GlobalTheory.ExtendLineBundle
