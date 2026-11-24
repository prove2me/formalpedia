-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.isGen_of_equations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:30.088802+00:00
-- url     : https://prove2.me/submissions/a8aae0a1-9ab3-491f-89b6-b94f2d82210a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_imageVal_res
import Theorems.Thm_GlobalTheory_ExtendLineBundle_image_unit_ext

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
theorem _root_.solution (M N : LB Y) (a : M.ι → X.functionFieldˣ) (b : N.ι → X.functionFieldˣ)
    (ha : ∀ i k, genericPoint X ∈ j ''ᵁ M.U i → genericPoint X ∈ j ''ᵁ M.U k →
      imageVal j _ (M.g i k) = a i / a k)
    (hb : ∀ i k, genericPoint X ∈ j ''ᵁ N.U i → genericPoint X ∈ j ''ᵁ N.U k →
      imageVal j _ (N.g i k) = b i / b k)
    (s : ∀ p : M.ι × N.ι, Γ(Y, M.U p.1 ⊓ N.U p.2)ˣ)
    (hs : ∀ p, genericPoint X ∈ j ''ᵁ (M.U p.1 ⊓ N.U p.2) → imageVal j _ (s p) = a p.1 / b p.2) :
    LB.Gen.IsGen (⟨s⟩ : LB.Iso N M) := by
  intro (p : M.ι × N.ι) (q : M.ι × N.ι)
  refine image_unit_ext j (V := M.U p.1 ⊓ N.U p.2 ⊓ (M.U q.1 ⊓ N.U q.2)) fun h => ?_
  have hp := j.image_mono inf_le_left h
  have hq := j.image_mono inf_le_right h
  have e₁ := ha p.1 q.1 (j.image_mono inf_le_left hp) (j.image_mono inf_le_left hq)
  have e₂ := hb p.2 q.2 (j.image_mono inf_le_right hp) (j.image_mono inf_le_right hq)
  have key : ∀ (V : Y.Opens) (_ : genericPoint X ∈ j ''ᵁ V) (l₁ : V ≤ M.U p.1 ⊓ N.U p.2)
      (l₂ : V ≤ M.U p.1 ⊓ M.U q.1) (l₃ : V ≤ N.U p.2 ⊓ N.U q.2) (l₄ : V ≤ M.U q.1 ⊓ N.U q.2),
      imageVal j V (res l₁ (s p)) =
        imageVal j V (res l₂ (M.g p.1 q.1) * (res l₃ (N.g p.2 q.2))⁻¹ * res l₄ (s q)) := by
    intro V h l₁ l₂ l₃ l₄
    rw [map_mul, map_mul, map_inv, imageVal_res j _ h, imageVal_res j _ h, imageVal_res j _ h,
      imageVal_res j _ h, e₁, e₂, hs p hp, hs q hq]
    rw [inv_div, mul_right_comm, div_mul_div_cancel, div_mul_div_cancel]
  exact key _ h _ _ _ _
end GlobalTheory.ExtendLineBundle
