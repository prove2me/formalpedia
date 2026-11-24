-- Prove2me | solution 1 for GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:47:01.32683+00:00
-- url     : https://prove2.me/submissions/02dc00e9-650a-4112-8dc6-468c618d296c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_realExtension_posDef_of_rat
import Theorems.Thm_GlobalTheory_ClassMin_polar_ofIntBilin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
variable {X : Type*} [AddCommGroup X] {ι : Type*} {Q : QuadraticMap ℤ X ℝ}
namespace GlobalTheory.ClassMin
theorem _root_.solution [Module.Free ℤ X] [Module.Finite ℤ X]
    {β : LinearMap.BilinForm ℤ X} (hβ : ∀ x y, β x y = β y x) (hpos : ∀ x, x ≠ 0 → 0 < β x x) :
    (realExtension (ofIntBilin β)).PosDef :=
  realExtension_posDef_of_rat
    (fun x hx => by
      rw [ofIntBilin_apply]
      exact div_pos (by exact_mod_cast hpos x hx) two_pos)
    fun x y => ⟨β x y, by rw [polar_ofIntBilin hβ]; simp⟩
end GlobalTheory.ClassMin
