-- Prove2me | solution 1 for GlobalTheory.AbTan.lifts_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:31:47.784807+00:00
-- url     : https://prove2.me/submissions/57bb8651-d4b9-4833-a114-7861174501b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HopfLaurent
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbTan
variable {R : Type} [CommRing R]
namespace GlobalTheory.AbTan
theorem _root_.solution {X : Scheme.{0}} (s : X ⟶ Sp R) {B : Type} (M : Type) [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ X) (h : P ≫ s = spMap (algebraMap R B)) :
    Lifts s P (spMap (TrivSqZeroExt.inlHom B M) ≫ P) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h]
    simp only [spMap, ← Spec.map_comp]
    rfl
  · rw [← Category.assoc]
    simp only [spMap, ← Spec.map_comp]
    have : (CommRingCat.ofHom (TrivSqZeroExt.inlHom B M) ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom B B M).toRingHom : CommRingCat.of B ⟶ CommRingCat.of B) = 𝟙 _ := by
      ext b; rfl
    rw [this, Spec.map_id, Category.id_comp]
end GlobalTheory.AbTan
