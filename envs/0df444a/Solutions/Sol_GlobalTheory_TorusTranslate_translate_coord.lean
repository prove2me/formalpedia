-- Prove2me | solution 1 for GlobalTheory.TorusTranslate.translate_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:58:09.223934+00:00
-- url     : https://prove2.me/submissions/2ab1e86c-b788-4ea4-a993-d9f4a741c756

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPointTranslatePure
import Theorems.Thm_GlobalTheory_TorusTranslate_appLE_res_pullU
import Theorems.Thm_GlobalTheory_TorusTranslate_appLE_app

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.TorusTranslate
variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G) {Z : Over S}
namespace GlobalTheory.TorusTranslate
theorem _root_.solution (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) (j : E.ChartIdx)
    (k : Module.Free.ChooseBasisIndex ℤ E.X)
    (h : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j))
    (h' : ⊤ ≤ ((τ ≫ D.i) * x).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j)) :
    (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (D.u j k).val =
      τ.left.appTop.hom (charUnit S E.X (E.basis k)).val * (x.left.appLE _ ⊤ h).hom (D.u j k).val := by
  let m : Z ⟶ splitTorus S E.X ⊗ G := lift τ x
  have e1 : m.left ≫ (fst (splitTorus S E.X) G).left = τ.left := by
    rw [← Over.comp_left, lift_fst]
  have e2 : m.left ≫ (snd (splitTorus S E.X) G).left = x.left := by
    rw [← Over.comp_left, lift_snd]
  have e3 : m.left ≫ (lift (fst (splitTorus S E.X) G ≫ D.i) (snd (splitTorus S E.X) G) ≫ μ[G]).left
      = ((τ ≫ D.i) * x).left := by
    rw [← Over.comp_left, Hom.mul_def, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have hm : ⊤ ≤ m.left ⁻¹ᵁ ((snd (splitTorus S E.X) G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j)) := by
    rw [← Scheme.Hom.comp_preimage, e2]; exact h
  have key := congrArg (m.left.appLE _ ⊤ hm).hom (congrArg Units.val (D.equiv j k))
  simp only [Units.val_mul, map_mul] at key
  rw [appLE_res_pullU _ _ _ e3 _ _ _ hm h'] at key
  rw [key]
  congr 1
  · refine (appLE_res_pullU _ _ _ e1 ⊤ _ _ hm le_top _).trans ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  · exact appLE_app _ _ _ e2 _ hm h _
end GlobalTheory.TorusTranslate
