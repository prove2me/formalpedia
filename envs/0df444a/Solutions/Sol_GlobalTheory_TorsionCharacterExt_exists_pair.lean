-- Prove2me | solution 1 for GlobalTheory.TorsionCharacterExt.exists_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:34:38.622457+00:00
-- url     : https://prove2.me/submissions/0be288c9-36da-4aed-9e35-7de778ff5d62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsReducedTorsionGeometricFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SectionEqZeroOfForallGeometricPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEvalEqOfMultiplicativeOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCharacterExtAndExistsOfIntegralPoints
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCharacterExt
variable {O : Type} [CommRing O]
namespace GlobalTheory.TorsionCharacterExt
theorem _root_.solution {A : Type} [CommRing A] [Algebra O A] {T : Over (Spec (CommRingCat.of O))}
    (x y : T ⟶ specO O A) : ∃ t : T ⟶ specO O (A ⊗[O] A),
      t ≫ ptMap Algebra.TensorProduct.includeLeft = x ∧
        t ≫ ptMap Algebra.TensorProduct.includeRight = y := by
  have h1 : ((lift x y).left ≫ (pullbackSpecIso O A A).hom) ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = x.left := by
    rw [Category.assoc, pullbackSpecIso_hom_fst]
    exact congrArg Over.Hom.left (lift_fst x y)
  have h2 : ((lift x y).left ≫ (pullbackSpecIso O A A).hom) ≫
      (ptMap (Algebra.TensorProduct.includeRight : A →ₐ[O] A ⊗[O] A)).left = y.left := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((lift x y).left ≫ ·) (pullbackSpecIso_hom_snd O A A)).trans ?_
    exact congrArg Over.Hom.left (lift_snd x y)
  refine ⟨Over.homMk ((lift x y).left ≫ (pullbackSpecIso O A A).hom) ?_,
    Over.OverMorphism.ext h1, Over.OverMorphism.ext h2⟩
  rw [← Over.w y, ← h2, Category.assoc _ (ptMap _).left, Over.w]
end GlobalTheory.TorsionCharacterExt
