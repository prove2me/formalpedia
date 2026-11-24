-- Prove2me | solution 1 for GlobalTheory.TorusUnit.isPushout_grpAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:37:20.242638+00:00
-- url     : https://prove2.me/submissions/214b41a9-ab9e-4be0-b94f-5e2fe84a4f05

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_uliftInt_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusUnit
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (torusFst ringHom_ext_ZU ringHom_uliftInt_ext)
open AddMonoidAlgebra (single)
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {Y : Over S}
attribute [local instance] TorusInj.zuAlg
namespace GlobalTheory.TorusUnit
theorem _root_.solution (A : Type) [CommRing A] :
    IsPushout (CommRingCat.ofHom (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} X)))
      (CommRingCat.ofHom (algebraMap ZU.{0} A))
      (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{0} X) (AddMonoidAlgebra A X)))
      (CommRingCat.ofHom (algebraMap A (AddMonoidAlgebra A X))) := by
  have : IsScalarTower ZU.{0} (AddMonoidAlgebra ZU.{0} X) (AddMonoidAlgebra A X) :=
    ⟨fun r a b => by
      obtain ⟨n⟩ := r
      show (n • a) • b = n • (a • b)
      simp only [Algebra.smul_def, map_mul, _root_.mul_assoc, eq_intCast, map_intCast]⟩
  have : Algebra.IsPushout ZU.{0} (AddMonoidAlgebra ZU.{0} X) A (AddMonoidAlgebra A X) :=
    AddMonoidAlgebra.instIsPushout'
  exact CommRingCat.isPushout_of_isPushout ZU.{0} (AddMonoidAlgebra ZU.{0} X) A
    (AddMonoidAlgebra A X)
end GlobalTheory.TorusUnit
