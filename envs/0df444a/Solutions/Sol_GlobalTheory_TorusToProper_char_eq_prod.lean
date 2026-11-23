-- Prove2me | solution 1 for GlobalTheory.TorusToProper.char_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:55.917282+00:00
-- url     : https://prove2.me/submissions/c50ce8b7-886a-4e09-8305-a275cab95203

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField

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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusToProper
variable {K : Type} [Field K]
variable (K) (X : Type) [AddCommGroup X]
namespace GlobalTheory.TorusToProper
theorem _root_.solution {I : Type} [Fintype I] (e : Module.Basis I ℤ X) (G : Type) [CommGroup G]
    (φ : Multiplicative X →* G) :
    φ = ∏ i, coch (e.coord i).toAddMonoidHom G (φ (Multiplicative.ofAdd (e i))) := by
  refine MonoidHom.ext fun a => ?_
  rw [MonoidHom.finset_prod_apply]
  conv_lhs => rw [← ofAdd_toAdd a, ← e.sum_repr a.toAdd, ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  rfl
end GlobalTheory.TorusToProper
