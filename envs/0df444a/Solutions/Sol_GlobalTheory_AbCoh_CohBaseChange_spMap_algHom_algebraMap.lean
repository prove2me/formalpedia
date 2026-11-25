-- Prove2me | solution 1 for GlobalTheory.AbCoh.CohBaseChange.spMap_algHom_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:11:10.431804+00:00
-- url     : https://prove2.me/submissions/013a1cf6-35b1-425e-a769-36da9dbdc4cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpMapAlgHomAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.CohBaseChange
variable {R : Type} [CommRing R]
namespace GlobalTheory.AbCoh.CohBaseChange
theorem _root_.solution {R' R'' : Type} [CommRing R'] [Algebra R R'] [CommRing R''] [Algebra R R'']
    (α : R' →ₐ[R] R'') : spMap (α : R' →+* R'') ≫ spMap (algebraMap R R') = spMap (algebraMap R R'') := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, α.comp_algebraMap]
end GlobalTheory.AbCoh.CohBaseChange
