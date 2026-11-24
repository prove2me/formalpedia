-- Prove2me | solution 1 for GlobalTheory.ExpandsLinear.scal_comp_specMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:49:26.003364+00:00
-- url     : https://prove2.me/submissions/623b0891-c7a9-47d0-a538-2f7ab02fd37a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ScalCompSpecMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ExpandsLinear
namespace GlobalTheory.ExpandsLinear
theorem _root_.solution {R C : Type} [CommRing R] [CommRing C] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of C)) (φ : R →+* C) (r : R) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by
  unfold scal
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  have := congrArg (fun g => g.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact this.symm
end GlobalTheory.ExpandsLinear
