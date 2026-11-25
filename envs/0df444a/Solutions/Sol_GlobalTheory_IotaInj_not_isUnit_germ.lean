-- Prove2me | solution 1 for GlobalTheory.IotaInj.not_isUnit_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:39.624238+00:00
-- url     : https://prove2.me/submissions/5127a568-5b59-43dc-9dd5-29d8642ee4f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MemOfNonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.IotaInj
open GlobalTheory.TorusExt
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.IotaInj
theorem _root_.solution {I : Ideal R} {V : (Spec (CommRingCat.of R)).Opens} {p : Spec (CommRingCat.of R)} (hp : p ∈ V)
    (hI : I ≤ p.asIdeal) {r : Γ(Spec (CommRingCat.of R), V)} (hr : r ∈ I.map (DegPre.toOpen V)) :
    ¬ IsUnit (((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom r) := by
  have key : I.map (DegPre.toOpen V) ≤ (maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk p)).comap
      ((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha hu
    have e : ((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom (DegPre.toOpen V a) =
        ((Spec (CommRingCat.of R)).presheaf.germ ⊤ p trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
      TopCat.Presheaf.germ_res_apply _ _ p hp _
    have hu' : IsUnit (((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom (DegPre.toOpen V a)) := hu
    rw [e] at hu'
    have hm := (Scheme.mem_basicOpen (Spec (CommRingCat.of R)) (U := ⊤) _ p trivial).2 hu'
    rw [show (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = _ from
      basicOpen_eq_of_affine (R := CommRingCat.of R) a] at hm
    exact hm (hI ha)
  exact key hr
end GlobalTheory.IotaInj
