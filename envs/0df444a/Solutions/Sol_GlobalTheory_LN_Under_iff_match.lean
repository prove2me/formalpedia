-- Prove2me | solution 1 for GlobalTheory.LN.Under.iff_match
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:56.280934+00:00
-- url     : https://prove2.me/submissions/1a1187e6-cc71-4352-8db2-e4603b159be1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.LN
open GlobalTheory.UU
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G'] [IsCommMonObj G']
namespace GlobalTheory.LN
namespace Under
theorem _root_.solution {D₀ : DegData R I} {U : PreU I D₀.toPre A G} {U₀ : UnifPre I D₀ A G} :
    Under U U₀ ↔ GlobalTheory.UU.Match U U₀ :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => ⟨h₁.symm, h₂.symm, h₃.symm, h₄.symm, h₅.symm, h₆.symm⟩,
    fun h => ⟨h.gen.symm, h.LG.symm, h.cub.symm, h.sym.symm, h.gt.symm, h.w.symm⟩⟩
end Under
end GlobalTheory.LN
