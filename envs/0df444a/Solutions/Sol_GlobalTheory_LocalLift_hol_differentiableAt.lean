-- Prove2me | solution 1 for GlobalTheory.LocalLift.hol_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:54:20.262811+00:00
-- url     : https://prove2.me/submissions/41a6890a-7095-46e1-9327-244f551ee575

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology GlobalTheory.TangentOrigin
noncomputable section
open GlobalTheory GlobalTheory.LocalLift
variable {Y : Scheme.{0}}
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open Filter Topology
variable {Y : Scheme.{0}}
namespace GlobalTheory.LocalLift
namespace _root_.GlobalTheory.LocalLift
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {B : Set V} {y : V → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y)}
    (hy : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo B y) {b : V} (hb : b ∈ B) {U : Y.Opens} (hU : ⊤ ≤ y b ⁻¹ᵁ U) (f : Γ(Y, U)) :
    DifferentiableAt ℂ (fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (y z) U f) b :=
  ((hy U f).2 b ⟨hb, hU⟩).differentiableAt ((hy U f).1.mem_nhds ⟨hb, hU⟩)
end _root_.GlobalTheory.LocalLift
end GlobalTheory.LocalLift
