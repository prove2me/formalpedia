-- Prove2me | solution 1 for GlobalTheory.SegreCoord.RankOne.map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:35.275369+00:00
-- url     : https://prove2.me/submissions/abe4db07-d8aa-4605-aa2e-940199be2236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
variable {R : Type} [CommRing R] (I : Ideal (MvPolynomial σ R))
variable {I} {s : X ⟶ Sp R} (H : ProjRep I s M th) {Y : Scheme.{0}} {p q : Y ⟶ X} (hP : IsPullback p q s s)
include H hP
omit H hP
namespace GlobalTheory.SegreCoord
namespace RankOne
theorem _root_.solution {β : R →+* T} {w : σ × σ → T} (hw : RankOne I β w) (φ : T →+* T') :
    RankOne I (φ.comp β) (fun i => φ (w i)) := by
  refine ⟨fun a b c d => by simp only [← map_mul, hw.1 a b c d], fun b F hF => ?_, fun a F hF => ?_⟩
  · have := MvPolynomial.eval₂_comp_left φ β (fun i => w (i, b)) F
    rw [hw.2.1 b F hF, map_zero] at this
    exact this.symm
  · have := MvPolynomial.eval₂_comp_left φ β (fun i => w (a, i)) F
    rw [hw.2.2 a F hF, map_zero] at this
    exact this.symm
end RankOne
end GlobalTheory.SegreCoord
