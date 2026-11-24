-- Prove2me | solution 1 for GlobalTheory.KS.DerMor.cH_spMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:27:10.956488+00:00
-- url     : https://prove2.me/submissions/7c65929d-851b-4110-a3d3-1add6a60f53c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomFromConstThickeningOfDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DerMor
namespace GlobalTheory.KS.DerMor
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] {X : Scheme.{0}} (q : X ⟶ Sp S) (g : R →+* S)
    (U : X.Opens) (a : R) : cH (q ≫ spMap g) U a = cH q U (g a) := by
  unfold cH spMap
  have k1 := Scheme.Hom.comp_appLE q (Spec.map (CommRingCat.ofHom g)) ⊤ U le_top
  have k3 := congrArg (fun φ => (φ ≫ q.appLE ⊤ U le_top).hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [Category.assoc] at k3
  exact (congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ).hom a) k1).trans k3.symm
end GlobalTheory.KS.DerMor
