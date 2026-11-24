-- Prove2me | solution 1 for GlobalTheory.ZM.appLE_spConst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:13.321805+00:00
-- url     : https://prove2.me/submissions/1cd33532-8021-4fbe-8408-03c7306e9962

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRing

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (W : (Sp R).Opens)
    (W' : (Sp R').Opens) (h : W' ≤ spMap φ ⁻¹ᵁ W) (r : R) :
    ((spMap φ).appLE W W' h).hom (spConst R W r) = spConst R' W' (φ r) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
      (spMap φ).appLE W W' h =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
        (Sp R').presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  exact congrArg (fun g => g.hom r) key
end GlobalTheory.ZM
