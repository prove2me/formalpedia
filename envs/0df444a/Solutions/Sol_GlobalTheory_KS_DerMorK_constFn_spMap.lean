-- Prove2me | solution 1 for GlobalTheory.KS.DerMorK.constFn_spMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:26:06.051243+00:00
-- url     : https://prove2.me/submissions/f6d5f35b-b9b1-48d2-ab0d-5cc483f26e27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomOfDerivation

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DerMorK
namespace GlobalTheory.KS.DerMorK
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} (p : X ⟶ Sp R')
    (φ : R →+* R') (U : X.Opens) (a : R) :
    constFn (p ≫ spMap φ) U a = constFn p U (φ a) := by
  unfold constFn
  rw [← Scheme.Hom.appLE_comp_appLE p (spMap φ) ⊤ ⊤ U (fun _ _ => trivial) (fun _ _ => trivial)]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 := congr(($h).hom a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 ⊢
  rw [h2]
  congr 1
end GlobalTheory.KS.DerMorK
