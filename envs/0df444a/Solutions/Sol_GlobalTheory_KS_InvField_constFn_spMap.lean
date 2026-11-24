-- Prove2me | solution 1 for GlobalTheory.KS.InvField.constFn_spMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:52.49767+00:00
-- url     : https://prove2.me/submissions/155d9ddc-ed44-44a1-92ee-813e5d3a3d9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructureStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangent

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.InvField
namespace GlobalTheory.KS.InvField
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] {Y : Scheme.{0}} (q : Y ⟶ Sp S) (φ : R →+* S)
    (O : Y.Opens) (a : R) : constFn (q ≫ spMap φ) O a = constFn q O (φ a) := by
  have h : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have h2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))
  rw [h] at h3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 h3
  unfold constFn
  rw [← h3, h2]
end GlobalTheory.KS.InvField
