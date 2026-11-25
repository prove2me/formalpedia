-- Prove2me | solution 1 for GlobalTheory.BoundedRegular.valF_spMap_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:12.904949+00:00
-- url     : https://prove2.me/submissions/00711bcd-040a-4ef9-9a01-fd655d83ca79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_RegularOfBoundedAtPadicAlgClPoints
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
open GlobalTheory.BoundedRegular
namespace GlobalTheory.BoundedRegular
theorem _root_.solution {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}}
    (t : Sp F ⟶ X) (U : X.Opens) (ht : ⊤ ≤ t ⁻¹ᵁ U) (φ : Γ(X, U)) :
    valF (spMap f ≫ t) U φ =
      f ((Scheme.ΓSpecIso (CommRingCat.of F)).hom (t.appLE U ⊤ ht φ)) := by
  have h' : ⊤ ≤ (spMap f ≫ t) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap f q))
  rw [valF, dif_pos h']
  have e : (spMap f ≫ t).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of F')).hom =
      t.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫ CommRingCat.ofHom f := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap f) t U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  exact congrArg (fun g => g.hom φ) e
end GlobalTheory.BoundedRegular
