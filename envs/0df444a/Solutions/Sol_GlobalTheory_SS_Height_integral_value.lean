-- Prove2me | solution 1 for GlobalTheory.SS.Height.integral_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:34:18.465242+00:00
-- url     : https://prove2.me/submissions/8cac725f-8ef0-44b0-9065-6bdccd9ff9e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme
import Theorems.Thm_GlobalTheory_SS_Height_isUnit_ev
import Theorems.Thm_GlobalTheory_SS_Height_ev_gs
import Theorems.Thm_GlobalTheory_SS_Height_isUnit_gs

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
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Height
open IsLocalRing
variable {k K : Type} [Field k] [Field K] [Algebra k K]
namespace GlobalTheory.SS.Height
theorem _root_.solution (O : ValuationSubring K) {X : Scheme.{0}} (b : Sp O ⟶ X) (U : X.Opens)
    (h : b (closedPoint O) ∈ U) :
    (spMap O.subtype ≫ b) (closedPoint K) ∈ U ∧ ∀ f : Γ(X, U), ∃ a : O,
      (a : K) = ev K (gs (spMap O.subtype ≫ b) (closedPoint K) U f) ∧
        (IsUnit a ↔ b (closedPoint O) ∈ X.basicOpen f) := by
  have h1 : ⊤ ≤ b ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of O) b h).ge
  have h2 : ⊤ ≤ (spMap O.subtype ≫ b) ⁻¹ᵁ U := fun x _ => h1 (x := spMap O.subtype x) trivial
  refine ⟨h2 trivial, fun f => ⟨ev O (gs b _ U f), ?_, (isUnit_ev _).trans (isUnit_gs b _ U h f)⟩⟩
  rw [ev_gs b U h h1, ev_gs _ U (h2 trivial) h2,
    ← Scheme.Hom.appLE_comp_appLE (spMap O.subtype) b U ⊤ ⊤ h1 le_rfl]
  have h3 : (spMap O.subtype).appLE ⊤ ⊤ le_rfl = (spMap O.subtype).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [h3, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl
end GlobalTheory.SS.Height
