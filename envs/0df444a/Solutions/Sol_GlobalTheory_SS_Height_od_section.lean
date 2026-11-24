-- Prove2me | solution 1 for GlobalTheory.SS.Height.od_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:50:18.871208+00:00
-- url     : https://prove2.me/submissions/adcfd55a-ddcd-49d6-a74b-085f0e49736b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme
import Theorems.Thm_GlobalTheory_SS_Height_integral_value
import Theorems.Thm_GlobalTheory_SS_Height_od_inv
import Theorems.Thm_GlobalTheory_SS_Height_od_mem

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
variable (Pl : Places k K)
namespace GlobalTheory.SS.Height
theorem _root_.solution (i) {X : Scheme.{0}} (b : Sp (Pl.O i) ⟶ X) (x : Sp K ⟶ X)
    (hb : spMap (Pl.O i).subtype ≫ b = x) (U : X.Opens) (h : b (closedPoint (Pl.O i)) ∈ U) (f : Γ(X, U))
    (u : ((Sp K).presheaf.stalk (closedPoint K))ˣ) (hu : gs x (closedPoint K) U f = u.val) :
    0 ≤ od Pl i u ∧ (od Pl i u = 0 ↔ b (closedPoint (Pl.O i)) ∈ X.basicOpen f) := by
  subst hb
  obtain ⟨a, ha, hi⟩ := (integral_value _ b U h).2 f
  rw [hu] at ha
  have h0 : 0 ≤ od Pl i u := (od_mem Pl i u).1 (ha ▸ a.2)
  have hm : (a : K) * ev K u⁻¹.val = 1 := by rw [ha, ← map_mul, Units.mul_inv, map_one]
  refine ⟨h0, Iff.trans ⟨fun h1 => ?_, fun h1 => ?_⟩ hi⟩
  · have h2 : ev K u⁻¹.val ∈ Pl.O i := (od_mem Pl i _).2 (by rw [od_inv, h1]; rfl)
    exact IsUnit.of_mul_eq_one (⟨_, h2⟩ : Pl.O i) (Subtype.ext hm)
  · obtain ⟨a', ha'⟩ := h1.exists_right_inv
    have h3 : (a : K) * a' = 1 := congrArg Subtype.val ha'
    have h4 : ev K u⁻¹.val = a' := mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h3) (hm.trans h3.symm)
    have h2 := (od_mem Pl i u⁻¹).1 (h4 ▸ a'.2)
    rw [od_inv] at h2
    omega
end GlobalTheory.SS.Height
