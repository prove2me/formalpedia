-- Prove2me | solution 1 for GlobalTheory.SS.PlacesExt.v_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:10:29.173742+00:00
-- url     : https://prove2.me/submissions/c33c6179-2cb9-49f8-ae01-f0539226eb5f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionField
import Theorems.Thm_GlobalTheory_SS_PlacesExt_v_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PlacesExt
open IsDedekindDomain Polynomial ReciprocityTheory.ChartRestriction.G.T0
variable {k F : Type} [Field k] [Field F] [Algebra k F] (Pl : Places k F)
namespace GlobalTheory.SS.PlacesExt
theorem _root_.solution (i : Pl.I) {u : Pl.O i} (hu : IsUnit u) (x : Fˣ) (hx : (x : F) = u) : Pl.v i x = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have h1 := (Pl.mem i x).1 (hx ▸ (w : Pl.O i).2)
  have h2 : ((x⁻¹ : Fˣ) : F) = ((w⁻¹ : (Pl.O i)ˣ) : Pl.O i) := by
    rw [Units.val_inv_eq_inv_val, hx]
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
  have h3 := (Pl.mem i x⁻¹).1 (h2 ▸ ((w⁻¹ : (Pl.O i)ˣ) : Pl.O i).2)
  rw [v_inv] at h3
  omega
end GlobalTheory.SS.PlacesExt
