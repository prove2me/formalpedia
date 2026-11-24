-- Prove2me | solution 1 for GlobalTheory.MulSplit.pl_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:31.139236+00:00
-- url     : https://prove2.me/submissions/7a0eada8-45e9-461b-882e-8e2af753db62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulSplit
variable {X Y B : Scheme.{0}} {L : LB X} {p : Y ⟶ B}
namespace GlobalTheory.MulSplit
theorem _root_.solution {h : Y ⟶ Y} (hh : h ≫ p = p) {u : (Vals L p)ˣ} {c : Γ(B, ⊤)ˣ}
    (e : pl L h hh u.val = c.val • u.val) : pl L h hh (u⁻¹).val = (c⁻¹).val • (u⁻¹).val := by
  have h1 : pl L h hh (u⁻¹).val * pl L h hh u.val = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  rw [e, mul_smul_comm] at h1
  have h2 := congrArg (fun t => (c⁻¹).val • (t * (u⁻¹).val)) h1
  simpa only [smul_mul_assoc, smul_smul, Units.inv_mul, one_smul, Units.mul_inv_cancel_right,
    _root_.one_mul] using h2
end GlobalTheory.MulSplit
