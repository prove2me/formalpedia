-- Prove2me | solution 1 for GlobalTheory.FrameValue.secValIn_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:44:48.781836+00:00
-- url     : https://prove2.me/submissions/a9e7d875-fed2-4d49-b005-6c0d54f0a988

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Theorems.Thm_GlobalTheory_FrameValue_val_sec
import Theorems.Thm_GlobalTheory_FrameValue_IsLift_le_iff
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_val_linComb
import Theorems.Thm_GlobalTheory_CubeValues_val_unit_ne_zero
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FrameValue
open CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A.left)} {ε' : K' → ℤ}
variable {u}
namespace GlobalTheory.FrameValue
theorem _root_.solution (s : LB.Sec (LB.LinComb L φ ε)) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} (hz : IsLift u φ y z)
    {j j' : K → L.ι} (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) (hj' : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j') :
    secValIn u s y z j = secValIn u s y z j' := by
  have e₁ := val_sec y s j j' hj hj'
  have e₂ := val_linComb y valueRules L φ ε j j' hj hj'
  have e₃ : frameProd u ε z j = valAt' y (L.wchart φ j ⊓ L.wchart φ j') ((L.LinComb φ ε).g j j').val *
      frameProd u ε z j' := by
    rw [e₂, frameProd, frameProd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [u.fr_compat (j k) (j' k) (z k) ((le_preimage_inf _ _ _).2 ⟨(hz.le_iff j).1 hj k, (hz.le_iff j').1 hj' k⟩),
      mul_zpow, hz k]
  have n := val_unit_ne_zero y valueRules ((le_preimage_inf y _ _).2 ⟨hj, hj'⟩) ((L.LinComb φ ε).g j j')
  rw [secValIn, secValIn, e₃]
  exact (congrArg (· / _) e₁).trans (mul_div_mul_left _ _ n)
end GlobalTheory.FrameValue
