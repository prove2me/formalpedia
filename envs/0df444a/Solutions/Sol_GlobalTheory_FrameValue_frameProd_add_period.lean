-- Prove2me | solution 1 for GlobalTheory.FrameValue.frameProd_add_period
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:11.617799+00:00
-- url     : https://prove2.me/submissions/d02ad72c-8f44-40a0-853b-b16113513842

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Theorems.Thm_GlobalTheory_FrameValue_IsLift_le_iff

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
variable {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
namespace GlobalTheory.FrameValue
theorem _root_.solution (h : u.IsAH Hm χ) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} (hz : IsLift u φ y z) (ε : K → ℤ)
    (l : K → u.Λ) {j : K → L.ι} (hj : ⊤ ≤ y ⁻¹ᵁ L.wchart φ j) :
    frameProd u ε z j = (∏ k, ahFactor Hm χ (l k) (z k) ^ ε k) * frameProd u ε (fun k => z k + l k) j := by
  rw [frameProd, frameProd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h.2.2.2 (l k) (j k) (z k) ((hz.le_iff j).1 hj k), mul_zpow]
  rfl
end GlobalTheory.FrameValue
