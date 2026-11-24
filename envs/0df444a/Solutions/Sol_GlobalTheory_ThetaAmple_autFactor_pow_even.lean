-- Prove2me | solution 1 for GlobalTheory.ThetaAmple.autFactor_pow_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:46:10.659644+00:00
-- url     : https://prove2.me/submissions/3c3faa03-f753-4e51-881a-0031c8bbfe71

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RelAmpleThetaBundleProjectiveModel
import Theorems.Thm_GlobalTheory_ThetaAmple_two_mul_dot_int
import Theorems.Thm_P2M_GlobalTheory_ThetaAmple_eC_nat_mul__dd0677f1844f
import Theorems.Thm_ReciprocityTheory_PTheta_eC_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAmple
namespace GlobalTheory.ThetaAmple
theorem _root_.solution {g : ℕ} {a b : Fin g → ℝ} (ha : ∀ i, a i = 0 ∨ a i = 1 / 2)
    (hb : ∀ i, b i = 0 ∨ b i = 1 / 2) (τ : Matrix (Fin g) (Fin g) ℂ) (n n' : Fin g → ℤ) (z : Fin g → ℂ) {N : ℕ}
    (hN : Even N) : autFactor a b τ n n' z ^ N =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) := by
  obtain ⟨m, rfl⟩ := hN
  obtain ⟨k, hk⟩ := two_mul_dot_int ha n'
  obtain ⟨l, hl⟩ := two_mul_dot_int hb n
  rw [autFactor, mul_pow, ← eC_nat_mul', ← eC_nat_mul']
  have : ((m + m : ℕ) : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n) = ((m * (k - l) : ℤ) : ℂ) := by
    push_cast
    rw [← hk, ← hl]
    ring
  rw [this, eC_int, _root_.one_mul]
  congr 1
  ring
end GlobalTheory.ThetaAmple
