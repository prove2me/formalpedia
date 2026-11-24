-- Prove2me | solution 1 for GlobalTheory.ThetaBundleSym.HasFactor.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:05.434505+00:00
-- url     : https://prove2.me/submissions/706ccd9f-b03f-430e-9367-1bdb29844931

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
import Theorems.Thm_GlobalTheory_ThetaBundleSym_basicFactor_neg
import Theorems.Thm_GlobalTheory_ThetaBundleSym_charFactor_neg

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
open GlobalTheory GlobalTheory.ThetaBundleSym
variable {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
variable {τ} {a b : Fin g → ℝ}
namespace GlobalTheory.ThetaBundleSym
namespace HasFactor
theorem _root_.solution (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    {m k : ℕ} {f : (Fin g → ℂ) → ℂ} (h : HasFactor τ a b m k f) : HasFactor τ a b m k (fun z => f (-z)) := by
  refine ⟨h.1.comp (f := fun z : Fin g → ℂ => -z) (by fun_prop), fun n n' z => ?_⟩
  have := h.2 (-n) (-n') (-z)
  rw [charFactor_neg ha hb, basicFactor_neg] at this
  simp only
  rw [← this]
  congr 1
  simp only [ofIntVec_neg, Matrix.mulVec_neg]
  abel
end HasFactor
end GlobalTheory.ThetaBundleSym
