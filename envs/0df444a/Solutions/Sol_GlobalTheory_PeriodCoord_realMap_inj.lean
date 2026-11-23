-- Prove2me | solution 1 for GlobalTheory.PeriodCoord.realMap_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:13:54.871105+00:00
-- url     : https://prove2.me/submissions/9b0066e8-9630-4bf7-8b8d-249d2e60f1f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Theorems.Thm_GlobalTheory_PeriodCoord_realMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodCoord
noncomputable section
variable {g : ℕ}
namespace GlobalTheory.PeriodCoord
theorem _root_.solution {A B A' B' : Matrix (Fin g) (Fin g) ℂ} (h : realMap A B = realMap A' B') :
    A = A' ∧ B = B' := by
  have key : ∀ i j, A i j = A' i j ∧ B i j = B' i j := fun i j => by
    have h1 := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
    have h2 := congrFun (LinearMap.congr_fun h (Pi.single j Complex.I)) i
    simp only [realMap_apply, ← Pi.single_star, star_one, mulVec_single, Pi.add_apply,
      RCLike.star_def, Complex.conj_I] at h1 h2
    simp at h1 h2
    have hI := Complex.I_mul_I
    constructor
    · linear_combination h1 / 2 - Complex.I / 2 * h2 + (A i j - B i j - A' i j + B' i j) / 2 * hI
    · linear_combination h1 / 2 + Complex.I / 2 * h2 - (A i j - B i j - A' i j + B' i j) / 2 * hI
  exact ⟨Matrix.ext fun i j => (key i j).1, Matrix.ext fun i j => (key i j).2⟩
end GlobalTheory.PeriodCoord
