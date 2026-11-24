-- Prove2me | solution 1 for GlobalTheory.Frames.existsUnique_comb_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:54:01.137012+00:00
-- url     : https://prove2.me/submissions/2ad8b067-1332-4b2c-98b3-7035fd742901

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ScaledBaseChangeFibreSectionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueScaledBaseChangeFibreSectionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueFrameChangeByMatrices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.Frames
namespace GlobalTheory.Frames
theorem _root_.solution {S N : Type} [CommRing S] [AddCommGroup N] [Module S N] {n : ℕ}
    (b : Fin n → N) (g : Matrix (Fin n) (Fin n) S) (hg : IsUnit g.det) (m : N)
    (h : ∃! a : Fin n → S, m = ∑ i, a i • b i) :
    ∃! a : Fin n → S, m = ∑ i, a i • ∑ j, g i j • b j := by
  have key : ∀ a : Fin n → S, ∑ i, a i • ∑ j, g i j • b j = ∑ j, (Matrix.vecMul a g) j • b j := by
    intro a
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
  obtain ⟨a, ha, hu⟩ := h
  refine ⟨Matrix.vecMul a g⁻¹, ?_, fun a' ha' => ?_⟩
  · show m = _
    rw [key, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul g hg, Matrix.vecMul_one]
    exact ha
  · have h1 := hu (Matrix.vecMul a' g) (Eq.trans ha' (key a'))
    rw [← h1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv g hg, Matrix.vecMul_one]
end GlobalTheory.Frames
