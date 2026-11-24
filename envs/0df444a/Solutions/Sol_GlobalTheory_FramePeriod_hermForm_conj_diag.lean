-- Prove2me | solution 1 for GlobalTheory.FramePeriod.hermForm_conj_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:28:19.518012+00:00
-- url     : https://prove2.me/submissions/779c0013-4fd5-48a3-a8b8-bf6fd209363c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FramePeriod
theorem _root_.solution {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → ℝ) (z w : Fin n → ℂ) :
    hermForm (Sᵀ * Matrix.diagonal (fun a => (e a : ℂ)) * S.map (starRingEnd ℂ)) z w =
      ∑ a, (e a : ℂ) * ((S *ᵥ z) a * conj ((S *ᵥ w) a)) := by
  unfold hermForm
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : (S.map (starRingEnd ℂ) *ᵥ star w) a = conj ((S *ᵥ w) a) := by
    simp [mulVec, dotProduct]
  rw [this]; ring
end GlobalTheory.FramePeriod
