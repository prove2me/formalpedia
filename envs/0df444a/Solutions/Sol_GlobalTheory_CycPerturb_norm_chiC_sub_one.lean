-- Prove2me | solution 1 for GlobalTheory.CycPerturb.norm_chiC_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:10.506686+00:00
-- url     : https://prove2.me/submissions/f6ca9841-4c65-4cad-858f-f0130c73c982

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbation
import Theorems.Thm_GlobalTheory_CycPerturb_norm_zpow_sub_one_le
import Theorems.Thm_GlobalTheory_CycPerturb_pow_lt_rho
import Theorems.Thm_GlobalTheory_CycPerturb_rho_lt_one
import Theorems.Thm_GlobalTheory_CloseToUnitNorm_norm_zpow_sub_one_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycPerturb
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycPerturb
theorem _root_.solution {χ : GQ l →* ℚ_[l]ˣ} {K : FinExt l} {j : ℕ} (hj : Lev l j) {g : GQ l}
    (hg : IsGen χ K j g) (i : ℤ) : ‖chiC χ i g - 1‖ < rho1 l := by
  have h1 : ‖(χ g : ℚ_[l]) - 1‖ < rho1 l := hg.2 ▸ pow_lt_rho hj
  have h2 := norm_zpow_sub_one_le _ (h1.trans rho_lt_one) i
  have e : chiC χ i g - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1) := by
    simp [chiC]
  rw [e, norm_algebraMap']
  exact h2.trans_lt h1
end GlobalTheory.CycPerturb
