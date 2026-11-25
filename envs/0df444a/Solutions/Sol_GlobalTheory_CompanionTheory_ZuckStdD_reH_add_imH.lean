-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckStdD.reH_add_imH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:04:31.502228+00:00
-- url     : https://prove2.me/submissions/7223d46d-6f1f-4fa3-947d-17dfcdf0c0ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StandardDifferential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckStdD
namespace GlobalTheory.CompanionTheory.ZuckStdD
theorem _root_.solution (k r : ℕ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    reH k r Y + Complex.I • imH k r Y = Y := by
  unfold reH imH
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    have := Complex.I_ne_zero
    field_simp
  rw [smul_smul, hI, ← smul_add]
  have : ∀ Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Y + Z + (Y - Z) = (2 : ℂ) • Y := by
    intro Z; rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num
end GlobalTheory.CompanionTheory.ZuckStdD
