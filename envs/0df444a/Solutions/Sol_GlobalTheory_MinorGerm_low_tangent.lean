-- Prove2me | solution 1 for GlobalTheory.MinorGerm.low_tangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:21:46.67132+00:00
-- url     : https://prove2.me/submissions/4740b562-b89a-4203-962b-4179215e6478

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_Low_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type}
namespace GlobalTheory.MinorGerm
theorem _root_.solution {t : σ → MvPowerSeries σ C} (ht : TangentId t) (x : σ) (n : ℕ) :
    Low (Finsupp.single x n) (t x ^ n) := by
  classical
  have h1 : Low (Finsupp.single x 1) (t x) := by
    refine ⟨?_, ?_⟩
    · rw [ht x _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X, if_pos rfl]
    · intro m hm hne
      rw [Finsupp.degree_single] at hm
      rw [ht x m hm, MvPowerSeries.coeff_X, if_neg hne]
  have h2 := h1.pow n
  rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at h2
end GlobalTheory.MinorGerm
