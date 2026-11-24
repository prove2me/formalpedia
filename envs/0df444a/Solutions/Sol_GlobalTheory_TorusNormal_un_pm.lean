-- Prove2me | solution 1 for GlobalTheory.TorusNormal.un_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:58:08.455149+00:00
-- url     : https://prove2.me/submissions/9ae768d7-7957-449f-9410-cc34e019539e

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UniformizerPowerTorusMemNormalUnitarySubgroup
import Theorems.Thm_GlobalTheory_TorusNormal_pm_mul
import Theorems.Thm_GlobalTheory_TorusNormal_cT_pm
import Theorems.Thm_GlobalTheory_TorusNormal_antiJ_pm
import Theorems.Thm_GlobalTheory_TorusNormal_pm_supp_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.TorusNormal
open Formalism.UG.P
variable {L : Type} [Field L]
namespace GlobalTheory.TorusNormal
theorem _root_.solution {n : ℕ} (σ : L →+* L) (u : Fin n → L) (hσ : ∀ i, σ (u i) = -u i)
    (hsupp : ∀ i, u i ≠ 0 → 2 * i.val + 1 < n) : fIwasawaUn σ (pm 1 u) := by
  unfold fIwasawaUn
  rw [cT_pm, antiJ_pm, pm_mul, pm_mul]
  congr 1 <;> funext i
  · simp [hσ]
  · simp [hσ, pm_supp_mul u hsupp i]
end GlobalTheory.TorusNormal
