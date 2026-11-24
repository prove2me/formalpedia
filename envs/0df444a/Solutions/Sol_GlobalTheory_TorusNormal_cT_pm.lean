-- Prove2me | solution 1 for GlobalTheory.TorusNormal.cT_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:12:41.144312+00:00
-- url     : https://prove2.me/submissions/ea8a1f9d-7f84-4be9-9627-bb819746d683

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UniformizerPowerTorusMemNormalUnitarySubgroup
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
theorem _root_.solution {n : ℕ} (σ : L →+* L) (f g : Fin n → L) :
    cT σ (pm f g) = pm (fun i => σ (f i)) (fun i => σ (g (Fin.rev i))) := by
  ext i j
  simp only [cT, pm, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_add]
  have h2 : (i = Fin.rev j) ↔ (j = Fin.rev i) := by
    constructor <;> rintro rfl <;> simp
  by_cases h1 : j = i
  · subst h1; by_cases h3 : j = Fin.rev j
    · rw [if_pos rfl, if_pos rfl, if_pos h3, if_pos h3, ← h3]
    · rw [if_pos rfl, if_pos rfl, if_neg h3, if_neg h3, map_zero]
  · rw [if_neg (Ne.symm h1), if_neg h1, map_zero]
    by_cases h3 : j = Fin.rev i
    · rw [if_pos (h2.2 h3), if_pos h3, h3]
    · rw [if_neg (fun h => h3 (h2.1 h)), if_neg h3, map_zero]
end GlobalTheory.TorusNormal
