-- Prove2me | solution 1 for GlobalTheory.TorusNormal.diagonal_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:48:19.206151+00:00
-- url     : https://prove2.me/submissions/88645f05-1843-45e0-bc51-a472e2db6133

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
theorem _root_.solution {n : ℕ} (d : Fin n → L) : Matrix.diagonal d = pm d 0 := by
  ext i j
  simp only [Matrix.diagonal_apply, pm, Matrix.of_apply, Pi.zero_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]; simp
end GlobalTheory.TorusNormal
