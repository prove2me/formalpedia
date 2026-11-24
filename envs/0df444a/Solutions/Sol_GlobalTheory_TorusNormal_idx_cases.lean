-- Prove2me | solution 1 for GlobalTheory.TorusNormal.idx_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:14:25.777617+00:00
-- url     : https://prove2.me/submissions/973e6f89-a56b-4097-8c25-49438857d116

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UniformizerPowerTorusMemNormalUnitarySubgroup
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.TorusNormal
open Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.TorusNormal
theorem _root_.solution {n : ℕ} (i : Fin n) :
    (2 * i.val + 1 < n ∧ ¬ 2 * (Fin.rev i).val + 1 < n) ∨
    (¬ 2 * i.val + 1 < n ∧ 2 * (Fin.rev i).val + 1 < n) ∨
    (¬ 2 * i.val + 1 < n ∧ ¬ 2 * (Fin.rev i).val + 1 < n ∧ Fin.rev i = i) := by
  have := i.isLt
  rw [Fin.val_rev]
  by_cases h : 2 * i.val + 1 < n
  · left; omega
  · right
    by_cases h' : 2 * (n - (i.val + 1)) + 1 < n
    · left; omega
    · right; refine ⟨h, h', ?_⟩
      rw [Fin.ext_iff, Fin.val_rev]; omega
end GlobalTheory.TorusNormal
