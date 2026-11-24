-- Prove2me | solution 1 for GlobalTheory.InertZeta.v_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:32:42.783483+00:00
-- url     : https://prove2.me/submissions/da9e1246-58e9-4cdf-9a60-96e2ffc4aa4d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_cartan_exists_glint
import Theorems.Thm_Formalism_UG_P_cartan_val_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution {a a' : Matrix (Fin n) (Fin n) L} (ha : IsInt a) (ha' : IsInt a') (e : a * a' = 1) :
    Valued.v a.det = 1 := by
  obtain ⟨U, hU, rfl⟩ := P.cartan_exists_glint (intL L) a a' e ha ha'
  exact P.cartan_val_det (intL L) Valued.v (fun _ => Iff.rfl) U hU
end GlobalTheory.InertZeta
