-- Prove2me | solution 1 for GlobalTheory.InertZeta.len_mat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:26:11.409949+00:00
-- url     : https://prove2.me/submissions/c91b2d74-45ff-453e-85a5-11fdd9c45e8d

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_GlobalTheory_InertZeta_len_mul_mul
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_fSatake_K_int
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_mul_inv


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
theorem _root_.solution {σ : L →+* L} {a b : GU σ n} (ha : a ∈ KU σ n) (hb : b ∈ KU σ n) (g : GU σ n) :
    len (mat (a * g * b)) = len (mat g) :=
  len_mul_mul (P.fSatake_K_int ha) (P.fSatake_K_int (inv_mem ha)) (P.fSatake_K_int hb) (P.fSatake_K_int (inv_mem hb))
    (mat_inv_mul a) (mat_mul_inv b)
end GlobalTheory.InertZeta
