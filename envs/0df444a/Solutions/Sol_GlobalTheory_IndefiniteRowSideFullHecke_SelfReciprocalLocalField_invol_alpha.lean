-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_alpha
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:23:01.151745+00:00
-- url     : https://prove2.me/submissions/80214c4b-b98a-456b-9730-0cfe4712866d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SelfReciprocalLocalField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
variable {r : ℕ} (P : SelfRecip E r)
namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
theorem _root_.solution : invol P (alpha P) = (alpha P)⁻¹ :=
  AdjoinRoot.lift_root (eval₂_conj_inv_root P)
end GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
