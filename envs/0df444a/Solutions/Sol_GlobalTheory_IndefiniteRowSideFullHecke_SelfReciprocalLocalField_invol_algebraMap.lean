-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:18:45.645455+00:00
-- url     : https://prove2.me/submissions/03e2c451-57ac-4a03-a004-e1715d6d4481

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
theorem _root_.solution (e : E) :
    invol P (algebraMap E (Fld P) e) = algebraMap E (Fld P) (IsCMField.complexConj E e) :=
  AdjoinRoot.lift_of (eval₂_conj_inv_root P)
end GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
