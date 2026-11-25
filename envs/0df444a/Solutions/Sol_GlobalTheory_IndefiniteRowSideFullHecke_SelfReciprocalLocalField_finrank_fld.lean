-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.finrank_fld
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:30.83745+00:00
-- url     : https://prove2.me/submissions/93cfa6ad-af53-4192-ae24-12e3ef18567a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SelfReciprocalLocalField
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_trans


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
theorem _root_.solution : Module.finrank E (Fld P) = r :=
  (AdjoinRoot.powerBasis (f := P.1) P.2.1.ne_zero).finrank.trans P.2.2.2.1
end GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
