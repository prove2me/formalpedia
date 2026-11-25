-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:51:34.770634+00:00
-- url     : https://prove2.me/submissions/64a50df2-f794-45a0-84c0-b25f18563e5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SelfReciprocalLocalField
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfReciprocalLocalField_invol_algebraMap
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfReciprocalLocalField_invol_alpha
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
variable {r : ℕ} (P : SelfRecip E r)
namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
theorem _root_.solution (y : Fld P) : invol P (invol P y) = y := by
  have : ((invol P : Fld P →+* Fld P).comp (invol P : Fld P →+* Fld P)) = RingHom.id _ := by
    refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
    · change invol P (invol P (algebraMap E (Fld P) e)) = algebraMap E (Fld P) e
      simp [invol_algebraMap]
    · change invol P (invol P (alpha P)) = alpha P
      simp [invol_alpha]
  exact DFunLike.congr_fun this y
end GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField
