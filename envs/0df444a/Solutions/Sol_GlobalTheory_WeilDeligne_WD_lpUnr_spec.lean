-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.lpUnr_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:56:49.721798+00:00
-- url     : https://prove2.me/submissions/6473dd79-ccec-4258-84e7-677e46a3e79b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
import Theorems.Thm_GlobalTheory_WeilDeligne_WDRep_unr_diag
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_coe_unitOf
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_frobEig_diag
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
open GlobalTheory.WeilDeligne.WD
open Unram
namespace GlobalTheory.WeilDeligne.WD
theorem _root_.solution (m : Multiset ℂ) (hm : (0 : ℂ) ∉ m) :
    unr (lpUnr h m) ∧ frobEig (lpUnr h m) = m ∧ lpDim (lpUnr h m) = Multiset.card m := by
  classical
  refine ⟨(unr_mk _).mpr (WDRep.unr_diag _), ?_, ?_⟩
  · rw [lpUnr, frobEig_diag]
    conv_rhs => rw [← Multiset.map_univ_coe m]
    refine Multiset.map_congr rfl fun i _ => coe_unitOf fun h0 => hm ?_
    rw [← h0]; exact Multiset.coe_mem
  · simp [lpUnr]
end GlobalTheory.WeilDeligne.WD
