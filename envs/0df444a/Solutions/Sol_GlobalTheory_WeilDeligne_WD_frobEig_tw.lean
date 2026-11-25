-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.frobEig_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:10:24.55609+00:00
-- url     : https://prove2.me/submissions/d2209007-d25c-4fbc-a674-2df3d520d853

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
import Theorems.Thm_GlobalTheory_WeilDeligne_Unram_exists_diag
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
theorem _root_.solution (a : WD h) (s : ℝ) (ha : unr a) :
    frobEig (lpTw a s) = (frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) := by
  obtain ⟨n, c, rfl⟩ := exists_diag ha
  have : mk ((WDRep.diag h c).tw s) = mk (WDRep.diag h fun i => c i * qPow w s) :=
    sound ⟨.refl _ _, fun σ v => funext fun i => by simp [mul_zpow]; ring, fun v => rfl⟩
  rw [lpTw_mk, this, frobEig_diag, frobEig_diag, Multiset.map_map]
  simp
end GlobalTheory.WeilDeligne.WD
