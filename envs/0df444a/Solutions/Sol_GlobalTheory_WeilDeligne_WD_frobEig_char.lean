-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.frobEig_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:15:48.969471+00:00
-- url     : https://prove2.me/submissions/96a2ac17-201f-47e0-aea0-269254510fd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
import Theorems.Thm_GlobalTheory_WeilDeligne_Unram_exists_diag
import Theorems.Thm_GlobalTheory_WeilDeligne_Unram_diag_eq_diag
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_diag
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
theorem _root_.solution (a χ : WD h) (z : ℂ) (ha : unr a) (hχ : unr χ) (hz : frobEig χ = {z}) :
    frobEig (lpChar a χ) = (frobEig a).map (· * z) := by
  obtain ⟨n, c, rfl⟩ := exists_diag ha
  obtain ⟨m, d, rfl⟩ := exists_diag hχ
  have h0 : z ≠ 0 := by
    rintro rfl
    rw [frobEig_diag] at hz
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp (hz ▸ Multiset.mem_singleton_self (0 : ℂ))
    exact (d i).ne_zero hi
  have e : mk (WDRep.diag h d) = mk (WDRep.diag h fun _ : Unit => Units.mk0 z h0) :=
    diag_eq_diag (by rw [← frobEig_diag (h := h), hz]; simp)
  rw [e, lpChar_diag, frobEig_diag, frobEig_diag, Multiset.map_map,
    ← Finset.map_univ_equiv (Equiv.prodPUnit (Fin n)).symm]
  rw [Finset.map_val, Multiset.map_map]
  rfl
end GlobalTheory.WeilDeligne.WD
