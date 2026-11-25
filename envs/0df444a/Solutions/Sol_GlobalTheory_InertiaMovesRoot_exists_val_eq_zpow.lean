-- Prove2me | solution 1 for GlobalTheory.InertiaMovesRoot.exists_val_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:51:26.730695+00:00
-- url     : https://prove2.me/submissions/1178aaac-2c91-4aff-bcef-e1a967505b78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCongOfCongOnFixed
import Theorems.Thm_GlobalTheory_InertiaMovesRoot_val_eq_one_of_notMem
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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise
open GlobalTheory GlobalTheory.InertiaMovesRoot
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
namespace GlobalTheory.InertiaMovesRoot
theorem _root_.solution (h : IsPlaceOver A w) {ϖ : 𝓞 E} (h1 : ϖ ∈ w.asIdeal)
    (h2 : ϖ ∉ w.asIdeal ^ 2) {a : E} (ha : a ≠ 0) :
    ∃ m : ℤ, A.valuation (algebraMap E Ω a) = A.valuation (algebraMap E Ω (ϖ : E)) ^ m := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hϖ0' : (ϖ : E) ≠ 0 := by simpa using hϖ0
  have hv : w.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
    have a1 := (w.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
    have a2 : ¬ _ := fun hh => h2 ((w.intValuation_le_pow_iff_mem ϖ 2).1 hh)
    rw [← WithZero.exp_log (w.intValuation_ne_zero ϖ hϖ0), WithZero.exp_le_exp] at a1 a2
    rw [← WithZero.exp_log (w.intValuation_ne_zero ϖ hϖ0)]
    congr 1
    omega
  have hv' : w.valuation E (ϖ : E) = WithZero.exp (-1 : ℤ) := by
    rw [← hv]; exact w.valuation_of_algebraMap ϖ
  have ha' : w.valuation E a ≠ 0 := by simpa using ha
  set n := WithZero.log (w.valuation E a)
  have hu : w.valuation E (a * (ϖ : E) ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hv', ← WithZero.exp_log ha', ← WithZero.exp_zsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero]
    congr 1
    simp [n]
  obtain ⟨t, d, htd⟩ := w.exists_primeCompl_mul_eq_of_integer _ hu.le
  have hd : w.valuation E (algebraMap (𝓞 E) E d) = 1 := (w.valuation_eq_one_iff_notMem).2 d.2
  have ht : w.valuation E (algebraMap (𝓞 E) E t) = 1 := by rw [← htd, map_mul, hu, hd, one_mul]
  have ht' := val_eq_one_of_notMem h ((w.valuation_eq_one_iff_notMem).1 ht)
  have hd' := val_eq_one_of_notMem h d.2
  have e := congrArg (fun z => A.valuation (algebraMap E Ω z)) htd
  simp only [map_mul, map_zpow₀] at e
  change _ * A.valuation (algebraMap E Ω ((d : 𝓞 E) : E)) = A.valuation (algebraMap E Ω (t : E)) at e
  rw [ht', hd', mul_one] at e
  exact ⟨-n, by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left e⟩
end GlobalTheory.InertiaMovesRoot
