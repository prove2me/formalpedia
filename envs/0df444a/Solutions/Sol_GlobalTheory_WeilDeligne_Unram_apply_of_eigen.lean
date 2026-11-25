-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.Unram.apply_of_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:46:42.525483+00:00
-- url     : https://prove2.me/submissions/0358c28a-06d8-42dc-ab09-89cc73b6d738

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_exists_eq_zpow_mul
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
open GlobalTheory.WeilDeligne.Unram
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
namespace GlobalTheory.WeilDeligne.Unram
theorem _root_.solution {a : WDRep h V} (ha : a.Unr) {v : V} {c : ℂˣ}
    (hv : a.ρ (frob h) v = (c : ℂ) • v) (σ : Weil h) : a.ρ σ v = (c : ℂ) ^ deg σ • v := by
  have hc : (c : ℂ) ≠ 0 := c.ne_zero
  have hinv : a.ρ (frob h)⁻¹ v = (c : ℂ)⁻¹ • v := by
    have := congrArg (a.ρ (frob h)⁻¹) hv
    rw [← End.mul_apply, ← map_mul, inv_mul_cancel, map_one, End.one_apply, map_smul] at this
    rw [eq_inv_smul_iff₀ hc, ← this]
  have hk : ∀ k : ℤ, a.ρ (frob h ^ k) v = (c : ℂ) ^ k • v := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, map_mul, End.mul_apply, hv, map_smul, ih, smul_smul, zpow_add_one₀ hc,
        mul_comm]
    | pred k ih =>
      rw [zpow_sub_one, map_mul, End.mul_apply, hinv, map_smul, ih, smul_smul, zpow_sub_one₀ hc,
        mul_comm]
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  conv_lhs => rw [hτ]
  rw [map_mul, ha.2, mul_one, hk]
end GlobalTheory.WeilDeligne.Unram
