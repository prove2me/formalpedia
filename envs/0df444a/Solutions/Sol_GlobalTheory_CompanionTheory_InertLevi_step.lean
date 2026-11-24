-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertLevi.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:26:00.536486+00:00
-- url     : https://prove2.me/submissions/9762cbab-a3a9-4a87-be39-d06ecabda34d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_RecursionIdentity
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_hasSum_aTerm
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_HasLen_unique
import Theorems.Thm_GlobalTheory_InertZeta_IsInt_mul
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid



set_option autoImplicit false
noncomputable section
open GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLevi
namespace GlobalTheory.CompanionTheory.InertLevi
theorem _root_.solution : Step := by
  intro Y C q N ℓ l φ₀ α X y Z hq hα hy hy1 hya hyb H hZ
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hy' : ‖(q : ℂ) ^ (N + 1) * X‖ < 1 := hy ▸ hy1
  have h1 : ‖y * α‖ < 1 := by rwa [norm_mul]
  have h2 : ‖y / α‖ < 1 := by rwa [norm_div, div_eq_mul_inv]
  have hA := hasSum_aTerm (N := N) (X := X) (α := α) hq0 (hy ▸ h1) (hy ▸ h2)
  rw [← hy] at hA
  set A := aTerm q N X α with hAdef
  set B : Y → ℂ := fun b => ((q : ℂ) ^ 2 * X) ^ l b * φ₀ b with hBdef
  set w : ℤ × Y → ℂ := fun p => α ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) * φ₀ p.2 with hw
  set f : (ℤ × Y) × C → ℂ := fun p => X ^ ℓ p.1.1 p.1.2 p.2 *
    (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2) with hf
  have hAn : Summable fun a => ‖A a‖ := hA.summable.norm
  have hBn : Summable fun b => ‖B b‖ := hZ.summable.norm
  have hABn : Summable fun p : ℤ × Y => ‖A p.1‖ * ‖B p.2‖ :=
    hAn.mul_of_nonneg hBn (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hAB : Summable fun p : ℤ × Y => A p.1 * B p.2 :=
    Summable.of_norm (by simpa only [norm_mul] using hABn)
  have key : ∀ (X' : ℂ) (p : ℤ × Y), (q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X' ^ (p.1.natAbs + l p.2) *
      (α ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) * φ₀ p.2) =
      aTerm q N X' α p.1 * (((q : ℂ) ^ 2 * X') ^ l p.2 * φ₀ p.2) := by
    intro X' p
    rw [aTerm]
    generalize α ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) = t
    ring

  have hin : ∀ p : ℤ × Y, HasSum (fun c => f (p, c)) (jFac q N X * (A p.1 * B p.2)) := by
    intro p
    have := (H X hy' p.1 p.2).mul_right (w p)
    have e : (q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X ^ (p.1.natAbs + l p.2) * w p = A p.1 * B p.2 := key X p
    have e' : jFac q N X * (A p.1 * B p.2) = (q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) *
        X ^ (p.1.natAbs + l p.2) * jFac q N X * w p := by
      rw [← e]
      ring
    rw [e']
    exact this

  have hX' : ‖(q : ℂ) ^ (N + 1) * ((‖X‖ : ℝ) : ℂ)‖ < 1 := by
    simpa only [norm_mul, Complex.norm_real, norm_norm] using hy'
  have hR : ∀ p : ℤ × Y, ∃ v : ℝ, HasSum (fun c => ‖f (p, c)‖) v ∧
      v ≤ ‖jFac q N (‖X‖ : ℝ)‖ * (‖A p.1‖ * ‖B p.2‖) := by
    intro p
    have h3 := Complex.hasSum_re (H _ hX' p.1 p.2)
    have h4 := h3.mul_right ‖w p‖
    refine ⟨((q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * ((‖X‖ : ℝ) : ℂ) ^ (p.1.natAbs + l p.2) *
      jFac q N (‖X‖ : ℝ)).re * ‖w p‖, ?_, ?_⟩
    · have e : (fun c => ‖f (p, c)‖) = fun c => (((‖X‖ : ℝ) : ℂ) ^ ℓ p.1 p.2 c).re * ‖w p‖ := funext fun c => by
        rw [← Complex.ofReal_pow, Complex.ofReal_re]
        change ‖X ^ ℓ p.1 p.2 c * w p‖ = _
        rw [norm_mul, norm_pow]
      rw [e]
      exact h4
    · have e : ‖(q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X ^ (p.1.natAbs + l p.2)‖ * ‖w p‖ =
          ‖A p.1‖ * ‖B p.2‖ := by
        rw [← norm_mul, ← norm_mul]
        exact congrArg norm (key X p)
      have e2 : ‖(q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * ((‖X‖ : ℝ) : ℂ) ^ (p.1.natAbs + l p.2) *
          jFac q N (‖X‖ : ℝ)‖ = ‖(q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X ^ (p.1.natAbs + l p.2)‖ *
          ‖jFac q N (‖X‖ : ℝ)‖ := by
        simp only [norm_mul, norm_pow, Complex.norm_real, norm_norm]
      refine (mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (norm_nonneg _)).trans (le_of_eq ?_)
      rw [e2, ← e]
      ring
  choose v hv1 hv2 using hR
  have hfs : Summable f := by
    refine Summable.of_norm ((summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      ⟨fun p => (hv1 p).summable, ?_⟩)
    have e : (fun p => ∑' c, ‖f (p, c)‖) = v := funext fun p => (hv1 p).tsum_eq
    rw [e]
    exact Summable.of_nonneg_of_le (fun p => (hv1 p).nonneg fun _ => norm_nonneg _) hv2 (hABn.mul_left _)
  have h5 := hfs.hasSum.prod_fiberwise hin
  have h6 := (hA.mul hZ hAB).mul_left (jFac q N X)
  have h7 := h5.unique h6
  have hy2 : 1 - y ^ 2 ≠ 0 := fun h => by
    have e : y ^ 2 = 1 := by linear_combination -h
    have e2 : ‖y‖ ^ 2 = 1 := by rw [← norm_pow, e, norm_one]
    have : ‖y‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) hy1 two_ne_zero
    linarith
  have hd1 : 1 - y * α ≠ 0 := fun h => by
    have e : y * α = 1 := by linear_combination -h
    rw [e, norm_one] at h1
    exact lt_irrefl _ h1
  have hd2 : 1 - y / α ≠ 0 := fun h => by
    have e : y / α = 1 := by linear_combination -h
    rw [e, norm_one] at h2
    exact lt_irrefl _ h2
  have hval : (1 - X) * (1 + q * X) * ((1 - y * α)⁻¹ * (1 - y / α)⁻¹) * Z =
      jFac q N X * (((1 - y * α)⁻¹ + y / α * (1 - y / α)⁻¹) * Z) := by
    obtain ⟨t, ht⟩ : ∃ t, t = y / α := ⟨_, rfl⟩
    have htα : t * α = y := by rw [ht]; field_simp
    rw [← ht] at hd2 ⊢
    have e : (1 - y * α)⁻¹ + t * (1 - t)⁻¹ = (1 - y ^ 2) * ((1 - y * α)⁻¹ * (1 - t)⁻¹) := by
      field_simp
      linear_combination (-y) * htα
    rw [e, jFac, ← hy]
    field_simp
  rw [hval, ← h7]
  exact hfs.hasSum
end GlobalTheory.CompanionTheory.InertLevi
