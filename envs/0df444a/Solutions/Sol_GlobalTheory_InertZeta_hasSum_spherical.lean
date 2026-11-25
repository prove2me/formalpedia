-- Prove2me | solution 1 for GlobalTheory.InertZeta.hasSum_spherical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:35:44.256367+00:00
-- url     : https://prove2.me/submissions/e317a15f-0b5c-4b40-afce-7bcd67b158c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumSpherical
import Theorems.Thm_GlobalTheory_InertZeta_constTerm
import Theorems.Thm_GlobalTheory_InertZeta_bijective_cells
import Theorems.Thm_GlobalTheory_InertZeta_zVal_succ
import Theorems.Thm_GlobalTheory_InertZeta_hasSum_small
import Theorems.Thm_GlobalTheory_InertZeta_len_of_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_SphericalExistsU
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_len_mat_mul
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


section
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
namespace GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q N : ℕ}
private lemma ordL_one_twisted_operators : ordL (1 : L) = 0 := by
  have h : Valued.v (1 : L) ≠ 0 := by simp
  have hu : WithZero.unzero h = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  unfold ordL
  rw [dif_neg h, hu]
  simp
private lemma chiDeltaU_one' {n m : ℕ} (α : Fin m → ℂ) : chiDeltaU (σ := σ) (n := n) q α 1 = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · simp [ordL_one_twisted_operators]
  · rfl
private lemma isBorelU_one' {n : ℕ} : IsBorelU (1 : GU σ n) := by
  intro i j h
  simp [Matrix.one_apply_ne h.ne']
private lemma isSphericalU_apply_mul_of_mem_KU {n m : ℕ} {α : Fin m → ℂ} {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) (g k : GU σ n)
    (hk : k ∈ KU σ n) : φ (g * k) = φ g := by
  have h := hφ 1 g k isBorelU_one' hk
  rwa [one_mul, chiDeltaU_one', one_mul] at h
private lemma exists_mem_KU_out_mk_eq_mul {n : ℕ} (g : GU σ n) :
    ∃ k ∈ KU σ n, (QuotientGroup.mk g : GU σ n ⧸ KU σ n).out = g * k := by
  refine ⟨g⁻¹ * (QuotientGroup.mk g : GU σ n ⧸ KU σ n).out, ?_, (mul_inv_cancel_left _ _).symm⟩
  have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : GU σ n ⧸ KU σ n))
  simpa [_root_.mul_inv_rev] using inv_mem h
end GlobalTheory.InertZeta
end
end

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q N : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution [CompleteSpace L] (hF : FracExists) (hP : Pointwise) (hC : Count) (hS : SmallCorner)
    (hG : GenFun) (hSu : CosetSurj) (hI : CosetInj) (hL : LeviExists) (hT : SphTrans) (hR : SmallRank) (hSt : Step)
    (hU : IsUnramInv ϖ σ q) (r : ℕ) : ∀ (n : ℕ), 2 * r ≤ n → n ≤ 2 * r + 1 → ∀ (α : Fin r → ℂ) (X y : ℂ)
      (φ : GU σ n → ℂ), (∀ i, α i ≠ 0) → y * q = X * (q : ℂ) ^ n → ‖y‖ < 1 →
      (∀ i, ‖y‖ * ‖α i‖ < 1 ∧ ‖y‖ * ‖α i‖⁻¹ < 1) → IsSphericalU q α φ → φ 1 = 1 →
      HasSum (fun x : GU σ n ⧸ KU σ n => X ^ len (mat x.out) * φ x.out) (zVal q n X y α) := by
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  induction r with
  | zero =>
    intro n hn0 hn1 α X y φ _ hyX hy _ hφ h1
    have hn : n ≤ 1 := by omega
    have hK : ∀ g : GU σ n, g ∈ KU σ n := fun g => hR L ϖ σ q n hU hn g
    have hφk : ∀ g : GU σ n, φ g = 1 := by
      intro g
      have h := isSphericalU_apply_mul_of_mem_KU hφ 1 g (hK g)
      rwa [one_mul, h1] at h
    have hsum := hasSum_small hR hU hn (fun g => X ^ len (mat g) * φ g)
      (fun k hk => by rw [len_of_mem hk, hφk, pow_zero, one_mul])
    convert hsum using 1
    interval_cases n
    · simp [zVal]
    · have hyx : y = X := by
        apply mul_right_cancel₀ hq0
        rw [hyX]; ring
      subst hyx
      have hy1 : (1 : ℂ) - y ≠ 0 := by
        intro h
        have h' : y = 1 := by linear_combination -h
        rw [h'] at hy; simp at hy
      simp [zVal, hy1]
  | succ r ih =>
    intro n hn0 hn1 α X y φ hα hyX hy hαy hφ h1
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
    obtain ⟨φ₀, hφ₀, hφ₀1, -⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q N r hU (by omega) (by omega)
      (Fin.tail α) (fun i => hα _)
    have hZ := ih N (by omega) (by omega) (Fin.tail α) ((q : ℂ) ^ 2 * X) y φ₀ (fun i => hα _)
      (by rw [hyX]; ring) hy (fun i => hαy _) hφ₀ hφ₀1
    have hy' : y = (q : ℂ) ^ (N + 1) * X := by
      apply mul_right_cancel₀ hq0
      rw [hyX]; ring
    choose m hm using fun (a : ℤ) (b : GU σ N ⧸ KU σ N) => hL L ϖ σ q N hU a b.out
    have hstep := hSt (GU σ N ⧸ KU σ N) (RadQuot σ N) q N
      (fun a b c => len (mat (m a b * (c.out : radQ σ N).1))) (fun b => len (mat b.out)) (fun b => φ₀ b.out)
      (α 0) X y (zVal q N ((q : ℂ) ^ 2 * X) y (Fin.tail α))
      (by omega) (hα 0) hy' hy (hαy 0).1 (hαy 0).2
      (fun X' hX' a b => constTerm hF hP hC hS hG hU (hm a b) X' hX') hZ
    rw [zVal_succ, ← (Equiv.ofBijective _ (bijective_cells hSu hI hU m hm)).hasSum_iff]
    convert hstep using 1
    funext p
    obtain ⟨⟨a, b⟩, c⟩ := p
    simp only [Function.comp_apply, Equiv.ofBijective_apply]
    obtain ⟨k, hk, hout⟩ := exists_mem_KU_out_mk_eq_mul (m a b * (c.out : radQ σ N).1)
    have hlen := len_mat_mul (KU σ (N + 2)).one_mem hk (m a b * (c.out : radQ σ N).1)
    rw [one_mul] at hlen
    rw [hout, isSphericalU_apply_mul_of_mem_KU hφ _ _ hk, hlen,
      hT L ϖ σ q N r hU (by omega) α φ φ₀ hα hφ h1 hφ₀ hφ₀1 a b.out (m a b) (hm a b) _ (c.out : radQ σ N).2]
end GlobalTheory.InertZeta
