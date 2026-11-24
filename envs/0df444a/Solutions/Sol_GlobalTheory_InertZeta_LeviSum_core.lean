-- Prove2me | solution 1 for GlobalTheory.InertZeta.LeviSum.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:28:06.762727+00:00
-- url     : https://prove2.me/submissions/35d20fc2-ef89-4792-a90b-64d0864108ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryLeviSummationGeometricSeries
import Theorems.Thm_GlobalTheory_InertZeta_LeviSum_int_geom
import Theorems.Thm_GlobalTheory_InertZeta_LeviSum_q_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
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
open GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.LeviSum
namespace GlobalTheory.InertZeta.LeviSum
theorem _root_.solution (Y : Type) (q N : ℕ) (l : Y → ℕ) (ψ : Y → ℂ) (β X₀ Z₀ : ℂ) (hq : 1 ≤ q) (hβ : β ≠ 0)
    (hy : ‖(q : ℂ) ^ (N + 1) * X₀‖ < 1) (h1 : ‖(q : ℂ) ^ (N + 1) * X₀‖ * ‖β‖ < 1)
    (h2 : ‖(q : ℂ) ^ (N + 1) * X₀‖ * ‖β‖⁻¹ < 1)
    (hZ : HasSum (fun b => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) Z₀) :
    HasSum (fun p : ℤ × Y => ((q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X₀ ^ (p.1.natAbs + l p.2) *
      jFac q N X₀) * (β ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) * ψ p.2))
      ((1 - X₀) * (1 + q * X₀) * ((1 - (q : ℂ) ^ (N + 1) * X₀ * β)⁻¹ * (1 - (q : ℂ) ^ (N + 1) * X₀ / β)⁻¹) * Z₀) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  set y₀ := (q : ℂ) ^ (N + 1) * X₀ with hy₀
  have hA := int_geom β y₀ hβ (by rw [norm_mul]; exact h1) (by rw [norm_div, div_eq_mul_inv]; exact h2)
  have sA : Summable (fun a : ℤ => ‖β ^ a * y₀ ^ a.natAbs‖) := summable_norm_iff.mpr hA.summable
  have sB : Summable (fun b : Y => ‖((q : ℂ) ^ 2 * X₀) ^ l b * ψ b‖) := summable_norm_iff.mpr hZ.summable
  have sAB : Summable (fun p : ℤ × Y => (β ^ p.1 * y₀ ^ p.1.natAbs) * (((q : ℂ) ^ 2 * X₀) ^ l p.2 * ψ p.2)) :=
    summable_mul_of_summable_norm (f := fun a : ℤ => β ^ a * y₀ ^ a.natAbs)
      (g := fun b : Y => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) sA sB
  have hprod := (HasSum.mul (f := fun a : ℤ => β ^ a * y₀ ^ a.natAbs)
      (g := fun b : Y => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) hA hZ sAB).mul_right (jFac q N X₀)
  have n1 : 1 - y₀ * β ≠ 0 := fun h => by
    have e : ‖y₀ * β‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_mul] at e; linarith
  have n2 : 1 - y₀ / β ≠ 0 := fun h => by
    have e : ‖y₀ / β‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_div, div_eq_mul_inv] at e; linarith
  have hβy : β - y₀ ≠ 0 := fun h => n2 (by rw [← sub_eq_zero.mp h, div_self hβ, sub_self])
  have hβy' : -y₀ + β ≠ 0 := by rwa [neg_add_eq_sub]
  have n3 : 1 - y₀ ^ 2 ≠ 0 := fun h => by
    rw [sub_eq_zero] at h
    have := congrArg norm h
    rw [norm_one, norm_pow] at this
    nlinarith [norm_nonneg y₀]
  have ev : ((1 - y₀ * β)⁻¹ + y₀ / β * (1 - y₀ / β)⁻¹) * Z₀ * jFac q N X₀ =
      (1 - X₀) * (1 + q * X₀) * ((1 - y₀ * β)⁻¹ * (1 - y₀ / β)⁻¹) * Z₀ := by
    simp only [jFac]
    rw [← hy₀]
    field_simp
    ring
  rw [← ev]
  convert hprod using 1
  case e'_3 => rfl
  funext p
  obtain ⟨a, b⟩ := p
  simp only
  rw [hy₀, mul_pow, ← q_pow (q : ℂ) hq0 N a, pow_add, pow_add, mul_pow, ← pow_mul]
  ring
end GlobalTheory.InertZeta.LeviSum
