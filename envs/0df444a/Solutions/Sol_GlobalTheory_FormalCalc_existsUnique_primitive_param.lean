-- Prove2me | solution 1 for GlobalTheory.FormalCalc.existsUnique_primitive_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:09:46.68324+00:00
-- url     : https://prove2.me/submissions/f696149d-86ea-4399-9488-cd1c54b77ca4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Theorems.Thm_GlobalTheory_FormalCalc_natCast_mul_coeff_of_pderiv_eq
import Theorems.Thm_GlobalTheory_FormalCalc_ext_of_pderiv_of_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Finsupp
variable {σ ι A : Type*} [CommRing A]
variable [Algebra ℚ A]
namespace GlobalTheory.FormalCalc
theorem _root_.solution {e : ι → σ} (he : Function.Injective e)
    (a : ι → MvPowerSeries σ A) (ha : ∀ i j, pderiv A (e i) (a j) = pderiv A (e j) (a i)) :
    ∃! f : MvPowerSeries σ A, (∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = 0) ∧
      ∀ i, pderiv A (e i) f = a i := by
  classical
  haveI : IsAddTorsionFree A := .of_module_rat A
  have key : ∀ (α : σ →₀ ℕ) (i j : ι), α (e i) ≠ 0 → α (e j) ≠ 0 →
      (α (e j) : A) * coeff (α - single (e i) 1) (a i) =
        (α (e i) : A) * coeff (α - single (e j) 1) (a j) := by
    intro α i j hi hj
    by_cases hij : i = j
    · rw [hij]
    have hne : e i ≠ e j := fun h => hij (he h)
    have e1 : (α - single (e i) 1 : σ →₀ ℕ) (e j) = α (e j) := by
      simp [single_eq_of_ne (Ne.symm hne)]
    have e2 : (α - single (e j) 1 : σ →₀ ℕ) (e i) = α (e i) := by
      simp [single_eq_of_ne hne]
    have h1 := natCast_mul_coeff_of_pderiv_eq (rfl : pderiv A (e j) (a i) = _) (e1 ▸ hj)
    have h2 := natCast_mul_coeff_of_pderiv_eq (rfl : pderiv A (e i) (a j) = _) (e2 ▸ hi)
    rw [e1] at h1
    rw [e2] at h2
    rw [h1, h2, ha, tsub_right_comm]
  let f : MvPowerSeries σ A := fun α =>
    if h : ∃ i, α (e i) ≠ 0 then
      ((α (e h.choose) : ℚ)⁻¹) • coeff (α - single (e h.choose) 1) (a h.choose) else 0
  have hf : ∀ α, coeff α f = if h : ∃ i, α (e i) ≠ 0 then
      ((α (e h.choose) : ℚ)⁻¹) • coeff (α - single (e h.choose) 1) (a h.choose) else 0 :=
    fun _ => rfl
  have hf0 : ∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = 0 := by
    intro α h
    rw [hf, dif_neg]
    push Not
    exact h
  have hf1 : ∀ i, pderiv A (e i) f = a i := by
    intro i
    ext n
    have hi : (n + single (e i) 1 : σ →₀ ℕ) (e i) ≠ 0 := by simp
    have hex : ∃ j, (n + single (e i) 1 : σ →₀ ℕ) (e j) ≠ 0 := ⟨i, hi⟩
    have hk := key _ hex.choose i hex.choose_spec hi
    have hq : (((n + single (e i) 1 : σ →₀ ℕ) (e hex.choose) : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hex.choose_spec
    rw [add_tsub_cancel_right] at hk
    rw [coeff_pderiv, hf, dif_pos hex, smul_mul_assoc, mul_comm]
    have : ((n (e i) : A) + 1) = (((n + single (e i) 1 : σ →₀ ℕ) (e i) : ℕ) : A) := by simp
    rw [this, hk, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hq,
      one_smul]
  refine ⟨f, ⟨hf0, hf1⟩, fun g hg => ?_⟩
  exact ext_of_pderiv_of_coeff e (fun i => by rw [hg.2, hf1]) fun α h => by rw [hg.1 α h, hf0 α h]
end GlobalTheory.FormalCalc
