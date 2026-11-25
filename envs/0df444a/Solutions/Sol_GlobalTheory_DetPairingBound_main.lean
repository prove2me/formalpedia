-- Prove2me | solution 1 for GlobalTheory.DetPairingBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:22:37.318151+00:00
-- url     : https://prove2.me/submissions/f86eed23-b828-4acf-9cf2-a7731385e56e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBound
import Theorems.Thm_GlobalTheory_DetPairingBound_coeff_cayDet_pow_nonneg
import Theorems.Thm_GlobalTheory_DetPairingBound_sum_eq_of_mem_support
import Theorems.Thm_GlobalTheory_DetPairingBound_le_val_div
import Theorems.Thm_GlobalTheory_DetPowPairing_main
import Theorems.Thm_GlobalTheory_LegendreBounds_legendre_bounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_div_eq_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_natCast_eq_factorization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.DetPairingBound
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
namespace GlobalTheory.DetPairingBound
theorem _root_.solution : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (i n₀ s : ℕ) (Q : MvPolynomial (Fin n₀ × Fin n₀) C), 1 ≤ s → 1 ≤ n₀ →
    (∀ A, (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.coeff A Q)) →
    (((s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (3 * Real.logb l n₀ + 2 * Real.logb l s + i + 3) : ℝ) : WithTop ℝ) ≤
      v ((∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * s)) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (Q)) / (∑ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * s)) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * s))))) := by
  intro C _ _ v l hl hvl i n₀ s Q hs hn₀ hQ
  have hvnat : ∀ m : ℕ, m ≠ 0 → v (m : C) = ((padicValNat l m : ℝ) : WithTop ℝ) := by
    intro m hm
    rw [natCast_eq_factorization v hl hvl hm, Nat.factorization_def m hl]
  obtain ⟨-, hL2, hL3⟩ := GlobalTheory.LegendreBounds.legendre_bounds l hl
  have hk0 : l ^ i * s ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hl.ne_zero) (by omega)

  have hP := GlobalTheory.DetPowPairing.main C n₀ (l ^ i * s)
  rw [← Nat.cast_prod, ← Nat.cast_prod] at hP
  have hF0 : (∏ c ∈ Finset.range n₀, c.factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun c _ => Nat.factorial_ne_zero c
  have hF1 : (∏ c ∈ Finset.range n₀, (l ^ i * s + c).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun c _ => Nat.factorial_ne_zero _
  have hF0' : ((∏ c ∈ Finset.range n₀, c.factorial : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.mpr hF0
  have hDen := (eq_div_iff hF0').mpr ((mul_comm _ _).trans hP)
  have hvD := div_eq_coe v hF0' (hvnat _ hF1) (hvnat _ hF0)
  rw [← hDen] at hvD

  obtain ⟨wb, hwb⟩ : ∃ wb : ℝ, wb = (n₀ : ℝ) * ((l : ℝ) ^ i * s) / ((l : ℝ) - 1) -
      (n₀ : ℝ) ^ 2 * (Real.logb l ((n₀ : ℝ) * ((l : ℝ) ^ i * s)) + 1) := ⟨_, rfl⟩
  obtain ⟨qb, hqb⟩ : ∃ qb : ℝ, qb = (s : ℝ) / 8 - (n₀ : ℝ) ^ 2 * (Real.logb l (n₀ * s) + 1) :=
    ⟨_, rfl⟩
  have hnum : ∀ A ∈ (cayDet n₀ C ^ (l ^ i * s)).support, ((wb + qb : ℝ) : WithTop ℝ) ≤
      v (MvPolynomial.coeff A (cayDet n₀ C ^ (l ^ i * s)) * (A.prod fun _ e => (e.factorial : C)) *
        MvPolynomial.coeff A Q) := by
    intro A hA
    have hsum := sum_eq_of_mem_support C n₀ (l ^ i * s) A hA
    have hW := hL2 (Fin n₀ × Fin n₀) A
      (by rw [hsum]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hk0))
    rw [hsum] at hW
    simp only [Fintype.card_prod, Fintype.card_fin] at hW
    push_cast at hW
    have hwt : (A.prod fun _ e => (e.factorial : C)) = ((∏ j, (A j).factorial : ℕ) : C) := by
      rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Nat.cast_prod]
    have hne : (∏ j, (A j).factorial) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _
    have h2 : (wb : WithTop ℝ) ≤ ((padicValNat l (∏ j, (A j).factorial) : ℝ) : WithTop ℝ) :=
      WithTop.coe_le_coe.mpr (by rw [hwb, sq]; linarith)
    have h3 : (qb : WithTop ℝ) ≤ v (MvPolynomial.coeff A Q) := by
      rw [hqb]; exact hQ A
    rw [AddValuation.map_mul, AddValuation.map_mul, hwt, hvnat _ hne]
    calc ((wb + qb : ℝ) : WithTop ℝ) = 0 + (wb : WithTop ℝ) + (qb : WithTop ℝ) := by
          rw [zero_add, WithTop.coe_add]
      _ ≤ _ := add_le_add (add_le_add (coeff_cayDet_pow_nonneg C v n₀ _ A) h2) h3
  refine le_val_div v (a := wb + qb) (AddValuation.map_le_sum v hnum) hvD ?_

  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hn1 : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hn0 : (n₀ : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n₀).ne'
  have hs0 : (s : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < s).ne'
  have hli : (l : ℝ) ^ i ≠ 0 := pow_ne_zero _ (by linarith : (0 : ℝ) < l).ne'
  have hLn := Real.logb_nonneg hl1 hn1
  have hLs := Real.logb_nonneg hl1 hs1
  have hlK : Real.logb l ((n₀ : ℝ) * ((l : ℝ) ^ i * s)) =
      Real.logb l n₀ + i + Real.logb l s := by
    rw [Real.logb_mul hn0 (mul_ne_zero hli hs0), Real.logb_mul hli hs0, Real.logb_pow,
      Real.logb_self_eq_one hl1]
    ring
  have hlQ : Real.logb l ((n₀ : ℝ) * s) = Real.logb l n₀ + Real.logb l s :=
    Real.logb_mul hn0 hs0
  have h3 := hL3 n₀ (l ^ i * s)
  push_cast at h3
  have hsq : (n₀ : ℝ) * (Real.logb l n₀ + 1) ≤ (n₀ : ℝ) ^ 2 * (Real.logb l n₀ + 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  rw [hwb, hqb, hlK, hlQ]
  linarith
end GlobalTheory.DetPairingBound
