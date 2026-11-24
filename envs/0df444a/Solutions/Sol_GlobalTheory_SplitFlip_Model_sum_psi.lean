-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Model.sum_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:06:19.971852+00:00
-- url     : https://prove2.me/submissions/de0c38fe-8fe6-428c-be5f-557bd98f2683

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
import Theorems.Thm_GlobalTheory_SplitFlip_Model_val_le_iff_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
open Classical
namespace GlobalTheory.SplitFlip.Model
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (e : ℕ) (s s' : Res k e) :
    ∑ t : Res k e, (ψ (((Quotient.out t : 𝒪[k]) : k) *
      ((((ϖ ^ e)⁻¹ : kˣ) : k) * (((Quotient.out s : 𝒪[k]) : k) - ((Quotient.out s' : 𝒪[k]) : k)))) : ℂ) =
      if s = s' then (Fintype.card (Res k e) : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  set x : k := (((ϖ ^ e)⁻¹ : kˣ) : k) * (((Quotient.out s : 𝒪[k]) : k) - ((Quotient.out s' : 𝒪[k]) : k)) with hx
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  have hvx : valuation k x = (valuation k ((ϖ ^ e : kˣ) : k))⁻¹ *
      valuation k ((Quotient.out s - Quotient.out s' : 𝒪[k]) : k) := by
    rw [hx, map_mul, Units.val_inv_eq_inv_val, map_inv₀]; rfl
  have triv : ∀ y : k, valuation k y ≤ 1 → ψ y = 1 := fun y hy => (hψ 1).2 le_rfl y (by simpa using hy)
  have hx1 : ¬ valuation k x ≤ valuation k ((1 : kˣ) : k) := by
    intro H
    rw [hvx, Units.val_one, map_one, inv_mul_le_iff₀ h0, mul_one, ← val_le_iff_mem hϖ, ← Ideal.Quotient.eq] at H
    exact h (by simpa using H)
  rw [← hψ x] at hx1
  push Not at hx1
  obtain ⟨y, hy, hy'⟩ := hx1
  have hx0 : x ≠ 0 := by
    rintro H
    rw [H, map_zero, le_zero_iff, map_eq_zero] at hy
    exact hy' (by simp [hy])
  have hr : y / x ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, map_div₀]; exact div_le_one_of_le₀ hy zero_le
  have key : ∀ a b : 𝒪[k], Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b →
      ψ ((a : k) * x) = ψ ((b : k) * x) := fun a b hab => by
    rw [Ideal.Quotient.eq, val_le_iff_mem hϖ] at hab
    rw [show (a : k) * x = b * x + ((a - b : 𝒪[k]) : k) * x by push_cast; ring, AddChar.map_add_eq_mul,
      triv (((a - b : 𝒪[k]) : k) * x), mul_one]
    rw [map_mul, hvx, ← mul_assoc]
    exact mul_le_one' (by rw [mul_inv_le_iff₀ h0, one_mul]; exact hab) (Quotient.out s - Quotient.out s' : 𝒪[k]).2
  set S := ∑ t : Res k e, (ψ (((Quotient.out t : 𝒪[k]) : k) * x) : ℂ) with hS
  have hshift : S = ψ y * S := by
    rw [hS, Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight (Ideal.Quotient.mk _ (⟨_, hr⟩ : 𝒪[k]) : Res k e))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [key _ (Quotient.out t + ⟨_, hr⟩) (by simp), ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 2
    push_cast
    field_simp
    ring
  by_contra hne
  exact hy' (Circle.ext (by simpa using (mul_left_eq_self₀.1 hshift.symm).resolve_right hne))
end GlobalTheory.SplitFlip.Model
