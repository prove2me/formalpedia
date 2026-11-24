-- Prove2me | solution 1 for GlobalTheory.sq_sum_bicharacter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:20.118806+00:00
-- url     : https://prove2.me/submissions/e0f2255e-d3ca-40b1-8b05-58fdf5badd1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Theorems.Thm_GlobalTheory_trace_sq_of_pow_four
import Theorems.Thm_GlobalTheory_eq_zero_of_add_self_eq_zero_of_odd_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {A : Type*} [AddCommGroup A] [Fintype A]
namespace GlobalTheory
theorem _root_.solution (hodd : Odd (Fintype.card A)) (B : A → AddChar A ℂ)
    (hsymm : ∀ x y, B x y = B y x) (hnd : ∀ x, B x = 0 → x = 0) :
    (∑ x, B x x) ^ 2 = (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) * (Fintype.card A : ℂ) := by
  classical
  have hsum : ∀ x, ∑ y, B x y = if x = 0 then (Fintype.card A : ℂ) else 0 := by
    intro x
    rw [AddChar.sum_eq_ite]
    refine if_congr ⟨hnd x, ?_⟩ rfl rfl
    rintro rfl
    ext y
    rw [hsymm]; simp
  have hD : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (Fintype.card A : ℂ) two_pos
  have hs0 : s ≠ 0 := by rintro rfl; exact hD (by simpa using hs.symm)
  let F : Matrix A A ℂ := Matrix.of fun x y => B x y
  let P : Matrix A A ℂ := Matrix.of fun x y => if x + y = 0 then 1 else 0
  have hFF : F * F = (Fintype.card A : ℂ) • P := by
    ext x z
    simp only [F, P, mul_apply, of_apply, Matrix.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [← hsum]
    refine sum_congr rfl fun y _ => ?_
    rw [hsymm x y, hsymm (x + z) y, AddChar.map_add_eq_mul]
  have hPP : P * P = 1 := by
    ext x z
    simp only [P, mul_apply, of_apply, one_apply, add_eq_zero_iff_neg_eq, ite_mul, one_mul, zero_mul,
      sum_ite_eq, mem_univ, if_true, neg_neg]
  have hP : P.trace = 1 := by
    have : ∀ x : A, x + x = 0 ↔ x = 0 := fun x =>
      ⟨eq_zero_of_add_self_eq_zero_of_odd_card hodd, fun h => by simp [h]⟩
    simp [P, trace, this]
  have hPF : (P * F).trace = ∑ x, B (-x) x := by
    simp [P, F, trace, mul_apply, add_eq_zero_iff_neg_eq]
  have hF : F.trace = ∑ x, B x x := by simp [F, trace]
  have hprod : F.trace * (P * F).trace = Fintype.card A := by
    rw [hF, hPF, sum_mul_sum, ← Fintype.sum_prod_type']
    let φ : A × A → A × A := fun p => (p.1 + p.2, p.1 - p.2)
    have hφ : Function.Bijective φ := by
      refine Finite.injective_iff_bijective.1 fun p q h => ?_
      have h1 : p.1 + p.2 = q.1 + q.2 := congrArg Prod.fst h
      have h2 : p.1 - p.2 = q.1 - q.2 := congrArg Prod.snd h
      have h3 : p.1 - q.1 = 0 := eq_zero_of_add_self_eq_zero_of_odd_card hodd (by
        have : p.1 - q.1 + (p.1 - q.1) =
            (p.1 + p.2 - (q.1 + q.2)) + (p.1 - p.2 - (q.1 - q.2)) := by abel
        rw [this, h1, h2]; simp)
      have h4 : p.1 = q.1 := sub_eq_zero.1 h3
      exact Prod.ext h4 (by rwa [h4, add_right_inj] at h1)
    rw [Fintype.sum_bijective φ hφ _ (fun p => B p.1 p.2), Fintype.sum_prod_type]
    · simp [hsum]
    · rintro ⟨x, y⟩
      simp only [φ]
      rw [hsymm (x + y), AddChar.map_add_eq_mul, hsymm (x - y) x, hsymm (x - y) y, sub_eq_add_neg,
        AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hsymm y x, hsymm (-y) y]
      have : B x (-y) * B x y = 1 := by rw [← AddChar.map_add_eq_mul]; simp
      linear_combination (-(B x x * B y (-y))) * this
  have hU2 : (s⁻¹ • F) ^ 2 = P := by
    rw [smul_pow, pow_two F, hFF, smul_smul, ← hs, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hs0),
      one_smul]
  have key := trace_sq_of_pow_four (U := s⁻¹ • F)
    (by rw [show 4 = 2 + 2 from rfl, pow_add, hU2, hPP]) (by rw [hU2, hP])
    (by
      rw [pow_succ, hU2, mul_smul_comm, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul,
        mul_mul_mul_comm, hprod, ← hs]
      field_simp) hodd
  rw [← key, ← hs, trace_smul, hF, smul_eq_mul]
  field_simp
end GlobalTheory
