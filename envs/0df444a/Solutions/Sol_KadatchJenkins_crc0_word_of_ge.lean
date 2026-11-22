-- Prove2me | solution 1 for KadatchJenkins.crc0_word_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T03:13:39.115411+00:00
-- url     : https://prove2.me/submissions/903ccb90-408b-414d-a437-890f01a424cf

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial
namespace KadatchJenkins

theorem AuxKJ_mm (P A B C : (ZMod 2)[X]) : (A % P * B + C) % P = (A * B + C) % P := by
  rw [EuclideanDomain.mod_eq_sub_mul_div A P]
  have : (A - P * (A / P)) * B + C = (A * B + C) - P * ((A / P) * B) := by ring
  rw [this, Polynomial.sub_mod, EuclideanDomain.mod_eq_zero.mpr (dvd_mul_right _ _), sub_zero]

theorem AuxKJ_polydeg (M : Message) : M.poly.degree < (M.length : WithBot ℕ) := by
  rw [← Polynomial.mem_degreeLT]
  unfold Message.poly
  refine Submodule.sum_mem _ (fun k _ => ?_)
  rw [Polynomial.mem_degreeLT]
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
  have := k.2
  exact_mod_cast (by omega : M.length - 1 - (k : ℕ) < M.length)

theorem AuxKJ_dec (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W : ℕ) (hWD : W ≤ P.natDegree)
    (v : (ZMod 2)[X]) (hv : v.degree < (P.natDegree : WithBot ℕ)) :
    v = v %ₘ X ^ (P.natDegree - W) + v /ₘ X ^ (P.natDegree - W) * X ^ (P.natDegree - W) ∧
    (v /ₘ X ^ (P.natDegree - W)).degree < (W : WithBot ℕ) ∧
    (v %ₘ X ^ (P.natDegree - W)).degree < (((P.natDegree - W : ℕ)) : WithBot ℕ) ∧
    ((v %ₘ X ^ (P.natDegree - W)) * X ^ W) % P = (v %ₘ X ^ (P.natDegree - W)) * X ^ W := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  have hmon : (X ^ (P.natDegree - W) : (ZMod 2)[X]).Monic := monic_X_pow _
  have hL : (v %ₘ X ^ (P.natDegree - W)).degree < (((P.natDegree - W : ℕ)) : WithBot ℕ) := by
    have := degree_modByMonic_lt v hmon
    rwa [degree_X_pow] at this
  refine ⟨?_, ?_, hL, ?_⟩
  · have := modByMonic_add_div v (X ^ (P.natDegree - W))
    rw [mul_comm] at this
    exact this.symm
  · by_cases h0 : v /ₘ X ^ (P.natDegree - W) = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree h0, natDegree_divByMonic _ hmon, natDegree_X_pow]
      have hv0 : v ≠ 0 := by rintro rfl; simp at h0
      have hge := mt (divByMonic_eq_zero_iff hmon).mpr h0
      rw [degree_X_pow, degree_eq_natDegree hv0, not_lt] at hge
      rw [degree_eq_natDegree hv0] at hv
      have h5 : v.natDegree < P.natDegree := WithBot.coe_lt_coe.mp hv
      have h6 : P.natDegree - W ≤ v.natDegree := WithBot.coe_le_coe.mp hge
      have h8 : v.natDegree - (P.natDegree - W) < W := by omega
      exact_mod_cast h8
  · rw [Polynomial.mod_eq_self_iff hP0, degree_eq_natDegree hP0]
    rw [degree_mul, degree_X_pow]
    have h7 : ((P.natDegree : ℕ) : WithBot ℕ) = ((P.natDegree - W : ℕ) : WithBot ℕ) + (W : WithBot ℕ) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [h7]
    exact WithBot.add_lt_add_right (by simp) hL

theorem crc0_word_of_ge (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W : ℕ) (hWD : W ≤ P.natDegree)
    (M : Message) (hM : M.length = W) (v : (ZMod 2)[X]) (hv : v.degree < (P.natDegree : WithBot ℕ)) :
    let vH := v /ₘ X ^ (P.natDegree - W)
    let vL := v %ₘ X ^ (P.natDegree - W)
    v = vL + vH * X ^ (P.natDegree - W) ∧ vH.degree < (W : WithBot ℕ) ∧ vL.degree < (((P.natDegree - W : ℕ)) : WithBot ℕ) ∧
      (vL * X ^ W) % P = vL * X ^ W ∧
      crc0 P M v = vL * X ^ W + mulByXpowD P (vH + M.poly) := by
  dsimp only
  have hX : (X : (ZMod 2)[X]) ^ P.natDegree = X ^ (P.natDegree - W) * X ^ W := by
    rw [← pow_add]; congr 1; omega
  obtain ⟨h1, h2, h3, h4⟩ := AuxKJ_dec P hP W hWD v hv
  refine ⟨h1, h2, h3, h4, ?_⟩
  unfold crc0 mulByXpowD
  conv_rhs => rw [← h4]
  rw [← Polynomial.add_mod, hM]
  congr 1
  linear_combination (X ^ W) * h1 - (v /ₘ X ^ (P.natDegree - W)) * hX

end KadatchJenkins

theorem solution (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W : ℕ) (hWD : W ≤ P.natDegree)
    (M : KadatchJenkins.Message) (hM : M.length = W) (v : (ZMod 2)[X]) (hv : v.degree < (P.natDegree : WithBot ℕ)) :
    let vH := v /ₘ X ^ (P.natDegree - W)
    let vL := v %ₘ X ^ (P.natDegree - W)
    v = vL + vH * X ^ (P.natDegree - W) ∧ vH.degree < (W : WithBot ℕ) ∧ vL.degree < (((P.natDegree - W : ℕ)) : WithBot ℕ) ∧
      (vL * X ^ W) % P = vL * X ^ W ∧
      KadatchJenkins.crc0 P M v = vL * X ^ W + KadatchJenkins.mulByXpowD P (vH + M.poly) :=
  KadatchJenkins.crc0_word_of_ge P hP W hWD M hM v hv
