-- Prove2me | solution 1 for GlobalTheory.LocalQuad.exists_zero_five_of_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:18.595712+00:00
-- url     : https://prove2.me/submissions/22addf3b-5142-4297-a16e-63860c89166f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_qf_smul
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_qf_three
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_val_bf_sq_le
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_exists_basis
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_exists_three
import Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_exists_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open FiveVar
namespace GlobalTheory.LocalQuad
theorem _root_.solution {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (v : Valuation K ℤᵐ⁰) (hv : Function.Surjective v)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x)
    (hcw : ∀ c : Fin 3 → Fin 3 → K, (∀ i j, v (c i j) ≤ 1) →
      ∃ x : Fin 3 → K, (∀ i, v (x i) ≤ 1) ∧ (∃ i, v (x i) = 1) ∧
        v (∑ i, ∑ j, c i j * x i * x j) < 1)
    (a : Fin 5 → K) : ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  by_contra hno
  have han : ∀ x, qf a x = 0 → x = 0 := by
    intro x hx
    by_contra h
    exact hno ⟨x, h, hx⟩
  obtain ⟨P, hP, hmin⟩ := exists_basis h2 v hsq a han
  obtain ⟨i, j, k, hij, hik, hjk, hj, hk⟩ :=
    exists_three fun i => decide (Even (WithZero.log (v (qf a (P i)))))
  obtain ⟨s, hs⟩ := exists_scale v hv (hP i) (hP j) hj
  obtain ⟨t, ht⟩ := exists_scale v hv (hP i) (hP k) hk
  set w := qf a (P i) with hw
  have hw0 : w ≠ 0 := hP i
  have hvw : 0 < v w := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hw0)
  have hq : ∀ x, v (qf a x) = v w → v (qf a x / w) ≤ 1 := by
    intro x hx
    rw [map_div₀, hx, div_self hvw.ne']
  have hb : ∀ x y, v (qf a x) = v w → v (qf a y) = v w → v (bf a x y / w) ≤ 1 := by
    intro x y hx hy
    rw [map_div₀, div_le_one₀ hvw]
    apply le_of_pow_le_pow_left₀ (n := 2) two_ne_zero zero_le'
    have := val_bf_sq_le h2 v hsq a han x y
    rwa [hx, hy, ← sq] at this
  have h0 : v (qf a (P i)) = v w := rfl
  have h1 : v (qf a (s • P j)) = v w := by rw [qf_smul, map_mul, map_pow, hs]
  have h2' : v (qf a (t • P k)) = v w := by rw [qf_smul, map_mul, map_pow, ht]
  obtain ⟨x, -, ⟨l, hl⟩, hx⟩ := hcw
    ![![qf a (P i) / w, bf a (P i) (s • P j) / w, bf a (P i) (t • P k) / w],
      ![0, qf a (s • P j) / w, bf a (s • P j) (t • P k) / w],
      ![0, 0, qf a (t • P k) / w]] (by
      intro p q
      fin_cases p <;> fin_cases q
      · exact hq _ h0
      · exact hb _ _ h0 h1
      · exact hb _ _ h0 h2'
      · simp
      · exact hq _ h1
      · exact hb _ _ h1 h2'
      · simp
      · simp
      · exact hq _ h2')
  set c : Fin 5 → K := Pi.single i (x 0) + Pi.single j (x 1 * s) + Pi.single k (x 2 * t) with hc
  have hsum : ∑ p, c p • P p = x 0 • P i + x 1 • s • P j + x 2 • t • P k := by
    simp only [hc, Pi.add_apply, add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul]
  have hlt : v (qf a (∑ p, c p • P p)) < v w := by
    rw [← div_lt_one₀ hvw, ← map_div₀]
    convert hx using 2
    rw [hsum]
    exact qf_three a _ _ _ x w
  fin_cases l
  · have := hmin c i
    have e : c i = x 0 := by simp [hc, hij, hik]
    have hl' : v (x 0) = 1 := hl
    rw [e, hl', one_pow, one_mul] at this
    exact absurd hlt (not_lt.mpr this)
  · have := hmin c j
    have e : c j = x 1 * s := by simp [hc, hij.symm, hjk]
    have hl' : v (x 1) = 1 := hl
    rw [e, map_mul, hl', one_mul, hs] at this
    exact absurd hlt (not_lt.mpr this)
  · have := hmin c k
    have e : c k = x 2 * t := by simp [hc, hik.symm, hjk.symm]
    have hl' : v (x 2) = 1 := hl
    rw [e, map_mul, hl', one_mul, ht] at this
    exact absurd hlt (not_lt.mpr this)
end GlobalTheory.LocalQuad
