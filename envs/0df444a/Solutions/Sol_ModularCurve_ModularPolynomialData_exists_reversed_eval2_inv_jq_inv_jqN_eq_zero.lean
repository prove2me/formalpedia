-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.exists_reversed_eval2_inv_jq_inv_jqN_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e6bbd7cf-8b99-570b-80d1-fd4d0fdf7b65

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_exists_reversed_eval2_inv_jq_inv_jqN_eq_zero
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve Polynomial

namespace INFPOLY

theorem swapBivar_C (c : Polynomial ℤ) :
    swapBivar (Polynomial.C c) = c.map Polynomial.C := by
  have hext : swapBivar.comp (Polynomial.C : Polynomial ℤ →+* Polynomial (Polynomial ℤ))
      = Polynomial.mapRingHom (Polynomial.C : ℤ →+* Polynomial ℤ) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    show swapBivar (Polynomial.C Polynomial.X)
      = Polynomial.mapRingHom (Polynomial.C : ℤ →+* Polynomial ℤ) Polynomial.X
    rw [swapBivar_C_X, Polynomial.coe_mapRingHom, Polynomial.map_X]
  exact RingHom.congr_fun hext c

theorem coeff_coeff_swapBivar (Φ : Polynomial (Polynomial ℤ)) (n m : ℕ) :
    ((swapBivar Φ).coeff n).coeff m = (Φ.coeff m).coeff n := by
  refine Polynomial.induction_on' Φ (fun p q hp hq => ?_) (fun i c => ?_)
  · simp only [map_add, Polynomial.coeff_add, hp, hq]
  · rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, swapBivar_C, swapBivar_X,
      ← map_pow]
    simp only [Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
      apply_ite (fun p : Polynomial ℤ => p.coeff n), Polynomial.coeff_zero]

noncomputable def rev (Φ : Polynomial (Polynomial ℤ)) (n : ℕ) : Polynomial (Polynomial ℤ) :=
  ∑ i ∈ Finset.range (n + 1), monomial i
    (∑ j ∈ Finset.range (n + 1), monomial j ((Φ.coeff (n - i)).coeff (n - j)))

theorem coeff_sum_monomial {R : Type*} [Semiring R] (g : ℕ → R) (n i : ℕ) :
    (∑ k ∈ Finset.range (n + 1), monomial k (g k)).coeff i = if i ≤ n then g i else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.lt_succ_iff]

theorem coeff_rev (Φ : Polynomial (Polynomial ℤ)) (n i : ℕ) :
    (rev Φ n).coeff i = if i ≤ n then
      ∑ j ∈ Finset.range (n + 1), monomial j ((Φ.coeff (n - i)).coeff (n - j)) else 0 := by
  rw [rev, coeff_sum_monomial]

theorem coeff_coeff_rev (Φ : Polynomial (Polynomial ℤ)) (n i j : ℕ) :
    ((rev Φ n).coeff i).coeff j =
      if i ≤ n ∧ j ≤ n then (Φ.coeff (n - i)).coeff (n - j) else 0 := by
  rw [coeff_rev]
  by_cases hi : i ≤ n
  · rw [if_pos hi, coeff_sum_monomial]
    by_cases hj : j ≤ n
    · rw [if_pos hj, if_pos ⟨hi, hj⟩]
    · rw [if_neg hj, if_neg (fun hh => hj hh.2)]
  · rw [if_neg hi, coeff_zero, if_neg (fun hh => hi hh.1)]

theorem coeff_rev_eq_zero_of_lt (Φ : Polynomial (Polynomial ℤ)) {n i : ℕ} (h : n < i) :
    (rev Φ n).coeff i = 0 := by
  ext j
  rw [coeff_coeff_rev, if_neg (fun hh => absurd hh.1 (not_le.mpr h)), coeff_zero]

theorem natDegree_rev_le (Φ : Polynomial (Polynomial ℤ)) (n : ℕ) : (rev Φ n).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hi => coeff_rev_eq_zero_of_lt Φ hi

theorem natDegree_coeff_rev_le (Φ : Polynomial (Polynomial ℤ)) (n i : ℕ) :
    ((rev Φ n).coeff i).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr fun j hj => by
    rw [coeff_coeff_rev, if_neg (fun hh => absurd hh.2 (not_le.mpr hj))]

theorem eval₂_rev {K : Type*} [CommRing K] [Algebra ℤ K] (Φ : Polynomial (Polynomial ℤ)) {n : ℕ}
    (hdeg : Φ.natDegree ≤ n) (hX : ∀ b, (Φ.coeff b).natDegree ≤ n)
    {x u y v : K} (hux : u * x = 1) (hvy : v * y = 1) :
    (rev Φ n).eval₂ (aeval (R := ℤ) u).toRingHom v =
      u ^ n * v ^ n * Φ.eval₂ (aeval (R := ℤ) x).toRingHom y := by

  have hL : (rev Φ n).eval₂ (aeval (R := ℤ) u).toRingHom v =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (((Φ.coeff (n - i)).coeff (n - j) : ℤ) : K) * u ^ j * v ^ i := by
    rw [eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_rev_le Φ n))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [show (aeval (R := ℤ) u).toRingHom ((rev Φ n).coeff i) = aeval u ((rev Φ n).coeff i)
        from rfl, aeval_def,
      eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_coeff_rev_le Φ n i)),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [coeff_coeff_rev, if_pos ⟨hi', hj'⟩, eq_intCast]

  have hR : Φ.eval₂ (aeval (R := ℤ) x).toRingHom y =
      ∑ b ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (n + 1),
        (((Φ.coeff b).coeff a : ℤ) : K) * x ^ a * y ^ b := by
    rw [eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hdeg)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show (aeval (R := ℤ) x).toRingHom (Φ.coeff b) = aeval x (Φ.coeff b) from rfl, aeval_def,
      eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (hX b)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [eq_intCast]
  rw [hL, hR, Finset.mul_sum]

  rw [← Finset.sum_range_reflect (fun b => u ^ n * v ^ n *
      ∑ a ∈ Finset.range (n + 1), (((Φ.coeff b).coeff a : ℤ) : K) * x ^ a * y ^ b) (n + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.add_sub_cancel, Finset.mul_sum]

  rw [← Finset.sum_range_reflect (fun a => u ^ n * v ^ n *
      ((((Φ.coeff (n - i)).coeff a : ℤ) : K) * x ^ a * y ^ (n - i))) (n + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Nat.add_sub_cancel]

  have hu : u ^ n * x ^ (n - j) = u ^ j := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj'
    rw [hk, Nat.add_sub_cancel_left, pow_add, mul_assoc, ← mul_pow, hux, one_pow, mul_one]
  have hv : v ^ n * y ^ (n - i) = v ^ i := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi'
    rw [hk, Nat.add_sub_cancel_left, pow_add, mul_assoc, ← mul_pow, hvy, one_pow, mul_one]
  rw [← hu, ← hv]
  ring

section Symm

variable {Φ : Polynomial (Polynomial ℤ)} {n : ℕ}

theorem coeff_coeff_symm (hsymm : swapBivar Φ = Φ) (a b : ℕ) :
    (Φ.coeff b).coeff a = (Φ.coeff a).coeff b := by
  rw [← coeff_coeff_swapBivar Φ a b, hsymm]

theorem coeff_coeff_top (hsymm : swapBivar Φ = Φ) (hmonic : Φ.Monic) (hdeg : Φ.natDegree = n)
    (b : ℕ) : (Φ.coeff b).coeff n = if b = 0 then 1 else 0 := by
  rw [coeff_coeff_symm hsymm]
  have h : Φ.coeff n = 1 := by rw [← hdeg]; exact hmonic.coeff_natDegree
  rw [h, coeff_one]

theorem coeff_coeff_eq_zero_of_lt (hsymm : swapBivar Φ = Φ) (hdeg : Φ.natDegree = n)
    {a : ℕ} (ha : n < a) (b : ℕ) : (Φ.coeff b).coeff a = 0 := by
  rw [coeff_coeff_symm hsymm, coeff_eq_zero_of_natDegree_lt (p := Φ) (by omega), coeff_zero]

theorem natDegree_coeff_le (hsymm : swapBivar Φ = Φ) (hdeg : Φ.natDegree = n) (b : ℕ) :
    (Φ.coeff b).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ ha => coeff_coeff_eq_zero_of_lt hsymm hdeg ha b

theorem coeff_rev_n_coeff_zero (hsymm : swapBivar Φ = Φ) (hmonic : Φ.Monic)
    (hdeg : Φ.natDegree = n) : ((rev Φ n).coeff n).coeff 0 = 1 := by
  rw [coeff_coeff_rev, if_pos ⟨le_rfl, Nat.zero_le _⟩, Nat.sub_self, Nat.sub_zero,
    coeff_coeff_top hsymm hmonic hdeg, if_pos rfl]

theorem natDegree_rev (hsymm : swapBivar Φ = Φ) (hmonic : Φ.Monic) (hdeg : Φ.natDegree = n) :
    (rev Φ n).natDegree = n := by
  refine le_antisymm (natDegree_rev_le Φ n) (le_natDegree_of_ne_zero fun h => ?_)
  have h1 := coeff_rev_n_coeff_zero hsymm hmonic hdeg
  rw [h, coeff_zero] at h1
  exact zero_ne_one h1

theorem coeff_rev_zero (hsymm : swapBivar Φ = Φ) (hmonic : Φ.Monic) (hdeg : Φ.natDegree = n) :
    (rev Φ n).coeff 0 = X ^ n := by
  ext j
  rw [coeff_coeff_rev, Nat.sub_zero, coeff_X_pow]
  by_cases hj : j ≤ n
  · rw [if_pos ⟨Nat.zero_le _, hj⟩, coeff_coeff_symm hsymm, coeff_coeff_top hsymm hmonic hdeg]
    by_cases hjn : j = n
    · subst hjn; simp
    · rw [if_neg (by omega), if_neg hjn]
  · rw [if_neg (fun hh => hj hh.2), if_neg (by omega)]

theorem swapBivar_rev (hsymm : swapBivar Φ = Φ) : swapBivar (rev Φ n) = rev Φ n := by
  ext i j
  rw [coeff_coeff_swapBivar, coeff_coeff_rev, coeff_coeff_rev]
  by_cases h : i ≤ n ∧ j ≤ n
  · rw [if_pos ⟨h.2, h.1⟩, if_pos h, coeff_coeff_symm hsymm]
  · rw [if_neg (fun hh => h ⟨hh.2, hh.1⟩), if_neg h]

end Symm

theorem jqN_ne_zero (N : ℕ) [NeZero N] : jqN N ≠ 0 := fun h =>
  jq_ne_zero ((qExpand_injective (R := ℚ) N) (by rw [map_zero]; exact h))

end INFPOLY

open INFPOLY in
theorem solution
    (p : ℕ) [Fact p.Prime] (data : ModularPolynomialData p) :
    ∃ Ψ : Polynomial (Polynomial ℤ),
      (∀ i j : ℕ, (Ψ.coeff i).coeff j =
        if i ≤ p + 1 ∧ j ≤ p + 1 then (data.Φ.coeff (p + 1 - i)).coeff (p + 1 - j) else 0) ∧
      Ψ.natDegree = p + 1 ∧
      (Ψ.coeff (p + 1)).coeff 0 = 1 ∧
      Ψ.coeff 0 = X ^ (p + 1) ∧
      swapBivar Ψ = Ψ ∧
      Ψ.eval₂ (Polynomial.aeval (R := ℤ) jq⁻¹).toRingHom (jqN p)⁻¹ = 0 := by
  have hdeg : data.Φ.natDegree = p + 1 := by
    rw [data.natDegree_eq, ModularCurve.dedekindPsi_prime Fact.out]
  have hsymm : swapBivar data.Φ = data.Φ :=
    ModularCurve.swapBivar_eq_of_evalSymm
      (ModularCurve.ModularPolynomialData.evalSymm_of_prime p data)
  refine ⟨INFPOLY.rev data.Φ (p + 1), INFPOLY.coeff_coeff_rev data.Φ (p + 1),
    natDegree_rev hsymm data.monic hdeg, coeff_rev_n_coeff_zero hsymm data.monic hdeg,
    coeff_rev_zero hsymm data.monic hdeg, swapBivar_rev hsymm, ?_⟩
  rw [eval₂_rev data.Φ hdeg.le (natDegree_coeff_le hsymm hdeg)
    (inv_mul_cancel₀ jq_ne_zero) (inv_mul_cancel₀ (jqN_ne_zero p))]
  have he : (Polynomial.aeval (R := ℤ) jq).toRingHom = evalAtJ :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by rw [evalAtJ_X]; exact aeval_X jq)
  have h0 : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) jq).toRingHom (jqN p) = 0 := by
    rw [he]; exact data.eval_eq_zero
  rw [h0, mul_zero]

end S_ModularCurve_ModularPolynomialData_exists_reversed_eval2_inv_jq_inv_jqN_eq_zero
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_exists_reversed_eval2_inv_jq_inv_jqN_eq_zero (solution)
