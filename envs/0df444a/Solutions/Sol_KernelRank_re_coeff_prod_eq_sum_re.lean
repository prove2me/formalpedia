-- Prove2me | solution 1 for KernelRank.re_coeff_prod_eq_sum_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:37:31.842087+00:00
-- url     : https://prove2.me/submissions/e346c928-e7f1-4b72-aae3-dbdeb429839c

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) (k : ℕ)
    (U : Fin d → ℂ[X]) (hdeg : ∀ j, (U j).natDegree ≤ k) :
    ((∏ j : Fin d, U j).coeff k).re =
      (2 : ℝ) ^ (d - 1) / (2 * (d - 1) * k + d : ℕ) *
        ∑ r : Fin (2 * (d - 1) * k + d), (-1 : ℝ) ^ (r : ℕ) *
          ∏ j : Fin d,
            ((U j).eval (exp (2 * Real.pi * I * (r : ℕ) / (2 * (d - 1) * k + d : ℕ))) *
              exp (-Real.pi * I * (r : ℕ) * (2 * k + 1 : ℕ) /
                (2 * (d - 1) * k + d : ℕ))).re := by
  set R : ℕ := 2 * (d - 1) * k + d
  have hR_pos : 0 < R := by omega
  have hR0 : (R : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hR_pos.ne'
  let ζ (r : ℕ) : ℂ := exp (2 * Real.pi * I * r / R)
  let rot (r : ℕ) : ℂ := exp (-Real.pi * I * r * (2 * k + 1 : ℕ) / R)
  change ((∏ j : Fin d, U j).coeff k).re =
    (2 : ℝ) ^ (d - 1) / R *
      ∑ r : Fin R, (-1 : ℝ) ^ (r : ℕ) *
        ∏ j : Fin d, ((U j).eval (ζ (r : ℕ)) * rot (r : ℕ)).re
  have hU_eq (j : Fin d) : U j = ∑ q : Fin (k + 1), C ((U j).coeff q) * X ^ (q : ℕ) := by
    rw [Fin.sum_univ_eq_sum_range (fun q => C ((U j).coeff q) * X ^ q) (k + 1)]
    simpa [C_mul_X_pow_eq_monomial] using as_sum_range' (U j) (k + 1) (Nat.lt_succ_of_le (hdeg j))
  have hU_eval (j : Fin d) (z : ℂ) :
      (U j).eval z = ∑ q : Fin (k + 1), (U j).coeff q * z ^ (q : ℕ) := by
    conv_lhs => rw [hU_eq j]
    simp [eval_finsetSum]
  have hprod_coeff : (∏ j : Fin d, U j).coeff k =
      ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (k + 1) => ∑ j, (q j : ℕ) = k),
        ∏ j : Fin d, (U j).coeff (q j) := by
    have hprod_expand : (∏ j : Fin d, U j) =
        ∑ q : Fin d → Fin (k + 1),
          C (∏ j : Fin d, (U j).coeff (q j)) * X ^ (∑ j : Fin d, (q j : ℕ)) := by
      have hlhs : (∏ j : Fin d, U j) =
          ∏ j : Fin d, ∑ q : Fin (k + 1), C ((U j).coeff q) * X ^ (q : ℕ) :=
        Finset.prod_congr rfl fun j _ => hU_eq j
      rw [hlhs, Fintype.prod_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.prod_mul_distrib, ← map_prod C, Finset.prod_pow_eq_pow_sum]
    rw [hprod_expand, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext q
    simp [eq_comm]
  rw [hprod_coeff]
  apply Complex.ofReal_inj.mp
  push_cast
  have hre (w : ℂ) : (w.re : ℂ) = (starRingEnd ℂ w + w) / 2 := by
    rw [Complex.re_eq_add_conj]; ring
  simp_rw [hre, hU_eval]
  have hconj_term (j : Fin d) (r : ℕ) :
      starRingEnd ℂ ((∑ q : Fin (k + 1), (U j).coeff q * ζ r ^ (q : ℕ)) * rot r) =
        ∑ q : Fin (k + 1),
          starRingEnd ℂ ((U j).coeff q) *
            exp (Real.pi * I * r * (((2 * k + 1 : ℕ) : ℤ) - 2 * (q : ℕ)) / R) := by
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_assoc, map_mul]
    congr 1
    simp only [ζ, rot, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_conj]
    congr 1
    push_cast
    simp only [map_add, map_mul, map_neg, map_div₀, map_ofNat, map_one, Complex.conj_ofReal,
      Complex.conj_I, Complex.conj_natCast]
    field_simp
    ring
  have hplain_term (j : Fin d) (r : ℕ) :
      (∑ q : Fin (k + 1), (U j).coeff q * ζ r ^ (q : ℕ)) * rot r =
        ∑ q : Fin (k + 1),
          (U j).coeff q *
            exp (Real.pi * I * r * (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q : ℕ)) / R) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_assoc]
    congr 1
    simp only [ζ, rot, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  simp_rw [hconj_term, hplain_term]
  have hprod_r (r : ℕ) :
      (∏ j : Fin d,
        ((∑ q : Fin (k + 1),
            starRingEnd ℂ ((U j).coeff q) *
              exp (Real.pi * I * r * (((2 * k + 1 : ℕ) : ℤ) - 2 * (q : ℕ)) / R)) +
          ∑ q : Fin (k + 1),
            (U j).coeff q *
              exp (Real.pi * I * r * (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q : ℕ)) / R)) / 2) =
      ((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          ∑ q : Fin d → Fin (k + 1),
            (∏ j : Fin d, if j ∈ S then starRingEnd ℂ ((U j).coeff (q j))
              else (U j).coeff (q j)) *
            exp (Real.pi * I * r *
              (∑ j : Fin d, if j ∈ S then (((2 * k + 1 : ℕ) : ℤ) - 2 * (q j : ℕ))
                else (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q j : ℕ))) / R) := by
    have hdiv :
        (∏ j : Fin d,
          ((∑ q : Fin (k + 1),
              starRingEnd ℂ ((U j).coeff q) *
                exp (Real.pi * I * r * (((2 * k + 1 : ℕ) : ℤ) - 2 * (q : ℕ)) / R)) +
            ∑ q : Fin (k + 1),
              (U j).coeff q *
                exp (Real.pi * I * r * (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q : ℕ)) / R)) / 2) =
        ∏ j : Fin d,
          ((∑ q : Fin (k + 1),
              starRingEnd ℂ ((U j).coeff q) *
                exp (Real.pi * I * r * (((2 * k + 1 : ℕ) : ℤ) - 2 * (q : ℕ)) / R)) +
            ∑ q : Fin (k + 1),
              (U j).coeff q *
                exp (Real.pi * I * r * (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q : ℕ)) / R)) *
            (2 : ℂ)⁻¹ :=
      Finset.prod_congr rfl fun _ _ => div_eq_mul_inv _ 2
    rw [hdiv, Finset.prod_mul_distrib]
    have h2 : (∏ _j : Fin d, (2 : ℂ)⁻¹) = ((2 : ℂ) ^ d)⁻¹ := by simp
    rw [h2, mul_comm _ (((2 : ℂ) ^ d)⁻¹)]
    congr 1
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hsub : S ⊆ Finset.univ := Finset.mem_powerset.mp hS
    have hmerge :
        (∏ j ∈ S, ∑ q : Fin (k + 1),
          starRingEnd ℂ ((U j).coeff q) *
            exp (Real.pi * I * r * (((2 * k + 1 : ℕ) : ℤ) - 2 * (q : ℕ)) / R)) *
        (∏ j ∈ Finset.univ \ S, ∑ q : Fin (k + 1),
          (U j).coeff q *
            exp (Real.pi * I * r * (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q : ℕ)) / R)) =
        ∏ j : Fin d, ∑ q : Fin (k + 1),
          (if j ∈ S then starRingEnd ℂ ((U j).coeff q) else (U j).coeff q) *
          exp (Real.pi * I * r *
            (if j ∈ S then (((2 * k + 1 : ℕ) : ℤ) - 2 * (q : ℕ))
             else (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q : ℕ))) / R) := by
      rw [← Finset.prod_sdiff hsub, mul_comm]
      congr 1
      · refine Finset.prod_congr rfl fun j hj => Finset.sum_congr rfl fun q _ => ?_
        have hjn : j ∉ S := (Finset.mem_sdiff.mp hj).2
        simp [hjn]
      · refine Finset.prod_congr rfl fun j hj => Finset.sum_congr rfl fun q _ => ?_
        simp [hj]
    rw [hmerge, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_div]
  simp_rw [hprod_r]
  let Z (S : Finset (Fin d)) (q : Fin d → Fin (k + 1)) : ℂ :=
    ∏ j : Fin d, if j ∈ S then starRingEnd ℂ ((U j).coeff (q j)) else (U j).coeff (q j)
  let E (S : Finset (Fin d)) (q : Fin d → Fin (k + 1)) : ℤ :=
    ∑ j : Fin d, if j ∈ S then (((2 * k + 1 : ℕ) : ℤ) - 2 * (q j : ℕ))
      else (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q j : ℕ))
  change _ = (2 : ℂ) ^ (d - 1) * (R : ℂ)⁻¹ *
    ∑ r : Fin R, (-1 : ℂ) ^ (r : ℕ) * (((2 : ℂ) ^ d)⁻¹ *
      ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ q : Fin d → Fin (k + 1), Z S q * exp (Real.pi * I * (r : ℕ) * (E S q) / R))
  have hpull :
      ∑ r : Fin R, (-1 : ℂ) ^ (r : ℕ) * (((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          ∑ q : Fin d → Fin (k + 1), Z S q * exp (Real.pi * I * (r : ℕ) * (E S q) / R)) =
      ((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          ∑ q : Fin d → Fin (k + 1), Z S q *
            ∑ r ∈ Finset.range R, (-1 : ℂ) ^ r * exp (Real.pi * I * r * (E S q) / R) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun r : ℕ => (-1 : ℂ) ^ r * (((2 : ℂ) ^ d)⁻¹ *
        ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          ∑ q : Fin d → Fin (k + 1), Z S q * exp (Real.pi * I * r * (E S q) / R))) R]
    simp_rw [← mul_assoc ((-1 : ℂ) ^ _) (((2 : ℂ) ^ d)⁻¹),
      mul_comm ((-1 : ℂ) ^ _) (((2 : ℂ) ^ d)⁻¹), mul_assoc (((2 : ℂ) ^ d)⁻¹), ← Finset.mul_sum]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by ring
  rw [hpull]
  have hR_int : (R : ℤ) = 2 * ((d : ℤ) - 1) * (k : ℤ) + (d : ℤ) := by
    have hd_sub : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := Int.ofNat_sub (by omega)
    dsimp [R]
    push_cast [hd_sub]
    ring
  have hE_eq (S : Finset (Fin d)) (q : Fin d → Fin (k + 1)) :
      (R : ℤ) + E S q =
        2 * ((2 * (k : ℤ) + 1) * (S.card : ℤ) +
          (∑ j ∈ Finset.univ \ S, ((q j : ℕ) : ℤ)) -
          (∑ j ∈ S, ((q j : ℕ) : ℤ)) - (k : ℤ)) := by
    have hsplit_E : E S q =
        (∑ j ∈ S, (((2 * k + 1 : ℕ) : ℤ) - 2 * (q j : ℕ))) +
        (∑ j ∈ Finset.univ \ S, (-((2 * k + 1 : ℕ) : ℤ) + 2 * (q j : ℕ))) := by
      dsimp [E]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
      have hf1 : Finset.univ.filter (· ∈ S) = S := by ext j; simp
      have hf2 : Finset.univ.filter (fun j => j ∉ S) = Finset.univ \ S := by ext j; simp
      rw [hf1, hf2]
      congr 1
      · exact Finset.sum_congr rfl fun j hj => by simp [hj]
      · exact Finset.sum_congr rfl fun j hj => by simp [(Finset.mem_sdiff.mp hj).2]
    have hcard_sdiff : (Finset.univ \ S).card = d - S.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
    have hcard_le : S.card ≤ d := by simpa using Finset.card_le_univ S
    rw [hsplit_E, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_const, hcard_sdiff, ← Finset.mul_sum, ← Finset.mul_sum]
    simp only [nsmul_eq_mul]
    have hsub_int : ((d - S.card : ℕ) : ℤ) = (d : ℤ) - S.card := Int.ofNat_sub hcard_le
    rw [hR_int, hsub_int]
    push_cast
    ring
  have hinner (S : Finset (Fin d)) (q : Fin d → Fin (k + 1)) :
      (∑ r ∈ Finset.range R, (-1 : ℂ) ^ r * exp (Real.pi * I * r * (E S q) / R)) =
        if (S = ∅ ∨ S = Finset.univ) ∧ ∑ j, (q j : ℕ) = k then (R : ℂ) else 0 := by
    let K : ℤ := (2 * (k : ℤ) + 1) * (S.card : ℤ) +
      (∑ j ∈ Finset.univ \ S, ((q j : ℕ) : ℤ)) - (∑ j ∈ S, ((q j : ℕ) : ℤ)) - (k : ℤ)
    let w : ℂ := exp (2 * Real.pi * I * K / R)
    have hterm (r : ℕ) :
        (-1 : ℂ) ^ r * exp (Real.pi * I * r * (E S q) / R) = w ^ r := by
      have hm1 : (-1 : ℂ) ^ r = exp (Real.pi * I * r) := by
        rw [mul_comm (Real.pi * I) (r : ℂ), exp_nat_mul, exp_pi_mul_I]
      rw [hm1, ← exp_add, ← exp_nat_mul]
      congr 1
      have hEK : (E S q : ℂ) = 2 * (K : ℂ) - (R : ℂ) := by
        have := congrArg (Int.cast (R := ℂ)) (hE_eq S q)
        dsimp [K]
        push_cast at this ⊢
        linear_combination this
      rw [hEK]
      field_simp
      ring
    simp_rw [hterm]
    have hsum_S_le : (∑ j ∈ S, ((q j : ℕ) : ℤ)) ≤ S.card * (k : ℤ) := by
      calc (∑ j ∈ S, ((q j : ℕ) : ℤ)) ≤ ∑ _j ∈ S, (k : ℤ) :=
            Finset.sum_le_sum fun j _ => by exact_mod_cast Nat.lt_succ_iff.mp (q j).2
        _ = S.card * (k : ℤ) := by simp
    have hsum_S_nonneg : 0 ≤ ∑ j ∈ S, ((q j : ℕ) : ℤ) :=
      Finset.sum_nonneg fun j _ => Int.natCast_nonneg _
    have hsum_c_le : (∑ j ∈ Finset.univ \ S, ((q j : ℕ) : ℤ)) ≤ (d - S.card : ℕ) * (k : ℤ) := by
      have hcard_sdiff : (Finset.univ \ S).card = d - S.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
      calc (∑ j ∈ Finset.univ \ S, ((q j : ℕ) : ℤ)) ≤ ∑ _j ∈ Finset.univ \ S, (k : ℤ) :=
            Finset.sum_le_sum fun j _ => by exact_mod_cast Nat.lt_succ_iff.mp (q j).2
        _ = (d - S.card : ℕ) * (k : ℤ) := by simp [hcard_sdiff]
    have hsum_c_nonneg : 0 ≤ ∑ j ∈ Finset.univ \ S, ((q j : ℕ) : ℤ) :=
      Finset.sum_nonneg fun j _ => Int.natCast_nonneg _
    have hd_int : 2 ≤ (d : ℤ) := by exact_mod_cast hd
    have hk_int : 0 ≤ (k : ℤ) := Int.natCast_nonneg k
    split_ifs with hcond
    · rcases hcond with ⟨rfl | rfl, hsum_k⟩
      · have hK0 : K = 0 := by
          have hq_int : (∑ j : Fin d, ((q j : ℕ) : ℤ)) = k := by exact_mod_cast hsum_k
          dsimp [K]
          simp [hq_int]
        simp [w, hK0]
      · have hKR : K = R := by
          have hq_int : (∑ j : Fin d, ((q j : ℕ) : ℤ)) = k := by exact_mod_cast hsum_k
          dsimp [K]
          simp only [Fintype.card_fin, Finset.sdiff_self, Finset.sum_empty, add_zero, hq_int]
          rw [hR_int]
          ring
        have hw1 : w = 1 := by
          simp only [w, hKR, Int.cast_natCast]
          have : 2 * Real.pi * I * (R : ℂ) / (R : ℂ) = 2 * Real.pi * I := by field_simp
          rw [this, exp_two_pi_mul_I]
        simp [hw1]
    · have hwR : w ^ R = 1 := by
        rw [← exp_nat_mul]
        have hexp : (R : ℂ) * (2 * Real.pi * I * (K : ℂ) / R) =
            (K : ℂ) * (2 * Real.pi * I) := by field_simp
        rw [hexp]
        simp [exp_int_mul_two_pi_mul_I]
      have hw1 : w ≠ 1 := by
        intro h1
        rw [exp_eq_one_iff] at h1
        obtain ⟨m, hm⟩ := h1
        have hpi : (2 : ℂ) * Real.pi * I ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            I_ne_zero
        have heq : (K : ℂ) = (m : ℂ) * R := by
          apply mul_right_cancel₀ hpi
          have hm' : 2 * Real.pi * I * (K : ℂ) = (m : ℂ) * (2 * Real.pi * I) * R :=
            (div_eq_iff hR0).mp hm
          linear_combination hm'
        have hz : K = m * R := by exact_mod_cast heq
        have hcard_le : S.card ≤ d := by simpa using Finset.card_le_univ S
        by_cases hSu : S = ∅ ∨ S = Finset.univ
        · have hne_k : ∑ j, (q j : ℕ) ≠ k := fun hk => hcond ⟨hSu, hk⟩
          rcases hSu with rfl | rfl
          · have hK_val : K = (∑ j : Fin d, ((q j : ℕ) : ℤ)) - k := by
              dsimp [K]; simp
            have hsum_ub : (∑ j : Fin d, ((q j : ℕ) : ℤ)) ≤ d * (k : ℤ) := by
              simpa using hsum_c_le
            have hsum_lb : 0 ≤ ∑ j : Fin d, ((q j : ℕ) : ℤ) := by simpa using hsum_c_nonneg
            have hK_ne0 : K ≠ 0 := by
              intro h0
              apply hne_k
              have : (∑ j : Fin d, ((q j : ℕ) : ℤ)) = k := by omega
              exact_mod_cast this
            have hm_ne0 : m ≠ 0 := by rintro rfl; exact hK_ne0 (by omega)
            rcases lt_or_gt_of_ne hm_ne0 with hm_neg | hm_pos
            · have : m * (R : ℤ) ≤ -1 * (R : ℤ) :=
                Int.mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg R)
              nlinarith [hR_int]
            · have : 1 * (R : ℤ) ≤ m * (R : ℤ) :=
                Int.mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg R)
              nlinarith [hR_int]
          · have hK_val : K = (R : ℤ) + k - ∑ j : Fin d, ((q j : ℕ) : ℤ) := by
              dsimp [K]
              simp only [Fintype.card_fin, Finset.sdiff_self, Finset.sum_empty, add_zero]
              rw [hR_int]
              ring
            have hsum_ub : (∑ j : Fin d, ((q j : ℕ) : ℤ)) ≤ d * (k : ℤ) := by
              simpa using hsum_S_le
            have hsum_lb : 0 ≤ ∑ j : Fin d, ((q j : ℕ) : ℤ) := by simpa using hsum_S_nonneg
            have hK_neR : K ≠ R := by
              intro hR_eq
              apply hne_k
              have : (∑ j : Fin d, ((q j : ℕ) : ℤ)) = k := by omega
              exact_mod_cast this
            have hm_ne1 : m ≠ 1 := by rintro rfl; exact hK_neR (by omega)
            rcases lt_or_gt_of_ne hm_ne1 with hm_le0 | hm_ge2
            · have : m * (R : ℤ) ≤ 0 * (R : ℤ) :=
                Int.mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg R)
              nlinarith [hR_int]
            · have : 2 * (R : ℤ) ≤ m * (R : ℤ) :=
                Int.mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg R)
              nlinarith [hR_int]
        · push Not at hSu
          have hS_pos : 1 ≤ S.card := Finset.card_pos.mpr hSu.1
          have hS_lt : S.card ≤ d - 1 := by
            have hlt : S.card < d := by
              simpa using Finset.card_lt_card
                (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S, hSu.2⟩)
            omega
          have hS_pos_int : 1 ≤ (S.card : ℤ) := by exact_mod_cast hS_pos
          have hS_lt_int : (S.card : ℤ) ≤ (d : ℤ) - 1 := by omega
          have hK_pos : 1 ≤ K := by
            dsimp [K]
            nlinarith
          have hK_lt : K ≤ (R : ℤ) - 1 := by
            have hsub_int : ((d - S.card : ℕ) : ℤ) = (d : ℤ) - S.card := Int.ofNat_sub hcard_le
            rw [hsub_int] at hsum_c_le
            dsimp [K]
            nlinarith [hR_int]
          rcases le_or_gt m 0 with hm_le0 | hm_ge1
          · have : m * (R : ℤ) ≤ 0 :=
              Int.mul_nonpos_of_nonpos_of_nonneg hm_le0 (Int.natCast_nonneg R)
            omega
          · have : 1 * (R : ℤ) ≤ m * (R : ℤ) :=
              Int.mul_le_mul_of_nonneg_right hm_ge1 (Int.natCast_nonneg R)
            omega
      have hgeom := geom_sum_mul w R
      rw [hwR, sub_self] at hgeom
      exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hw1)
  have hsumZ :
      (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ q : Fin d → Fin (k + 1), Z S q *
          ∑ r ∈ Finset.range R, (-1 : ℂ) ^ r * exp (Real.pi * I * r * (E S q) / R)) =
      ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ q : Fin d → Fin (k + 1), Z S q *
          if (S = ∅ ∨ S = Finset.univ) ∧ ∑ j, (q j : ℕ) = k then (R : ℂ) else 0 :=
    Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun q _ => by rw [hinner S q]
  rw [hsumZ]
  have hsplit_S :
      (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        ∑ q : Fin d → Fin (k + 1), Z S q *
          if (S = ∅ ∨ S = Finset.univ) ∧ ∑ j, (q j : ℕ) = k then (R : ℂ) else 0) =
      (∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (k + 1) => ∑ j, (q j : ℕ) = k),
        Z ∅ q * R) +
      (∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (k + 1) => ∑ j, (q j : ℕ) = k),
        Z Finset.univ q * R) := by
    have hcond_split (S : Finset (Fin d)) :
        (∑ q : Fin d → Fin (k + 1), Z S q *
          if (S = ∅ ∨ S = Finset.univ) ∧ ∑ j, (q j : ℕ) = k then (R : ℂ) else 0) =
        if S = ∅ ∨ S = Finset.univ then
          ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (k + 1) => ∑ j, (q j : ℕ) = k),
            Z S q * R
        else 0 := by
      by_cases hS : S = ∅ ∨ S = Finset.univ
      · simp [hS, mul_ite, ← Finset.sum_filter]
      · simp [hS]
    simp_rw [hcond_split, ← Finset.sum_filter]
    have hfilt : (Finset.univ : Finset (Fin d)).powerset.filter
        (fun S => S = ∅ ∨ S = Finset.univ) = {∅, Finset.univ} := by
      ext S; simp
    have hne : (∅ : Finset (Fin d)) ≠ Finset.univ := by
      intro h; have := congrArg Finset.card h; simp at this; omega
    rw [hfilt, Finset.sum_pair hne]
  rw [hsplit_S, ← Finset.sum_mul, ← Finset.sum_mul]
  have hZ0 (q : Fin d → Fin (k + 1)) : Z ∅ q = ∏ j, (U j).coeff (q j) := by simp [Z]
  have hZ1 (q : Fin d → Fin (k + 1)) :
      Z Finset.univ q = starRingEnd ℂ (∏ j, (U j).coeff (q j)) := by
    simp [Z, map_prod]
  simp_rw [hZ0, hZ1]
  rw [← map_sum (starRingEnd ℂ)]
  have hpow2 : (2 : ℂ) ^ d = (2 : ℂ) ^ (d - 1) * 2 := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
  have h2ne : (2 : ℂ) ^ (d - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [hpow2]
  field_simp
  ring
end KernelRank
