-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.natDegree_coeff_le_level_mul_dedekindPsi_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6c4a773e-4b20-5ed7-a3d6-8a67159e3b15

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots
import Theorems.Thm_ModularCurve_minpoly_jqN_eq_toAdjoin
import Theorems.Thm_ModularCurve_phiIrreducible_all
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_natDegree_coeff_le_level_mul_dedekindPsi_sub
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open ModularCurve Polynomial

noncomputable section

namespace SolHdegX

section Good

variable {K : Type*} [Field K]

def Good (B : ℤ) (P : Polynomial (LaurentSeries K)) (n : ℕ) : Prop :=
  ∀ i : ℕ, ((((i : ℤ) - n) * B : ℤ) : WithTop ℤ) ≤ (P.coeff i).orderTop

theorem le_orderTop_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries K) (e : WithTop ℤ)
    (h : ∀ j ∈ s, e ≤ (f j).orderTop) : e ≤ (∑ j ∈ s, f j).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
    exact le_min (h a (Finset.mem_insert_self a s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem good_one (B : ℤ) : Good B (1 : Polynomial (LaurentSeries K)) 0 := by
  intro i
  rw [coeff_one]
  split_ifs with h
  · subst h; simp
  · simp

theorem good_mul {B : ℤ} {P Q : Polynomial (LaurentSeries K)} {n m : ℕ}
    (hP : Good B P n) (hQ : Good B Q m) : Good B (P * Q) (n + m) := by
  intro i
  rw [coeff_mul]
  refine le_orderTop_sum _ _ _ fun x hx => ?_
  have hx' : x.1 + x.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  refine le_trans ?_ HahnSeries.orderTop_add_le_mul
  refine le_trans ?_ (add_le_add (hP x.1) (hQ x.2))
  rw [← WithTop.coe_add, WithTop.coe_le_coe]
  have : ((i : ℤ) - ↑(n + m)) * B = (((x.1 : ℤ) - n) * B) + (((x.2 : ℤ) - m) * B) := by
    push_cast; rw [← hx']; push_cast; ring
  rw [this]

theorem good_X_sub_C {B : ℤ} (r : LaurentSeries K)
    (hr : ((-B : ℤ) : WithTop ℤ) ≤ r.orderTop) : Good B (X - C r) 1 := by
  intro i
  rw [coeff_sub, coeff_X, coeff_C]
  rcases Nat.lt_trichotomy i 1 with hi | rfl | hi
  · have hi0 : i = 0 := by omega
    subst hi0
    simp only [↓reduceIte, Nat.cast_zero, zero_sub, neg_mul]
    simpa using hr
  · simp
  · have h1 : (1 : ℕ) ≠ i := by omega
    have h0 : i ≠ 0 := by omega
    rw [if_neg h1, if_neg h0, sub_zero, HahnSeries.orderTop_zero]
    exact le_top

theorem good_prod {B : ℤ} {ι : Type*} (s : Finset ι) (r : ι → LaurentSeries K)
    (hr : ∀ j ∈ s, ((-B : ℤ) : WithTop ℤ) ≤ (r j).orderTop) :
    Good B (∏ j ∈ s, (X - C (r j))) s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_one B
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.add_comm]
    exact good_mul (good_X_sub_C _ (hr a (Finset.mem_insert_self a s)))
      (ih fun j hj => hr j (Finset.mem_insert_of_mem hj))

end Good

section Orders

variable (K : Type*) [Field K] [Algebra ℚ K]

theorem coeffEmb_jq_coeff_of_lt {k : ℤ} (hk : k < -1) : (coeffEmb K jq).coeff k = 0 := by
  rw [coeffEmb_coeff, coeff_jq_of_lt hk, map_zero]

omit [Algebra ℚ K] in
theorem le_orderTop_qExpand {n : ℕ} [NeZero n] (f : LaurentSeries K) (e : ℤ)
    (hf : ∀ k < e, f.coeff k = 0) :
    (((n : ℤ) * e : ℤ) : WithTop ℤ) ≤ (qExpand K n f).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro j hj
  have hj' : j < (n : ℤ) * e := by exact_mod_cast hj
  by_cases hdvd : (n : ℤ) ∣ j
  · obtain ⟨m, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    apply hf
    have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    by_contra hme
    push Not at hme
    have := mul_le_mul_of_nonneg_left hme hn.le
    omega
  · exact qExpand_coeff_of_not_dvd n f hdvd

theorem le_orderTop_slot (N : ℕ) [NeZero N] (ζ : Kˣ) (a b : ℕ) (ha : a ∈ N.divisors) :
    ((-((N : ℤ) * N) : ℤ) : WithTop ℤ) ≤
      (if h : a = 0 then (0 : LaurentSeries K) else
        letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))).orderTop := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
  rw [dif_neg ha0]
  letI : NeZero a := ⟨ha0⟩
  haveI : NeZero (a * a) := ⟨mul_ne_zero ha0 ha0⟩
  have hle : a ≤ N := Nat.divisor_le ha
  have h1 := le_orderTop_qExpand K (n := a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)) (-1)
    (fun k hk => by rw [qTwist_coeff, coeffEmb_jq_coeff_of_lt K hk, mul_zero])
  refine le_trans ?_ h1
  have : -((N : ℤ) * N) ≤ ((a * a : ℕ) : ℤ) * (-1) := by
    have : (a : ℤ) * a ≤ (N : ℤ) * N := by
      have := Nat.mul_le_mul hle hle
      exact_mod_cast this
    push_cast; linarith
  exact_mod_cast this

theorem coeff_evalAtJ (c : Polynomial ℤ) (k : ℤ) :
    (evalAtJ c).coeff k = ∑ i ∈ Finset.range (c.natDegree + 1), (c.coeff i : ℚ) * (jq ^ i).coeff k := by
  rw [evalAtJ_def]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [aeval_def, eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show algebraMap ℤ (LaurentSeries ℚ) (c.coeff i) = HahnSeries.C ((c.coeff i : ℚ)) by
      rw [eq_intCast, ← map_intCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ)],
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem coeff_evalAtJ_neg_natDegree (c : Polynomial ℤ) :
    (evalAtJ c).coeff (-(c.natDegree : ℤ)) = (c.leadingCoeff : ℚ) := by
  rw [coeff_evalAtJ, Finset.sum_eq_single c.natDegree]
  · rw [coeff_jq_pow_self, mul_one, leadingCoeff]
  · intro i hi hne
    have hlt : i < c.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
    rw [coeff_jq_pow_of_lt (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

theorem coeff_evalAtJ_of_lt (c : Polynomial ℤ) {k : ℤ} (hk : k < -(c.natDegree : ℤ)) :
    (evalAtJ c).coeff k = 0 := by
  rw [coeff_evalAtJ]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hle : i ≤ c.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [coeff_jq_pow_of_lt (by omega), mul_zero]

end Orders

theorem main (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (i : ℕ) :
    (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i) := by
  classical
  set c := data.Φ.coeff i with hc_def
  by_cases hc : c = 0
  · rw [hc, natDegree_zero]; exact Nat.zero_le _
  have hiψ : i ≤ dedekindPsi N := by
    rw [← data.natDegree_eq]; exact le_natDegree_of_ne_zero hc

  have hN0 : N ≠ 0 := NeZero.ne N
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hζ_def
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN0
  have hζu : IsPrimitiveRoot ((Units.mk0 ζ hζ0 : ℂˣ) : ℂ) N := by simpa using hζ

  have hprod := minpoly_jqN_map_eq_prod_slots (K := ℂ) N (Units.mk0 ζ hζ0) hζu
    (fun d _ _ => ⟨finrank_adjoin_jqN_eq_dedekindPsi d, modularFunctionField_eq_full d⟩)
  rw [minpoly_jqN_eq_toAdjoin data (phiIrreducible_all N data), Finset.prod_sigma'] at hprod
  set φ : (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) →+* LaurentSeries ℂ :=
    ((coeffEmb ℂ).comp (qExpand ℚ N)).comp
      (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ))
    with hφ
  set S := N.divisors.sigma fun a =>
    (Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1) with hS
  set r : (Σ _ : ℕ, ℕ) → LaurentSeries ℂ := fun x =>
    if h : x.1 = 0 then 0 else
      letI : NeZero x.1 := ⟨h⟩; qExpand ℂ (x.1 * x.1) (qTwist ((Units.mk0 ζ hζ0) ^ (x.2 * x.1))
        (coeffEmb ℂ jq)) with hr
  have hprod' : data.toAdjoin.map φ = ∏ x ∈ S, (X - C (r x)) := hprod

  have hcard : S.card = dedekindPsi N := by
    have h1 := congrArg natDegree hprod'
    rw [natDegree_finsetProd_X_sub_C_eq_card, (data.toAdjoin_monic).natDegree_map,
      ModularPolynomialData.toAdjoin, (data.monic).natDegree_map, data.natDegree_eq] at h1
    exact h1.symm

  set y : LaurentSeries ℂ := coeffEmb ℂ (qExpand ℚ N (evalAtJ c)) with hy
  have hyeq : y = (∏ x ∈ S, (X - C (r x))).coeff i := by
    rw [← hprod', coeff_map, ModularPolynomialData.toAdjoin, coeff_map, hy, hφ]
    simp only [RingHom.coe_comp, Function.comp_apply]
    congr 2
    have := congrArg (fun f : Polynomial ℤ →+* LaurentSeries ℚ => f c) algebraMap_comp_evalAtJGen
    simpa using this.symm

  have hgood := good_prod (K := ℂ) (B := (N : ℤ) * N) S r fun x hx => by
    have hx1 : x.1 ∈ N.divisors := (Finset.mem_sigma.mp hx).1
    exact le_orderTop_slot ℂ N (Units.mk0 ζ hζ0) x.1 x.2 hx1
  have hlow : ((((i : ℤ) - dedekindPsi N) * ((N : ℤ) * N) : ℤ) : WithTop ℤ) ≤ y.orderTop := by
    rw [hyeq, ← hcard]; exact hgood i

  have hcoeff : y.coeff ((N : ℤ) * (-(c.natDegree : ℤ))) ≠ 0 := by
    rw [hy, coeffEmb_coeff, qExpand_coeff_mul, coeff_evalAtJ_neg_natDegree]
    simp only [ne_eq, map_eq_zero, Int.cast_eq_zero, leadingCoeff_eq_zero]
    exact hc
  have hup : y.orderTop ≤ (((N : ℤ) * (-(c.natDegree : ℤ)) : ℤ) : WithTop ℤ) :=
    HahnSeries.orderTop_le_of_coeff_ne_zero hcoeff
  have hineq := WithTop.coe_le_coe.mp (hlow.trans hup)

  have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have h1 : ((c.natDegree : ℤ)) * N ≤ ((dedekindPsi N : ℤ) - i) * N * N := by nlinarith
  have h2 : (c.natDegree : ℤ) ≤ ((dedekindPsi N : ℤ) - i) * N :=
    le_of_mul_le_mul_right (by nlinarith) hNpos
  have h3 : (c.natDegree : ℤ) ≤ ((N * (dedekindPsi N - i) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hiψ]; linarith
  exact_mod_cast h3

end SolHdegX

open ModularCurve Polynomial in
theorem solution (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (i : ℕ) :
    (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i) :=
  SolHdegX.main N data i

end
end S_ModularCurve_ModularPolynomialData_natDegree_coeff_le_level_mul_dedekindPsi_sub
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_natDegree_coeff_le_level_mul_dedekindPsi_sub (solution)
