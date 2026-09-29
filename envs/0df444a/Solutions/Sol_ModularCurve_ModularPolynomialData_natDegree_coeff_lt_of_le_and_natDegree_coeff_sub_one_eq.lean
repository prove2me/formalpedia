-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.natDegree_coeff_lt_of_le_and_natDegree_coeff_sub_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4a262dd9-7d99-531c-a3b3-4aa2d2bb2693

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

namespace P2MW.S_ModularCurve_ModularPolynomialData_natDegree_coeff_lt_of_le_and_natDegree_coeff_sub_one_eq
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open ModularCurve Polynomial

noncomputable section

namespace SolStrictNewton

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

section Sharp

variable (K : Type*) [Field K] [Algebra ℚ K]

theorem le_orderTop_slot' (N : ℕ) [NeZero N] (ζ : Kˣ) (a b : ℕ) (ha : a ∈ N.divisors) :
    ((-((a : ℤ) * a) : ℤ) : WithTop ℤ) ≤
      (if h : a = 0 then (0 : LaurentSeries K) else
        letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))).orderTop := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
  rw [dif_neg ha0]
  letI : NeZero a := ⟨ha0⟩
  haveI : NeZero (a * a) := ⟨mul_ne_zero ha0 ha0⟩
  have h1 := le_orderTop_qExpand K (n := a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)) (-1)
    (fun k hk => by rw [qTwist_coeff, coeffEmb_jq_coeff_of_lt K hk, mul_zero])
  refine le_trans ?_ h1
  have : -((a : ℤ) * a) ≤ ((a * a : ℕ) : ℤ) * (-1) := by push_cast; linarith
  exact_mod_cast this

theorem coeff_slot_top (N : ℕ) [NeZero N] (ζ : Kˣ) :
    (if h : N = 0 then (0 : LaurentSeries K) else
        letI : NeZero N := ⟨h⟩; qExpand K (N * N) (qTwist (ζ ^ (0 * N)) (coeffEmb K jq))).coeff (-((N : ℤ) * N)) = 1 := by
  rw [dif_neg (NeZero.ne N)]
  haveI : NeZero (N * N) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne N)⟩
  have : (-((N : ℤ) * N)) = ((N * N : ℕ) : ℤ) * (-1) := by push_cast; ring
  rw [this, qExpand_coeff_mul, qTwist_coeff, zero_mul, pow_zero, coeffEmb_coeff, coeff_jq_neg_one]
  simp

end Sharp

theorem main (N : ℕ) [NeZero N] (hN : 2 ≤ N) (data : ModularPolynomialData N) :
    (∀ k : ℕ, k + 2 ≤ dedekindPsi N → (data.Φ.coeff k).natDegree < N * (dedekindPsi N - k)) ∧
      (data.Φ.coeff (dedekindPsi N - 1)).natDegree = N ∧
      (data.Φ.coeff (dedekindPsi N - 1)).leadingCoeff = -1 := by
  classical
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

  have hyeq : ∀ k, coeffEmb ℂ (qExpand ℚ N (evalAtJ (data.Φ.coeff k))) = (∏ x ∈ S, (X - C (r x))).coeff k := by
    intro k
    rw [← hprod', coeff_map, ModularPolynomialData.toAdjoin, coeff_map, hφ]
    simp only [RingHom.coe_comp, Function.comp_apply]
    congr 2
    have := congrArg (fun f : Polynomial ℤ →+* LaurentSeries ℚ => f (data.Φ.coeff k)) algebraMap_comp_evalAtJGen
    simpa using this.symm
  have hycoeff : ∀ k, (coeffEmb ℂ (qExpand ℚ N (evalAtJ (data.Φ.coeff k)))).coeff ((N : ℤ) * (-((data.Φ.coeff k).natDegree : ℤ))) =
      (((data.Φ.coeff k).leadingCoeff : ℚ) : ℂ) := by
    intro k
    rw [coeffEmb_coeff, qExpand_coeff_mul, coeff_evalAtJ_neg_natDegree]
    rfl
  have hyup : ∀ k, data.Φ.coeff k ≠ 0 →
      (coeffEmb ℂ (qExpand ℚ N (evalAtJ (data.Φ.coeff k)))).orderTop ≤ (((N : ℤ) * (-((data.Φ.coeff k).natDegree : ℤ))) : ℤ) := by
    intro k hk
    apply HahnSeries.orderTop_le_of_coeff_ne_zero
    rw [hycoeff]
    have : ((data.Φ.coeff k).leadingCoeff : ℚ) ≠ 0 := by exact_mod_cast (leadingCoeff_ne_zero.mpr hk)
    exact (map_ne_zero (algebraMap ℚ ℂ)).mpr this
  have hylow : ∀ k (m : ℤ), m < (N : ℤ) * (-((data.Φ.coeff k).natDegree : ℤ)) →
      (coeffEmb ℂ (qExpand ℚ N (evalAtJ (data.Φ.coeff k)))).coeff m = 0 := by
    intro k m hm
    rw [coeffEmb_coeff]
    by_cases hdvd : (N : ℤ) ∣ m
    · obtain ⟨m', rfl⟩ := hdvd
      have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
      rw [qExpand_coeff_mul, coeff_evalAtJ_of_lt _ (lt_of_mul_lt_mul_left hm hNpos.le), map_zero]
    · rw [qExpand_coeff_of_not_dvd N _ hdvd, map_zero]

  set x₀ : (Σ _ : ℕ, ℕ) := ⟨N, 0⟩ with hx₀
  have hx₀S : x₀ ∈ S := by
    rw [hS, Finset.mem_sigma]
    refine ⟨Nat.mem_divisors_self N hN0, ?_⟩
    rw [Finset.mem_filter, Finset.mem_range, Nat.div_self (Nat.pos_of_ne_zero hN0)]
    exact ⟨Nat.one_pos, by simp⟩
  set S' := S.erase x₀ with hS'
  have hcard' : S'.card = dedekindPsi N - 1 := by rw [hS', Finset.card_erase_of_mem hx₀S, hcard]
  have hsplit : ∏ x ∈ S, (X - C (r x)) = (∏ x ∈ S', (X - C (r x))) * (X - C (r x₀)) := by
    rw [hS', Finset.prod_erase_mul _ _ hx₀S]

  set B : ℤ := ((N / 2 : ℕ) : ℤ) * ((N / 2 : ℕ) : ℤ) with hB
  have hBlt : B < (N : ℤ) * N := by
    have h1 : (N / 2 : ℕ) < N := Nat.div_lt_self (Nat.pos_of_ne_zero hN0) one_lt_two
    have h2 : ((N / 2 : ℕ) : ℤ) < N := by exact_mod_cast h1
    have h3 : (0 : ℤ) ≤ ((N / 2 : ℕ) : ℤ) := by positivity
    rw [hB]; nlinarith
  have hB0 : (0 : ℤ) ≤ B := by rw [hB]; positivity
  have hS'ord : ∀ x ∈ S', ((-B : ℤ) : WithTop ℤ) ≤ (r x).orderTop := by
    intro x hx
    have hxS : x ∈ S := Finset.mem_of_mem_erase hx
    have hxne : x ≠ x₀ := Finset.ne_of_mem_erase hx
    have hx1 : x.1 ∈ N.divisors := (Finset.mem_sigma.mp hxS).1
    have hx2 := (Finset.mem_sigma.mp hxS).2
    rw [Finset.mem_filter, Finset.mem_range] at hx2
    have hlt : x.1 < N := by
      rcases lt_or_eq_of_le (Nat.divisor_le hx1) with h | h
      · exact h
      · exfalso
        apply hxne
        have hb : x.2 = 0 := by
          have := hx2.1; rw [h, Nat.div_self (Nat.pos_of_ne_zero hN0)] at this; omega
        rcases x with ⟨x1, x2⟩
        simp only at h hb
        subst h; subst hb; rfl
    have hle2 : x.1 ≤ N / 2 := by
      obtain ⟨c, hc⟩ := Nat.dvd_of_mem_divisors hx1
      have hx10 : 0 < x.1 := Nat.pos_of_mem_divisors hx1
      have hc2 : 2 ≤ c := by
        rcases Nat.lt_or_ge c 2 with h | h
        · interval_cases c
          · rw [mul_zero] at hc; exact absurd hc hN0
          · rw [mul_one] at hc; exact absurd hc.symm (ne_of_lt hlt)
        · exact h
      rw [Nat.le_div_iff_mul_le two_pos, hc]
      exact Nat.mul_le_mul_left _ hc2
    refine le_trans ?_ (le_orderTop_slot' ℂ N (Units.mk0 ζ hζ0) x.1 x.2 hx1)
    have : -B ≤ -((x.1 : ℤ) * x.1) := by
      have : (x.1 : ℤ) * x.1 ≤ B := by
        rw [hB]; have := Nat.mul_le_mul hle2 hle2; exact_mod_cast this
      linarith
    exact_mod_cast this
  have hgood := good_prod (K := ℂ) (B := B) S' r hS'ord
  rw [hcard'] at hgood
  have hr₀ord : ((-((N : ℤ) * N) : ℤ) : WithTop ℤ) ≤ (r x₀).orderTop :=
    le_orderTop_slot' ℂ N (Units.mk0 ζ hζ0) N 0 (Nat.mem_divisors_self N hN0)
  have hr₀coeff : (r x₀).coeff (-((N : ℤ) * N)) = 1 := coeff_slot_top ℂ N (Units.mk0 ζ hζ0)
  set P' := ∏ x ∈ S', (X - C (r x)) with hP'
  have hP'monic : P'.Monic := monic_prod_of_monic _ _ fun x _ => monic_X_sub_C _
  have hP'deg : P'.natDegree = dedekindPsi N - 1 := by rw [hP', natDegree_finsetProd_X_sub_C_eq_card, hcard']
  have hcoef : ∀ k : ℕ, (P' * (X - C (r x₀))).coeff (k + 1) = P'.coeff k - P'.coeff (k + 1) * r x₀ := fun k => coeff_mul_X_sub_C
  have hcoef0 : (P' * (X - C (r x₀))).coeff 0 = -(P'.coeff 0 * r x₀) := by
    rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]; ring
  have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have hψ1 : 1 ≤ dedekindPsi N := by
    rw [← hcard]; exact Finset.card_pos.mpr ⟨x₀, hx₀S⟩
  refine ⟨?_, ?_⟩
  ·
    intro k hk
    set c := data.Φ.coeff k with hc_def
    by_cases hc : c = 0
    · rw [hc, natDegree_zero]; exact Nat.mul_pos (Nat.pos_of_ne_zero hN0) (by omega)
    have hlowk : ((-((N : ℤ) * N) - ((dedekindPsi N : ℤ) - k - 1) * B : ℤ) : WithTop ℤ) ≤
        (coeffEmb ℂ (qExpand ℚ N (evalAtJ (data.Φ.coeff k)))).orderTop := by
      rw [hyeq, hsplit]
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        rw [hcoef0, HahnSeries.orderTop_neg]
        refine le_trans ?_ HahnSeries.orderTop_add_le_mul
        refine le_trans ?_ (add_le_add (hgood 0) hr₀ord)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]; push_cast [Nat.cast_sub hψ1]; nlinarith [hBlt, hB0]
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [hcoef]
        refine le_trans ?_ (HahnSeries.min_orderTop_le_orderTop_sub)
        refine le_min ?_ ?_
        · refine le_trans ?_ (hgood k')
          rw [WithTop.coe_le_coe]; push_cast [Nat.cast_sub hψ1]; nlinarith [hBlt, hB0]
        · refine le_trans ?_ HahnSeries.orderTop_add_le_mul
          refine le_trans ?_ (add_le_add (hgood (k' + 1)) hr₀ord)
          rw [← WithTop.coe_add, WithTop.coe_le_coe]; push_cast [Nat.cast_sub hψ1]; nlinarith [hBlt, hB0]
    have hineq := WithTop.coe_le_coe.mp (hlowk.trans (hyup k hc))
    have hψk : (2 : ℤ) ≤ (dedekindPsi N : ℤ) - k := by
      have : k + 2 ≤ dedekindPsi N := hk
      omega
    have h1 : (N : ℤ) * (c.natDegree : ℤ) < (N : ℤ) * (N * ((dedekindPsi N : ℤ) - k)) := by nlinarith
    have h2 : (c.natDegree : ℤ) < N * ((dedekindPsi N : ℤ) - k) := lt_of_mul_lt_mul_left h1 hNpos.le
    have h3 : (c.natDegree : ℤ) < ((N * (dedekindPsi N - k) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : k ≤ dedekindPsi N)]; linarith
    exact_mod_cast h3
  ·
    set c := data.Φ.coeff (dedekindPsi N - 1) with hc_def
    set y := coeffEmb ℂ (qExpand ℚ N (evalAtJ c)) with hy
    set Q : LaurentSeries ℂ := if dedekindPsi N - 1 = 0 then 0 else P'.coeff (dedekindPsi N - 2) with hQ
    have hyψ : y = Q - r x₀ := by
      rw [hy, hyeq, hsplit, hQ]
      rcases Nat.eq_zero_or_pos (dedekindPsi N - 1) with h0 | hpos
      · rw [h0, hcoef0, if_pos rfl]
        have : P'.coeff 0 = 1 := by
          have : P'.natDegree = 0 := by rw [hP'deg, h0]
          rw [← this]; exact hP'monic
        rw [this, one_mul, zero_sub]
      · obtain ⟨k', hk'⟩ : ∃ k', dedekindPsi N - 1 = k' + 1 := ⟨dedekindPsi N - 2, by omega⟩
        rw [hk', hcoef, if_neg (by omega)]
        have : P'.coeff (k' + 1) = 1 := by rw [← hk', ← hP'deg]; exact hP'monic
        rw [this, one_mul, show dedekindPsi N - 2 = k' by omega]
    have hQord : ((-B : ℤ) : WithTop ℤ) ≤ Q.orderTop := by
      rw [hQ]
      split_ifs with h
      · simp
      · refine le_trans ?_ (hgood (dedekindPsi N - 2))
        rw [WithTop.coe_le_coe]; push_cast [Nat.cast_sub (by omega : 2 ≤ dedekindPsi N), Nat.cast_sub hψ1]; nlinarith [hBlt, hB0]
    have hQc : ∀ m ≤ -((N : ℤ) * N), Q.coeff m = 0 := fun m hm =>
      HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le (by exact_mod_cast (by linarith : m < -B)) hQord)
    have hyc : y.coeff (-((N : ℤ) * N)) = -1 := by
      rw [hyψ, HahnSeries.coeff_sub, hQc _ le_rfl, hr₀coeff]; ring
    have hyz : ∀ m < -((N : ℤ) * N), y.coeff m = 0 := by
      intro m hm
      rw [hyψ, HahnSeries.coeff_sub, hQc m hm.le,
        HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le (by exact_mod_cast hm) hr₀ord), sub_zero]
    have hc0 : c ≠ 0 := by
      intro h
      have : y = 0 := by rw [hy, h, map_zero, map_zero, map_zero]
      rw [this] at hyc
      simp at hyc
    have hdeg : (c.natDegree : ℤ) = N := by
      have ha : ¬ ((N : ℤ) * (-(c.natDegree : ℤ)) < -((N : ℤ) * N)) := by
        intro hlt
        have := hyz _ hlt
        rw [hy, hycoeff] at this
        have : (c.leadingCoeff : ℚ) = 0 := by exact_mod_cast (map_eq_zero (algebraMap ℚ ℂ)).mp this
        exact (leadingCoeff_ne_zero.mpr hc0) (by exact_mod_cast this)
      have hb : ¬ (-((N : ℤ) * N) < (N : ℤ) * (-(c.natDegree : ℤ))) := by
        intro hlt
        have := hylow (dedekindPsi N - 1) _ hlt
        rw [← hy, hyc] at this
        norm_num at this
      push Not at ha hb
      nlinarith
    refine ⟨by exact_mod_cast hdeg, ?_⟩
    have := hycoeff (dedekindPsi N - 1)
    rw [← hy, show (N : ℤ) * (-(c.natDegree : ℤ)) = -((N : ℤ) * N) by rw [hdeg]; ring, hyc] at this
    have : ((c.leadingCoeff : ℚ) : ℂ) = ((-1 : ℚ) : ℂ) := by rw [← this]; push_cast; rfl
    have : (c.leadingCoeff : ℚ) = -1 := by exact_mod_cast this
    exact_mod_cast this

end SolStrictNewton

open ModularCurve Polynomial in

theorem solution
    (N : ℕ) [NeZero N] (hN : 2 ≤ N) (data : ModularPolynomialData N) :
    (∀ k : ℕ, k + 2 ≤ dedekindPsi N → (data.Φ.coeff k).natDegree < N * (dedekindPsi N - k)) ∧
      (data.Φ.coeff (dedekindPsi N - 1)).natDegree = N ∧
      (data.Φ.coeff (dedekindPsi N - 1)).leadingCoeff = -1 :=
  SolStrictNewton.main N hN data

end
end S_ModularCurve_ModularPolynomialData_natDegree_coeff_lt_of_le_and_natDegree_coeff_sub_one_eq
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_natDegree_coeff_lt_of_le_and_natDegree_coeff_sub_one_eq (solution)
