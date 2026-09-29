-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.weighted_support_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/f6c69ab8-e5d6-50f8-90ad-c6c5fd18758b

import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.NumberTheory.Cyclotomic.Basic
import Theorems.Thm_ModularCurve_PhiGen_exists_phiGenDescends
import Theorems.Thm_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq
import Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_intCoeffs
import Theorems.Thm_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends
import Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_poleOrderLE
import Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_c_top
import Theorems.Thm_ModularCurve_PhiGen_PhiGenDescends_sum_mul_jqN_pow_eq_zero
import Theorems.Thm_ModularCurve_PhiGen_tPoleOrderLE_phiProd_conj_of_ne_zero
import Theorems.Thm_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead
import Theorems.Thm_ModularCurve_PhiGen_tPoleOrderLE_coeffEmb_iff
import Theorems.Thm_ModularCurve_PhiGen_tPoleOrderLE_of_qExpand
import Theorems.Thm_ModularCurve_ModularPolynomialData_eq_all
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_weighted_support_le
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "PoleOrderLE qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq coeff_jq_pow_self coeff_jq_pow_of_lt jqN evalAtJ evalAtJ_X ModularPolynomialData coeffEmb_coeff PhiGen.exists_phiGenDescends PhiGen.exists_modularPolynomialData_coeff_eq PhiGen.mem_adjoin_jq_of_phiGenDescends PhiGen.tPoleOrderLE_phiProd_conj_of_ne_zero PhiGen.phiProd_conj_coeff_zero_lead PhiGen.tPoleOrderLE_coeffEmb_iff PhiGen.tPoleOrderLE_of_qExpand ModularPolynomialData.eq_all dedekindPsi_prime"
p2m_open "ModularCurve"

p2m_open "Polynomial ModularCurve.PhiGen"

private theorem intCast_mul_coeff (z : ℤ) (f : LaurentSeries ℚ) (m : ℤ) :
    ((z : LaurentSeries ℚ) * f).coeff m = (z : ℚ) * f.coeff m := by
  rw [← HahnSeries.single_zero_intCast (Γ := ℤ) (R := ℚ) z]
  rw [← add_zero m, HahnSeries.coeff_single_mul_add, add_zero]

private theorem sum_coeff {α : Type} (s : Finset α) (F : α → LaurentSeries ℚ) (m : ℤ) :
    (∑ i ∈ s, F i).coeff m = ∑ i ∈ s, (F i).coeff m := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, HahnSeries.coeff_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, HahnSeries.coeff_add, ih]

private theorem poleOrderLE_mul {f g : LaurentSeries ℚ} {a b : ℕ}
    (hf : PoleOrderLE f a) (hg : PoleOrderLE g b) : PoleOrderLE (f * g) (a + b) := by
  intro m hm
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨hi, hj, hsum⟩ := hij
  rw [HahnSeries.mem_support] at hi hj
  exfalso
  have h1 : -(a : ℤ) ≤ ij.1 := not_lt.mp fun hlt => hi (hf _ hlt)
  have h2 : -(b : ℤ) ≤ ij.2 := not_lt.mp fun hlt => hj (hg _ hlt)
  push_cast at hm
  omega

private theorem mul_coeff_corner {f g : LaurentSeries ℚ} {a b : ℕ}
    (hf : PoleOrderLE f a) (hg : PoleOrderLE g b) :
    (f * g).coeff (-((a : ℤ) + b)) = f.coeff (-(a : ℤ)) * g.coeff (-(b : ℤ)) := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_single (-(a : ℤ), -(b : ℤ)) (fun ij hij hne => ?_) (fun hnmem => ?_)
  · rw [Finset.mem_antidiagonal] at hij
    obtain ⟨hi, hj, hsum⟩ := hij
    rw [HahnSeries.mem_support] at hi hj
    exfalso
    have h1 : -(a : ℤ) ≤ ij.1 := not_lt.mp fun hlt => hi (hf _ hlt)
    have h2 : -(b : ℤ) ≤ ij.2 := not_lt.mp fun hlt => hj (hg _ hlt)
    have hij1 : ij.1 = -(a : ℤ) := by omega
    have hij2 : ij.2 = -(b : ℤ) := by omega
    exact hne (Prod.ext hij1 hij2)
  · by_cases hf0 : f.coeff (-(a : ℤ)) = 0
    · rw [hf0, zero_mul]
    · by_cases hg0 : g.coeff (-(b : ℤ)) = 0
      · rw [hg0, mul_zero]
      · exact absurd (Finset.mem_antidiagonal.mpr
          ⟨(HahnSeries.mem_support _ _).mpr hf0, (HahnSeries.mem_support _ _).mpr hg0,
            (neg_add (a : ℤ) (b : ℤ)).symm⟩) hnmem

private theorem evalAtJ_coeff_neg (P : Polynomial ℤ) (d : ℕ) (hP : P.natDegree ≤ d) :
    (evalAtJ P).coeff (-(d : ℤ)) = ((P.coeff d : ℤ) : ℚ) := by
  have hE : evalAtJ P = Polynomial.eval₂ (algebraMap ℤ (LaurentSeries ℚ)) jq P :=
    Polynomial.aeval_def jq P
  rw [hE, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hP) jq]
  simp only [eq_intCast]
  rw [sum_coeff]
  have h1 : ∀ i ∈ Finset.range (d + 1), i ≠ d →
      ((P.coeff i : LaurentSeries ℚ) * jq ^ i).coeff (-(d : ℤ)) = 0 := by
    intro i hi hne
    rw [intCast_mul_coeff]
    have hilt : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
    rw [coeff_jq_pow_of_lt (by omega), mul_zero]
  rw [Finset.sum_eq_single_of_mem d (Finset.mem_range.mpr (Nat.lt_succ_of_le le_rfl)) h1]
  rw [intCast_mul_coeff, coeff_jq_pow_self, mul_one]

private theorem natDegree_le_of_poleOrderLE (P : Polynomial ℤ) (n : ℕ)
    (h : PoleOrderLE (evalAtJ P) n) : P.natDegree ≤ n := by
  by_contra hlt
  push Not at hlt
  have h1 := evalAtJ_coeff_neg P P.natDegree le_rfl
  have h2 : (evalAtJ P).coeff (-(P.natDegree : ℤ)) = 0 := h _ (by omega)
  rw [h2] at h1
  have hP0 : P ≠ 0 := fun h0 => by simp [h0] at hlt
  have h3 : P.coeff P.natDegree ≠ 0 := Polynomial.coeff_ne_zero_of_eq_degree
    (Polynomial.degree_eq_natDegree hP0)
  exact h3 (by exact_mod_cast h1.symm)

private theorem tPoleOrderLE_qExpand_round (p : ℕ) [NeZero p] (g : LaurentSeries ℚ)
    (h : TPoleOrderLE (qExpand ℚ p g) (p * p + p - 1)) :
    TPoleOrderLE (qExpand ℚ p g) (p * p) := by
  intro m hm
  by_cases hdvd : (p : ℤ) ∣ m
  · obtain ⟨m', rfl⟩ := hdvd
    refine h _ ?_
    have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
    push_cast at hm
    have hm' : m' < -(p : ℤ) := by
      by_contra hge
      push Not at hge
      have := mul_le_mul_of_nonneg_left hge (by linarith : (0 : ℤ) ≤ (p : ℤ))
      nlinarith
    have hle : m' ≤ -(p : ℤ) - 1 := by omega
    have h2 : (p : ℤ) * m' ≤ (p : ℤ) * (-(p : ℤ) - 1) := by
      exact mul_le_mul_of_nonneg_left hle (by linarith)
    have hcast : (((p * p + p - 1 : ℕ)) : ℤ) = (p : ℤ) * p + p - 1 := by
      have hp1n : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
      have h1le : 1 ≤ p * p + p := by nlinarith
      push_cast [Nat.cast_sub h1le]
      ring
    rw [hcast]
    nlinarith
  · rw [qExpand_coeff_of_not_dvd p g (by exact_mod_cast hdvd)]

private theorem support_of_degree_data_fold (Φ : Polynomial (Polynomial ℤ)) (p : ℕ) (hp : 2 ≤ p)
    (hdegΦ : Φ.natDegree ≤ p + 1) (htop : Φ.coeff (p + 1) = 1)
    (hk : ∀ k, k ≠ 0 → k ≤ p → (Φ.coeff k).natDegree ≤ p)
    (h0 : (Φ.coeff 0 - X ^ (p + 1)).natDegree ≤ p) (hpp : (Φ.coeff p).coeff p = -1) :
    (∀ b a : ℕ, ((Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 →
        1 * a + p * b ≤ p ^ 2 + p - 1) ∧
      (∀ b a : ℕ, ((Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 →
        p * a + 1 * b ≤ p ^ 2 + p - 1) := by
  have hsq : p ^ 2 = p * p := sq p
  have hp4 : 4 ≤ p * p := Nat.mul_le_mul hp hp
  have hΦb : ∀ b, p + 1 < b → Φ.coeff b = 0 := fun b hb =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegΦ hb)
  have h0deg : (Φ.coeff 0).natDegree ≤ p + 1 := by
    have : Φ.coeff 0 = (Φ.coeff 0 - X ^ (p + 1)) + X ^ (p + 1) := by ring
    rw [this]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (h0.trans (Nat.le_succ p)) ?_)
    rw [Polynomial.natDegree_X_pow]

  have hbp : ∀ a, (Φ.coeff p).coeff a + (X ^ p : Polynomial ℤ).coeff a ≠ 0 → a + 1 ≤ p := by
    intro a ha
    rw [Polynomial.coeff_X_pow] at ha
    rcases Nat.lt_trichotomy a p with hap | rfl | hap
    · omega
    · rw [if_pos rfl, hpp] at ha
      exact absurd (by ring) ha
    · rw [if_neg (Nat.ne_of_gt hap), add_zero] at ha
      exact absurd (Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hk p (by omega) le_rfl) hap)) ha

  have hmid : ∀ b a, b ≠ 0 → b < p → (Φ.coeff b).coeff a ≠ 0 → a ≤ p := fun b a hb0 hb ha =>
    (Polynomial.le_natDegree_of_ne_zero ha).trans (hk b hb0 hb.le)

  have hD : ∀ b, (X ^ (p + 1) - C (X ^ p) * X ^ p : Polynomial (Polynomial ℤ)).coeff b
      = (if b = p + 1 then 1 else 0) - (if b = p then X ^ p else 0) := fun b => by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
  have hD' : ∀ b, (C (X ^ (p + 1)) - C (X ^ p) * X ^ p : Polynomial (Polynomial ℤ)).coeff b
      = (if b = 0 then X ^ (p + 1) else 0) - (if b = p then X ^ p else 0) := fun b => by
    rw [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
  constructor
  · intro b a h
    rw [Polynomial.coeff_sub, hD b] at h
    rcases Nat.lt_trichotomy b p with hb | hbq | hb
    · rw [if_neg (by omega), if_neg (Nat.ne_of_lt hb), sub_zero, sub_zero] at h
      rcases Nat.eq_zero_or_pos b with rfl | hb0
      · have ha : a ≤ p + 1 := (Polynomial.le_natDegree_of_ne_zero h).trans h0deg
        omega
      · have ha : a ≤ p := hmid b a (Nat.pos_iff_ne_zero.mp hb0) hb h
        have hpb : p * b + p ≤ p * p := by
          have := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hb)
          rwa [Nat.mul_succ] at this
        omega
    · rw [hbq] at h ⊢
      rw [if_neg (by omega), if_pos rfl, zero_sub, sub_neg_eq_add, Polynomial.coeff_add] at h
      have ha := hbp a h
      omega
    · by_cases hb1 : b = p + 1
      · subst hb1
        rw [if_pos rfl, if_neg (Nat.succ_ne_self p), sub_zero, htop, sub_self,
          Polynomial.coeff_zero] at h
        exact absurd rfl h
      · rw [if_neg hb1, if_neg (Nat.ne_of_gt hb), sub_zero, sub_zero, hΦb b (by omega),
          Polynomial.coeff_zero] at h
        exact absurd rfl h
  · intro b a h
    rw [Polynomial.coeff_sub, hD' b] at h
    rcases Nat.lt_trichotomy b p with hb | hbq | hb
    · rw [if_neg (Nat.ne_of_lt hb), sub_zero] at h
      rcases Nat.eq_zero_or_pos b with rfl | hb0
      · rw [if_pos rfl] at h
        have ha : a ≤ p := (Polynomial.le_natDegree_of_ne_zero h).trans h0
        have hpa : p * a ≤ p * p := Nat.mul_le_mul_left p ha
        omega
      · rw [if_neg (Nat.pos_iff_ne_zero.mp hb0), sub_zero] at h
        have ha : a ≤ p := hmid b a (Nat.pos_iff_ne_zero.mp hb0) hb h
        have hpa : p * a ≤ p * p := Nat.mul_le_mul_left p ha
        omega
    · rw [hbq] at h ⊢
      rw [if_neg (by omega), if_pos rfl, zero_sub, sub_neg_eq_add, Polynomial.coeff_add] at h
      have ha := hbp a h
      have hpa : p * a + p ≤ p * p := by
        have := Nat.mul_le_mul_left p ha
        rwa [Nat.mul_succ] at this
      omega
    · by_cases hb1 : b = p + 1
      · subst hb1
        rw [if_neg (Nat.succ_ne_zero p), if_neg (Nat.succ_ne_self p), sub_zero, sub_zero, htop,
          Polynomial.coeff_one] at h
        have ha : a = 0 := by
          by_contra ha
          rw [if_neg ha] at h
          exact h rfl
        subst ha
        omega
      · rw [if_neg (by omega), if_neg (Nat.ne_of_gt hb), sub_zero, sub_zero, hΦb b (by omega),
          Polynomial.coeff_zero] at h
        exact absurd rfl h

set_option maxHeartbeats 3200000 in

theorem _root_.P2MW.S_ModularCurve_ModularPolynomialData_weighted_support_le.solution (p : ℕ) [hp : Fact p.Prime] (data : ModularPolynomialData p) :
    (∀ b a : ℕ, ((data.Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 →
        1 * a + p * b ≤ p ^ 2 + p - 1) ∧
      (∀ b a : ℕ, ((data.Φ - (C (X ^ (p + 1)) - C (X ^ p) * X ^ p)).coeff b).coeff a ≠ 0 →
        p * a + 1 * b ≤ p ^ 2 + p - 1) := by
  classical

  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  haveI hcyc : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  haveI hgal : IsGalois ℚ (CyclotomicField p ℚ) := IsCyclotomicExtension.isGalois (S := {p})
    (K := ℚ) (L := CyclotomicField p ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (A := ℚ)
    (B := CyclotomicField p ℚ) (S := ({p} : Set ℕ)) (Set.mem_singleton p) hp.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hp.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField p ℚ)ˣ) : CyclotomicField p ℚ) p := by
    rwa [IsUnit.unit_spec]
  obtain ⟨c, hc⟩ := PhiGen.exists_phiGenDescends p hzu.unit hζ
  have hζ1 : hzu.unit ^ p = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one]
    exact hz.pow_eq_one)

  obtain ⟨data₀, hd₀⟩ := PhiGen.exists_modularPolynomialData_coeff_eq hc
    (hc.intCoeffs hζ1) (PhiGen.mem_adjoin_jq_of_phiGenDescends p hzu.unit hζ c hc)
  have hdd : data = data₀ := ModularPolynomialData.eq_all p data data₀
  subst hdd

  have hdeg : data.Φ.natDegree = p + 1 :=
    data.natDegree_eq.trans (dedekindPsi_prime hp.out)

  have hck : ∀ k, k ≠ 0 → PoleOrderLE (c k) p := by
    intro k hk
    have h1 := PhiGen.tPoleOrderLE_phiProd_conj_of_ne_zero p hzu.unit k hk
    rw [hc k] at h1
    have h2 := (PhiGen.tPoleOrderLE_coeffEmb_iff _ _).mp h1
    have h3 := tPoleOrderLE_qExpand_round p (c k) h2
    exact PhiGen.tPoleOrderLE_of_qExpand h3
  have hkdeg : ∀ k, k ≠ 0 → (data.Φ.coeff k).natDegree ≤ p := by
    intro k hk
    refine natDegree_le_of_poleOrderLE _ p ?_
    rw [hd₀ k]
    exact hck k hk

  have htop : data.Φ.coeff (p + 1) = 1 := by
    have hm := data.monic
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg] at hm
    exact hm

  have hlead := PhiGen.phiProd_conj_coeff_zero_lead p hzu.unit hζ
  rw [hc 0, coeffEmb_coeff] at hlead
  have hc0top : (c 0).coeff (-((p : ℤ) + 1)) = 1 := by
    have hq : (qExpand ℚ p (c 0)).coeff ((p : ℤ) * (-((p : ℤ) + 1)))
        = (c 0).coeff (-((p : ℤ) + 1)) := by rw [qExpand_coeff_mul]
    have harg : -(((p * p + p : ℕ)) : ℤ) = (p : ℤ) * (-((p : ℤ) + 1)) := by push_cast; ring
    rw [harg, hq] at hlead
    exact (algebraMap ℚ (CyclotomicField p ℚ)).injective (by rw [hlead, map_one])
  have h00 : PoleOrderLE (c 0) (p + 1) := hc.poleOrderLE 0

  have h0 : (data.Φ.coeff 0 - X ^ (p + 1)).natDegree ≤ p := by
    refine natDegree_le_of_poleOrderLE _ p ?_
    have hev : evalAtJ (data.Φ.coeff 0 - X ^ (p + 1)) = c 0 - jq ^ (p + 1) := by
      rw [map_sub, map_pow, evalAtJ_X, hd₀ 0]
    rw [hev]
    intro m hm
    rw [HahnSeries.coeff_sub]
    rcases eq_or_lt_of_le (show m ≤ -((p : ℤ) + 1) by omega) with heq | hlt
    · rw [heq, hc0top]
      have hjq : (jq ^ (p + 1)).coeff (-((p : ℤ) + 1)) = 1 := by
        have h := coeff_jq_pow_self (p + 1)
        rwa [show -(((p + 1 : ℕ)) : ℤ) = -((p : ℤ) + 1) by push_cast; ring] at h
      rw [hjq, sub_self]
    · rw [h00 m (by push_cast; omega), coeff_jq_pow_of_lt (by push_cast; omega), sub_self]

  have hrel := hc.sum_mul_jqN_pow_eq_zero
  have hcoeffsum : ∑ k ∈ Finset.range (p + 2),
      ((c k) * (jqN p) ^ k).coeff (-((p : ℤ) ^ 2 + p)) = 0 := by
    rw [← sum_coeff, hrel, HahnSeries.coeff_zero]
  have hjqNpow : ∀ k : ℕ, (jqN p) ^ k = qExpand ℚ p (jq ^ k) := fun k => by
    rw [show jqN p = qExpand ℚ p jq from rfl, ← map_pow]
  have hqpole : ∀ k : ℕ, PoleOrderLE (qExpand ℚ p (jq ^ k)) (p * k) := by
    intro k m hm
    by_cases hdvd : (p : ℤ) ∣ m
    · obtain ⟨m', rfl⟩ := hdvd
      rw [qExpand_coeff_mul]
      refine coeff_jq_pow_of_lt ?_
      push_cast at hm
      by_contra hge
      push Not at hge
      have := mul_le_mul_of_nonneg_left hge (by positivity : (0 : ℤ) ≤ (p : ℤ))
      nlinarith
    · rw [qExpand_coeff_of_not_dvd p _ (by exact_mod_cast hdvd)]
  have hqtop : ∀ k : ℕ, (qExpand ℚ p (jq ^ k)).coeff (-(((p * k : ℕ)) : ℤ)) = 1 := by
    intro k
    have harg : -(((p * k : ℕ)) : ℤ) = (p : ℤ) * (-(k : ℤ)) := by push_cast; ring
    rw [harg, qExpand_coeff_mul, coeff_jq_pow_self]

  have hterm0 : ((c 0) * (jqN p) ^ 0).coeff (-((p : ℤ) ^ 2 + p)) = 0 := by
    rw [hjqNpow 0]
    refine poleOrderLE_mul h00 (hqpole 0) _ ?_
    have hp2 : 2 ≤ p := hp.out.two_le
    push_cast
    nlinarith
  have hterm_mid : ∀ k, k ≠ 0 → k < p →
      ((c k) * (jqN p) ^ k).coeff (-((p : ℤ) ^ 2 + p)) = 0 := by
    intro k hk0 hkp
    rw [hjqNpow k]
    refine poleOrderLE_mul (hck k hk0) (hqpole k) _ ?_
    have hp2 : 2 ≤ p := hp.out.two_le
    push_cast
    nlinarith
  have hterm_p : ((c p) * (jqN p) ^ p).coeff (-((p : ℤ) ^ 2 + p))
      = (c p).coeff (-(p : ℤ)) := by
    rw [hjqNpow p]
    have harg : -((p : ℤ) ^ 2 + p) = -(((p : ℕ) : ℤ) + ((p * p : ℕ) : ℤ)) := by
      push_cast
      ring
    rw [harg, mul_coeff_corner (hck p hp.out.ne_zero) (hqpole p), hqtop p, mul_one]
  have hterm_p1 : ((c (p + 1)) * (jqN p) ^ (p + 1)).coeff (-((p : ℤ) ^ 2 + p)) = 1 := by
    rw [hc.c_top, one_mul, hjqNpow]
    have harg : -((p : ℤ) ^ 2 + p) = -(((p * (p + 1) : ℕ)) : ℤ) := by push_cast; ring
    rw [harg, hqtop]

  have hcptop : (c p).coeff (-(p : ℤ)) = -1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hcoeffsum
    have hz0 : ∑ k ∈ Finset.range p,
        ((c k) * (jqN p) ^ k).coeff (-((p : ℤ) ^ 2 + p)) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkp : k < p := Finset.mem_range.mp hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact hterm0
      · exact hterm_mid k (by omega) hkp
    rw [hz0, zero_add, hterm_p, hterm_p1] at hcoeffsum
    linarith

  have hpp : (data.Φ.coeff p).coeff p = -1 := by
    have hE := evalAtJ_coeff_neg (data.Φ.coeff p) p (hkdeg p hp.out.ne_zero)
    rw [hd₀ p, hcptop] at hE
    exact_mod_cast hE.symm

  exact support_of_degree_data_fold data.Φ p hp.out.two_le hdeg.le htop
    (fun k hk0 _ => hkdeg k hk0) h0 hpp

end ModularCurve

end S_ModularCurve_ModularPolynomialData_weighted_support_le
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_weighted_support_le (solution)
