-- Prove2me | solution 1 for HDXHitting.cpoly_monotone_log_concave
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:52.756678+00:00
-- url     : https://prove2.me/submissions/32f4112c-dd37-42ab-a302-3a5a5c3d55a4

import Mathlib
import Definitions.Def_HDXHitting_cPoly

section
set_option autoImplicit false
namespace HDXHitting.Dev.CPLC
open HDXHitting

lemma cpoly_nonneg {ι : Type*} [DecidableEq ι] (S : Finset ι) (lam : ℝ) (hlam : 0 ≤ lam)
    (μ : ι → ℝ) (hμ : ∀ j ∈ S, 0 ≤ μ j) : 0 ≤ cPoly S lam μ := by
  unfold cPoly
  refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun i hi => mul_nonneg (hμ i hi) ?_))
  exact Finset.prod_nonneg (fun j hj => by
    have := hμ j (Finset.mem_of_mem_erase hj); positivity)

/-- `c_d = ∏ a - λ ∑ ∏_{j≠i} a_j` for `a = μ + dλ`, `d ≥ 1`. -/
lemma cpoly_eq {ι : Type*} [DecidableEq ι] (S : Finset ι) (hd : 1 ≤ S.card) (lam : ℝ)
    (μ : ι → ℝ) :
    cPoly S lam μ = ∏ j ∈ S, (μ j + S.card * lam) -
      lam * ∑ i ∈ S, ∏ j ∈ S.erase i, (μ j + S.card * lam) := by
  have hd0 : (S.card : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast hd
    linarith
  unfold cPoly
  have h1 : ∀ i ∈ S, μ i * ∏ j ∈ S.erase i, (μ j + S.card * lam)
      = ∏ j ∈ S, (μ j + S.card * lam) - S.card * lam * ∏ j ∈ S.erase i, (μ j + S.card * lam) := by
    intro i hi
    rw [← Finset.mul_prod_erase S (fun j => μ j + S.card * lam) hi]; ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum]
  simp only [nsmul_eq_mul]
  field_simp

lemma sum_erase_prod {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ j ∈ S, 0 < a j) :
    ∑ i ∈ S, ∏ j ∈ S.erase i, a j = (∏ j ∈ S, a j) * ∑ i ∈ S, 1 / a i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have := ha i hi
  rw [← Finset.mul_prod_erase S a hi]
  field_simp

/-- the main log-concavity step in positive form -/
lemma main_step {ι : Type*} [DecidableEq ι] (S : Finset ι) (lam : ℝ) (hlam : 0 ≤ lam)
    (a a' : ι → ℝ) (ha : ∀ j ∈ S, 0 < a j) (ha' : ∀ j ∈ S, 0 < a' j) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (X X' : ℝ) (hX : X = 1 - lam * ∑ i ∈ S, 1 / a i)
    (hX' : X' = 1 - lam * ∑ i ∈ S, 1 / a' i) (hXp : 0 ≤ X) (hXp' : 0 ≤ X') :
    ((∏ j ∈ S, a j) * X) ^ t * ((∏ j ∈ S, a' j) * X') ^ (1 - t) ≤
      (∏ j ∈ S, (t * a j + (1 - t) * a' j)) *
        (1 - lam * ∑ i ∈ S, 1 / (t * a i + (1 - t) * a' i)) := by
  have ht1' : 0 ≤ 1 - t := by linarith
  have hP : 0 ≤ ∏ j ∈ S, a j := Finset.prod_nonneg (fun j hj => (ha j hj).le)
  have hP' : 0 ≤ ∏ j ∈ S, a' j := Finset.prod_nonneg (fun j hj => (ha' j hj).le)
  have hpos'' : ∀ j ∈ S, 0 < t * a j + (1 - t) * a' j := by
    intro j hj
    have := ha j hj; have := ha' j hj
    rcases eq_or_lt_of_le ht0 with h | h
    · subst h; simp; linarith
    · nlinarith [mul_pos h (ha j hj)]
  have hP'' : 0 ≤ ∏ j ∈ S, (t * a j + (1 - t) * a' j) :=
    Finset.prod_nonneg (fun j hj => (hpos'' j hj).le)
  rw [Real.mul_rpow hP hXp, Real.mul_rpow hP' hXp']
  have h1 : (∏ j ∈ S, a j) ^ t * (∏ j ∈ S, a' j) ^ (1 - t) ≤ ∏ j ∈ S, (t * a j + (1 - t) * a' j) := by
    rw [← Real.finsetProd_rpow S a (fun j hj => (ha j hj).le),
      ← Real.finsetProd_rpow S a' (fun j hj => (ha' j hj).le), ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun j hj => by
      have := ha j hj; have := ha' j hj; positivity) (fun j hj => ?_)
    exact Real.geom_mean_le_arith_mean2_weighted ht0 ht1' (ha j hj).le (ha' j hj).le (by ring)
  have h2 : X ^ t * X' ^ (1 - t) ≤ 1 - lam * ∑ i ∈ S, 1 / (t * a i + (1 - t) * a' i) := by
    have hg := Real.geom_mean_le_arith_mean2_weighted ht0 ht1' hXp hXp' (by ring : t + (1 - t) = 1)
    refine hg.trans ?_
    have hs : ∑ i ∈ S, 1 / (t * a i + (1 - t) * a' i) ≤
        t * ∑ i ∈ S, 1 / a i + (1 - t) * ∑ i ∈ S, 1 / a' i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun i hi => ?_)
      have h1 := ha i hi
      have h2 := ha' i hi
      have h3 := hpos'' i hi
      have key : 1 / (t * a i + (1 - t) * a' i) ≤ t * (1 / a i) + (1 - t) * (1 / a' i) := by
        rw [div_le_iff₀ h3]
        have e : (t * (1 / a i) + (1 - t) * (1 / a' i)) * (t * a i + (1 - t) * a' i)
            = t ^ 2 + (1 - t) ^ 2 + t * (1 - t) * (a' i / a i + a i / a' i) := by
          field_simp; ring
        rw [e]
        have : 2 ≤ a' i / a i + a i / a' i := by
          rw [div_add_div _ _ h1.ne' h2.ne', le_div_iff₀ (mul_pos h1 h2)]
          nlinarith [sq_nonneg (a i - a' i)]
        nlinarith [mul_nonneg ht0 ht1']
      exact key
    rw [hX, hX']
    nlinarith [mul_le_mul_of_nonneg_left hs hlam]
  calc (∏ j ∈ S, a j) ^ t * X ^ t * ((∏ j ∈ S, a' j) ^ (1 - t) * X' ^ (1 - t))
      = ((∏ j ∈ S, a j) ^ t * (∏ j ∈ S, a' j) ^ (1 - t)) * (X ^ t * X' ^ (1 - t)) := by ring
    _ ≤ _ := mul_le_mul h1 h2 (mul_nonneg (Real.rpow_nonneg hXp _) (Real.rpow_nonneg hXp' _)) hP''

lemma cpoly_prod_form {ι : Type*} [DecidableEq ι] (S : Finset ι) (hd : 1 ≤ S.card) (lam : ℝ)
    (μ : ι → ℝ) (ha : ∀ j ∈ S, 0 < μ j + S.card * lam) :
    cPoly S lam μ = (∏ j ∈ S, (μ j + S.card * lam)) *
      (1 - lam * ∑ i ∈ S, 1 / (μ i + S.card * lam)) := by
  rw [cpoly_eq S hd, sum_erase_prod S (fun j => μ j + S.card * lam) ha]
  ring

lemma card_pos_of_cpoly_pos {ι : Type*} [DecidableEq ι] (S : Finset ι) (lam : ℝ) (μ : ι → ℝ)
    (hc : 0 < cPoly S lam μ) : 1 ≤ S.card := by
  rcases Nat.eq_zero_or_pos S.card with h | h
  · rw [Finset.card_eq_zero] at h
    subst h
    simp [cPoly] at hc
  · exact h

lemma apos {ι : Type*} [DecidableEq ι] (S : Finset ι) (lam : ℝ) (hlam : 0 ≤ lam)
    (μ : ι → ℝ) (h0 : ∀ j ∈ S, 0 ≤ μ j) (hc : 0 < cPoly S lam μ) :
    ∀ j ∈ S, 0 < μ j + S.card * lam := by
  have hd := card_pos_of_cpoly_pos S lam μ hc
  have hdpos : (0 : ℝ) < S.card := by exact_mod_cast hd
  intro j hj
  by_contra hle
  have hz : μ j + S.card * lam = 0 := by
    have := h0 j hj
    have : 0 ≤ (S.card : ℝ) * lam := by positivity
    linarith
  have hl : lam = 0 := by
    have := h0 j hj
    have : (S.card : ℝ) * lam = 0 := by
      have : 0 ≤ (S.card : ℝ) * lam := by positivity
      linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hdpos.ne'
    · exact h
  rw [cpoly_eq S hd, Finset.prod_eq_zero hj hz, hl] at hc
  simp at hc

end HDXHitting.Dev.CPLC
namespace HDXHitting
open HDXHitting.Dev.CPLC in
theorem chk_cpoly_monotone_log_concave {ι : Type*} [DecidableEq ι] (S : Finset ι) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    (∀ μ μ' : ι → ℝ, (∀ j ∈ S, 0 ≤ μ j) → (∀ j ∈ S, μ j ≤ μ' j) →
        cPoly S lam μ ≤ cPoly S lam μ') ∧
      (∀ μ μ' : ι → ℝ, (∀ j ∈ S, 0 ≤ μ j) → (∀ j ∈ S, 0 ≤ μ' j) → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        cPoly S lam μ ^ t * cPoly S lam μ' ^ (1 - t) ≤ cPoly S lam (t • μ + (1 - t) • μ')) ∧
      (∀ μ : ι → ℝ, (∀ j ∈ S, μ j + S.card * lam ≠ 0) →
        cPoly S lam μ = (1 / (S.card : ℝ)) * (∏ j ∈ S, (μ j + S.card * lam)) *
          ∑ j ∈ S, μ j / (μ j + S.card * lam)) := by
  have hdl : 0 ≤ (S.card : ℝ) * lam := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro μ μ' h0 hle
    unfold cPoly
    have hs : ∑ i ∈ S, μ i * ∏ j ∈ S.erase i, (μ j + S.card * lam) ≤
        ∑ i ∈ S, μ' i * ∏ j ∈ S.erase i, (μ' j + S.card * lam) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      refine mul_le_mul (hle i hi) (Finset.prod_le_prod (fun j hj => ?_) (fun j hj => ?_))
        (Finset.prod_nonneg (fun j hj => ?_)) ((h0 i hi).trans (hle i hi))
      · have := h0 j (Finset.mem_of_mem_erase hj); linarith
      · have := hle j (Finset.mem_of_mem_erase hj); linarith
      · have := h0 j (Finset.mem_of_mem_erase hj); linarith
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  · intro μ μ' h0 h0' t ht0 ht1
    have hdl' : ∀ j ∈ S, 0 ≤ (t • μ + (1 - t) • μ') j := by
      intro j hj
      have := h0 j hj; have := h0' j hj
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : 0 ≤ 1 - t := by linarith
      positivity
    have hnn := cpoly_nonneg S lam hlam _ hdl'
    rcases eq_or_lt_of_le ht0 with h | htp
    · subst h; simp
    rcases eq_or_lt_of_le ht1 with h | htq
    · subst h; simp
    have ht1' : 0 < 1 - t := by linarith
    rcases eq_or_lt_of_le (cpoly_nonneg S lam hlam μ h0) with hc | hc
    · rw [← hc, Real.zero_rpow htp.ne', zero_mul]; exact hnn
    rcases eq_or_lt_of_le (cpoly_nonneg S lam hlam μ' h0') with hc' | hc'
    · rw [← hc', Real.zero_rpow ht1'.ne', mul_zero]; exact hnn
    have hd := card_pos_of_cpoly_pos S lam μ hc
    have ha := apos S lam hlam μ h0 hc
    have ha' := apos S lam hlam μ' h0' hc'
    have e : ∀ j, (t • μ + (1 - t) • μ') j + S.card * lam
        = t * (μ j + S.card * lam) + (1 - t) * (μ' j + S.card * lam) := by
      intro j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have ha'' : ∀ j ∈ S, 0 < (t • μ + (1 - t) • μ') j + S.card * lam := by
      intro j hj
      rw [e]
      have := ha j hj; have := ha' j hj
      nlinarith [mul_pos htp (ha j hj), mul_pos ht1' (ha' j hj)]
    have hXp : 0 ≤ 1 - lam * ∑ i ∈ S, 1 / (μ i + S.card * lam) := by
      have := cpoly_prod_form S hd lam μ ha
      have hP : 0 < ∏ j ∈ S, (μ j + S.card * lam) := Finset.prod_pos ha
      rw [this] at hc
      exact (pos_of_mul_pos_right hc hP.le).le
    have hXp' : 0 ≤ 1 - lam * ∑ i ∈ S, 1 / (μ' i + S.card * lam) := by
      have := cpoly_prod_form S hd lam μ' ha'
      have hP : 0 < ∏ j ∈ S, (μ' j + S.card * lam) := Finset.prod_pos ha'
      rw [this] at hc'
      exact (pos_of_mul_pos_right hc' hP.le).le
    rw [cpoly_prod_form S hd lam μ ha, cpoly_prod_form S hd lam μ' ha',
      cpoly_prod_form S hd lam _ ha'']
    simp only [e]
    exact main_step S lam hlam (fun j => μ j + S.card * lam) (fun j => μ' j + S.card * lam)
      ha ha' t ht0 ht1 _ _ rfl rfl hXp hXp'
  · intro μ hne
    unfold cPoly
    have key : ∑ i ∈ S, μ i * ∏ j ∈ S.erase i, (μ j + S.card * lam)
        = (∏ j ∈ S, (μ j + S.card * lam)) * ∑ j ∈ S, μ j / (μ j + S.card * lam) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have := hne i hi
      rw [← Finset.mul_prod_erase S (fun j => μ j + S.card * lam) hi]
      field_simp
    rw [key]; ring
end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_cpoly_monotone_log_concave := @HDXHitting.chk_cpoly_monotone_log_concave
