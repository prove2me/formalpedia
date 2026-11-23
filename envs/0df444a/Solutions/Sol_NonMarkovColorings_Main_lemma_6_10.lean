-- Prove2me | solution 1 for NonMarkovColorings.Main.lemma_6_10
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T02:24:22.337257+00:00
-- url     : https://prove2.me/submissions/37a61cd9-3d73-4059-9b28-153c11bdc62d

import Mathlib
open MeasureTheory ProbabilityTheory



open Finset in
lemma weier_aux {ι : Type*} [DecidableEq ι] (s : Finset ι) (m c : ι → ℝ) (hm : ∀ a, 0 ≤ m a)
    (hpos : ∀ a, 0 ≤ m a + c a) (hs : (∀ a, 0 ≤ c a) ∨ (∀ a, c a ≤ 0)) :
    ∏ a ∈ s, m a + ∑ b ∈ s, c b * ∏ a ∈ s.erase b, m a ≤ ∏ a ∈ s, (m a + c a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [prod_insert hx, prod_insert hx, sum_insert hx, erase_insert hx]
    have h1 : ∑ b ∈ s, c b * ∏ a ∈ (insert x s).erase b, m a = m x * ∑ b ∈ s, c b * ∏ a ∈ s.erase b, m a := by
      rw [mul_sum]
      refine sum_congr rfl fun b hb => ?_
      have hbx : b ≠ x := fun h => hx (h ▸ hb)
      rw [erase_insert_of_ne (Ne.symm hbx), prod_insert (fun h => hx (mem_of_mem_erase h))]
      ring
    rw [h1]
    have hP : 0 ≤ ∏ a ∈ s, m a := prod_nonneg fun a _ => hm a
    have hS : 0 ≤ c x * ∑ b ∈ s, c b * ∏ a ∈ s.erase b, m a := by
      rw [mul_sum]
      refine sum_nonneg fun b _ => ?_
      have : 0 ≤ c x * c b := by
        rcases hs with h | h
        · exact mul_nonneg (h x) (h b)
        · exact mul_nonneg_of_nonpos_of_nonpos (h x) (h b)
      have h2 : 0 ≤ ∏ a ∈ s.erase b, m a := prod_nonneg fun a _ => hm a
      calc 0 ≤ (c x * c b) * ∏ a ∈ s.erase b, m a := mul_nonneg this h2
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_left ih (hpos x)
    nlinarith

open Finset in
/-- Negative association of the missing-color indicators. -/
lemma na_main (k : ℕ) : ∀ (d : ℕ) (q : Fin d → Fin k → ℝ), (∀ j a, 0 ≤ q j a) →
    (∀ j, ∑ a, q j a = 1) → ∀ gt gf : Fin k → ℝ,
    ((∀ a, 0 ≤ gf a ∧ gf a ≤ gt a) ∨ (∀ a, 0 ≤ gt a ∧ gt a ≤ gf a)) →
    ∑ ξ : Fin d → Fin k, (∏ j, q j (ξ j)) * ∏ a, (if (∀ j, ξ j ≠ a) then gt a else gf a) ≤
      ∏ a, ((∏ j, (1 - q j a)) * gt a + (1 - ∏ j, (1 - q j a)) * gf a) := by
  classical
  intro d
  induction d with
  | zero =>
    intro q _ _ gt gf _
    simp
  | succ d ih =>
    intro q hq hq1 gt gf hg
    set M : Fin k → ℝ := fun a => ∏ j : Fin d, (1 - q j.succ a) with hM
    set m : Fin k → ℝ := fun a => M a * gt a + (1 - M a) * gf a with hmdef
    have hq' : ∀ (j : Fin d) a, 0 ≤ q j.succ a := fun j a => hq _ _
    have hMle : ∀ a, 0 ≤ M a ∧ M a ≤ 1 := by
      intro a
      have h1 : ∀ j : Fin d, 0 ≤ 1 - q j.succ a ∧ 1 - q j.succ a ≤ 1 := by
        intro j
        have : q j.succ a ≤ ∑ a, q j.succ a := Finset.single_le_sum (fun a _ => hq _ a) (Finset.mem_univ a)
        rw [hq1] at this
        exact ⟨by linarith, by linarith [hq j.succ a]⟩
      exact ⟨Finset.prod_nonneg fun j _ => (h1 j).1, Finset.prod_le_one (fun j _ => (h1 j).1) fun j _ => (h1 j).2⟩
    have hm0 : ∀ a, 0 ≤ m a := by
      intro a
      obtain ⟨h0, h1⟩ := hMle a
      rcases hg with h | h
      · have := h a; simp only [hmdef]; nlinarith [this.1, this.2]
      · have := h a; simp only [hmdef]; nlinarith [this.1, this.2]
    have step : ∀ b : Fin k, ∑ ξ : Fin d → Fin k, (∏ j, q j.succ (ξ j)) *
        ∏ a, (if (∀ j, ξ j ≠ a) then Function.update gt b (gf b) a else gf a) ≤
        gf b * ∏ a ∈ Finset.univ.erase b, m a := by
      intro b
      have hg' : (∀ a, 0 ≤ gf a ∧ gf a ≤ Function.update gt b (gf b) a) ∨
          (∀ a, 0 ≤ Function.update gt b (gf b) a ∧ Function.update gt b (gf b) a ≤ gf a) := by
        rcases hg with h | h
        · left; intro a
          by_cases hab : a = b
          · subst hab; simp [(h a).1]
          · rw [Function.update_of_ne hab]; exact h a
        · right; intro a
          by_cases hab : a = b
          · subst hab; simp; linarith [(h a).1, (h a).2]
          · rw [Function.update_of_ne hab]; exact h a
      refine (ih (fun j => q j.succ) hq' (fun j => hq1 _) _ gf hg').trans ?_
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]
      have hb : (∏ j : Fin d, (1 - q j.succ b)) * Function.update gt b (gf b) b +
          (1 - ∏ j : Fin d, (1 - q j.succ b)) * gf b = gf b := by
        simp; ring
      rw [hb]
      refine le_of_eq (congrArg _ (Finset.prod_congr rfl fun a ha => ?_))
      rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
    -- decompose the sum
    have hL : ∑ ξ : Fin (d+1) → Fin k, (∏ j, q j (ξ j)) * ∏ a, (if (∀ j, ξ j ≠ a) then gt a else gf a)
        = ∑ b : Fin k, q 0 b * ∑ ξ : Fin d → Fin k, (∏ j, q j.succ (ξ j)) *
        ∏ a, (if (∀ j, ξ j ≠ a) then Function.update gt b (gf b) a else gf a) := by
      rw [← (Fin.consEquiv (fun _ : Fin (d+1) => Fin k)).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.forall_fin_succ]
      have : ∏ a, (if (b ≠ a ∧ ∀ j, ξ j ≠ a) then gt a else gf a) =
          ∏ a, (if (∀ j, ξ j ≠ a) then Function.update gt b (gf b) a else gf a) := by
        refine Finset.prod_congr rfl fun a _ => ?_
        by_cases hab : a = b
        · subst hab; simp
        · simp [Function.update_of_ne hab, Ne.symm hab]
      rw [this]; ring
    rw [hL]
    have hR : ∀ a, (∏ j : Fin (d+1), (1 - q j a)) * gt a + (1 - ∏ j : Fin (d+1), (1 - q j a)) * gf a
        = m a + q 0 a * (gf a - m a) := by
      intro a
      rw [Fin.prod_univ_succ]
      simp only [hmdef, hM]
      ring
    simp_rw [hR]
    have hsum : ∑ b : Fin k, q 0 b * (gf b * ∏ a ∈ Finset.univ.erase b, m a) =
        ∏ a, m a + ∑ b : Fin k, (q 0 b * (gf b - m b)) * ∏ a ∈ Finset.univ.erase b, m a := by
      have : ∏ a, m a = ∑ b : Fin k, q 0 b * (m b * ∏ a ∈ Finset.univ.erase b, m a) := by
        have h2 : ∀ b, m b * ∏ a ∈ Finset.univ.erase b, m a = ∏ a, m a :=
          fun b => Finset.mul_prod_erase _ _ (Finset.mem_univ b)
        simp_rw [h2, ← Finset.sum_mul, hq1 0, one_mul]
      rw [this, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => by ring
    calc _ ≤ ∑ b : Fin k, q 0 b * (gf b * ∏ a ∈ Finset.univ.erase b, m a) :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (step b) (hq 0 b)
      _ = _ := hsum
      _ ≤ _ := by
        refine weier_aux Finset.univ m (fun a => q 0 a * (gf a - m a)) hm0 ?_ ?_
        · intro a
          have h0 := hMle a
          have hgf : 0 ≤ gf a := by rcases hg with h | h; exacts [(h a).1, le_trans (h a).1 (h a).2]
          have h1 : q 0 a ≤ 1 := by
            have : q 0 a ≤ ∑ a, q 0 a := Finset.single_le_sum (fun a _ => hq 0 a) (Finset.mem_univ a)
            linarith [hq1 0]
          nlinarith [mul_nonneg (sub_nonneg.2 h1) (hm0 a), mul_nonneg (hq 0 a) hgf]
        · rcases hg with h | h
          · right; intro a
            have := hq 0 a
            have : m a ≥ gf a := by simp only [hmdef]; nlinarith [(h a).2, (hMle a).1, (hMle a).2]
            exact mul_nonpos_of_nonneg_of_nonpos (hq 0 a) (by linarith)
          · left; intro a
            have : m a ≤ gf a := by simp only [hmdef]; nlinarith [(h a).2, (hMle a).1, (hMle a).2]
            exact mul_nonneg (hq 0 a) (by linarith)

lemma expect_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k d : ℕ)
    (ξ : Fin d → Ω → Fin k) (hξ : ∀ j, Measurable (ξ j)) (hind : iIndepFun ξ P)
    (F : (Fin d → Fin k) → ℝ) :
    ∫ ω, F (fun j => ξ j ω) ∂P = ∑ x : Fin d → Fin k, (∏ j, P.real {ω | ξ j ω = x j}) * F x := by
  have hm : Measurable (fun ω j => ξ j ω) := measurable_pi_lambda _ hξ
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hξ j).aemeasurable)).1 hind
  rw [← integral_map hm.aemeasurable (measurable_of_finite F).aestronglyMeasurable, hmap,
    integral_fintype (Integrable.of_finite)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_eq_mul, Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Measure.map_apply (hξ j) (measurableSet_singleton _), Measure.real]
  rfl

lemma q_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (f : Ω → Fin k) (hf : Measurable f) : ∑ a : Fin k, P.real {ω | f ω = a} = 1 := by
  have := sum_measureReal_preimage_singleton (μ := P) (Finset.univ : Finset (Fin k)) (f := f)
    (fun y _ => hf (measurableSet_singleton y))
  simpa [Set.preimage] using this

lemma sum_prod_q {k d : ℕ} (q : Fin d → Fin k → ℝ) (h1 : ∀ j, ∑ a, q j a = 1) :
    ∑ x : Fin d → Fin k, ∏ j, q j (x j) = 1 := by
  rw [← Fintype.prod_sum]; simp [h1]

lemma sum_prod_q_ind {k d : ℕ} (q : Fin d → Fin k → ℝ) (h1 : ∀ j, ∑ a, q j a = 1) (a : Fin k) :
    ∑ x : Fin d → Fin k, (∏ j, q j (x j)) * (if ∀ j, x j ≠ a then (1:ℝ) else 0) =
      ∏ j, (1 - q j a) := by
  have h2 : ∀ x : Fin d → Fin k, (∏ j, q j (x j)) * (if ∀ j, x j ≠ a then (1:ℝ) else 0) =
      ∏ j, (q j (x j) * (if x j ≠ a then 1 else 0)) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_boole]
    simp
  simp_rw [h2]
  rw [← Fintype.prod_sum (fun j b => q j b * if b ≠ a then (1:ℝ) else 0)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have := h1 j
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)] at this
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
  simp only [ne_eq, not_true_eq_false, if_false, mul_zero, add_zero]
  rw [Finset.sum_congr rfl (g := fun b => q j b)]
  · linarith
  · intro b hb; simp [Finset.ne_of_mem_erase hb]

lemma factor_eq {k d : ℕ} (q : Fin d → Fin k → ℝ) (h1 : ∀ j, ∑ a, q j a = 1) (a : Fin k)
    (gt gf : ℝ) :
    ∑ x : Fin d → Fin k, (∏ j, q j (x j)) * (if ∀ j, x j ≠ a then gt else gf) =
      (∏ j, (1 - q j a)) * gt + (1 - ∏ j, (1 - q j a)) * gf := by
  have h2 : ∀ x : Fin d → Fin k, (∏ j, q j (x j)) * (if ∀ j, x j ≠ a then gt else gf) =
      gf * ∏ j, q j (x j) + (gt - gf) * ((∏ j, q j (x j)) * (if ∀ j, x j ≠ a then (1:ℝ) else 0)) := by
    intro x
    by_cases h : ∀ j, x j ≠ a <;> simp [h] <;> ring
  simp_rw [h2]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_prod_q q h1,
    sum_prod_q_ind q h1 a]
  ring

lemma card_missing {k d : ℕ} {Ω : Type*} (ξ : Fin d → Ω → Fin k) (ω : Ω) :
    (((Finset.univ \ Finset.univ.image fun j => ξ j ω).card : ℕ) : ℝ) =
      ∑ a : Fin k, (if ∀ j, ξ j ω ≠ a then (1:ℝ) else 0) := by
  have : (Finset.univ \ Finset.univ.image fun j => ξ j ω) =
      Finset.univ.filter (fun a => ∀ j, ξ j ω ≠ a) := by
    ext a; simp
  rw [this, Finset.card_filter]
  push_cast
  rfl

lemma mgf_card {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k d : ℕ)
    (ξ : Fin d → Ω → Fin k) (hξ : ∀ j, Measurable (ξ j)) (hind : iIndepFun ξ P) (t : ℝ) :
    ∫ ω, Real.exp (t * ((((Finset.univ \ Finset.univ.image fun j => ξ j ω).card : ℕ) : ℝ) -
      ∑ a : Fin k, ∏ j, (1 - P.real {ω | ξ j ω = a}))) ∂P ≤ Real.exp (k * t ^ 2 / 8) := by
  set q : Fin d → Fin k → ℝ := fun j a => P.real {ω | ξ j ω = a} with hqdef
  have hq0 : ∀ j a, 0 ≤ q j a := fun j a => measureReal_nonneg
  have hq1 : ∀ j, ∑ a, q j a = 1 := fun j => q_sum P (ξ j) (hξ j)
  set μa : Fin k → ℝ := fun a => ∏ j, (1 - q j a) with hμ
  set gt : Fin k → ℝ := fun a => Real.exp (t * (1 - μa a)) with hgt
  set gf : Fin k → ℝ := fun a => Real.exp (t * (0 - μa a)) with hgf
  have hm : Measurable (fun ω j => ξ j ω) := measurable_pi_lambda _ hξ
  -- Step 1
  have e1 : ∀ ω, Real.exp (t * ((((Finset.univ \ Finset.univ.image fun j => ξ j ω).card : ℕ) : ℝ) -
      ∑ a : Fin k, ∏ j, (1 - P.real {ω | ξ j ω = a}))) =
      (fun x : Fin d → Fin k => ∏ a, (if (∀ j, x j ≠ a) then gt a else gf a)) (fun j => ξ j ω) := by
    intro ω
    simp only
    rw [card_missing, ← Finset.sum_sub_distrib, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun a _ => ?_
    by_cases h : ∀ j, ξ j ω ≠ a <;> simp [h, hgt, hgf, hμ, hqdef]
  refine le_of_eq_of_le (integral_congr_ae (Filter.Eventually.of_forall e1)) ?_
  rw [expect_eq P k d ξ hξ hind (fun x : Fin d → Fin k => ∏ a, (if (∀ j, x j ≠ a) then gt a else gf a))]
  have hmono : ((∀ a, 0 ≤ gf a ∧ gf a ≤ gt a) ∨ (∀ a, 0 ≤ gt a ∧ gt a ≤ gf a)) := by
    rcases le_total 0 t with ht | ht
    · left; intro a
      refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 ?_⟩
      nlinarith
    · right; intro a
      refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 ?_⟩
      nlinarith
  refine (na_main k d q hq0 hq1 gt gf hmono).trans ?_
  have hfac : ∀ a, (∏ j, (1 - q j a)) * gt a + (1 - ∏ j, (1 - q j a)) * gf a ≤ Real.exp (t ^ 2 / 8) := by
    intro a
    set Y : Ω → ℝ := fun ω => (fun x : Fin d → Fin k => if ∀ j, x j ≠ a then (1:ℝ) else 0) (fun j => ξ j ω)
      with hY
    have hYm : Measurable Y := (measurable_of_finite (fun x : Fin d → Fin k => if ∀ j, x j ≠ a then (1:ℝ) else 0)).comp hm
    have hYb : ∀ᵐ ω ∂P, Y ω ∈ Set.Icc (0:ℝ) 1 := by
      refine Filter.Eventually.of_forall fun ω => ?_
      simp only [hY]; split_ifs <;> simp
    have hsg := hasSubgaussianMGF_of_mem_Icc hYm.aemeasurable hYb
    have hEY : P[Y] = μa a := by
      simp only [hY]
      rw [expect_eq P k d ξ hξ hind (fun x => if ∀ j, x j ≠ a then (1:ℝ) else 0)]
      exact sum_prod_q_ind q hq1 a
    have hmg := hsg.mgf_le t
    rw [hEY] at hmg
    have hint : mgf (fun ω => Y ω - μa a) P t =
        (∏ j, (1 - q j a)) * gt a + (1 - ∏ j, (1 - q j a)) * gf a := by
      unfold mgf
      have : ∀ ω, Real.exp (t * (Y ω - μa a)) =
          (fun x : Fin d → Fin k => if ∀ j, x j ≠ a then gt a else gf a) (fun j => ξ j ω) := by
        intro ω
        simp only [hY]
        by_cases h : ∀ j, ξ j ω ≠ a <;> simp [h, hgt, hgf]
      simp_rw [this]
      refine (expect_eq P k d ξ hξ hind (fun x : Fin d → Fin k => if ∀ j, x j ≠ a then gt a else gf a)).trans ?_
      exact factor_eq q hq1 a (gt a) (gf a)
    rw [← hint]
    refine hmg.trans (le_of_eq ?_)
    congr 1
    simp
    ring
  calc ∏ a, ((∏ j, (1 - q j a)) * gt a + (1 - ∏ j, (1 - q j a)) * gf a)
      ≤ ∏ a : Fin k, Real.exp (t ^ 2 / 8) := by
        refine Finset.prod_le_prod (fun a _ => ?_) (fun a _ => hfac a)
        rw [factor_eq q hq1 a (gt a) (gf a) |>.symm]
        refine Finset.sum_nonneg fun x _ => mul_nonneg (Finset.prod_nonneg fun j _ => hq0 j _) ?_
        split_ifs <;> exact (Real.exp_pos _).le
    _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
        congr 1; ring

lemma ball_bound {k : ℕ} (q : Fin k → ℝ) (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) (p : ℝ)
    (hp : ∀ a, q a ≤ p) (hp0 : 0 < p) (hp1 : p < 1) :
    (1 - p) / Real.exp 1 ≤ ∏ a, (1 - q a) := by
  set L := Real.log (1 - p) with hL
  have h1p : 0 < 1 - p := by linarith
  have hLge : 1 - (1 - p)⁻¹ ≤ L := Real.one_sub_inv_le_log_of_pos h1p
  have hLp : -L * (1 - p) ≤ p := by
    have : -L ≤ (1 - p)⁻¹ - 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_right this h1p.le
    have h3 : ((1 - p)⁻¹ - 1) * (1 - p) = p := by field_simp; ring
    linarith
  have hfac : ∀ a, Real.exp (q a / p * L) ≤ 1 - q a := by
    intro a
    have hr0 : 0 ≤ q a / p := div_nonneg (hq0 a) hp0.le
    have hr1 : q a / p ≤ 1 := (div_le_one hp0).2 (hp a)
    have := rpow_one_add_le_one_add_mul_self (s := -p) (by linarith) hr0 hr1
    have e : Real.exp (q a / p * L) = (1 + -p) ^ (q a / p) := by
      rw [Real.rpow_def_of_pos (by linarith), mul_comm]
      simp [hL, sub_eq_add_neg]
    rw [e]
    have : q a / p * -p = - q a := by field_simp
    linarith
  calc (1 - p) / Real.exp 1 = Real.exp (L - 1) := by
        rw [Real.exp_sub, Real.exp_log h1p]
    _ ≤ Real.exp (∑ a, q a / p * L) := by
        apply Real.exp_le_exp.2
        rw [← Finset.sum_mul, ← Finset.sum_div, hq1]
        rw [show L - 1 ≤ 1 / p * L ↔ _ from Iff.rfl]
        have : L - 1 ≤ 1 / p * L := by
          rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hp0]
          nlinarith
        exact this
    _ = ∏ a, Real.exp (q a / p * L) := Real.exp_sum _ _
    _ ≤ _ := Finset.prod_le_prod (fun a _ => (Real.exp_pos _).le) fun a _ => hfac a

lemma part1_core {k d : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d) (q : Fin d → Fin k → ℝ)
    (hq0 : ∀ j a, 0 ≤ q j a) (hq1 : ∀ j, ∑ a, q j a = 1) (p : ℝ) (hp : ∀ j a, q j a ≤ p)
    (hp1 : p < 1) :
    (k : ℝ) * ((1 - p) / Real.exp 1) ^ ((d : ℝ) / k) ≤ ∑ a : Fin k, ∏ j, (1 - q j a) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hp0 : 0 < p := by
    have j0 : Fin d := ⟨0, hd⟩
    have : ∑ a, q j0 a ≤ ∑ a : Fin k, p := Finset.sum_le_sum fun a _ => hp j0 a
    rw [hq1] at this
    simp at this
    by_contra h
    push Not at h
    nlinarith
  have hball : ∀ j, (1 - p) / Real.exp 1 ≤ ∏ a, (1 - q j a) :=
    fun j => ball_bound (q j) (hq0 j) (hq1 j) p (hp j) hp0 hp1
  have hb0 : 0 ≤ (1 - p) / Real.exp 1 := div_nonneg (by linarith) (Real.exp_pos _).le
  have hz : ∀ a ∈ (Finset.univ : Finset (Fin k)), 0 ≤ ∏ j, (1 - q j a) := by
    intro a _
    refine Finset.prod_nonneg fun j _ => ?_
    have : q j a ≤ ∑ a, q j a := Finset.single_le_sum (fun a _ => hq0 j a) (Finset.mem_univ a)
    linarith [hq1 j]
  have hgm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1:ℝ)) (fun a => ∏ j, (1 - q j a))
    (fun _ _ => zero_le_one) (by simp; omega) hz
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hgm
  have hprod : ((1 - p) / Real.exp 1) ^ d ≤ ∏ a : Fin k, ∏ j, (1 - q j a) := by
    rw [Finset.prod_comm]
    calc ((1 - p) / Real.exp 1) ^ d = ∏ j : Fin d, (1 - p) / Real.exp 1 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.prod_le_prod (fun j _ => hb0) fun j _ => hball j
  have h2 : ((1 - p) / Real.exp 1) ^ ((d : ℝ) / k) ≤ (∏ a : Fin k, ∏ j, (1 - q j a)) ^ ((k : ℝ)⁻¹) := by
    have := Real.rpow_le_rpow (by positivity) hprod (inv_nonneg.2 hkpos.le)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0] at this
    convert this using 2
    ring
  rw [le_div_iff₀ hkpos] at hgm
  nlinarith

lemma exp_card {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k d : ℕ)
    (ξ : Fin d → Ω → Fin k) (hξ : ∀ j, Measurable (ξ j)) (hind : iIndepFun ξ P) :
    ∫ ω, (((Finset.univ \ Finset.univ.image fun j => ξ j ω).card : ℕ) : ℝ) ∂P =
      ∑ a : Fin k, ∏ j, (1 - P.real {ω | ξ j ω = a}) := by
  have h1 : ∀ j, ∑ a, P.real {ω | ξ j ω = a} = 1 := fun j => q_sum P (ξ j) (hξ j)
  have e : ∀ ω, (((Finset.univ \ Finset.univ.image fun j => ξ j ω).card : ℕ) : ℝ) =
      (fun x : Fin d → Fin k => ∑ a : Fin k, (if ∀ j, x j ≠ a then (1:ℝ) else 0)) (fun j => ξ j ω) :=
    fun ω => card_missing ξ ω
  refine (integral_congr_ae (Filter.Eventually.of_forall e)).trans ?_
  refine (expect_eq P k d ξ hξ hind
    (fun x : Fin d → Fin k => ∑ a : Fin k, (if ∀ j, x j ≠ a then (1:ℝ) else 0))).trans ?_
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ =>
    sum_prod_q_ind (fun j a => P.real {ω | ξ j ω = a}) h1 a

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (ξ : Fin d → Ω → Fin k) (hξ : ∀ j, Measurable (ξ j))
    (hind : ProbabilityTheory.iIndepFun ξ P) :
    let p : ℝ := ⨆ j : Fin d, ⨆ a : Fin k, P.real {ω | ξ j ω = a}
    let A : Ω → Finset (Fin k) := fun ω => Finset.univ \ Finset.univ.image fun j => ξ j ω
    (k : ℝ) * ((1 - p) / Real.exp 1) ^ ((d : ℝ) / k) ≤ ∫ ω, ((A ω).card : ℝ) ∂P ∧
      ∀ a : ℝ, 0 ≤ a →
        P.real {ω | a ≤ |((A ω).card : ℝ) - ∫ ω', ((A ω').card : ℝ) ∂P|} ≤
          2 * Real.exp (-(a ^ 2) / (2 * k)) := by
  intro p A
  have hA : ∀ ω, A ω = Finset.univ \ Finset.univ.image fun j => ξ j ω := fun ω => rfl
  simp only [hA]
  set q : Fin d → Fin k → ℝ := fun j a => P.real {ω | ξ j ω = a} with hqdef
  have hq0 : ∀ j a, 0 ≤ q j a := fun j a => measureReal_nonneg
  have hq1 : ∀ j, ∑ a, q j a = 1 := fun j => q_sum P (ξ j) (hξ j)
  have hE := exp_card P k d ξ hξ hind
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : Measurable (fun ω j => ξ j ω) := measurable_pi_lambda _ hξ
  have hqle1 : ∀ j a, q j a ≤ 1 := by
    intro j a
    have : q j a ≤ ∑ a, q j a := Finset.single_le_sum (fun a _ => hq0 j a) (Finset.mem_univ a)
    linarith [hq1 j]
  have hpq : ∀ j a, q j a ≤ p := by
    intro j a
    refine le_trans ?_ (le_ciSup (f := fun j : Fin d => ⨆ a : Fin k, P.real {ω | ξ j ω = a})
      (Finite.bddAbove_range _) j)
    exact le_ciSup (f := fun a : Fin k => P.real {ω | ξ j ω = a}) (Finite.bddAbove_range _) a
  have hp1 : p ≤ 1 := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    exact ciSup_le fun j => ciSup_le fun a => hqle1 j a
  have hMnn : ∀ a, 0 ≤ ∏ j, (1 - q j a) := fun a =>
    Finset.prod_nonneg fun j _ => by linarith [hqle1 j a]
  refine ⟨?_, ?_⟩
  · rw [hE]
    rcases lt_or_eq_of_le hp1 with h | h
    · exact part1_core hk hd q hq0 hq1 p hpq h
    · have : (1 - p) = 0 := by linarith
      rw [this, zero_div, Real.zero_rpow]
      · simp only [mul_zero]; exact Finset.sum_nonneg fun a _ => hMnn a
      · have : (0 : ℝ) < d := by exact_mod_cast hd
        exact (div_pos this hkpos).ne'
  · intro a ha
    rw [hE]
    set Z : Ω → ℝ := fun ω => (((Finset.univ \ Finset.univ.image fun j => ξ j ω).card : ℕ) : ℝ) -
      ∑ a : Fin k, ∏ j, (1 - q j a) with hZ
    let G : (Fin d → Fin k) → ℝ := fun x => (((Finset.univ \ Finset.univ.image fun j => x j).card : ℕ) : ℝ) -
      ∑ a : Fin k, ∏ j, (1 - q j a)
    have hZG : Z = fun ω => G (fun j => ξ j ω) := rfl
    have hsg : HasSubgaussianMGF Z ((k : NNReal) / 4) P := by
      refine ⟨fun t => ?_, fun t => ?_⟩
      · have hmap : Integrable (fun x : Fin d → Fin k => Real.exp (t * G x))
          (P.map (fun ω j => ξ j ω)) := Integrable.of_finite
        exact (integrable_map_measure (measurable_of_finite _).aestronglyMeasurable
          hm.aemeasurable).1 hmap
      · have := mgf_card P k d ξ hξ hind t
        refine this.trans (le_of_eq ?_)
        push_cast
        ring_nf
    have h1 := hsg.measure_ge_le ha
    have h2 := hsg.neg.measure_ge_le ha
    have hc : -a ^ 2 / (2 * (((k : NNReal) / 4 : NNReal) : ℝ)) = -(2 * a ^ 2 / k) := by
      push_cast; field_simp; ring
    rw [hc] at h1 h2
    have hexp : Real.exp (-(2 * a ^ 2 / k)) ≤ Real.exp (-(a ^ 2) / (2 * k)) := by
      apply Real.exp_le_exp.2
      have : a ^ 2 / (2 * k) ≤ 2 * a ^ 2 / k := by
        rw [div_le_div_iff₀ (by positivity) hkpos]; nlinarith [sq_nonneg a]
      rw [neg_div]; linarith
    have hsub : {ω | a ≤ |Z ω|} ⊆ {ω | a ≤ Z ω} ∪ {ω | a ≤ (-Z) ω} := by
      intro ω hω
      simp only [Set.mem_union, Set.mem_setOf_eq, Pi.neg_apply] at hω ⊢
      rcases le_abs'.1 hω with h | h
      · right; linarith
      · left; exact h
    calc P.real {ω | a ≤ |Z ω|} ≤ P.real ({ω | a ≤ Z ω} ∪ {ω | a ≤ (-Z) ω}) :=
          measureReal_mono hsub
      _ ≤ P.real {ω | a ≤ Z ω} + P.real {ω | a ≤ (-Z) ω} := measureReal_union_le _ _
      _ ≤ 2 * Real.exp (-(a ^ 2) / (2 * k)) := by linarith
