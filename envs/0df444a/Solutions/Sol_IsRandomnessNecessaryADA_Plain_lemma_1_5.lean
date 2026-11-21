-- Prove2me | solution 1 for IsRandomnessNecessaryADA.Plain.lemma_1_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T16:22:46.249847+00:00
-- url     : https://prove2.me/submissions/36b188ec-16a8-48a0-97ab-66ea355c115a

import Definitions.Def_IsRandomnessNecessaryADA_Plain_ConditionalCube

section
set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain.Dev.L15

open IsRandomnessNecessaryADA.Plain

noncomputable def sg (b : Bool) : ℝ := if b then 1 else -1

theorem law_apply {M d : ℕ} (f : (Fin M → Bool) → (Fin d → Bool)) (u : Fin M) (b : Bool)
    (y : Fin d → Bool) :
    (((coordinateLaw u b).map f) y).toReal =
      (1 / (Fintype.card (Fin M → Bool) : ℝ)) *
        ∑ x : Fin M → Bool, if f (Function.update x u b) = y then (1 : ℝ) else 0 := by
  classical
  unfold coordinateLaw
  rw [PMF.map_comp, PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Function.comp]
  rw [ENNReal.toReal_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : f (Function.update x u b) = y
    · simp [h, eq_comm]
    · simp [h, Ne.symm h]
  · intro x _
    split_ifs <;> simp

/-- flipping coordinate u -/
theorem sum_update {M : ℕ} (u : Fin M) (G : (Fin M → Bool) → ℝ) (b : Bool) :
    ∑ x : Fin M → Bool, G (Function.update x u b) =
      2 * ∑ x : Fin M → Bool, if x u = b then G x else 0 := by
  classical
  let e : (Fin M → Bool) ≃ (Fin M → Bool) :=
    { toFun := fun x => Function.update x u (!x u)
      invFun := fun x => Function.update x u (!x u)
      left_inv := fun x => by ext i; by_cases h : i = u <;> simp [h]
      right_inv := fun x => by ext i; by_cases h : i = u <;> simp [h] }
  have hsplit : ∑ x : Fin M → Bool, G (Function.update x u b) =
      ∑ x : Fin M → Bool, (if x u = b then G (Function.update x u b) else 0) +
      ∑ x : Fin M → Bool, (if x u = b then 0 else G (Function.update x u b)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs <;> simp
  have hp1 : ∑ x : Fin M → Bool, (if x u = b then G (Function.update x u b) else 0) =
      ∑ x : Fin M → Bool, if x u = b then G x else 0 := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : x u = b
    · simp only [h, if_true]; rw [← h, Function.update_eq_self]
    · simp [h]
  have hp2 : ∑ x : Fin M → Bool, (if x u = b then 0 else G (Function.update x u b)) =
      ∑ x : Fin M → Bool, if x u = b then G x else 0 := by
    rw [← e.sum_comp (fun z : Fin M → Bool => if z u = b then G z else 0)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have : (e x) u = !x u := by simp [e]
    have he : e x = Function.update x u b ∨ True := Or.inr trivial
    by_cases h : x u = b
    · simp [this, h]
    · have hb : (!x u) = b := by cases hx : x u <;> cases b <;> simp_all
      simp [this, h, hb, e]
  rw [hsplit, hp1, hp2]; ring

end IsRandomnessNecessaryADA.Plain.Dev.L15

namespace IsRandomnessNecessaryADA.Plain.Dev.L15

theorem core {M d : ℕ} (f : (Fin M → Bool) → (Fin d → Bool))
    (c : (Fin d → Bool) → Fin M → ℝ) (hc : ∀ y u, c y u = 1 ∨ c y u = -1)
    (l : ℝ) (hl : 0 < l) :
    l * ((1 / (Fintype.card (Fin M → Bool) : ℝ)) *
        ∑ x : Fin M → Bool, ∑ u : Fin M, sg (x u) * c (f x) u) ≤
      d * Real.log 2 + l ^ 2 * M / 2 := by
  classical
  set K : ℝ := (Fintype.card (Fin M → Bool) : ℝ) with hK
  have hKpos : 0 < K := by simp [hK]
  set m : (Fin M → Bool) → ℝ := fun x => ∑ u : Fin M, sg (x u) * c (f x) u with hm
  have hJ : Real.exp (l * ((1 / K) * ∑ x, m x)) ≤ ∑ x, (1 / K) * Real.exp (l * m x) := by
    have := convexOn_exp.map_sum_le (t := (Finset.univ : Finset (Fin M → Bool)))
      (w := fun _ => 1 / K) (p := fun x => l * m x)
      (fun _ _ => by positivity)
      (by simp [hK]) (fun _ _ => Set.mem_univ _)
    simpa [smul_eq_mul, ← Finset.mul_sum, Finset.mul_sum, mul_assoc, ← mul_assoc, mul_comm] using this
  have h2 : ∀ x, Real.exp (l * m x) ≤
      ∑ y : Fin d → Bool, Real.exp (l * ∑ u : Fin M, sg (x u) * c y u) := by
    intro x
    exact Finset.single_le_sum (f := fun y : Fin d → Bool =>
      Real.exp (l * ∑ u : Fin M, sg (x u) * c y u)) (fun _ _ => (Real.exp_pos _).le)
      (Finset.mem_univ (f x))
  have h3 : ∀ y : Fin d → Bool, (1 / K) * ∑ x : Fin M → Bool,
      Real.exp (l * ∑ u : Fin M, sg (x u) * c y u) ≤ Real.exp (M * l ^ 2 / 2) := by
    intro y
    have e1 : ∀ x : Fin M → Bool, Real.exp (l * ∑ u : Fin M, sg (x u) * c y u) =
        ∏ u : Fin M, Real.exp (l * (sg (x u) * c y u)) := by
      intro x
      rw [Finset.mul_sum, Real.exp_sum]
    simp only [e1]
    have e2 : ∑ x : Fin M → Bool, ∏ u : Fin M, Real.exp (l * (sg (x u) * c y u)) =
        ∏ u : Fin M, ∑ b : Bool, Real.exp (l * (sg b * c y u)) := by
      rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset Bool))
        (fun u b => Real.exp (l * (sg b * c y u)))]
      rw [Fintype.piFinset_univ]
    rw [e2]
    have e3 : ∀ u : Fin M, ∑ b : Bool, Real.exp (l * (sg b * c y u)) ≤
        2 * Real.exp (l ^ 2 / 2) := by
      intro u
      have hcosh := Real.cosh_le_exp_half_sq l
      rw [Real.cosh_eq] at hcosh
      rw [Fintype.sum_bool]
      rcases hc y u with h | h <;> simp [sg, h] <;> linarith
    calc (1 / K) * ∏ u : Fin M, ∑ b : Bool, Real.exp (l * (sg b * c y u))
        ≤ (1 / K) * ∏ u : Fin M, (2 * Real.exp (l ^ 2 / 2)) := by
          exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod
            (fun u _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
            (fun u _ => e3 u)) (by positivity)
      _ = Real.exp (M * l ^ 2 / 2) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← Real.exp_nat_mul]
          have : K = 2 ^ M := by simp [hK]
          rw [this]
          field_simp
  have h4 : Real.exp (l * ((1 / K) * ∑ x, m x)) ≤ 2 ^ d * Real.exp (M * l ^ 2 / 2) := by
    refine hJ.trans ?_
    calc ∑ x, (1 / K) * Real.exp (l * m x)
        ≤ ∑ x : Fin M → Bool, (1 / K) * ∑ y : Fin d → Bool,
            Real.exp (l * ∑ u : Fin M, sg (x u) * c y u) := by
          exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h2 x) (by positivity))
      _ = ∑ y : Fin d → Bool, (1 / K) * ∑ x : Fin M → Bool,
            Real.exp (l * ∑ u : Fin M, sg (x u) * c y u) := by
          simp only [Finset.mul_sum]; exact Finset.sum_comm
      _ ≤ ∑ y : Fin d → Bool, Real.exp (M * l ^ 2 / 2) := Finset.sum_le_sum (fun y _ => h3 y)
      _ = 2 ^ d * Real.exp (M * l ^ 2 / 2) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
  have h5 := Real.log_le_log (Real.exp_pos _) h4
  rw [Real.log_exp, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp] at h5
  have : (d : ℝ) * Real.log 2 + M * l ^ 2 / 2 = d * Real.log 2 + l ^ 2 * M / 2 := by ring
  linarith

end IsRandomnessNecessaryADA.Plain.Dev.L15

namespace IsRandomnessNecessaryADA.Plain.Dev.L15

open IsRandomnessNecessaryADA.Plain

noncomputable def Tsum {M d : ℕ} (f : (Fin M → Bool) → (Fin d → Bool)) (u : Fin M)
    (y : Fin d → Bool) : ℝ :=
  ∑ x : Fin M → Bool, sg (x u) * (if f x = y then (1 : ℝ) else 0)

theorem tv_formula {M d : ℕ} (f : (Fin M → Bool) → (Fin d → Bool)) (u : Fin M) :
    pmfTV ((coordinateLaw u false).map f) ((coordinateLaw u true).map f) =
      (1 / (Fintype.card (Fin M → Bool) : ℝ)) * ∑ y : Fin d → Bool, |Tsum f u y| := by
  classical
  unfold pmfTV QAlgorithms.Papers.Independent.Bridge50.P44.discreteTV
  rw [tsum_fintype]
  simp only [law_apply]
  have hT : ∀ y : Fin d → Bool,
      |(1 / (Fintype.card (Fin M → Bool) : ℝ)) *
          ∑ x : Fin M → Bool, (if f (Function.update x u false) = y then (1 : ℝ) else 0) -
        (1 / (Fintype.card (Fin M → Bool) : ℝ)) *
          ∑ x : Fin M → Bool, (if f (Function.update x u true) = y then (1 : ℝ) else 0)| =
      2 * (1 / (Fintype.card (Fin M → Bool) : ℝ)) * |Tsum f u y| := by
    intro y
    rw [sum_update u (fun z => if f z = y then (1 : ℝ) else 0) false,
      sum_update u (fun z => if f z = y then (1 : ℝ) else 0) true]
    have hTs : Tsum f u y =
        (∑ x : Fin M → Bool, if x u = true then (if f x = y then (1 : ℝ) else 0) else 0) -
        ∑ x : Fin M → Bool, if x u = false then (if f x = y then (1 : ℝ) else 0) else 0 := by
      unfold Tsum
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      cases hx : x u <;> by_cases h : f x = y <;> simp [sg, h]
    rw [hTs, ← abs_of_pos (show (0:ℝ) < 2 * (1 / (Fintype.card (Fin M → Bool) : ℝ)) by positivity),
      ← abs_mul, ← abs_neg]
    congr 1; ring
  simp only [hT]
  rw [← Finset.mul_sum]
  ring


theorem sum_tv {M d : ℕ} (f : (Fin M → Bool) → (Fin d → Bool)) :
    ∃ c : (Fin d → Bool) → Fin M → ℝ, (∀ y u, c y u = 1 ∨ c y u = -1) ∧
      ∑ u : Fin M, pmfTV ((coordinateLaw u false).map f) ((coordinateLaw u true).map f) =
        (1 / (Fintype.card (Fin M → Bool) : ℝ)) *
          ∑ x : Fin M → Bool, ∑ u : Fin M, sg (x u) * c (f x) u := by
  classical
  refine ⟨fun y u => if 0 ≤ Tsum f u y then 1 else -1, ?_, ?_⟩
  · intro y u; by_cases h : 0 ≤ Tsum f u y <;> simp [h]
  simp only [tv_formula]
  rw [← Finset.mul_sum]
  congr 1
  have habs : ∀ u y, |Tsum f u y| =
      (if 0 ≤ Tsum f u y then (1:ℝ) else -1) * Tsum f u y := by
    intro u y
    by_cases h : 0 ≤ Tsum f u y
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (not_le.1 h)]
  calc ∑ u : Fin M, ∑ y : Fin d → Bool, |Tsum f u y|
      = ∑ u : Fin M, ∑ y : Fin d → Bool, ∑ x : Fin M → Bool,
          (if 0 ≤ Tsum f u y then (1:ℝ) else -1) *
            (sg (x u) * (if f x = y then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun y _ => ?_))
        rw [habs]; unfold Tsum; rw [Finset.mul_sum]
    _ = ∑ u : Fin M, ∑ x : Fin M → Bool, ∑ y : Fin d → Bool,
          (if 0 ≤ Tsum f u y then (1:ℝ) else -1) *
            (sg (x u) * (if f x = y then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
    _ = ∑ x : Fin M → Bool, ∑ u : Fin M, ∑ y : Fin d → Bool,
          (if 0 ≤ Tsum f u y then (1:ℝ) else -1) *
            (sg (x u) * (if f x = y then (1 : ℝ) else 0)) := Finset.sum_comm
    _ = ∑ x : Fin M → Bool, ∑ u : Fin M, sg (x u) *
          (if 0 ≤ Tsum f u (f x) then (1:ℝ) else -1) := by
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun u _ => ?_))
        rw [Finset.sum_eq_single (f x)]
        · simp
        · intro y _ hy; simp [Ne.symm hy]
        · intro h; exact absurd (Finset.mem_univ _) h

end IsRandomnessNecessaryADA.Plain.Dev.L15

namespace IsRandomnessNecessaryADA.Plain

theorem chk_lemma_1_5 (M d : ℕ) (hM : 0 < M)
    (f : (Fin M → Bool) → (Fin d → Bool)) :
    (∑ u : Fin M, pmfTV ((coordinateLaw u false).map f)
      ((coordinateLaw u true).map f)) / (M : ℝ) ≤ Real.sqrt (2 * (d : ℝ) / M) := by
  obtain ⟨c, hc, hsum⟩ := Dev.L15.sum_tv f
  rw [hsum]
  set A := (1 / (Fintype.card (Fin M → Bool) : ℝ)) *
    ∑ x : Fin M → Bool, ∑ u : Fin M, Dev.L15.sg (x u) * c (f x) u with hA
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hcore := fun l hl => Dev.L15.core f c hc l hl
  have hln : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hApos0 : 0 ≤ A := by
    rw [← hsum]
    refine Finset.sum_nonneg (fun u _ => ?_)
    unfold pmfTV QAlgorithms.Papers.Independent.Bridge50.P44.discreteTV
    exact mul_nonneg (by norm_num) (tsum_nonneg fun _ => abs_nonneg _)
  have hsq : A ^ 2 ≤ 2 * M * d := by
    rcases hApos0.eq_or_lt with h0 | hApos
    · rw [← h0]; simp; positivity
    · have h := hcore (A / M) (div_pos hApos hMpos)
      rw [← hA] at h
      have e1 : A / M * A = A ^ 2 / M := by ring
      have e2 : (A / M) ^ 2 * M / 2 = A ^ 2 / (2 * M) := by field_simp
      have e3 : A ^ 2 / M = 2 * (A ^ 2 / (2 * M)) := by field_simp
      have hd : (d : ℝ) * Real.log 2 ≤ d := by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith
      have h4 : A ^ 2 / (2 * M) ≤ d := by linarith
      have := (div_le_iff₀ (by positivity)).1 h4
      linarith
  have hfin : (A / M) ^ 2 ≤ 2 * (d : ℝ) / M := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hMpos]
    nlinarith [hsq, hMpos]
  exact (le_abs_self _).trans (Real.abs_le_sqrt hfin)

end IsRandomnessNecessaryADA.Plain
end

theorem solution : type_of% @IsRandomnessNecessaryADA.Plain.chk_lemma_1_5 := @IsRandomnessNecessaryADA.Plain.chk_lemma_1_5
