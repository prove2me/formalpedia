-- Prove2me | solution 1 for LiquidDemocracy.Upward.upward_cond_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:53:04.275075+00:00
-- url     : https://prove2.me/submissions/56da6bec-12e2-4476-b068-d9415f62bfc2

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Setting

open MeasureTheory Filter Topology Asymptotics LiquidDemocracy.Upward
open scoped Classical

/-! ### Finite-sum facts about `voteProb` -/

noncomputable def LC2_w {n : ℕ} (c : Fin n → ℝ) (i : Fin n) (b : Bool) : ℝ :=
  if b then c i else 1 - c i

theorem LC2_voteProb_eq {n : ℕ} (c : Fin n → ℝ) (E : (Fin n → Bool) → Prop) :
    voteProb c E = ∑ v, if E v then ∏ i, LC2_w c i (v i) else 0 := by
  unfold voteProb LC2_w
  rw [Finset.sum_filter]

theorem LC2_prod_nonneg {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (v : Fin n → Bool) : 0 ≤ ∏ i, LC2_w c i (v i) := by
  apply Finset.prod_nonneg
  intro i _
  unfold LC2_w
  have := hc i
  split_ifs <;> simp only [Set.mem_Icc] at this <;> linarith

/-- Product formula: `∑_v ∏_k h_k(v_k) = ∏_k ∑_b h_k(b)`. -/
theorem LC2_sum_prod {n : ℕ} (h : Fin n → Bool → ℝ) :
    ∑ v : Fin n → Bool, ∏ k, h k (v k) = ∏ k, ∑ b, h k b :=
  (Fintype.prod_sum h).symm

theorem LC2_total {n : ℕ} (c : Fin n → ℝ) : ∑ v : Fin n → Bool, ∏ i, LC2_w c i (v i) = 1 := by
  rw [LC2_sum_prod]
  simp [LC2_w]

theorem LC2_vp_mono {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (E F : (Fin n → Bool) → Prop) (h : ∀ v, E v → F v) : voteProb c E ≤ voteProb c F := by
  rw [LC2_voteProb_eq, LC2_voteProb_eq]
  apply Finset.sum_le_sum
  intro v _
  have := LC2_prod_nonneg c hc v
  by_cases hE : E v
  · rw [if_pos hE, if_pos (h v hE)]
  · rw [if_neg hE]; split_ifs <;> linarith

theorem LC2_vp_union {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (E F : (Fin n → Bool) → Prop) :
    voteProb c (fun v => E v ∨ F v) ≤ voteProb c E + voteProb c F := by
  rw [LC2_voteProb_eq, LC2_voteProb_eq, LC2_voteProb_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have := LC2_prod_nonneg c hc v
  by_cases hE : E v <;> by_cases hF : F v <;> simp [hE, hF] <;> linarith

theorem LC2_vp_compl {n : ℕ} (c : Fin n → ℝ) (E : (Fin n → Bool) → Prop) :
    voteProb c E + voteProb c (fun v => ¬ E v) = 1 := by
  rw [LC2_voteProb_eq, LC2_voteProb_eq, ← Finset.sum_add_distrib, ← LC2_total c]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hE : E v <;> simp [hE]

/-! ### Second moment of a linear statistic -/

noncomputable def LC2_y {n : ℕ} (c : Fin n → ℝ) (i : Fin n) (b : Bool) : ℝ :=
  (if b then 1 else 0) - c i

theorem LC2_cross {n : ℕ} (c : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    ∑ v : Fin n → Bool, (∏ k, LC2_w c k (v k)) * (LC2_y c i (v i) * LC2_y c j (v j)) = 0 := by
  have hrw : ∀ v : Fin n → Bool, (∏ k, LC2_w c k (v k)) * (LC2_y c i (v i) * LC2_y c j (v j)) =
      ∏ k, (LC2_w c k (v k) * (if k = i then LC2_y c i (v k) else 1) *
        (if k = j then LC2_y c j (v k) else 1)) := by
    intro v
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i,
      Finset.prod_ite_eq' Finset.univ j]
    simp only [Finset.mem_univ, if_true]
    ring
  simp_rw [hrw]
  rw [LC2_sum_prod (fun k b => LC2_w c k b * (if k = i then LC2_y c i b else 1) *
    (if k = j then LC2_y c j b else 1))]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [LC2_w, LC2_y, hij]
  ring

theorem LC2_diag {n : ℕ} (c : Fin n → ℝ) (i : Fin n) :
    ∑ v : Fin n → Bool, (∏ k, LC2_w c k (v k)) * (LC2_y c i (v i) * LC2_y c i (v i)) =
      c i * (1 - c i) := by
  have hrw : ∀ v : Fin n → Bool, (∏ k, LC2_w c k (v k)) * (LC2_y c i (v i) * LC2_y c i (v i)) =
      ∏ k, (LC2_w c k (v k) * (if k = i then LC2_y c i (v k) * LC2_y c i (v k) else 1)) := by
    intro v
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i]
    simp
  simp_rw [hrw]
  rw [LC2_sum_prod (fun k b => LC2_w c k b *
    (if k = i then LC2_y c i b * LC2_y c i b else 1))]
  rw [Finset.prod_eq_single i]
  · simp [LC2_w, LC2_y]; ring
  · intro k _ hk
    simp [LC2_w, LC2_y, hk]
  · simp

theorem LC2_second_moment {n : ℕ} (c : Fin n → ℝ) (a : Fin n → ℝ) :
    ∑ v : Fin n → Bool, (∏ k, LC2_w c k (v k)) * (∑ i, a i * LC2_y c i (v i)) ^ 2 =
      ∑ i, a i ^ 2 * (c i * (1 - c i)) := by
  have hexp : ∀ v : Fin n → Bool, (∏ k, LC2_w c k (v k)) * (∑ i, a i * LC2_y c i (v i)) ^ 2 =
      ∑ i, ∑ j, a i * a j * ((∏ k, LC2_w c k (v k)) * (LC2_y c i (v i) * LC2_y c j (v j))) := by
    intro v
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single i]
  · rw [← Finset.mul_sum, LC2_diag]; ring
  · intro j _ hji
    rw [← Finset.mul_sum, LC2_cross c i j (Ne.symm hji), mul_zero]
  · simp

/-- Chebyshev for a linear statistic of the votes. -/
theorem LC2_cheb {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1) (a : Fin n → ℝ)
    (β : ℝ) (hβ : 0 < β) :
    voteProb c (fun v => β ≤ |∑ i, a i * (if v i then 1 else 0) - ∑ i, a i * c i|) ≤
      (∑ i, a i ^ 2 * (c i * (1 - c i))) / β ^ 2 := by
  rw [← LC2_second_moment c a, LC2_voteProb_eq, Finset.sum_div]
  apply Finset.sum_le_sum
  intro v _
  have hP := LC2_prod_nonneg c hc v
  have hlin : ∑ i, a i * LC2_y c i (v i) =
      ∑ i, a i * (if v i then 1 else 0) - ∑ i, a i * c i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    simp only [LC2_y]; ring
  rw [hlin]
  split_ifs with hE
  · rw [le_div_iff₀ (by positivity)]
    have h2 : β ^ 2 ≤ (∑ i, a i * (if v i then 1 else 0) - ∑ i, a i * c i) ^ 2 := by
      have := sq_le_sq' (by linarith [abs_nonneg (∑ i, a i * (if v i then (1:ℝ) else 0) -
        ∑ i, a i * c i), neg_abs_le (∑ i, a i * (if v i then (1:ℝ) else 0) - ∑ i, a i * c i)])
        hE
      rw [sq_abs] at this
      linarith [sq_abs (∑ i, a i * (if v i then (1:ℝ) else 0) - ∑ i, a i * c i)]
    nlinarith
  · positivity

theorem LC2_var_le {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin n → ℝ) : ∑ i, a i ^ 2 * (c i * (1 - c i)) ≤ (∑ i, a i ^ 2) / 4 := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have h := hc i
  simp only [Set.mem_Icc] at h
  nlinarith [sq_nonneg (c i - 1 / 2), sq_nonneg (a i)]

/-! ### Deterministic core of Lemma 1 -/

theorem LC2_XD_eq {n : ℕ} (v : Fin n → Bool) :
    XD v = ∑ i, (1 : ℝ) * (if v i then 1 else 0) := by
  unfold XD
  rw [Finset.card_filter]
  push_cast
  simp

theorem LC2_dev_D {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1) (β : ℝ)
    (hβ : 0 < β) :
    voteProb c (fun v => β ≤ |XD v - ∑ i, c i|) ≤ (n / 4) / β ^ 2 := by
  have h := LC2_cheb c hc (fun _ => 1) β hβ
  simp only [one_mul] at h
  have hv := LC2_var_le c hc (fun _ => 1)
  simp only [one_pow, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hv
  calc voteProb c (fun v => β ≤ |XD v - ∑ i, c i|)
      = voteProb c (fun v => β ≤ |∑ i, (if v i then (1 : ℝ) else 0) - ∑ i, c i|) := by
        congr 1; ext v; rw [LC2_XD_eq]; simp
    _ ≤ (∑ i, (c i * (1 - c i))) / β ^ 2 := by simpa using h
    _ ≤ (n / 4) / β ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa using hv


/-! ### An atomless law on `[0,1]` has mass strictly below `a` and strictly above `b > a` -/

theorem LC2_exists_ab (D : Measure ℝ) (hD : D ∈ ContClass) :
    ∃ a b : ℝ, a < b ∧ 0 < D (Set.Iio a) ∧ 0 < D (Set.Ioi b) := by
  obtain ⟨hP, hS, hN⟩ := hD
  -- some `a` with `0 < D (Iio a) < 1`
  have hmid : ∃ a : ℝ, 0 < D (Set.Iio a) ∧ D (Set.Iio a) < 1 := by
    by_contra hcon
    push Not at hcon
    have hdich : ∀ x : ℝ, D (Set.Iio x) = 0 ∨ D (Set.Iio x) = 1 := by
      intro x
      rcases eq_or_lt_of_le (zero_le : (0 : ENNReal) ≤ D (Set.Iio x)) with h | h
      · left; exact h.symm
      · right; exact le_antisymm prob_le_one (hcon x h)
    set T := {x : ℝ | D (Set.Iio x) = 1} with hT
    have hT2 : (2 : ℝ) ∈ T := by
      show D (Set.Iio 2) = 1
      apply le_antisymm prob_le_one
      have h1 : D (Set.Icc 0 1) = 1 := by
        have := measure_add_measure_compl (μ := D) (measurableSet_Icc (a := (0:ℝ)) (b := 1))
        rw [hS, add_zero, measure_univ] at this; exact this
      rw [← h1]
      apply measure_mono
      intro x hx; simp only [Set.mem_Icc] at hx; simp only [Set.mem_Iio]; linarith
    have hTlow : ∀ x ∈ T, (0 : ℝ) ≤ x := by
      intro x hx
      by_contra hneg; push Not at hneg
      have : D (Set.Iio x) = 0 := by
        apply measure_mono_null _ hS
        intro y hy; simp only [Set.mem_Iio] at hy
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and, not_le]; intro h; linarith
      rw [hx] at this; exact one_ne_zero this
    have hTne : T.Nonempty := ⟨2, hT2⟩
    have hTbdd : BddBelow T := ⟨0, hTlow⟩
    set s := sInf T with hs
    -- below `s`, mass `0`
    have hbelow : ∀ x < s, D (Set.Iio x) = 0 := by
      intro x hx
      rcases hdich x with h | h
      · exact h
      · exact absurd (csInf_le hTbdd h) (not_le.mpr hx)
    -- above `s`, mass `1`
    have habove : ∀ x > s, D (Set.Ici x) = 0 := by
      intro x hx
      obtain ⟨y, hyT, hyx⟩ := exists_lt_of_csInf_lt hTne hx
      have hy1 : D (Set.Iio y) = 1 := hyT
      have hcompl := measure_add_measure_compl (μ := D) (measurableSet_Iio (a := y))
      rw [hy1, measure_univ] at hcompl
      have hc0 : D (Set.Iio y)ᶜ = 0 := by
        have : (1 : ENNReal) + D (Set.Iio y)ᶜ = 1 + 0 := by rw [add_zero]; exact hcompl
        exact (ENNReal.add_right_inj ENNReal.one_ne_top).mp this
      apply measure_mono_null _ hc0
      intro z hz; simp only [Set.mem_Ici] at hz
      simp only [Set.mem_compl_iff, Set.mem_Iio, not_lt]; linarith
    have hIio : D (Set.Iio s) = 0 := by
      have : Set.Iio s = ⋃ k : ℕ, Set.Iio (s - 1 / ((k : ℝ) + 1)) := by
        ext x; simp only [Set.mem_Iio, Set.mem_iUnion]
        constructor
        · intro hx
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
          exact ⟨k, by linarith⟩
        · rintro ⟨k, hk⟩
          have : 0 < 1 / ((k : ℝ) + 1) := by positivity
          linarith
      rw [this, measure_iUnion_null_iff]
      intro k
      apply hbelow
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    have hIoi : D (Set.Ioi s) = 0 := by
      have : Set.Ioi s = ⋃ k : ℕ, Set.Ici (s + 1 / ((k : ℝ) + 1)) := by
        ext x; simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ici]
        constructor
        · intro hx
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
          exact ⟨k, by linarith⟩
        · rintro ⟨k, hk⟩
          have : 0 < 1 / ((k : ℝ) + 1) := by positivity
          linarith
      rw [this, measure_iUnion_null_iff]
      intro k
      apply habove
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    have hpt : D {s} = 0 := measure_singleton s
    have huniv : (Set.univ : Set ℝ) = Set.Iio s ∪ {s} ∪ Set.Ioi s := by
      ext x; simp only [Set.mem_univ, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff,
        Set.mem_Ioi, true_iff]
      rcases lt_trichotomy x s with h | h | h
      · left; left; exact h
      · left; right; exact h
      · right; exact h
    have : D Set.univ = 0 := by
      rw [huniv]
      apply measure_union_null (measure_union_null hIio hpt) hIoi
    rw [measure_univ] at this
    exact one_ne_zero this
  obtain ⟨a, ha0, ha1⟩ := hmid
  -- the mass above `a` is positive
  have hIci : 0 < D (Set.Ici a) := by
    have hcompl := measure_add_measure_compl (μ := D) (measurableSet_Iio (a := a))
    rw [measure_univ] at hcompl
    have : (Set.Iio a)ᶜ = Set.Ici a := by ext; simp
    rw [this] at hcompl
    by_contra h0; push Not at h0
    have h0' : D (Set.Ici a) = 0 := le_antisymm h0 zero_le
    rw [h0', add_zero] at hcompl
    rw [hcompl] at ha1; exact lt_irrefl _ ha1
  have hIoi : 0 < D (Set.Ioi a) := by
    have : Set.Ici a = Set.Ioi a ∪ {a} := by
      ext x; simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ioi, Set.mem_singleton_iff]
      constructor
      · intro h; rcases eq_or_lt_of_le h with h' | h'
        · right; exact h'.symm
        · left; exact h'
      · rintro (h | h)
        · exact h.le
        · exact h.symm.le
    rw [this] at hIci
    have hle := measure_union_le (μ := D) (Set.Ioi a) {a}
    rw [measure_singleton, add_zero] at hle
    exact lt_of_lt_of_le hIci hle
  have : Set.Ioi a = ⋃ k : ℕ, Set.Ioi (a + 1 / ((k : ℝ) + 1)) := by
    ext x; simp only [Set.mem_Ioi, Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [this] at hIoi
  by_contra hcon
  push Not at hcon
  have : D (⋃ k : ℕ, Set.Ioi (a + 1 / ((k : ℝ) + 1))) = 0 := by
    rw [measure_iUnion_null_iff]
    intro k
    have h1 : a < a + 1 / ((k : ℝ) + 1) := by
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    exact le_antisymm (hcon a (a + 1 / ((k : ℝ) + 1)) h1 ha0) zero_le
  rw [this] at hIoi
  exact lt_irrefl _ hIoi

/-! ### Concentration of the number of competencies in a set -/

theorem LC2_count_bound (D : Measure ℝ) [IsProbabilityMeasure D] (A : Set ℝ)
    (hA : MeasurableSet A) (n : ℕ) (hn : 1 ≤ n) (hπ : 0 < (D A).toReal) :
    (Measure.pi fun _ : Fin n => D)
        {c | (((Finset.univ.filter fun i => c i ∈ A).card : ℕ) : ℝ) < (D A).toReal * n / 2} ≤
      ENNReal.ofReal (1 / ((D A).toReal ^ 2 * n)) := by
  set π := (D A).toReal with hπdef
  have hπ1 : π ≤ 1 := by
    rw [hπdef]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set dec : ℝ → Bool := fun x => decide (x ∈ A) with hdec
  have hdecm : Measurable dec := by
    apply measurable_to_bool
    have : dec ⁻¹' {true} = A := by ext x; simp [hdec]
    rw [this]; exact hA
  set φ : (Fin n → ℝ) → (Fin n → Bool) := fun c i => dec (c i) with hφ
  set E : Set (Fin n → Bool) := {v | XD v < π * n / 2} with hE
  have hset : {c : Fin n → ℝ | (((Finset.univ.filter fun i => c i ∈ A).card : ℕ) : ℝ) <
      π * n / 2} = φ ⁻¹' E := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hE, XD, hφ, hdec, decide_eq_true_eq]
  rw [hset, ← Measure.map_apply (by fun_prop) MeasurableSet.of_discrete]
  rw [hφ, Measure.pi_map_pi (fun i => hdecm.aemeasurable)]
  set ν : Measure Bool := D.map dec with hν
  have hνt : ν {true} = ENNReal.ofReal (LC2_w (fun _ : Fin n => π) ⟨0, hn⟩ true) := by
    rw [hν, Measure.map_apply hdecm (measurableSet_singleton _)]
    have : dec ⁻¹' {true} = A := by ext x; simp [hdec]
    rw [this, LC2_w, if_pos rfl, hπdef, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hνf : ν {false} = ENNReal.ofReal (LC2_w (fun _ : Fin n => π) ⟨0, hn⟩ false) := by
    rw [hν, Measure.map_apply hdecm (measurableSet_singleton _)]
    have : dec ⁻¹' {false} = Aᶜ := by ext x; simp [hdec]
    rw [this, LC2_w, if_neg (by simp), prob_compl_eq_one_sub hA,
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hνb : ∀ (i : Fin n) (b : Bool), ν {b} = ENNReal.ofReal (LC2_w (fun _ : Fin n => π) i b) := by
    intro i b
    cases b
    · rw [hνf]; rfl
    · rw [hνt]; rfl
  have hEfin : E = ((Finset.univ.filter fun v => v ∈ E : Finset (Fin n → Bool)) : Set _) := by
    ext v; simp
  rw [hEfin, ← sum_measure_singleton]
  have hsum : ∑ v ∈ Finset.univ.filter (fun v => v ∈ E), (Measure.pi fun _ : Fin n => ν) {v} =
      ∑ v ∈ Finset.univ.filter (fun v => v ∈ E),
        ∏ i, ENNReal.ofReal (LC2_w (fun _ : Fin n => π) i (v i)) :=
    Finset.sum_congr rfl (fun v _ => by
      rw [Measure.pi_singleton]
      exact Finset.prod_congr rfl (fun i _ => hνb i (v i)))
  rw [hsum]
  have hnn : ∀ v : Fin n → Bool, ∀ i, 0 ≤ LC2_w (fun _ : Fin n => π) i (v i) := by
    intro v i; unfold LC2_w; split_ifs <;> linarith
  simp_rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hnn _ i)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => Finset.prod_nonneg fun i _ => hnn v i)]
  apply ENNReal.ofReal_le_ofReal
  have hbox : ∀ i : Fin n, (fun _ : Fin n => π) i ∈ Set.Icc (0 : ℝ) 1 :=
    fun _ => ⟨ENNReal.toReal_nonneg, hπ1⟩
  have hvp : ∑ v ∈ Finset.univ.filter (fun v => v ∈ E), ∏ i, LC2_w (fun _ : Fin n => π) i (v i) =
      voteProb (fun _ : Fin n => π) (fun v => v ∈ E) := by
    unfold voteProb LC2_w; rfl
  rw [hvp]
  have hβ : 0 < π * n / 2 := by positivity
  calc voteProb (fun _ : Fin n => π) (fun v => v ∈ E)
      ≤ voteProb (fun _ : Fin n => π) (fun v => π * n / 2 ≤ |XD v - ∑ _i : Fin n, π|) := by
        apply LC2_vp_mono _ hbox
        intro v hv
        simp only [hE, Set.mem_setOf_eq] at hv
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [abs_sub_comm, le_abs]; left; linarith
    _ ≤ (n / 4) / (π * n / 2) ^ 2 := LC2_dev_D _ hbox _ hβ
    _ = 1 / (π ^ 2 * n) := by field_simp; ring

/-! ### Chebyshev for sums of coordinate functions under product weights on graphs -/

section GraphCheb
variable {n : ℕ} (P : Fin n → Fin n → ℝ) (f : Fin n → Fin n → ℝ)

noncomputable def LC2_mean (i : Fin n) : ℝ := ∑ j, P i j * f i j

theorem LC2_g_cross (hP1 : ∀ i, ∑ j, P i j = 1) (i k : Fin n) (hik : i ≠ k) :
    ∑ g : Fin n → Fin n, (∏ l, P l (g l)) *
      ((f i (g i) - LC2_mean P f i) * (f k (g k) - LC2_mean P f k)) = 0 := by
  have hrw : ∀ g : Fin n → Fin n, (∏ l, P l (g l)) *
      ((f i (g i) - LC2_mean P f i) * (f k (g k) - LC2_mean P f k)) =
      ∏ l, (P l (g l) * (if l = i then f i (g l) - LC2_mean P f i else 1) *
        (if l = k then f k (g l) - LC2_mean P f k else 1)) := by
    intro g
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i,
      Finset.prod_ite_eq' Finset.univ k]
    simp only [Finset.mem_univ, if_true]
    ring
  simp_rw [hrw]
  rw [← Fintype.prod_sum (fun l j => P l j * (if l = i then f i j - LC2_mean P f i else 1) *
    (if l = k then f k j - LC2_mean P f k else 1))]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hj : ∀ j, P i j * (if i = i then f i j - LC2_mean P f i else 1) *
      (if i = k then f k j - LC2_mean P f k else 1) = P i j * f i j - P i j * LC2_mean P f i := by
    intro j; simp [hik]; ring
  rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_sub_distrib, ← Finset.sum_mul, hP1,
    one_mul]
  unfold LC2_mean
  ring

theorem LC2_g_diag (hP1 : ∀ i, ∑ j, P i j = 1) (i : Fin n) :
    ∑ g : Fin n → Fin n, (∏ l, P l (g l)) *
      ((f i (g i) - LC2_mean P f i) * (f i (g i) - LC2_mean P f i)) =
      ∑ j, P i j * (f i j - LC2_mean P f i) ^ 2 := by
  have hrw : ∀ g : Fin n → Fin n, (∏ l, P l (g l)) *
      ((f i (g i) - LC2_mean P f i) * (f i (g i) - LC2_mean P f i)) =
      ∏ l, (P l (g l) * (if l = i then (f i (g l) - LC2_mean P f i) ^ 2 else 1)) := by
    intro g
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i]
    simp only [Finset.mem_univ, if_true]
    ring
  simp_rw [hrw]
  rw [← Fintype.prod_sum (fun l j => P l j * (if l = i then (f i j - LC2_mean P f i) ^ 2 else 1))]
  rw [Finset.prod_eq_single i]
  · simp
  · intro l _ hl
    simp [hl, hP1]
  · simp

theorem LC2_g_second (hP1 : ∀ i, ∑ j, P i j = 1) :
    ∑ g : Fin n → Fin n, (∏ l, P l (g l)) * (∑ i, (f i (g i) - LC2_mean P f i)) ^ 2 =
      ∑ i, ∑ j, P i j * (f i j - LC2_mean P f i) ^ 2 := by
  have hexp : ∀ g : Fin n → Fin n, (∏ l, P l (g l)) * (∑ i, (f i (g i) - LC2_mean P f i)) ^ 2 =
      ∑ i, ∑ k, ((∏ l, P l (g l)) *
        ((f i (g i) - LC2_mean P f i) * (f k (g k) - LC2_mean P f k))) := by
    intro g
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single i]
  · exact LC2_g_diag P f hP1 i
  · intro k _ hki
    exact LC2_g_cross P f hP1 i k (Ne.symm hki)
  · simp

theorem LC2_g_cheb (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1) (β : ℝ) (hβ : 0 < β) :
    ∑ g : Fin n → Fin n, (∏ l, P l (g l)) *
      (if β ≤ |∑ i, f i (g i) - ∑ i, LC2_mean P f i| then 1 else 0) ≤
      (∑ i, ∑ j, P i j * (f i j - LC2_mean P f i) ^ 2) / β ^ 2 := by
  rw [← LC2_g_second P f hP1, Finset.sum_div]
  apply Finset.sum_le_sum
  intro g _
  have hW : 0 ≤ ∏ l, P l (g l) := Finset.prod_nonneg fun l _ => hP0 l (g l)
  have hlin : ∑ i, (f i (g i) - LC2_mean P f i) = ∑ i, f i (g i) - ∑ i, LC2_mean P f i :=
    Finset.sum_sub_distrib _ _
  rw [hlin]
  split_ifs with hE
  · rw [mul_one, le_div_iff₀ (by positivity)]
    have h2 : β ^ 2 ≤ (∑ i, f i (g i) - ∑ i, LC2_mean P f i) ^ 2 := by
      have := pow_le_pow_left₀ hβ.le hE 2
      rwa [sq_abs] at this
    nlinarith
  · rw [mul_zero]; positivity

theorem LC2_g_var_le (hP0 : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1)
    (hf : ∀ i j, f i j ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i, ∑ j, P i j * (f i j - LC2_mean P f i) ^ 2 ≤ n := by
  have hm : ∀ i, LC2_mean P f i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    unfold LC2_mean
    constructor
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (hP0 i j) (hf i j).1
    · calc ∑ j, P i j * f i j ≤ ∑ j, P i j := Finset.sum_le_sum fun j _ =>
            mul_le_of_le_one_right (hP0 i j) (hf i j).2
        _ = 1 := hP1 i
  calc ∑ i, ∑ j, P i j * (f i j - LC2_mean P f i) ^ 2 ≤ ∑ i : Fin n, ∑ j, P i j := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        have h1 := hf i j; have h2 := hm i
        simp only [Set.mem_Icc] at h1 h2
        have : (f i j - LC2_mean P f i) ^ 2 ≤ 1 := by nlinarith
        exact mul_le_of_le_one_right (hP0 i j) this
    _ = n := by simp [hP1]

end GraphCheb

/-! ### Upward graphs: roots are direct voters and the competence gain -/

section Upward
variable {n : ℕ} (c : Fin n → ℝ) (g : DelegGraph n)

theorem LC2_iter_mono (hup : ∀ j, g j ≠ j → c j < c (g j)) (k : ℕ) (j : Fin n) :
    c j ≤ c (g^[k] j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine ih.trans ?_
    by_cases h : g (g^[k] j) = g^[k] j
    · rw [h]
    · exact (hup _ h).le

theorem LC2_root_fixed (hup : ∀ j, g j ≠ j → c j < c (g j)) (j : Fin n) :
    g (root g j) = root g j := by
  by_contra h
  have hstep : ∀ m ≤ n, g (g^[m] j) ≠ g^[m] j := by
    intro m hm hfix
    apply h
    have key : ∀ d, g^[d + m] j = g^[m] j := fun d => by
      rw [Function.iterate_add_apply, Function.iterate_fixed hfix]
    have : g^[n] j = g^[m] j := by
      have := key (n - m); rwa [Nat.sub_add_cancel hm] at this
    unfold root; rw [this]; exact hfix
  have hlt : ∀ a d : ℕ, a + d + 1 ≤ n → c (g^[a] j) < c (g^[a + d + 1] j) := by
    intro a d
    induction d with
    | zero =>
      intro had
      rw [show a + 0 + 1 = a + 1 by ring, Function.iterate_succ_apply']
      exact hup _ (hstep a (by omega))
    | succ d ih =>
      intro had
      refine (ih (by omega)).trans ?_
      have e : g^[a + d + 1 + 1] j = g (g^[a + d + 1] j) := Function.iterate_succ_apply' g _ j
      rw [show a + (d + 1) + 1 = a + d + 1 + 1 by ring, e]
      exact hup _ (hstep _ (by omega))
  have hinj : Function.Injective (fun k : Fin (n + 1) => g^[k] j) := by
    intro x y hxy
    simp only at hxy
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with hl | hl
    · have := hlt x (y - x - 1) (by omega)
      rw [show (x : ℕ) + (y - x - 1) + 1 = y by omega, ← hxy] at this
      exact lt_irrefl _ this
    · have := hlt y (x - y - 1) (by omega)
      rw [show (y : ℕ) + (x - y - 1) + 1 = x by omega, hxy] at this
      exact lt_irrefl _ this
  have := Fintype.card_le_of_injective _ hinj
  simp at this

theorem LC2_sum_wc (hfix : ∀ j, g (root g j) = root g j) :
    ∑ i, (weight g i : ℝ) * c i = ∑ j, c (root g j) := by
  rw [← Finset.sum_fiberwise Finset.univ (root g) (fun j => c (root g j))]
  apply Finset.sum_congr rfl
  intro i _
  have hinner : ∑ j ∈ Finset.univ.filter (fun j => root g j = i), c (root g j) =
      ∑ j ∈ Finset.univ.filter (fun j => root g j = i), c i :=
    Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2]
  rw [hinner, Finset.sum_const, nsmul_eq_mul]
  unfold weight
  split_ifs with hgi
  · rfl
  · have : Finset.univ.filter (fun j => root g j = i) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hj
      apply hgi
      rw [← hj]; exact hfix j
    rw [this]; simp

theorem LC2_gain_lb (hup : ∀ j, g j ≠ j → c j < c (g j)) (a b : ℝ) (hab : a < b) :
    (b - a) * ((Finset.univ.filter fun j => c j < a ∧ g j ≠ j ∧ b < c (g j)).card : ℝ) ≤
      ∑ i, (weight g i : ℝ) * c i - ∑ i, c i := by
  have hfix := LC2_root_fixed c g hup
  rw [LC2_sum_wc c g hfix, ← Finset.sum_sub_distrib]
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h0 : c j ≤ c (root g j) := LC2_iter_mono c g hup n j
  split_ifs with hj
  · obtain ⟨hja, hjg, hjb⟩ := hj
    have hroot : g^[n] (g j) = root g j := by
      unfold root
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      exact hfix j
    have h1 : c (g j) ≤ c (root g j) := by
      rw [← hroot]; exact LC2_iter_mono c g hup n (g j)
    linarith
  · linarith

end Upward

/-! ### Instance law machinery (as in Lemma 1) -/

theorem LC2I_choice_nonneg (M : Model) {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1)
    (hq : ∀ x ∈ Set.Icc (0 : ℝ) 1, M.q x ∈ Set.Icc (0 : ℝ) 1)
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M.φ x y) (i j : Fin n) :
    0 ≤ choiceProb M c i j := by
  unfold choiceProb
  have hS : 0 ≤ ∑ k ∈ Finset.univ.filter (· ≠ i), M.φ (c i) (c k) :=
    Finset.sum_nonneg fun k _ => hφ _ (hc i) _ (hc k)
  have hqi := hq _ (hc i)
  simp only [Set.mem_Icc] at hqi
  split_ifs
  · norm_num
  · norm_num
  · linarith
  · exact div_nonneg (mul_nonneg hqi.1 (hφ _ (hc i) _ (hc j))) hS

theorem LC2I_choice_sum (M : Model) {n : ℕ} (c : Fin n → ℝ) (i : Fin n) :
    ∑ j, choiceProb M c i j = 1 := by
  unfold choiceProb
  set S := ∑ k ∈ Finset.univ.filter (· ≠ i), M.φ (c i) (c k) with hS
  by_cases h0 : S = 0
  · simp [h0]
  · simp only [h0, if_false]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl]
    have : ∑ x ∈ Finset.univ.erase i, (if x = i then 1 - M.q (c i)
        else M.q (c i) * M.φ (c i) (c x) / S) =
        ∑ x ∈ Finset.univ.erase i, M.q (c i) * M.φ (c i) (c x) / S := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [if_neg (Finset.ne_of_mem_erase hx)]
    rw [this, ← Finset.sum_div, ← Finset.mul_sum]
    have he : Finset.univ.erase i = Finset.univ.filter (· ≠ i) := by
      ext x; simp
    rw [he, ← hS]
    field_simp
    ring

theorem LC2I_density_sum (M : Model) {n : ℕ} (c : Fin n → ℝ) :
    ∑ g : DelegGraph n, ∏ i, choiceProb M c i (g i) = 1 := by
  rw [← Fintype.prod_sum (fun i j => choiceProb M c i j)]
  exact Finset.prod_eq_one fun i _ => LC2I_choice_sum M c i

theorem LC2I_meas_choice (M : Model) (hqm : Measurable M.q)
    (hφm : Measurable (Function.uncurry M.φ)) {n : ℕ} (i j : Fin n) :
    Measurable fun c : Fin n → ℝ => choiceProb M c i j := by
  have hφk : ∀ k : Fin n, Measurable fun c : Fin n → ℝ => M.φ (c i) (c k) := by
    intro k
    change Measurable (Function.uncurry M.φ ∘ fun c : Fin n → ℝ => (c i, c k))
    exact hφm.comp (by fun_prop)
  have hS : Measurable fun c : Fin n → ℝ => ∑ k ∈ Finset.univ.filter (· ≠ i), M.φ (c i) (c k) :=
    Finset.measurable_sum _ fun k _ => hφk k
  have hqi : Measurable fun c : Fin n → ℝ => M.q (c i) := hqm.comp (measurable_pi_apply i)
  unfold choiceProb
  refine Measurable.ite (measurableSet_eq_fun hS measurable_const) measurable_const ?_
  split_ifs
  · exact measurable_const.sub hqi
  · exact (hqi.mul (hφk j)).div hS

theorem LC2I_box_null (D : Measure ℝ) [IsProbabilityMeasure D] (hD : D (Set.Icc 0 1)ᶜ = 0)
    (n : ℕ) : (Measure.pi fun _ : Fin n => D) {c | ¬ ∀ i, c i ∈ Set.Icc (0 : ℝ) 1} = 0 := by
  have : {c : Fin n → ℝ | ¬ ∀ i, c i ∈ Set.Icc (0 : ℝ) 1} =
      ⋃ i, (Function.eval i) ⁻¹' (Set.Icc 0 1)ᶜ := by
    ext c; simp
  rw [this, measure_iUnion_null_iff]
  intro i
  exact Measure.pi_eval_preimage_null _ hD

theorem LC2I_box_meas (n : ℕ) : MeasurableSet {c : Fin n → ℝ | ¬ ∀ i, c i ∈ Set.Icc (0 : ℝ) 1} := by
  have : {c : Fin n → ℝ | ¬ ∀ i, c i ∈ Set.Icc (0 : ℝ) 1} =
      ⋃ i, (Function.eval i) ⁻¹' (Set.Icc 0 1)ᶜ := by
    ext c; simp
  rw [this]
  exact MeasurableSet.iUnion fun i => (measurable_pi_apply i) measurableSet_Icc.compl

theorem LC2I_law_box (D : Measure ℝ) [IsProbabilityMeasure D] (hD : D (Set.Icc 0 1)ᶜ = 0)
    (M : Model) (n : ℕ) :
    ∀ᵐ ω ∂instanceLaw D M n, ∀ i, ω.1 i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  unfold instanceLaw
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro g _
  have hmeas : MeasurableSet {ω : (Fin n → ℝ) × DelegGraph n | ¬ ∀ i, ω.1 i ∈ Set.Icc (0 : ℝ) 1} :=
    measurable_fst (LC2I_box_meas n)
  rw [Measure.map_apply (by fun_prop) hmeas]
  apply withDensity_absolutelyContinuous
  exact LC2I_box_null D hD n

theorem LC2I_law_prob (D : Measure ℝ) [IsProbabilityMeasure D] (hD : D (Set.Icc 0 1)ᶜ = 0)
    (M : Model) (hq : ∀ x ∈ Set.Icc (0 : ℝ) 1, M.q x ∈ Set.Icc (0 : ℝ) 1)
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M.φ x y)
    (hqm : Measurable M.q) (hφm : Measurable (Function.uncurry M.φ)) (n : ℕ) :
    IsProbabilityMeasure (instanceLaw D M n) := by
  constructor
  unfold instanceLaw
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  have hdens : ∀ g : DelegGraph n, Measurable fun c : Fin n → ℝ =>
      ENNReal.ofReal (∏ i, choiceProb M c i (g i)) := by
    intro g
    exact ENNReal.measurable_ofReal.comp
      (Finset.measurable_prod _ fun i _ => LC2I_meas_choice M hqm hφm i (g i))
  have hterm : ∀ g : DelegGraph n, (((Measure.pi fun _ : Fin n => D).withDensity
      (fun c => ENNReal.ofReal (∏ i, choiceProb M c i (g i)))).map (fun c => (c, g))) Set.univ =
      ∫⁻ c, ENNReal.ofReal (∏ i, choiceProb M c i (g i)) ∂(Measure.pi fun _ : Fin n => D) := by
    intro g
    rw [Measure.map_apply (by fun_prop : Measurable fun c : Fin n → ℝ => (c, g)) MeasurableSet.univ,
      Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [← lintegral_finsetSum _ fun g _ => hdens g]
  have hae : ∀ᵐ c ∂(Measure.pi fun _ : Fin n => D),
      ∑ g : DelegGraph n, ENNReal.ofReal (∏ i, choiceProb M c i (g i)) = 1 := by
    have h0 := LC2I_box_null D hD n
    have : ∀ᵐ c ∂(Measure.pi fun _ : Fin n => D), ∀ i, c i ∈ Set.Icc (0 : ℝ) 1 := by
      rw [ae_iff]; exact h0
    filter_upwards [this] with c hc
    rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => Finset.prod_nonneg fun i _ =>
      LC2I_choice_nonneg M c hc hq hφ i (g i)), LC2I_density_sum, ENNReal.ofReal_one]
  rw [lintegral_congr_ae hae]
  simp


theorem LC2I_meas_lin (n : ℕ) (f : DelegGraph n → (Fin n → ℝ) → ℝ)
    (hf : ∀ g, Measurable (f g)) :
    Measurable fun ω : (Fin n → ℝ) × DelegGraph n => f ω.2 ω.1 :=
  measurable_from_prod_countable_left fun g => hf g


theorem LC2I_kernel (D : Measure ℝ) (M : Model) (hqm : Measurable M.q)
    (hφm : Measurable (Function.uncurry M.φ)) (n : ℕ)
    (S : Set ((Fin n → ℝ) × DelegGraph n)) (hS : MeasurableSet S) :
    instanceLaw D M n S = ∫⁻ c, ∑ g : DelegGraph n, ({c' | (c', g) ∈ S}.indicator
      (fun c' => ENNReal.ofReal (∏ i, choiceProb M c' i (g i))) c) ∂(Measure.pi fun _ : Fin n => D) := by
  have hdens : ∀ g : DelegGraph n, Measurable fun c : Fin n → ℝ =>
      ENNReal.ofReal (∏ i, choiceProb M c i (g i)) := by
    intro g
    exact ENNReal.measurable_ofReal.comp
      (Finset.measurable_prod _ fun i _ => LC2I_meas_choice M hqm hφm i (g i))
  have hpre : ∀ g : DelegGraph n, MeasurableSet {c' : Fin n → ℝ | (c', g) ∈ S} :=
    fun g => (by fun_prop : Measurable fun c : Fin n → ℝ => (c, g)) hS
  rw [lintegral_finsetSum _ fun g _ => (hdens g).indicator (hpre g)]
  unfold instanceLaw
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro g _
  rw [Measure.map_apply (by fun_prop : Measurable fun c : Fin n → ℝ => (c, g)) hS,
    show ((fun c : Fin n → ℝ => (c, g)) ⁻¹' S) = {c' | (c', g) ∈ S} from rfl,
    withDensity_apply _ (hpre g), lintegral_indicator (hpre g)]

/-! ### Upward choice probabilities -/

theorem LC2_up_upward (p : ℝ) {n : ℕ} (c : Fin n → ℝ) (g : DelegGraph n)
    (hW : ∀ j, choiceProb (upward p) c j (g j) ≠ 0) : ∀ j, g j ≠ j → c j < c (g j) := by
  intro j hj
  have h := hW j
  unfold choiceProb at h
  by_cases hS : (∑ k ∈ Finset.univ.filter (· ≠ j), (upward p).φ (c j) (c k)) = 0
  · rw [if_pos hS, if_neg hj] at h; exact absurd rfl h
  · rw [if_neg hS, if_neg hj] at h
    by_contra hc
    simp only [upward, if_neg hc, mul_zero, zero_div] at h
    exact h rfl

theorem LC2_up_mean (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) {n : ℕ} (c : Fin n → ℝ) (j : Fin n)
    (a b : ℝ) (hab : a < b) (hja : c j < a)
    (hNb : 1 ≤ (Finset.univ.filter fun k => b < c k).card) :
    p * ((Finset.univ.filter fun k => b < c k).card : ℝ) / n ≤
      ∑ k, choiceProb (upward p) c j k * (if c j < a ∧ k ≠ j ∧ b < c k then 1 else 0) := by
  set S : ℝ := ∑ k ∈ Finset.univ.filter (· ≠ j), (if c j < c k then (1 : ℝ) else 0) with hSdef
  set Nb : ℕ := (Finset.univ.filter fun k => b < c k).card with hNbdef
  have hNbS : (Nb : ℝ) ≤ S := by
    rw [hSdef, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_filter]
    exact_mod_cast Finset.card_le_card (fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      refine ⟨?_, by linarith⟩
      intro hkj; rw [hkj] at hk; linarith)
  have hSn : S ≤ n := by
    rw [hSdef]
    calc ∑ k ∈ Finset.univ.filter (· ≠ j), (if c j < c k then (1 : ℝ) else 0)
        ≤ ∑ k ∈ Finset.univ.filter (· ≠ j), (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => by split_ifs <;> norm_num
      _ ≤ ∑ k : Fin n, (1 : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => zero_le_one)
      _ = n := by simp
  have hNb1 : (1 : ℝ) ≤ Nb := by exact_mod_cast hNb
  have hSpos : 0 < S := by linarith
  have hterm : ∀ k, choiceProb (upward p) c j k * (if c j < a ∧ k ≠ j ∧ b < c k then 1 else 0) =
      if b < c k then p / S else 0 := by
    intro k
    by_cases hkj : k = j
    · subst hkj
      have : ¬ b < c k := by linarith
      simp [this]
    · by_cases hbk : b < c k
      · have hjk : c j < c k := by linarith
        rw [if_pos ⟨hja, hkj, hbk⟩, if_pos hbk, mul_one]
        unfold choiceProb
        split_ifs with h1
        · exfalso; simp only [upward] at h1; rw [← hSdef] at h1; linarith
        · simp only [upward, if_pos hjk, mul_one]
          rw [hSdef]
      · rw [if_neg (by tauto), if_neg hbk, mul_zero]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, ← hNbdef]
  have hn : (0 : ℝ) < n := lt_of_lt_of_le hSpos hSn
  rw [div_le_iff₀ hn]
  have : (Nb : ℝ) * (p / S) * n = p * Nb * (n / S) := by ring
  rw [this]
  have h1 : 1 ≤ (n : ℝ) / S := by rw [le_div_iff₀ hSpos]; linarith
  have h2 : 0 ≤ p * Nb := by have := hp.1.le; positivity
  nlinarith

/-! ### Graph-level bound for a fixed competence vector -/

theorem LC2_fixed_c (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ)
    (hc : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1) (a b πa πb : ℝ) (hab : a < b) (hπa : 0 < πa)
    (hπb : 0 < πb)
    (hNa : πa * n / 2 ≤ ((Finset.univ.filter fun i => c i ∈ Set.Iio a).card : ℝ))
    (hNb : πb * n / 2 ≤ ((Finset.univ.filter fun i => c i ∈ Set.Ioi b).card : ℝ))
    (α : ℝ) (hα : α ≤ (b - a) * p * πa * πb / 16) :
    ∑ g : DelegGraph n, (if 2 * α * n ≤ ∑ i, (weight g i : ℝ) * c i - ∑ i, c i then (0 : ℝ)
      else ∏ i, choiceProb (upward p) c i (g i)) ≤ 64 / (p ^ 2 * πa ^ 2 * πb ^ 2 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : ∀ x ∈ Set.Icc (0 : ℝ) 1, (upward p).q x ∈ Set.Icc (0 : ℝ) 1 :=
    fun _ _ => ⟨hp.1.le, hp.2.le⟩
  have hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (upward p).φ x y := by
    intro x _ y _; simp only [upward]; split_ifs <;> norm_num
  set P : Fin n → Fin n → ℝ := fun j k => choiceProb (upward p) c j k with hP
  have hP0 : ∀ j k, 0 ≤ P j k := fun j k => LC2I_choice_nonneg _ c hc hq hφ j k
  have hP1 : ∀ j, ∑ k, P j k = 1 := fun j => LC2I_choice_sum _ c j
  set f : Fin n → Fin n → ℝ := fun j k => if c j < a ∧ k ≠ j ∧ b < c k then 1 else 0 with hf
  have hf01 : ∀ j k, f j k ∈ Set.Icc (0 : ℝ) 1 := by
    intro j k; simp only [hf]; split_ifs <;> norm_num
  set θ : ℝ := p * πa * πb * n / 8 with hθ
  have hθpos : 0 < θ := by have := hp.1; positivity
  -- the total mean is at least `2θ`
  have hNb1 : 1 ≤ (Finset.univ.filter fun k => b < c k).card := by
    have : (0 : ℝ) < ((Finset.univ.filter fun i => c i ∈ Set.Ioi b).card : ℝ) := by
      have : 0 < πb * n / 2 := by positivity
      linarith
    have h' : 0 < (Finset.univ.filter fun i => c i ∈ Set.Ioi b).card := by exact_mod_cast this
    simpa [Set.mem_Ioi] using h'
  have hmean : 2 * θ ≤ ∑ j, LC2_mean P f j := by
    have hj : ∀ j, (if c j < a then p * ((Finset.univ.filter fun k => b < c k).card : ℝ) / n
        else 0) ≤ LC2_mean P f j := by
      intro j
      unfold LC2_mean
      split_ifs with hja
      · exact LC2_up_mean p hp c j a b hab hja hNb1
      · exact Finset.sum_nonneg fun k _ => mul_nonneg (hP0 j k) (hf01 j k).1
    refine le_trans ?_ (Finset.sum_le_sum fun j _ => hj j)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hNa' : πa * n / 2 ≤ ((Finset.univ.filter fun j => c j < a).card : ℝ) := by
      simpa [Set.mem_Iio] using hNa
    have hNb' : πb * n / 2 ≤ ((Finset.univ.filter fun k => b < c k).card : ℝ) := by
      simpa [Set.mem_Ioi] using hNb
    rw [hθ]
    have hp0 := hp.1
    have e : ((Finset.univ.filter fun j => c j < a).card : ℝ) *
        (p * ((Finset.univ.filter fun k => b < c k).card : ℝ) / n) =
        p * ((Finset.univ.filter fun j => c j < a).card : ℝ) *
          ((Finset.univ.filter fun k => b < c k).card : ℝ) / n := by ring
    rw [e, le_div_iff₀ hn']
    have h1 : 0 ≤ πa * n / 2 := by positivity
    have h2 : 0 ≤ πb * n / 2 := by positivity
    have := mul_le_mul hNa' hNb' h2 (by positivity)
    nlinarith
  -- pointwise comparison of the bad event with a deviation event
  have hpt : ∀ g : DelegGraph n, (if 2 * α * n ≤ ∑ i, (weight g i : ℝ) * c i - ∑ i, c i
      then (0 : ℝ) else ∏ i, choiceProb (upward p) c i (g i)) ≤
      (∏ l, P l (g l)) * (if θ ≤ |∑ i, f i (g i) - ∑ i, LC2_mean P f i| then 1 else 0) := by
    intro g
    have hW : 0 ≤ ∏ l, P l (g l) := Finset.prod_nonneg fun l _ => hP0 l (g l)
    by_cases hB : 2 * α * n ≤ ∑ i, (weight g i : ℝ) * c i - ∑ i, c i
    · rw [if_pos hB]; split_ifs <;> positivity
    by_cases hdev : θ ≤ |∑ i, f i (g i) - ∑ i, LC2_mean P f i|
    · rw [if_neg hB, if_pos hdev, mul_one]
    rw [if_neg hB, if_neg hdev]
    · rw [mul_zero]
      by_contra hne
      push Not at hne
      have hne' : ∏ i, choiceProb (upward p) c i (g i) ≠ 0 := hne.ne'
      rw [Finset.prod_ne_zero_iff] at hne'
      have hup := LC2_up_upward p c g (fun j => hne' j (Finset.mem_univ j))
      have hlb := LC2_gain_lb c g hup a b hab
      have hY : ∑ i, f i (g i) =
          ((Finset.univ.filter fun j => c j < a ∧ g j ≠ j ∧ b < c (g j)).card : ℝ) := by
        rw [Finset.natCast_card_filter]
      have hdev' := (abs_lt.mp (not_le.mp hdev)).1
      rw [hY] at hdev'
      have hYθ : θ ≤ ((Finset.univ.filter fun j => c j < a ∧ g j ≠ j ∧ b < c (g j)).card : ℝ) := by
        linarith
      have hba : 0 ≤ b - a := by linarith
      have h1 := mul_le_mul_of_nonneg_left hYθ hba
      have h2 : 2 * α * n ≤ (b - a) * θ := by
        rw [hθ]
        have : 2 * α * n ≤ 2 * ((b - a) * p * πa * πb / 16) * n :=
          mul_le_mul_of_nonneg_right (by linarith) hn'.le
        linarith
      exact hB (by linarith)
  calc ∑ g : DelegGraph n, (if 2 * α * n ≤ ∑ i, (weight g i : ℝ) * c i - ∑ i, c i then (0 : ℝ)
        else ∏ i, choiceProb (upward p) c i (g i))
      ≤ ∑ g : DelegGraph n, (∏ l, P l (g l)) *
          (if θ ≤ |∑ i, f i (g i) - ∑ i, LC2_mean P f i| then 1 else 0) :=
        Finset.sum_le_sum fun g _ => hpt g
    _ ≤ (∑ i, ∑ j, P i j * (f i j - LC2_mean P f i) ^ 2) / θ ^ 2 :=
        LC2_g_cheb P f hP0 hP1 θ hθpos
    _ ≤ n / θ ^ 2 := div_le_div_of_nonneg_right (LC2_g_var_le P f hP0 hP1 hf01) (by positivity)
    _ = 64 / (p ^ 2 * πa ^ 2 * πb ^ 2 * n) := by
        rw [hθ]; have := hp.1; field_simp; ring

/-! ### Assembly -/

theorem LC2_meas_count (n : ℕ) (A : Set ℝ) (hA : MeasurableSet A) (r : ℝ) :
    MeasurableSet {c : Fin n → ℝ | (((Finset.univ.filter fun i => c i ∈ A).card : ℕ) : ℝ) < r} := by
  have : (fun c : Fin n → ℝ => (((Finset.univ.filter fun i => c i ∈ A).card : ℕ) : ℝ)) =
      fun c => ∑ i, if c i ∈ A then (1 : ℝ) else 0 := by
    ext c; rw [Finset.natCast_card_filter]
  apply measurableSet_lt _ measurable_const
  rw [this]
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurable_pi_apply i hA) measurable_const measurable_const

theorem solution (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (D : Measure ℝ) (hD : D ∈ ContClass) :
    ∃ α ∈ Set.Ioo (0 : ℝ) 1, Tendsto (fun n => (instanceLaw D (upward p) n).real
      {ω | 2 * α * n ≤ ∑ i, (weight ω.2 i : ℝ) * ω.1 i - ∑ i, ω.1 i}) atTop (𝓝 1) := by
  obtain ⟨a, b, hab, ha, hb⟩ := LC2_exists_ab D hD
  obtain ⟨hP, hS, -⟩ := hD
  have hq : ∀ x ∈ Set.Icc (0 : ℝ) 1, (upward p).q x ∈ Set.Icc (0 : ℝ) 1 :=
    fun _ _ => ⟨hp.1.le, hp.2.le⟩
  have hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (upward p).φ x y := by
    intro x _ y _; simp only [upward]; split_ifs <;> norm_num
  have hqm : Measurable (upward p).q := measurable_const
  have hφm : Measurable (Function.uncurry (upward p).φ) := by
    simp only [upward]
    change Measurable fun z : ℝ × ℝ => if z.1 < z.2 then (1 : ℝ) else 0
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      measurable_const measurable_const
  set πa : ℝ := (D (Set.Iio a)).toReal with hπa
  set πb : ℝ := (D (Set.Ioi b)).toReal with hπb
  have hπa0 : 0 < πa := ENNReal.toReal_pos ha.ne' (measure_ne_top _ _)
  have hπb0 : 0 < πb := ENNReal.toReal_pos hb.ne' (measure_ne_top _ _)
  set α0 : ℝ := (b - a) * p * πa * πb / 16 with hα0
  have hα00 : 0 < α0 := by
    have := hp.1; have : 0 < b - a := by linarith
    positivity
  set α : ℝ := min α0 (1 / 2) with hαdef
  have hα0' : 0 < α := lt_min hα00 (by norm_num)
  have hα1 : α < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hαle : α ≤ α0 := min_le_left _ _
  refine ⟨α, ⟨hα0', hα1⟩, ?_⟩
  set K : ℝ := 64 / (p ^ 2 * πa ^ 2 * πb ^ 2) + 1 / πa ^ 2 + 1 / πb ^ 2 with hK
  -- the main estimate
  have hmain : ∀ n : ℕ, 1 ≤ n → 1 - K / n ≤ (instanceLaw D (upward p) n).real
      {ω | 2 * α * n ≤ ∑ i, (weight ω.2 i : ℝ) * ω.1 i - ∑ i, ω.1 i} := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hprob := LC2I_law_prob D hS (upward p) hq hφ hqm hφm n
    set B : Set ((Fin n → ℝ) × DelegGraph n) :=
      {ω | 2 * α * n ≤ ∑ i, (weight ω.2 i : ℝ) * ω.1 i - ∑ i, ω.1 i} with hBdef
    have hBm : MeasurableSet B := by
      apply measurableSet_le measurable_const
      exact LC2I_meas_lin n (fun g c => ∑ i, (weight g i : ℝ) * c i - ∑ i, c i)
        (fun g => by fun_prop)
    set badA : Set (Fin n → ℝ) :=
      {c | (((Finset.univ.filter fun i => c i ∈ Set.Iio a).card : ℕ) : ℝ) < πa * n / 2}
    set badB : Set (Fin n → ℝ) :=
      {c | (((Finset.univ.filter fun i => c i ∈ Set.Ioi b).card : ℕ) : ℝ) < πb * n / 2}
    have hbadA := LC2_count_bound D (Set.Iio a) measurableSet_Iio n hn hπa0
    have hbadB := LC2_count_bound D (Set.Ioi b) measurableSet_Ioi n hn hπb0
    have hbadAm : MeasurableSet badA := LC2_meas_count n _ measurableSet_Iio _
    have hbadBm : MeasurableSet badB := LC2_meas_count n _ measurableSet_Ioi _
    have hbox : ∀ᵐ c ∂(Measure.pi fun _ : Fin n => D), ∀ i, c i ∈ Set.Icc (0 : ℝ) 1 := by
      rw [ae_iff]; exact LC2I_box_null D hS n
    set ε : ℝ := 64 / (p ^ 2 * πa ^ 2 * πb ^ 2 * n) with hε
    have hε0 : 0 ≤ ε := by positivity
    have hpt : ∀ᵐ c ∂(Measure.pi fun _ : Fin n => D),
        ∑ g : DelegGraph n, ({c' | (c', g) ∈ Bᶜ}.indicator
          (fun c' => ENNReal.ofReal (∏ i, choiceProb (upward p) c' i (g i))) c) ≤
        ENNReal.ofReal ε + (badA ∪ badB).indicator 1 c := by
      filter_upwards [hbox] with c hc
      have hnn : ∀ g : DelegGraph n, 0 ≤ ∏ i, choiceProb (upward p) c i (g i) :=
        fun g => Finset.prod_nonneg fun i _ => LC2I_choice_nonneg _ c hc hq hφ i (g i)
      by_cases hbad : c ∈ badA ∪ badB
      · rw [Set.indicator_of_mem hbad, Pi.one_apply]
        calc ∑ g : DelegGraph n, ({c' | (c', g) ∈ Bᶜ}.indicator
              (fun c' => ENNReal.ofReal (∏ i, choiceProb (upward p) c' i (g i))) c)
            ≤ ∑ g : DelegGraph n, ENNReal.ofReal (∏ i, choiceProb (upward p) c i (g i)) :=
              Finset.sum_le_sum fun g _ => Set.indicator_le_self _ _ _
          _ = 1 := by
              rw [← ENNReal.ofReal_sum_of_nonneg (fun g _ => hnn g), LC2I_density_sum,
                ENNReal.ofReal_one]
          _ ≤ ENNReal.ofReal ε + 1 := le_add_self
      · rw [Set.indicator_of_notMem hbad, add_zero]
        simp only [Set.mem_union, not_or] at hbad
        obtain ⟨hgA, hgB⟩ := hbad
        simp only [badA, badB, Set.mem_setOf_eq, not_lt] at hgA hgB
        have hind : ∀ g : DelegGraph n, {c' | (c', g) ∈ Bᶜ}.indicator
            (fun c' => ENNReal.ofReal (∏ i, choiceProb (upward p) c' i (g i))) c =
            ENNReal.ofReal (if 2 * α * n ≤ ∑ i, (weight g i : ℝ) * c i - ∑ i, c i then 0
              else ∏ i, choiceProb (upward p) c i (g i)) := by
          intro g
          by_cases hBg : 2 * α * n ≤ ∑ i, (weight g i : ℝ) * c i - ∑ i, c i
          · rw [if_pos hBg, ENNReal.ofReal_zero, Set.indicator_of_notMem]
            simp only [Set.mem_setOf_eq, Set.mem_compl_iff, hBdef, not_not]
            exact hBg
          · rw [if_neg hBg, Set.indicator_of_mem]
            simp only [Set.mem_setOf_eq, Set.mem_compl_iff, hBdef]
            exact hBg
        rw [Finset.sum_congr rfl (fun g _ => hind g), ← ENNReal.ofReal_sum_of_nonneg
          (fun g _ => by split_ifs; exact le_refl 0; exact hnn g)]
        apply ENNReal.ofReal_le_ofReal
        exact LC2_fixed_c p hp hn c hc a b πa πb hab hπa0 hπb0 hgA hgB α hαle
    have hcompl : instanceLaw D (upward p) n Bᶜ ≤ ENNReal.ofReal (K / n) := by
      rw [LC2I_kernel D (upward p) hqm hφm n Bᶜ hBm.compl]
      calc ∫⁻ c, ∑ g : DelegGraph n, ({c' | (c', g) ∈ Bᶜ}.indicator
            (fun c' => ENNReal.ofReal (∏ i, choiceProb (upward p) c' i (g i))) c)
            ∂(Measure.pi fun _ : Fin n => D)
          ≤ ∫⁻ c, (ENNReal.ofReal ε + (badA ∪ badB).indicator 1 c)
              ∂(Measure.pi fun _ : Fin n => D) := lintegral_mono_ae hpt
        _ = ENNReal.ofReal ε + (Measure.pi fun _ : Fin n => D) (badA ∪ badB) := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
              lintegral_indicator_one (hbadAm.union hbadBm)]
        _ ≤ ENNReal.ofReal ε + ((Measure.pi fun _ : Fin n => D) badA +
              (Measure.pi fun _ : Fin n => D) badB) := by
            gcongr; exact measure_union_le _ _
        _ ≤ ENNReal.ofReal ε + (ENNReal.ofReal (1 / (πa ^ 2 * n)) +
              ENNReal.ofReal (1 / (πb ^ 2 * n))) := by
            gcongr
            · exact hbadA
            · exact hbadB
        _ = ENNReal.ofReal (K / n) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add hε0 (by positivity)]
            congr 1
            rw [hε, hK]
            field_simp
            ring
    have hreal : (instanceLaw D (upward p) n).real Bᶜ ≤ K / n := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hcompl
    rw [probReal_compl_eq_one_sub hBm] at hreal
    linarith
  -- squeeze
  have hlow : Tendsto (fun n : ℕ => 1 - K / n) atTop (𝓝 1) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat K).const_sub 1
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact hmain n hn
  · filter_upwards with n
    have := LC2I_law_prob D hS (upward p) hq hφ hqm hφm n
    exact measureReal_le_one
