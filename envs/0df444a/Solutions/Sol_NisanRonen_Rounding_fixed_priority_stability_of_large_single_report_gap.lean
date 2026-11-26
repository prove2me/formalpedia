-- Prove2me | solution 1 for NisanRonen.Rounding.fixed_priority_stability_of_large_single_report_gap
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T08:02:13.761943+00:00
-- url     : https://prove2.me/submissions/7d478496-d154-40bf-aafa-e23c6c294e9a

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion

open NisanRonen.Rounding
open scoped BigOperators

set_option autoImplicit false

private theorem choose_bounded_sum {α : Type} [DecidableEq α] (s : Finset α)
    (L U : α → ℤ) (h : ∀ j ∈ s, L j ≤ U j) (m : ℤ)
    (hL : (∑ j ∈ s, L j) ≤ m) (hU : m ≤ ∑ j ∈ s, U j) :
    ∃ D : α → ℤ, (∀ j ∈ s, L j ≤ D j ∧ D j ≤ U j) ∧ (∑ j ∈ s, D j) = m := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty =>
    refine ⟨L, by simp, ?_⟩
    simp at hL hU
    simpa using le_antisymm hL hU
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha] at hL hU
    let q := max (L a) (m - ∑ j ∈ s, U j)
    have hqa : L a ≤ q := le_max_left _ _
    have hqu : q ≤ U a := max_le (h a (Finset.mem_insert_self _ _)) (by omega)
    have hremL : (∑ j ∈ s, L j) ≤ m - q := by
      have hsum := Finset.sum_le_sum (f := L) (g := U)
        (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have hq : q ≤ m - ∑ j ∈ s, L j := max_le (by omega) (by omega)
      omega
    have hremU : m - q ≤ ∑ j ∈ s, U j := by
      have hq : m - ∑ j ∈ s, U j ≤ q := le_max_right _ _
      omega
    obtain ⟨D, hd, hds⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      (m-q) hremL hremU
    let D' := Function.update D a q
    refine ⟨D', ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · simpa [D'] using And.intro hqa hqu
      · have hjne : j ≠ a := fun e => ha (e ▸ hj)
        simpa [D', Function.update_of_ne hjne] using hd j hj
    · have he : (∑ j ∈ s, D' j) = ∑ j ∈ s, D j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjne : j ≠ a := fun e => ha (e ▸ hj)
        simp [D', Function.update_of_ne hjne]
      rw [Finset.sum_insert ha, he, hds]
      simp [D']

private theorem time_ge {δ u : ℝ} (hδ : 0 < δ) : u ≤ roundUp δ u := by
  have hm := mul_le_mul_of_nonneg_left (Int.le_ceil (u / δ)) hδ.le
  rw [mul_comm δ (u / δ), div_mul_cancel₀ _ hδ.ne'] at hm
  exact hm

private theorem time_mono {δ : ℝ} (hδ : 0 < δ) {u v : ℝ} (h : u ≤ v) :
    roundUp δ u ≤ roundUp δ v := by
  unfold roundUp
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast Int.ceil_mono (div_le_div_of_nonneg_right h hδ.le)) hδ.le

private theorem time_grid {δ : ℝ} (hδ : 0 < δ) (z : ℤ) :
    roundUp δ (δ * (z : ℝ)) = δ * (z : ℝ) := by
  simp [roundUp, mul_div_cancel_left₀ _ hδ.ne']

private theorem cap_row {k : ℕ} {a b δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Fin k)) (row : Fin k → ℝ) (hrow : ∀ j, a ≤ row j ∧ row j ≤ b)
    (m : ℤ) (hfloor : (∑ _j ∈ S, roundUp δ a) ≤ δ * (m : ℝ)) :
    ∃ newRow : Fin k → ℝ, (∀ j, a ≤ newRow j ∧ newRow j ≤ b) ∧
      (∀ j ∉ S, newRow j = row j) ∧
      (∀ j, roundUp δ (newRow j) ≤ roundUp δ (row j)) ∧
      (∑ j ∈ S, roundUp δ (newRow j)) = min (∑ j ∈ S, roundUp δ (row j)) (δ * (m : ℝ)) := by
  classical
  let L : ℤ := ⌈a / δ⌉
  let U (j : Fin k) : ℤ := ⌈row j / δ⌉
  let z := min (∑ j ∈ S, U j) m
  have hLU (j : Fin k) : L ≤ U j :=
    Int.ceil_mono (div_le_div_of_nonneg_right (hrow j).1 hδ.le)
  have hLf : (∑ _j ∈ S, L) ≤ m := by
    have hm : δ * (↑(∑ _j ∈ S, L) : ℝ) ≤ δ * (m : ℝ) := by
      simpa only [Int.cast_sum, Finset.mul_sum, L, roundUp] using hfloor
    exact_mod_cast (le_of_mul_le_mul_left hm hδ)
  obtain ⟨D, hd, hsum⟩ := choose_bounded_sum S (fun _ => L) U
    (fun j _ => hLU j) z
    (le_min (Finset.sum_le_sum (fun j _ => hLU j)) hLf) (min_le_left _ _)
  let newRow (j : Fin k) := if j ∈ S then min (row j) (δ * (D j : ℝ)) else row j
  have hround (j : Fin k) (hj : j ∈ S) : roundUp δ (newRow j) = δ * (D j : ℝ) := by
    have hD : δ * (D j : ℝ) ≤ roundUp δ (row j) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (hd j hj).2) hδ.le
    change roundUp δ (if j ∈ S then min (row j) (δ * (D j : ℝ)) else row j) = _
    rw [if_pos hj]
    by_cases hh : row j ≤ δ * (D j : ℝ)
    · rw [min_eq_left hh]
      exact le_antisymm (by simpa [time_grid hδ] using time_mono hδ hh) hD
    · rw [min_eq_right (le_of_not_ge hh), time_grid hδ]
  refine ⟨newRow, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ S
    · have hmin : a ≤ δ * (D j : ℝ) := (time_ge hδ).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast (hd j hj).1) hδ.le)
      exact ⟨by simpa only [newRow, if_pos hj] using le_min (hrow j).1 hmin,
        by simpa only [newRow, if_pos hj] using (min_le_left _ _).trans (hrow j).2⟩
    · simpa [newRow, hj] using hrow j
  · intro j hj; simp [newRow, hj]
  · intro j
    apply time_mono hδ
    by_cases hj : j ∈ S <;> simp [newRow, hj]
  · have he : (∑ j ∈ S, roundUp δ (newRow j)) = δ * (z : ℝ) := by
      calc
        (∑ j ∈ S, roundUp δ (newRow j)) = ∑ j ∈ S, δ * (D j : ℝ) :=
          Finset.sum_congr rfl hround
        _ = δ * (z : ℝ) := by rw [← Finset.mul_sum, ← Int.cast_sum, hsum]
    rw [he]
    have hU : (∑ j ∈ S, roundUp δ (row j)) = δ * (↑(∑ j ∈ S, U j) : ℝ) := by
      simp only [Int.cast_sum, Finset.mul_sum, U, roundUp]
    rw [hU]
    rcases le_total (∑ j ∈ S, U j) m with h | h
    · have hc : δ * (↑(∑ j ∈ S, U j) : ℝ) ≤ δ * (m : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast h) hδ.le
      simp only [z, min_eq_left h, min_eq_left hc]
    · have hc : δ * (m : ℝ) ≤ δ * (↑(∑ j ∈ S, U j) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast h) hδ.le
      simp only [z, min_eq_right h, min_eq_right hc]

private noncomputable def rowLoad {n k : ℕ} (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) (l : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => x j = l), roundUp δ (d l j)

private noncomputable def span {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) : ℝ :=
  roundedMakespan δ x (corrStar x d)

private theorem span_eq {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) :
    span δ x d = Finset.univ.sup' Finset.univ_nonempty (rowLoad δ x d) := by
  unfold span roundedMakespan makespan
  congr 1
  funext l
  unfold rowLoad load
  apply Finset.sum_congr rfl
  intro j hj
  simp [corrStar, (Finset.mem_filter.1 hj).2]

private theorem row_le_span {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) (i : Fin n) : rowLoad δ x d i ≤ span δ x d := by
  rw [span_eq]
  exact Finset.le_sup' _ (Finset.mem_univ i)

private theorem span_grid {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (d : Fin n → Fin k → ℝ) : ∃ m : ℤ, span δ x d = δ * (m : ℝ) := by
  rw [span_eq]
  obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (rowLoad δ x d)
  refine ⟨∑ j ∈ Finset.univ.filter (fun j => x j = i), ⌈d i j / δ⌉, h.trans ?_⟩
  simp [rowLoad, roundUp, Finset.mul_sum]

private theorem span_mono {n k : ℕ} [NeZero n] (δ : ℝ) (x : Fin k → Fin n)
    (u v : Fin n → Fin k → ℝ) (h : ∀ l j, roundUp δ (u l j) ≤ roundUp δ (v l j)) :
    span δ x u ≤ span δ x v := by
  rw [span_eq]
  apply Finset.sup'_le
  intro l _
  exact (Finset.sum_le_sum (fun j _ => h l j)).trans (row_le_span δ x v l)

private theorem truth_mono {n k : ℕ} (δ : ℝ) (i : Fin n) (t : Fin k → ℝ)
    (u v : Fin n → Fin k → ℝ) (h : ∀ l j, roundUp δ (u l j) ≤ roundUp δ (v l j)) :
    ∀ l j, roundUp δ (Function.update u i t l j) ≤ roundUp δ (Function.update v i t l j) := by
  intro l j
  by_cases hl : l = i
  · subst l; simp
  · simpa [hl] using h l j

private theorem ceil_step {a b δ p : ℝ} (hδ : 0 < δ) (hp : a ≤ p ∧ p ≤ b)
    (h : ⌈a / δ⌉ < ⌈p / δ⌉) :
    ∃ r : ℝ, a ≤ r ∧ r ≤ b ∧ ⌈r / δ⌉ = ⌈p / δ⌉ - 1 := by
  let q : ℤ := ⌈p / δ⌉ - 1
  refine ⟨δ * (q : ℝ), ?_, ?_, ?_⟩
  · apply (time_ge (u := a) hδ).trans
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Int.le_sub_one_of_lt h) hδ.le
  · have hh := mul_lt_mul_of_pos_left (Int.ceil_lt_add_one (p / δ)) hδ
    rw [mul_add, mul_one, mul_comm δ (p / δ), div_mul_cancel₀ _ hδ.ne'] at hh
    have hlt : δ * (q : ℝ) < p := by dsimp [q]; push_cast; linarith
    exact hlt.le.trans hp.2
  · simp [q, mul_div_cancel_left₀ _ hδ.ne']

private theorem cap_base_bound {n k : ℕ} [NeZero n] {a b δ C : ℝ} (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (i : Fin n) (t r : Fin k → ℝ) (hop : DeclarationOptimal f δ a b i t r)
    (base : Fin n → Fin k → ℝ) (hbase : base i = r)
    (hmin : ∀ l ≠ i, ∀ j, base l j = a) :
    ∀ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) → v i = r →
      (∃ y : Fin k → Fin n, span δ y (Function.update v i t) ≤ C) →
      span δ (allocOf f δ v) v ≤ max (span δ (allocOf f δ base) base) (C + δ) := by
  classical
  let U := span δ (allocOf f δ base) base
  let height (v : Fin n → Fin k → ℝ) :=
    ∑ l : Fin n, ∑ j : Fin k, (⌈v l j / δ⌉ - ⌈base l j / δ⌉).toNat
  have main (N : ℕ) :
      ∀ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) → v i = r →
        (∃ y : Fin k → Fin n, span δ y (Function.update v i t) ≤ C) →
        height v = N → span δ (allocOf f δ v) v ≤ max U (C + δ) := by
    induction N using Nat.strongRecOn with
    | ind N ih =>
      intro v hv hvi hcmp hN
      have hg (l j) : ⌈base l j / δ⌉ ≤ ⌈v l j / δ⌉ := by
        by_cases hl : l = i
        · subst l; rw [hvi, hbase]
        · rw [hmin l hl]
          exact Int.ceil_mono (div_le_div_of_nonneg_right (hv l j).1 hδ.le)
      by_cases hstage : ∃ l : Fin n, ∃ j : Fin k, ⌈base l j / δ⌉ < ⌈v l j / δ⌉
      · obtain ⟨l, j, hlj⟩ := hstage
        have hli : l ≠ i := by intro h; subst l; simp [hbase, hvi] at hlj
        obtain ⟨r', hra, hrb, hr'⟩ := ceil_step hδ (hv l j)
          (by simpa [hmin l hli] using hlj)
        let w := Function.update v l (Function.update (v l) j r')
        have hw (l' : Fin n) (u : Fin k) : a ≤ w l' u ∧ w l' u ≤ b := by
          by_cases h : l' = l
          · subst l'
            by_cases hj : u = j
            · subst u; simp [w, hra, hrb]
            · simpa [w, hj] using hv l u
          · simpa [w, h] using hv l' u
        have hwi : w i = r := by simpa [w, Ne.symm hli] using hvi
        have hchanged (l' : Fin n) (u : Fin k) :
            ⌈w l' u / δ⌉ = ⌈v l' u / δ⌉ - (if l' = l ∧ u = j then 1 else 0) := by
          by_cases hh : l' = l
          · subst l'
            by_cases hj : u = j
            · subst u; simpa [w] using hr'
            · simp [w, hj]
          · simp [w, hh]
        have hdec : height w < N := by
          rw [← hN]
          unfold height
          apply Finset.sum_lt_sum
          · intro l' _
            apply Finset.sum_le_sum
            intro u _
            rw [hchanged]
            split <;> omega
          · refine ⟨l, Finset.mem_univ _, ?_⟩
            apply Finset.sum_lt_sum
            · intro u _
              rw [hchanged]
              split <;> omega
            · refine ⟨j, Finset.mem_univ _, ?_⟩
              rw [hchanged]
              simp only [true_and, if_true]
              omega
        have hwv (l' : Fin n) (u : Fin k) : roundUp δ (w l' u) ≤ roundUp δ (v l' u) := by
          unfold roundUp
          refine mul_le_mul_of_nonneg_left ?_ hδ.le
          rw [hchanged]
          split <;> (apply Int.cast_le.mpr; omega)
        obtain ⟨y, hy⟩ := hcmp
        have hwy : span δ y (Function.update w i t) ≤ C :=
          (span_mono δ y _ _ (truth_mono δ i t w v hwv)).trans hy
        let z := allocOf f δ w
        have hoptW : span δ z w ≤ max U (C + δ) := ih (height w) hdec w hw hwi ⟨y, hwy⟩ rfl
        have htrueW : span δ z (Function.update w i t) ≤ C := (hop w hw hwi y).trans hwy
        refine ((hf k v hv).2 z).trans ?_
        change span δ z v ≤ max U (C + δ)
        rw [span_eq]
        apply Finset.sup'_le
        intro l' _
        by_cases hI : l' = i
        · subst l'
          rw [show rowLoad δ z v i = rowLoad δ z w i by simp [rowLoad, hvi, hwi]]
          exact (row_le_span δ z w i).trans hoptW
        · have hrow : rowLoad δ z w l' ≤ C := by
            have htop := (row_le_span δ z (Function.update w i t) l').trans htrueW
            simpa [rowLoad, hI] using htop
          have hgain : rowLoad δ z v l' - rowLoad δ z w l' ≤ δ := by
            unfold rowLoad
            rw [← Finset.sum_sub_distrib]
            have hterm (u : Fin k) :
                roundUp δ (v l' u) - roundUp δ (w l' u) ≤ if u = j then δ else 0 := by
              unfold roundUp
              rw [hchanged]
              by_cases hu : u = j
              · by_cases hl' : l' = l <;> simp [hu, hl', mul_sub, hδ.le]
              · simp [hu]
            refine (Finset.sum_le_sum (fun u _ => hterm u)).trans ?_
            rw [Finset.sum_ite_eq']
            split <;> simp [hδ.le]
          exact (show rowLoad δ z v l' ≤ C + δ by linarith).trans (le_max_right _ _)
      · push Not at hstage
        have he (l j) : roundUp δ (v l j) = roundUp δ (base l j) := by
          have hi := le_antisymm (hstage l j) (hg l j)
          simp [roundUp, hi]
        have h := span_mono δ (allocOf f δ base) v base (fun l j => (he l j).le)
        exact (((hf k v hv).2 _).trans h).trans (le_max_left _ _)
  intro v hv hvi hcmp
  exact main (height v) v hv hvi hcmp rfl

theorem solution {n k : ℕ} [NeZero n] {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (rank : (Fin k → Fin n) → ℕ) (hinj : Function.Injective rank)
    (hpriority : ∀ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin k → Fin n, roundedMakespan δ y (corrStar y v) =
        roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        rank (allocOf f δ v) ≤ rank y)
    (t d : Fin n → Fin k → ℝ) (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b)
    (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (i : Fin n) (hop : DeclarationOptimal f δ a b i (t i) (d i)) (m : ℤ)
    (y : Fin k → Fin n) (hy : roundedMakespan δ y (corrStar y t) ≤ δ * (m : ℝ)) :
    let s := Function.update t i (d i)
    let x := allocOf f δ s
    δ * (m : ℝ) + δ < roundedMakespan δ x (corrStar x s) →
    ∀ v : Fin n → Fin k → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) → v i = d i →
      (∃ z : Fin k → Fin n,
        roundedMakespan δ z (corrStar z (Function.update v i (t i))) ≤ δ * (m : ℝ)) →
      allocOf f δ v = x ∧
      roundedMakespan δ x (corrStar x (Function.update v i (t i))) ≤ δ * (m : ℝ) ∧
      roundedMakespan δ x (corrStar x v) = roundedMakespan δ x (corrStar x s) := by
  classical
  dsimp only
  let C := δ * (m : ℝ)
  let s := Function.update t i (d i)
  let X := allocOf f δ s
  let base : Fin n → Fin k → ℝ := Function.update (fun _ _ => a) i (d i)
  let x := allocOf f δ base
  let U := span δ x base
  intro hhigh
  have hs (l : Fin n) (j : Fin k) : a ≤ s l j ∧ s l j ≤ b := by
    by_cases hl : l = i
    · subst l; simpa [s] using hd i j
    · simpa [s, hl] using ht l j
  have hb (l : Fin n) (j : Fin k) : a ≤ base l j ∧ base l j ≤ b := by
    by_cases hl : l = i
    · subst l; simpa [base] using hd i j
    · simp [base, hl, hab]
  have hb_i : base i = d i := by simp [base]
  have hs_i : s i = d i := by simp [s]
  have base_min (l : Fin n) (hl : l ≠ i) (j : Fin k) : base l j = a := by simp [base, hl]
  have baseMono (v : Fin n → Fin k → ℝ) (hv : ∀ l j, a ≤ v l j ∧ v l j ≤ b)
      (hvi : v i = d i) (l : Fin n) (j : Fin k) :
      roundUp δ (base l j) ≤ roundUp δ (v l j) := by
    by_cases hl : l = i
    · subst l; simp [hb_i, hvi]
    · rw [base_min l hl]
      exact time_mono hδ (hv l j).1
  have trueS : Function.update s i (t i) = t := by simp [s]
  have hReportUpper : span δ X s ≤ max U (C + δ) := by
    apply cap_base_bound hδ f hf i (t i) (d i) hop base hb_i base_min s hs hs_i
    exact ⟨y, by rwa [trueS]⟩
  have hU : C + δ < U := by
    have h := hhigh.trans_le hReportUpper
    exact (lt_max_iff.1 h).resolve_right (lt_irrefl _)
  have hUS : U = span δ X s := by
    apply le_antisymm
    · exact ((hf k base hb).2 X).trans (span_mono δ X base s (baseMono s hs hs_i))
    · exact hReportUpper.trans_eq (max_eq_left hU.le)
  have trueBase : span δ x (Function.update base i (t i)) ≤ C := by
    refine (hop base hb hb_i y).trans ?_
    have h := span_mono δ y _ _ (truth_mono δ i (t i) base s (baseMono s hs hs_i))
    rw [trueS] at h
    exact h.trans hy
  have focalBase : rowLoad δ x base i = U := by
    obtain ⟨l, _, hl⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (rowLoad δ x base)
    have he : U = rowLoad δ x base l := (span_eq δ x base).trans hl
    by_cases hl' : l = i
    · simpa [hl'] using he.symm
    · have h := (row_le_span δ x (Function.update base i (t i)) l).trans trueBase
      have hh : rowLoad δ x base l ≤ C := by simpa [rowLoad, hl'] using h
      linarith
  have holds (v : Fin n → Fin k → ℝ) (hv : ∀ l j, a ≤ v l j ∧ v l j ≤ b)
      (hvi : v i = d i) (hxU : span δ x v ≤ U) :
      allocOf f δ v = x ∧ span δ x v = U := by
    let z := allocOf f δ v
    have hxBase := (hf k base hb).2 z
    have hzV := (hf k v hv).2 x
    have hzMono := span_mono δ z base v (baseMono v hv hvi)
    have hzEq : span δ z v = U := le_antisymm (hzV.trans hxU) (hxBase.trans hzMono)
    have hzBase : span δ z base = U := le_antisymm (hzMono.trans_eq hzEq) hxBase
    have hxEq : span δ x v = U := le_antisymm hxU (hzEq.symm.trans_le hzV)
    have h1 : rank z ≤ rank x := hpriority v hv x (hxEq.trans hzEq.symm)
    have h2 : rank x ≤ rank z := hpriority base hb z hzBase
    exact ⟨hinj (le_antisymm h1 h2), hxEq⟩
  have stable (v : Fin n → Fin k → ℝ) (hv : ∀ l j, a ≤ v l j ∧ v l j ≤ b)
      (hvi : v i = d i)
      (hcmp : ∃ z : Fin k → Fin n, span δ z (Function.update v i (t i)) ≤ C) :
      allocOf f δ v = x ∧ span δ x (Function.update v i (t i)) ≤ C ∧ span δ x v = U := by
    obtain ⟨z, hz⟩ := hcmp
    have oppBound (l : Fin n) (hl : l ≠ i) : rowLoad δ x v l ≤ C := by
      by_contra hh
      let S := Finset.univ.filter (fun j => x j = l)
      have hB := (row_le_span δ x (Function.update base i (t i)) l).trans trueBase
      have hfloor : (∑ _j ∈ S, roundUp δ a) ≤ C := by
        simpa [rowLoad, S, hl, base_min l hl] using hB
      have hGrid : C + δ = δ * ((m + 1 : ℤ) : ℝ) := by simp [C, mul_add]
      have hGridDrop : C + δ ≤ rowLoad δ x v l := by
        let p : ℤ := ∑ j ∈ S, ⌈v l j / δ⌉
        have hp : rowLoad δ x v l = δ * (p : ℝ) := by
          simp [p, rowLoad, S, roundUp, Finset.mul_sum]
        have hlt : (m : ℤ) < p := by
          rw [hp] at hh
          exact_mod_cast lt_of_mul_lt_mul_left (lt_of_not_ge hh) hδ.le
        rw [hGrid, hp]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast Int.add_one_le_of_lt hlt) hδ.le
      obtain ⟨r, hr, _, hrt, hs⟩ :=
        cap_row hδ S (v l) (hv l) (m + 1) (hGrid ▸ hfloor.trans (le_add_of_nonneg_right hδ.le))
      let w := Function.update base l r
      have hw (u : Fin n) (j : Fin k) : a ≤ w u j ∧ w u j ≤ b := by
        by_cases hu : u = l
        · subst u; simpa [w] using hr j
        · simpa [w, hu] using hb u j
      have hwi : w i = d i := by simpa [w, Ne.symm hl] using hb_i
      have hwSame (u : Fin n) (hu : u ≠ l) : w u = base u := by simp [w, hu]
      have hwLoad : rowLoad δ x w l = C + δ := by
        rw [rowLoad, show w l = r by simp [w], hs, ← hGrid]
        exact min_eq_right hGridDrop
      have hwSpan : span δ x w ≤ U := by
        rw [span_eq]
        apply Finset.sup'_le
        intro u _
        by_cases hu : u = l
        · subst u; rw [hwLoad]; exact hU.le
        · have hh := row_le_span δ x base u
          simpa [rowLoad, hwSame u hu] using hh
      have hwChosen := (holds w hw hwi hwSpan).1
      have hwm (u : Fin n) (j : Fin k) : roundUp δ (w u j) ≤ roundUp δ (v u j) := by
        by_cases hu : u = l
        · subst u; simpa [w] using hrt j
        · simpa [w, hu] using baseMono v hv hvi u j
      have hzW := (span_mono δ z _ _ (truth_mono δ i (t i) w v hwm)).trans hz
      have hwC : span δ (allocOf f δ w) (Function.update w i (t i)) ≤ C :=
        (hop w hw hwi z).trans hzW
      rw [hwChosen] at hwC
      have hlow := (row_le_span δ x (Function.update w i (t i)) l).trans hwC
      have hh' : rowLoad δ x w l ≤ C := by simpa [rowLoad, hl] using hlow
      rw [hwLoad] at hh'
      linarith
    have hxU : span δ x v ≤ U := by
      rw [span_eq]
      apply Finset.sup'_le
      intro l _
      by_cases hl : l = i
      · subst l
        simpa [rowLoad, hb_i, hvi] using focalBase.le
      · exact (oppBound l hl).trans (by linarith)
    obtain ⟨hxv, hr⟩ := holds v hv hvi hxU
    have htrue : span δ (allocOf f δ v) (Function.update v i (t i)) ≤ C :=
      (hop v hv hvi z).trans hz
    rw [hxv] at htrue
    exact ⟨hxv, htrue, hr⟩
  have hX : X = x := (stable s hs hs_i ⟨y, by rwa [trueS]⟩).1
  intro v hv hvi hcmp
  obtain ⟨ha, hb, hc⟩ := stable v hv hvi hcmp
  rw [← hX] at ha hb hc
  exact ⟨ha, hb, hc.trans hUS⟩
