-- Prove2me | solution 1 for NisanRonen.Rounding.allocation_certificates_with_spare_machine_or_trivial_instance
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:24:15.766154+00:00
-- url     : https://prove2.me/submissions/d7f6c6f0-7178-4312-a18f-ae72dcfba940

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion
import Theorems.Thm_NisanRonen_Rounding_rounding_error_bound

open NisanRonen.Rounding

private theorem ru_ge {δ u : ℝ} (hδ : 0 < δ) : u ≤ roundUp δ u := by
  have hm := mul_le_mul_of_nonneg_left (Int.le_ceil (u / δ)) hδ.le
  rw [mul_comm δ (u / δ), div_mul_cancel₀ _ hδ.ne'] at hm
  exact hm

private theorem ru_lt {δ u : ℝ} (hδ : 0 < δ) : roundUp δ u < u + δ := by
  have hm := mul_lt_mul_of_pos_left (Int.ceil_lt_add_one (u / δ)) hδ
  rw [mul_add, mul_one, mul_comm δ (u / δ), div_mul_cancel₀ _ hδ.ne'] at hm
  exact hm

private theorem ru_mono {δ : ℝ} (hδ : 0 < δ) {u v : ℝ} (h : u ≤ v) :
    roundUp δ u ≤ roundUp δ v := by
  unfold roundUp
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast Int.ceil_mono (div_le_div_of_nonneg_right h hδ.le)) hδ.le

private theorem grid_between {a b δ u v : ℝ} (hδ : 0 < δ)
    (hu : a ≤ u) (hv : v ≤ b) (h : roundUp δ u + δ < roundUp δ v) :
    ∃ m : ℝ, a ≤ m ∧ m ≤ b ∧ roundUp δ m = m ∧
      roundUp δ u < m ∧ m < roundUp δ v := by
  let z : ℤ := ⌈u / δ⌉ + 1
  let m : ℝ := δ * (z : ℝ)
  have hm : m = roundUp δ u + δ := by simp [m, z, roundUp, mul_add]
  have hv' : m < roundUp δ v := hm.symm ▸ h
  have hzi : z < ⌈v / δ⌉ := by
    exact_mod_cast (lt_of_mul_lt_mul_left
      (show δ * (z : ℝ) < δ * (⌈v / δ⌉ : ℤ) from hv') hδ.le)
  have hgap : m + δ ≤ roundUp δ v := by
    have hzr : ((z + 1 : ℤ) : ℝ) ≤ (⌈v / δ⌉ : ℤ) := by
      exact_mod_cast Int.add_one_le_of_lt hzi
    simpa [m, roundUp, mul_add] using mul_le_mul_of_nonneg_left hzr hδ.le
  refine ⟨m, ?_, ?_, by simp [m, roundUp, mul_div_cancel_left₀ _ hδ.ne'], ?_, hv'⟩
  · linarith [ru_ge (u := u) hδ]
  · linarith [ru_lt (u := v) hδ]
  · linarith

private theorem bound_of_injective_alloc {n k : ℕ} [NeZero n]
    (x : Fin k → Fin n) (hx : Function.Injective x) (v : Fin k → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hv : ∀ j, v j ≤ C) : makespan x v ≤ C := by
  unfold makespan
  apply Finset.sup'_le
  intro i _
  classical
  by_cases h : ∃ j, x j = i
  · obtain ⟨j, hj⟩ := h
    have H : Finset.univ.filter (fun l => x l = i) = {j} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [← hj]
      exact hx.eq_iff
    simpa only [load, H, Finset.sum_singleton] using hv j
  · push Not at h
    simpa [load, h] using hC

private theorem task_time_le_span {n k : ℕ} [NeZero n]
    (x : Fin k → Fin n) (v : Fin k → ℝ) (hv : ∀ j, 0 ≤ v j) (j : Fin k) :
    v j ≤ makespan x v := by
  unfold makespan
  refine le_trans ?_ (Finset.le_sup' (load x v) (Finset.mem_univ (x j)))
  exact Finset.single_le_sum (fun l _ => hv l) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

private theorem report_le_of_spare_machine {n k : ℕ} [NeZero n] {a b δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hspare : k < n)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (i : Fin n) (t r : Fin k → ℝ) (ht : ∀ j, a ≤ t j ∧ t j ≤ b)
    (hr : ∀ j, a ≤ r j ∧ r j ≤ b) (hop : DeclarationOptimal f δ a b i t r) (j₀ : Fin k) :
    roundUp δ (r j₀) ≤ roundUp δ (t j₀) + δ := by
  classical
  have hba : a ≤ b := (ht j₀).1.trans (ht j₀).2
  by_contra hfail
  obtain ⟨m, hma, hmb, hmround, hmt, hmr⟩ :=
    grid_between hδ (ht j₀).1 (hr j₀).2 (lt_of_not_ge hfail)
  have hyexists : ∃ y : Fin k → Fin n, Function.Injective y ∧ ∀ j, y j ≠ i := by
    cases n with
    | zero => omega
    | succ n =>
      let hkn : k ≤ n := Nat.lt_succ_iff.mp hspare
      exact ⟨fun j => i.succAbove (Fin.castLE hkn j),
        fun _ _ h => Fin.castLE_injective hkn (Fin.succAbove_right_injective h),
        fun j => i.succAbove_ne _⟩
  obtain ⟨y, hy, hyi⟩ := hyexists
  let v (l : Fin n) (j : Fin k) := if l = i then r j else if j = j₀ then m else a
  have hv (l : Fin n) (j : Fin k) : a ≤ v l j ∧ v l j ≤ b := by
    by_cases hi : l = i <;> by_cases hj : j = j₀ <;> simp [v, hi, hj, hr, hma, hmb, hba]
  have hvi : v i = r := by funext j; simp [v]
  have hra : roundUp δ a ≤ roundUp δ (t j₀) := ru_mono hδ (ht j₀).1
  have hybound : roundedMakespan δ y (corrStar y v) ≤ m := by
    unfold roundedMakespan
    apply bound_of_injective_alloc y hy _ m (ha.le.trans hma)
    intro j
    by_cases hj : j = j₀
    · simp [corrStar, v, hyi, hj, hmround]
    · simpa [corrStar, v, hyi, hj] using (hra.trans hmt.le)
  let x := allocOf f δ v
  have hx : roundedMakespan δ x (corrStar x v) ≤ m := ((hf k v hv).2 y).trans hybound
  have hxi : x j₀ ≠ i := by
    intro hxj
    have hxlower := task_time_le_span x (fun j => roundUp δ (corrStar x v j))
      (fun j => (ha.le.trans (hv (x j) j).1).trans (ru_ge hδ)) j₀
    simp only [corrStar, v, hxj, if_pos rfl] at hxlower
    exact (hmr.trans_le (hxlower.trans hx)).false
  let y' := Function.update y j₀ i
  have hy' : Function.Injective y' := by
    intro j j' he
    by_cases h : j = j₀ <;> by_cases h' : j' = j₀
    · exact h.trans h'.symm
    · exact ((hyi j') (by simpa [y', Function.update_of_ne h', h] using he.symm)).elim
    · exact ((hyi j) (by simpa [y', Function.update_of_ne h, h'] using he)).elim
    · exact hy (by simpa [y', Function.update_of_ne h, Function.update_of_ne h'] using he)
  let w := Function.update v i t
  have hw (l : Fin n) (j : Fin k) : a ≤ w l j := by
    by_cases hl : l = i
    · simpa [w, hl] using (ht j).1
    · simpa [w, Function.update_of_ne hl] using (hv l j).1
  have htrue : roundedMakespan δ y' (corrStar y' w) ≤ roundUp δ (t j₀) := by
    unfold roundedMakespan
    apply bound_of_injective_alloc y' hy' _ _ ((ha.le.trans (ht j₀).1).trans (ru_ge hδ))
    intro j
    by_cases h : j = j₀
    · subst j
      simp [corrStar, y', w]
    · change roundUp δ (w (y' j) j) ≤ _
      rw [show y' j = y j by simp [y', Function.update_of_ne h]]
      simpa [corrStar, w, v, h, hyi, Function.update_of_ne] using hra
  have hcorrect := (hop v hv hvi y').trans htrue
  have htooHigh := task_time_le_span x (fun j => roundUp δ (corrStar x w j))
    (fun j => (ha.le.trans (hw (x j) j)).trans (ru_ge hδ)) j₀
  simp only [corrStar, w, Function.update_of_ne hxi, v, if_neg hxi, eq_self, if_true, hmround] at htooHigh
  exact (hmt.trans_le (htooHigh.trans hcorrect)).false

theorem solution {n k : ℕ} [NeZero n] {a b δ ε : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hε : 0 ≤ ε) (hstep : 2 * δ ≤ ε * a) (hsmall : n = 1 ∨ k ≤ 1 ∨ k < n)
    (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t d : Fin n → Fin k → ℝ) (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b)
    (hd : ∀ i j, a ≤ d i j ∧ d i j ≤ b)
    (hop : ∀ i, DeclarationOptimal f δ a b i (t i) (d i)) (y : Fin k → Fin n) :
    HasAllocationCertificates f δ a b t d ((1 + ε) * makespan y (corrStar y t)) := by
  classical
  by_cases hn : n = 1
  · subst n
    intro i _
    refine ⟨d, hd, rfl, rfl, y, ?_⟩
    have he : Function.update d i (t i) = t := by
      funext j
      have hi : j = i := Subsingleton.elim j i
      subst j
      exact Function.update_self i (t i) d
    rw [he]
    have hτ (j : Fin k) : a ≤ corrStar y t j := (ht (y j) j).1
    have hα : δ / a ≤ ε := (div_le_iff₀ ha).mpr (by linarith)
    refine (rounding_error_bound ha hδ y (corrStar y t) hτ).2.trans
      (mul_le_mul_of_nonneg_right (add_le_add_right hα 1) ?_)
    have hl : 0 ≤ load y (corrStar y t) (0 : Fin 1) :=
      Finset.sum_nonneg (fun j _ => ha.le.trans (hτ j))
    exact hl.trans (Finset.le_sup' _ (Finset.mem_univ _))
  · have hspare : k < n := by
      have hnpos := NeZero.pos n
      omega
    have hrow i j := report_le_of_spare_machine ha hδ hspare f hf i (t i) (d i)
      (ht i) (hd i) (hop i) j
    intro i _
    refine ⟨d, hd, rfl, rfl, y, ?_⟩
    let v := Function.update d i (t i)
    change roundedMakespan δ y (corrStar y v) ≤ _
    have hτ (j : Fin k) :
        roundUp δ (corrStar y v j) ≤ (1 + ε) * corrStar y t j := by
      have hx : roundUp δ (corrStar y v j) ≤ roundUp δ (corrStar y t j) + δ := by
        by_cases hj : y j = i
        · simp [corrStar, v, hj, hδ.le]
        · simpa [corrStar, v, Function.update_of_ne hj] using hrow (y j) j
      have ht' : a ≤ corrStar y t j := (ht (y j) j).1
      have hεt := mul_le_mul_of_nonneg_left ht' hε
      have hr := ru_lt (u := corrStar y t j) hδ
      nlinarith
    unfold roundedMakespan makespan
    apply Finset.sup'_le
    intro l hl
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (Finset.le_sup' (load y (corrStar y t)) hl)
      (by positivity))
    unfold load
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hτ j)
