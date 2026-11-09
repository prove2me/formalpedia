-- Prove2me | solution 1 for JobShopLTAS.Core.lemma1_interval_lp_feasible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T01:09:32.071207+00:00
-- url     : https://prove2.me/submissions/a16455b3-8590-4d8e-99ad-b89aa100788e

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_JobShopLTAS_Core_RestrictedProblem
import Definitions.Def_JobShopLTAS_Core_IntervalLP
import Theorems.Thm_JobShopLTAS_Core_restrictedOpt_le
import Theorems.Thm_JobShopLTAS_Core_optMakespan_le_m_mul_Pmax

namespace JobShopLTAS.Core

open Classical

/-- Clamped overlap length of `[α₀, β₀]` with `[a, b]`. -/
noncomputable def overlap (α₀ β₀ a b : ℝ) : ℝ :=
  max 0 (min β₀ b - max α₀ a)

lemma overlap_nonneg (α₀ β₀ a b : ℝ) : 0 ≤ overlap α₀ β₀ a b :=
  le_max_left 0 _

lemma overlap_eq_clamp_left {α₀ β₀ a b : ℝ} (hαβ : α₀ ≤ β₀) (hab : a ≤ b) :
    overlap α₀ β₀ a b = min β₀ (max α₀ b) - min β₀ (max α₀ a) := by
  simp only [overlap, min_def, max_def]
  split_ifs <;> linarith

lemma overlap_eq_clamp_right {α₀ β₀ a b : ℝ} (hαβ : α₀ ≤ β₀) (hab : a ≤ b) :
    overlap α₀ β₀ a b = min b (max a β₀) - min b (max a α₀) := by
  simp only [overlap, min_def, max_def]
  split_ifs <;> linarith

lemma overlap_pos_iff {α₀ β₀ a b : ℝ} :
    0 < overlap α₀ β₀ a b ↔ max α₀ a < min β₀ b := by
  unfold overlap
  rw [lt_max_iff]
  simp [sub_pos]

lemma overlap_self_zero (x a b : ℝ) : overlap x x a b = 0 := by
  simp only [overlap, min_def, max_def]
  split_ifs <;> linarith

lemma overlap_eq_zero_of_le_left {α₀ β₀ a b : ℝ} (h : β₀ ≤ a) :
    overlap α₀ β₀ a b = 0 := by
  simp only [overlap, min_def, max_def]
  split_ifs <;> linarith

lemma overlap_eq_zero_of_le_right {α₀ β₀ a b : ℝ} (h : b ≤ α₀) :
    overlap α₀ β₀ a b = 0 := by
  simp only [overlap, min_def, max_def]
  split_ifs <;> linarith

/-- Disjoint subintervals inside `[a, b]` have total length at most `b - a`. -/
lemma sum_disjoint_intervals_le {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (u v : ι → ℝ) (a b : ℝ) (hab : a ≤ b)
    (h_in : ∀ x ∈ S, a ≤ u x ∧ u x ≤ v x ∧ v x ≤ b)
    (h_disj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → v x ≤ u y ∨ v y ≤ u x) :
    ∑ x ∈ S, (v x - u x) ≤ b - a := by
  induction hn : S.card generalizing S b with
  | zero =>
    have hS : S = ∅ := Finset.card_eq_zero.mp hn
    subst hS
    simp
    linarith
  | succ k ih =>
    by_cases hzero : ∃ x ∈ S, v x = u x
    · rcases hzero with ⟨x₀, hx₀, hvx₀⟩
      rw [← Finset.add_sum_erase S (fun x => v x - u x) hx₀]
      have hcard : (S.erase x₀).card = k := by
        rw [Finset.card_erase_of_mem hx₀, hn]
        omega
      have hle := ih (S.erase x₀) b hab
        (fun x hx => h_in x (Finset.mem_of_mem_erase hx))
        (fun x hx y hy hxy => h_disj x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy)
        hcard
      linarith
    · have hzero' : ∀ x ∈ S, v x ≠ u x := by simpa using hzero
      have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
      rcases Finset.exists_max_image S v hS_ne with ⟨x_max, hx_max, hmax⟩
      rw [← Finset.add_sum_erase S (fun x => v x - u x) hx_max]
      have hcard : (S.erase x_max).card = k := by
        rw [Finset.card_erase_of_mem hx_max, hn]
        omega
      have hx_in := h_in x_max hx_max
      have hle := ih (S.erase x_max) (u x_max) hx_in.1
        (fun y hy => by
          have hyS := Finset.mem_of_mem_erase hy
          have hy_ne : y ≠ x_max := Finset.ne_of_mem_erase hy
          have hy_in := h_in y hyS
          refine ⟨hy_in.1, hy_in.2.1, ?_⟩
          rcases h_disj y hyS x_max hx_max hy_ne with h1 | h2
          · exact h1
          · have hlt : u y < v y := lt_of_le_of_ne hy_in.2.1 (Ne.symm (hzero' y hyS))
            have hmax_y := hmax y hyS
            linarith)
        (fun x hx y hy hxy => h_disj x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy)
        hcard
      linarith [hx_in.2.2]

lemma breakpoint_zero (A : Finset ℝ) (C : ℝ) : breakpoint A C 0 = 0 := by
  simp [breakpoint]

lemma breakpoint_card_add_one (A : Finset ℝ) (C : ℝ) :
    breakpoint A C (A.card + 1) = C := by
  have h1 : A.card + 1 ≠ 0 := by omega
  have h2 : ¬ (A.card + 1 ≤ A.card) := by omega
  simp [breakpoint, h1, h2]

lemma breakpoint_step_le (A : Finset ℝ) (C : ℝ)
    (hA0 : ∀ x ∈ A, 0 ≤ x) (hAC : ∀ x ∈ A, x ≤ C) (hC : 0 ≤ C) :
    ∀ k, breakpoint A C k ≤ breakpoint A C (k + 1) := by
  intro k
  by_cases hk0 : k = 0
  · subst hk0
    rw [breakpoint_zero]
    have h1 : (1 : ℕ) ≠ 0 := by omega
    by_cases h2 : 1 ≤ A.card
    · simp only [breakpoint, h1, h2, ↓reduceDIte]
      exact hA0 _ (Finset.orderEmbOfFin_mem A rfl ⟨0, by omega⟩)
    · simp only [breakpoint, h1, h2, ↓reduceDIte]
      exact hC
  · by_cases hk : k < A.card
    · unfold breakpoint
      have hk1 : k + 1 ≠ 0 := by omega
      have hk2 : k + 1 ≤ A.card := by omega
      have hk3 : k ≤ A.card := by omega
      simp only [hk0, hk3, hk1, hk2, ↓reduceDIte]
      exact (A.orderEmbOfFin rfl).monotone (by simp [Fin.le_iff_val_le_val])
    · by_cases hk_eq : k = A.card
      · subst hk_eq
        rw [breakpoint_card_add_one]
        unfold breakpoint
        simp only [hk0, le_refl, ↓reduceDIte]
        exact hAC _ (Finset.orderEmbOfFin_mem A rfl ⟨A.card - 1, by omega⟩)
      · unfold breakpoint
        have hk1 : k + 1 ≠ 0 := by omega
        have hk2 : ¬ (k + 1 ≤ A.card) := by omega
        have hk3 : ¬ (k ≤ A.card) := by omega
        simp only [hk0, hk3, hk1, hk2, ↓reduceDIte, le_refl]

lemma breakpoint_monotone (A : Finset ℝ) (C : ℝ)
    (hA0 : ∀ x ∈ A, 0 ≤ x) (hAC : ∀ x ∈ A, x ≤ C) (hC : 0 ≤ C) :
    Monotone (breakpoint A C) :=
  monotone_nat_of_le_succ (breakpoint_step_le A C hA0 hAC hC)

lemma mem_A_eq_breakpoint (A : Finset ℝ) (C : ℝ) {x : ℝ} (hx : x ∈ A) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ A.card ∧ breakpoint A C m = x := by
  have hx_range : x ∈ Set.range (A.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hx
  rcases hx_range with ⟨idx, hidx⟩
  refine ⟨idx.val + 1, by omega, by omega, ?_⟩
  unfold breakpoint
  have h1 : idx.val + 1 ≠ 0 := by omega
  have h2 : idx.val + 1 ≤ A.card := by omega
  simp only [h1, h2, ↓reduceDIte, Nat.add_sub_cancel]
  exact hidx

lemma sum_overlap_breakpoints (A : Finset ℝ) (C : ℝ)
    (hA0 : ∀ x ∈ A, 0 ≤ x) (hAC : ∀ x ∈ A, x ≤ C) (hC : 0 ≤ C)
    {α₀ β₀ : ℝ} (h0 : 0 ≤ α₀) (hαβ : α₀ ≤ β₀) (hβC : β₀ ≤ C) :
    ∑ k : Fin (A.card + 1),
      overlap α₀ β₀ (breakpoint A C k.val) (breakpoint A C (k.val + 1)) = β₀ - α₀ := by
  rw [Fin.sum_univ_eq_sum_range (fun k => overlap α₀ β₀ (breakpoint A C k) (breakpoint A C (k + 1)))]
  have hcongr : ∀ k ∈ Finset.range (A.card + 1),
      overlap α₀ β₀ (breakpoint A C k) (breakpoint A C (k + 1)) =
      min β₀ (max α₀ (breakpoint A C (k + 1))) - min β₀ (max α₀ (breakpoint A C k)) := by
    intro k _
    exact overlap_eq_clamp_left hαβ (breakpoint_step_le A C hA0 hAC hC k)
  rw [Finset.sum_congr rfl hcongr]
  rw [Finset.sum_range_sub (fun k => min β₀ (max α₀ (breakpoint A C k))) (A.card + 1)]
  rw [breakpoint_card_add_one, breakpoint_zero]
  have hmax1 : max α₀ C = C := max_eq_right (le_trans hαβ hβC)
  have hmin1 : min β₀ C = β₀ := min_eq_left hβC
  have hmax0 : max α₀ 0 = α₀ := max_eq_left h0
  have hmin0 : min β₀ α₀ = α₀ := min_eq_right hαβ
  rw [hmax1, hmin1, hmax0, hmin0]

/-- Filter of indices `k` whose breakpoint `a_k` is `≤ t`. -/
noncomputable def slotFilter (A : Finset ℝ) (C t : ℝ) : Finset (Fin (A.card + 1)) :=
  Finset.univ.filter (fun k => breakpoint A C k.val ≤ t)

lemma slotFilter_nonempty (A : Finset ℝ) (C : ℝ) {t : ℝ} (h0 : 0 ≤ t) :
    (slotFilter A C t).Nonempty := by
  refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ 0, ?_⟩⟩
  simp [breakpoint_zero, h0]

/-- Largest index `k : Fin (A.card + 1)` with `breakpoint A C k ≤ t`. -/
noncomputable def slotIndex (A : Finset ℝ) (C t : ℝ) : Fin (A.card + 1) :=
  if h : (slotFilter A C t).Nonempty then (slotFilter A C t).max' h else 0

lemma le_slotIndex_iff (A : Finset ℝ) (C : ℝ)
    (hA0 : ∀ x ∈ A, 0 ≤ x) (hAC : ∀ x ∈ A, x ≤ C) (hC : 0 ≤ C)
    {t : ℝ} (h0 : 0 ≤ t) (k : Fin (A.card + 1)) :
    k ≤ slotIndex A C t ↔ breakpoint A C k.val ≤ t := by
  have hne := slotFilter_nonempty A C h0
  have heq : slotIndex A C t = (slotFilter A C t).max' hne := dif_pos hne
  rw [heq]
  constructor
  · intro hk
    have hmem : (slotFilter A C t).max' hne ∈ slotFilter A C t := Finset.max'_mem _ hne
    have hmax : breakpoint A C ((slotFilter A C t).max' hne).val ≤ t :=
      (Finset.mem_filter.mp hmem).2
    exact le_trans (breakpoint_monotone A C hA0 hAC hC hk) hmax
  · intro hk
    exact Finset.le_max' (slotFilter A C t) k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)

lemma slotIndex_mono (A : Finset ℝ) (C : ℝ)
    (hA0 : ∀ x ∈ A, 0 ≤ x) (hAC : ∀ x ∈ A, x ≤ C) (hC : 0 ≤ C)
    {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    slotIndex A C t₁ ≤ slotIndex A C t₂ := by
  rw [le_slotIndex_iff A C hA0 hAC hC (le_trans h0 h12)]
  exact le_trans ((le_slotIndex_iff A C hA0 hAC hC h0 (slotIndex A C t₁)).mp le_rfl) h12

lemma slotIndex_le_of_lt_succ (A : Finset ℝ) (C : ℝ)
    (hA0 : ∀ x ∈ A, 0 ≤ x) (hAC : ∀ x ∈ A, x ≤ C) (hC : 0 ≤ C)
    {t : ℝ} (h0 : 0 ≤ t) (k : Fin (A.card + 1))
    (hlt : t < breakpoint A C (k.val + 1)) :
    slotIndex A C t ≤ k := by
  by_contra! hgt
  have h1 : k.val + 1 ≤ (slotIndex A C t).val := hgt
  have h2 : breakpoint A C (k.val + 1) ≤ breakpoint A C (slotIndex A C t).val :=
    breakpoint_monotone A C hA0 hAC hC h1
  have h3 : breakpoint A C (slotIndex A C t).val ≤ t :=
    (le_slotIndex_iff A C hA0 hAC hC h0 (slotIndex A C t)).mp le_rfl
  linarith

namespace Instance

variable {m n : ℕ} (inst : Instance m n)

lemma start_mono {J : Finset (Fin n)} {s : inst.Op → ℝ}
    (hs : inst.IsFeasibleSchedule J s) {j : Fin n} (hj : j ∈ J)
    {i i' : Fin (inst.μ j)} (hii' : i ≤ i') :
    s ⟨j, i⟩ ≤ s ⟨j, i'⟩ := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Fin.le_iff_val_le_val.mp hii')
  induction d generalizing i' with
  | zero =>
    have heq : i = i' := Fin.ext (by omega)
    subst heq
    exact le_rfl
  | succ d ih =>
    let mid : Fin (inst.μ j) := ⟨i.val + d, by omega⟩
    have h1 : s ⟨j, i⟩ ≤ s ⟨j, mid⟩ := ih (by simp [mid, Fin.le_iff_val_le_val]) rfl
    have h2 : s ⟨j, mid⟩ + inst.p j mid ≤ s ⟨j, i'⟩ :=
      hs.precedence j hj mid i' (by simp [mid]; omega)
    have h3 : 0 ≤ inst.p j mid := inst.p_nonneg j mid
    linarith

lemma precedence_lt {J : Finset (Fin n)} {s : inst.Op → ℝ}
    (hs : inst.IsFeasibleSchedule J s) {j : Fin n} (hj : j ∈ J)
    {i i' : Fin (inst.μ j)} (hii' : i < i') :
    s ⟨j, i⟩ + inst.p j i ≤ s ⟨j, i'⟩ := by
  let mid : Fin (inst.μ j) := ⟨i.val + 1, by omega⟩
  have h1 : s ⟨j, i⟩ + inst.p j i ≤ s ⟨j, mid⟩ := hs.precedence j hj i mid rfl
  have h2 : s ⟨j, mid⟩ ≤ s ⟨j, i'⟩ :=
    inst.start_mono hs hj (by simp [mid, Fin.le_iff_val_le_val]; omega)
  linarith

lemma finish_le_makespan (J : Finset (Fin n)) (s : inst.Op → ℝ)
    (o : inst.Op) (ho : o.1 ∈ J) :
    s o + inst.proc o ≤ inst.makespan J s :=
  le_ciSup (Set.Finite.bddAbove (Set.finite_range (fun x : {o : inst.Op // o.1 ∈ J} => s x.1 + inst.proc x.1))) ⟨o, ho⟩

lemma makespan_nonneg {J : Finset (Fin n)} {s : inst.Op → ℝ}
    (hs : inst.IsFeasibleSchedule J s) :
    0 ≤ inst.makespan J s := by
  by_cases hne : Nonempty {o : inst.Op // o.1 ∈ J}
  · rcases hne with ⟨⟨o, ho⟩⟩
    have h1 := hs.start_nonneg o ho
    have h2 : 0 ≤ inst.proc o := inst.p_nonneg o.1 o.2
    have h3 := inst.finish_le_makespan J s o ho
    linarith
  · haveI : IsEmpty {o : inst.Op // o.1 ∈ J} := not_nonempty_iff.mp hne
    simp [Instance.makespan]

lemma continuous_makespan (J : Finset (Fin n)) :
    Continuous (inst.makespan J) := by
  let SubOp := {o : inst.Op // o.1 ∈ J}
  by_cases hE : IsEmpty SubOp
  · have heq : inst.makespan J = fun _ => (0 : ℝ) := by
      ext s
      simp [Instance.makespan]
    rw [heq]
    exact continuous_const
  · haveI : Nonempty SubOp := not_isEmpty_iff.mp hE
    have hne : (Finset.univ : Finset SubOp).Nonempty := Finset.univ_nonempty
    have heq : inst.makespan J =
        (Finset.univ : Finset SubOp).sup' hne (fun (o : SubOp) (s : inst.Op → ℝ) => s o.1 + inst.proc o.1) := by
      ext s
      rw [Finset.sup'_apply]
      refine le_antisymm ?_ ?_
      · exact ciSup_le (fun o => Finset.le_sup' (fun x : SubOp => s x.1 + inst.proc x.1) (Finset.mem_univ o))
      · exact Finset.sup'_le hne _ (fun o _ =>
          le_ciSup (Set.Finite.bddAbove (Set.finite_range (fun x : SubOp => s x.1 + inst.proc x.1))) o)
    rw [heq]
    exact Continuous.finset_sup' (f := fun (o : SubOp) (s : inst.Op → ℝ) => s o.1 + inst.proc o.1)
      hne (fun o _ => (continuous_apply o.1).add continuous_const)

lemma isClosed_forall' {α ι : Type*} [TopologicalSpace α] {P : ι → α → Prop}
    (h : ∀ i, IsClosed {a : α | P i a}) : IsClosed {a : α | ∀ i, P i a} := by
  have heq : {a : α | ∀ i, P i a} = ⋂ i, {a : α | P i a} := by
    ext a
    simp
  rw [heq]
  exact isClosed_iInter h

lemma isClosed_feasible_restricted (ε α : ℝ) :
    IsClosed {s : inst.Op → ℝ |
      inst.IsFeasibleSchedule (inst.bigJobs α ∪ inst.tinyJobs ε α) s ∧
      inst.IsRestricted ε α s} := by
  let J_BT := inst.bigJobs α ∪ inst.tinyJobs ε α
  have heq : {s : inst.Op → ℝ | inst.IsFeasibleSchedule J_BT s ∧ inst.IsRestricted ε α s} =
      ({s | ∀ o : inst.Op, o.1 ∈ J_BT → 0 ≤ s o} ∩
       {s | ∀ j : Fin n, j ∈ J_BT → ∀ i i' : Fin (inst.μ j), i.val + 1 = i'.val →
          s ⟨j, i⟩ + inst.p j i ≤ s ⟨j, i'⟩} ∩
       {s | ∀ o o' : inst.Op, o.1 ∈ J_BT → o'.1 ∈ J_BT → o ≠ o' →
          inst.mach o = inst.mach o' → s o + inst.proc o ≤ s o' ∨ s o' + inst.proc o' ≤ s o}) ∩
      {s | ∀ o : inst.Op, o.1 ∈ inst.bigJobs α →
        ∃ r ∈ Finset.range (inst.numIntervals ε α), s o = (r : ℝ) * inst.gridLength ε α} := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨h1, h2, h3⟩, h4⟩
  rw [heq]
  refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
  · exact isClosed_forall' (fun o => isClosed_imp isOpen_const (isClosed_le continuous_const (continuous_apply o)))
  · exact isClosed_forall' (fun j => isClosed_imp isOpen_const
      (isClosed_forall' (fun i => isClosed_forall' (fun i' => isClosed_imp isOpen_const
        (isClosed_le ((continuous_apply (⟨j, i⟩ : inst.Op)).add continuous_const)
          (continuous_apply (⟨j, i'⟩ : inst.Op)))))))
  · exact isClosed_forall' (fun o => isClosed_forall' (fun o' =>
      isClosed_imp isOpen_const (isClosed_imp isOpen_const (isClosed_imp isOpen_const
        (isClosed_imp isOpen_const
          (IsClosed.union
            (isClosed_le ((continuous_apply o).add continuous_const) (continuous_apply o'))
            (isClosed_le ((continuous_apply o').add continuous_const) (continuous_apply o))))))))
  · refine isClosed_forall' (fun o => isClosed_imp isOpen_const ?_)
    have h_un : {s : inst.Op → ℝ | ∃ r ∈ Finset.range (inst.numIntervals ε α), s o = (r : ℝ) * inst.gridLength ε α} =
        ⋃ r ∈ Finset.range (inst.numIntervals ε α), {s : inst.Op → ℝ | s o = (r : ℝ) * inst.gridLength ε α} := by
      ext s
      simp
    rw [h_un]
    exact (Finset.finite_toSet (Finset.range (inst.numIntervals ε α))).isClosed_biUnion
      (fun r _ => isClosed_eq (continuous_apply o) continuous_const)

lemma exists_optimal_restricted (ε α : ℝ)
    (h_ex : ∃ s : inst.Op → ℝ,
      inst.IsFeasibleSchedule (inst.bigJobs α ∪ inst.tinyJobs ε α) s ∧
      inst.IsRestricted ε α s) :
    ∃ σ : inst.Op → ℝ,
      inst.IsFeasibleSchedule (inst.bigJobs α ∪ inst.tinyJobs ε α) σ ∧
      inst.IsRestricted ε α σ ∧
      inst.makespan (inst.bigJobs α ∪ inst.tinyJobs ε α) σ = inst.restrictedOpt ε α := by
  let J_BT := inst.bigJobs α ∪ inst.tinyJobs ε α
  let F : Set (inst.Op → ℝ) := {s | inst.IsFeasibleSchedule J_BT s ∧ inst.IsRestricted ε α s}
  rcases h_ex with ⟨s₀, hs₀⟩
  let M₀ : ℝ := inst.makespan J_BT s₀
  have hM₀_nonneg : 0 ≤ M₀ := inst.makespan_nonneg hs₀.1
  let clamp : (inst.Op → ℝ) → (inst.Op → ℝ) := fun s o => if o.1 ∈ J_BT then s o else 0
  have hclamp_F : ∀ s ∈ F, clamp s ∈ F := by
    intro s ⟨hfeas, hrest⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro o ho
      simp only [clamp, ho, ↓reduceIte]
      exact hfeas.start_nonneg o ho
    · intro j hj i i' hii'
      simp only [clamp, hj, ↓reduceIte]
      exact hfeas.precedence j hj i i' hii'
    · intro o o' ho ho' hne hmach
      simp only [clamp, ho, ho', ↓reduceIte]
      exact hfeas.machine_disjoint o o' ho ho' hne hmach
    · intro o ho
      have ho_BT : o.1 ∈ J_BT := Finset.mem_union_left _ ho
      simp only [clamp, ho_BT, ↓reduceIte]
      exact hrest o ho
  have hclamp_mk : ∀ s, inst.makespan J_BT (clamp s) = inst.makespan J_BT s := by
    intro s
    unfold Instance.makespan
    congr 1
    ext ⟨o, ho⟩
    simp [clamp, ho]
  have hclamp_box : ∀ s ∈ F, inst.makespan J_BT s ≤ M₀ →
      clamp s ∈ Set.pi Set.univ (fun _ : inst.Op => Set.Icc 0 M₀) := by
    intro s hs hle o _
    by_cases ho : o.1 ∈ J_BT
    · simp only [clamp, ho, ↓reduceIte, Set.mem_Icc]
      refine ⟨hs.1.start_nonneg o ho, ?_⟩
      have h1 : 0 ≤ inst.proc o := inst.p_nonneg o.1 o.2
      have h2 := inst.finish_le_makespan J_BT s o ho
      linarith
    · simp only [clamp, ho, ↓reduceIte, Set.mem_Icc]
      exact ⟨le_rfl, hM₀_nonneg⟩
  let K : Set (inst.Op → ℝ) := Set.pi Set.univ (fun _ : inst.Op => Set.Icc 0 M₀) ∩ F
  have hK_compact : IsCompact K :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right (inst.isClosed_feasible_restricted ε α)
  have hs₀_K : clamp s₀ ∈ K := ⟨hclamp_box s₀ hs₀ le_rfl, hclamp_F s₀ hs₀⟩
  have hK_ne : K.Nonempty := ⟨clamp s₀, hs₀_K⟩
  obtain ⟨σ, hσK, hσ_min⟩ :=
    hK_compact.exists_isMinOn hK_ne (inst.continuous_makespan J_BT).continuousOn
  refine ⟨σ, hσK.2.1, hσK.2.2, ?_⟩
  unfold Instance.restrictedOpt
  refine le_antisymm ?_ ?_
  · refine le_csInf ⟨inst.makespan J_BT s₀, s₀, hs₀, rfl⟩ ?_
    rintro _ ⟨s, hs, rfl⟩
    by_cases hle : inst.makespan J_BT s ≤ M₀
    · have h_in : clamp s ∈ K := ⟨hclamp_box s hs hle, hclamp_F s hs⟩
      have h1 : inst.makespan J_BT σ ≤ inst.makespan J_BT (clamp s) := hσ_min h_in
      rwa [hclamp_mk] at h1
    · have h1 : inst.makespan J_BT σ ≤ inst.makespan J_BT (clamp s₀) := hσ_min hs₀_K
      rw [hclamp_mk] at h1
      linarith
  · refine csInf_le ⟨0, ?_⟩ ⟨σ, hσK.2, rfl⟩
    rintro _ ⟨s, hs, rfl⟩
    exact inst.makespan_nonneg hs.1

/-- Weight `w_{j, i}(k)` of operation `⟨j, i⟩` on interval `k : Fin (A.card + 1)`. -/
noncomputable def opWeight (A : Finset ℝ) (C : ℝ) (σ : inst.Op → ℝ)
    (j : Fin n) (i : Fin (inst.μ j)) (k : Fin (A.card + 1)) : ℝ :=
  if inst.p j i = 0 then
    if k = slotIndex A C (σ ⟨j, i⟩) then 1 else 0
  else
    overlap (σ ⟨j, i⟩) (σ ⟨j, i⟩ + inst.p j i) (breakpoint A C k.val) (breakpoint A C (k.val + 1)) /
      inst.p j i

lemma opWeight_nonneg (A : Finset ℝ) (C : ℝ) (σ : inst.Op → ℝ)
    (j : Fin n) (i : Fin (inst.μ j)) (k : Fin (A.card + 1)) :
    0 ≤ inst.opWeight A C σ j i k := by
  unfold opWeight
  split_ifs with hp hk
  · norm_num
  · norm_num
  · exact div_nonneg (overlap_nonneg _ _ _ _) (inst.p_nonneg j i)

lemma mul_opWeight (A : Finset ℝ) (C : ℝ) (σ : inst.Op → ℝ)
    (j : Fin n) (i : Fin (inst.μ j)) (k : Fin (A.card + 1)) :
    inst.p j i * inst.opWeight A C σ j i k =
      overlap (σ ⟨j, i⟩) (σ ⟨j, i⟩ + inst.p j i) (breakpoint A C k.val) (breakpoint A C (k.val + 1)) := by
  by_cases hp : inst.p j i = 0
  · simp [opWeight, hp, overlap_self_zero]
  · simp [opWeight, hp, mul_div_cancel₀ _ hp]

lemma sum_opWeight (A : Finset ℝ) (C : ℝ) (σ : inst.Op → ℝ)
    (hA0 : ∀ x ∈ A, 0 ≤ x) (hAC : ∀ x ∈ A, x ≤ C) (hC : 0 ≤ C)
    (j : Fin n) (i : Fin (inst.μ j))
    (h0 : 0 ≤ σ ⟨j, i⟩) (hβC : σ ⟨j, i⟩ + inst.p j i ≤ C) :
    ∑ k : Fin (A.card + 1), inst.opWeight A C σ j i k = 1 := by
  unfold opWeight
  by_cases hp : inst.p j i = 0
  · simp [hp]
  · simp only [hp, ↓reduceIte]
    rw [← Finset.sum_div]
    have hαβ : σ ⟨j, i⟩ ≤ σ ⟨j, i⟩ + inst.p j i := by linarith [inst.p_nonneg j i]
    rw [sum_overlap_breakpoints A C hA0 hAC hC h0 hαβ hβC]
    rw [add_sub_cancel_left]
    exact div_self hp

lemma opWeight_pos_bounds (A : Finset ℝ) (C : ℝ) (σ : inst.Op → ℝ)
    (hA0 : ∀ x ∈ A, 0 ≤ x) (hAC : ∀ x ∈ A, x ≤ C) (hC : 0 ≤ C)
    (j : Fin n) (i : Fin (inst.μ j)) (k : Fin (A.card + 1))
    (h0 : 0 ≤ σ ⟨j, i⟩) (hw : 0 < inst.opWeight A C σ j i k) :
    slotIndex A C (σ ⟨j, i⟩) ≤ k ∧ k ≤ slotIndex A C (σ ⟨j, i⟩ + inst.p j i) := by
  unfold opWeight at hw
  by_cases hp : inst.p j i = 0
  · simp only [hp, ↓reduceIte] at hw
    by_cases hk : k = slotIndex A C (σ ⟨j, i⟩)
    · subst hk
      simp [hp]
    · simp [hk] at hw
  · simp only [hp, ↓reduceIte] at hw
    have hp_pos : 0 < inst.p j i := lt_of_le_of_ne (inst.p_nonneg j i) (Ne.symm hp)
    have hov_pos : 0 < overlap (σ ⟨j, i⟩) (σ ⟨j, i⟩ + inst.p j i)
        (breakpoint A C k.val) (breakpoint A C (k.val + 1)) := by
      exact (div_pos_iff_of_pos_right hp_pos).mp hw
    rw [overlap_pos_iff] at hov_pos
    have hlt1 : σ ⟨j, i⟩ < breakpoint A C (k.val + 1) :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hov_pos (min_le_right _ _))
    have hlt2 : breakpoint A C k.val < σ ⟨j, i⟩ + inst.p j i :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hov_pos (min_le_left _ _))
    refine ⟨slotIndex_le_of_lt_succ A C hA0 hAC hC h0 k hlt1, ?_⟩
    have h0' : 0 ≤ σ ⟨j, i⟩ + inst.p j i := by linarith
    exact (le_slotIndex_iff A C hA0 hAC hC h0' k).mpr (le_of_lt hlt2)

lemma prod_opWeight_eq_zero_of_not_mono (A : Finset ℝ) (C : ℝ) (σ : inst.Op → ℝ)
    (hA0 : ∀ x ∈ A, 0 ≤ x) (hAC : ∀ x ∈ A, x ≤ C) (hC : 0 ≤ C)
    {J : Finset (Fin n)} (hσ : inst.IsFeasibleSchedule J σ)
    {j : Fin n} (hj : j ∈ J)
    (K : Fin (inst.μ j) → Fin (A.card + 1))
    (hK : K ∉ inst.monotoneTuples A j) :
    (∏ i : Fin (inst.μ j), inst.opWeight A C σ j i (K i)) = 0 := by
  have hnot_mono : ¬ Monotone K := by
    intro hm
    exact hK (Finset.mem_filter.mpr ⟨Finset.mem_univ K, hm⟩)
  by_contra hne
  apply hnot_mono
  intro i i' hii'
  by_cases heq : i = i'
  · subst heq
    exact le_rfl
  · have hlt : i < i' := lt_of_le_of_ne hii' heq
    have hw_ne : ∀ idx : Fin (inst.μ j), inst.opWeight A C σ j idx (K idx) ≠ 0 := by
      intro idx hzero
      exact hne (Finset.prod_eq_zero (Finset.mem_univ idx) hzero)
    have hw_pos : ∀ idx : Fin (inst.μ j), 0 < inst.opWeight A C σ j idx (K idx) :=
      fun idx => lt_of_le_of_ne (inst.opWeight_nonneg A C σ j idx (K idx)) (Ne.symm (hw_ne idx))
    have h0_i : 0 ≤ σ ⟨j, i⟩ := hσ.start_nonneg ⟨j, i⟩ hj
    have h0_i' : 0 ≤ σ ⟨j, i'⟩ := hσ.start_nonneg ⟨j, i'⟩ hj
    have hb_i := (inst.opWeight_pos_bounds A C σ hA0 hAC hC j i (K i) h0_i (hw_pos i)).2
    have hb_i' := (inst.opWeight_pos_bounds A C σ hA0 hAC hC j i' (K i') h0_i' (hw_pos i')).1
    have hprec : σ ⟨j, i⟩ + inst.p j i ≤ σ ⟨j, i'⟩ := inst.precedence_lt hσ hj hlt
    have h0_end : 0 ≤ σ ⟨j, i⟩ + inst.p j i := by linarith [inst.p_nonneg j i]
    have hmono := slotIndex_mono A C hA0 hAC hC h0_end hprec
    exact le_trans hb_i (le_trans hmono hb_i')

lemma sum_ite_prod_opWeight (A : Finset ℝ) (C : ℝ) (σ : inst.Op → ℝ)
    (hA0 : ∀ x ∈ A, 0 ≤ x) (hAC : ∀ x ∈ A, x ≤ C) (hC : 0 ≤ C)
    (j : Fin n)
    (h0 : ∀ i : Fin (inst.μ j), 0 ≤ σ ⟨j, i⟩)
    (hβC : ∀ i : Fin (inst.μ j), σ ⟨j, i⟩ + inst.p j i ≤ C)
    (i : Fin (inst.μ j)) (k : Fin (A.card + 1)) :
    (∑ K : Fin (inst.μ j) → Fin (A.card + 1),
      if K i = k then ∏ i' : Fin (inst.μ j), inst.opWeight A C σ j i' (K i') else 0) =
    inst.opWeight A C σ j i k := by
  let f : Fin (inst.μ j) → Fin (A.card + 1) → ℝ :=
    fun i' k' =>
      if i' = i then (if k' = k then inst.opWeight A C σ j i' k' else 0)
      else inst.opWeight A C σ j i' k'
  have h_term : ∀ K : Fin (inst.μ j) → Fin (A.card + 1),
      (if K i = k then ∏ i' : Fin (inst.μ j), inst.opWeight A C σ j i' (K i') else 0) =
      ∏ i' : Fin (inst.μ j), f i' (K i') := by
    intro K
    by_cases hKi : K i = k
    · simp only [hKi, ↓reduceIte, f]
      refine Finset.prod_congr rfl (fun i' _ => ?_)
      by_cases hi' : i' = i
      · subst hi'
        simp [hKi]
      · simp [hi']
    · simp only [hKi, ↓reduceIte, f]
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp [hKi]
  simp_rw [h_term]
  rw [← Fintype.prod_sum f]
  have h_factor : ∀ i' : Fin (inst.μ j),
      (∑ k' : Fin (A.card + 1), f i' k') =
      if i' = i then inst.opWeight A C σ j i k else 1 := by
    intro i'
    dsimp [f]
    by_cases hi' : i' = i
    · subst hi'
      simp
    · simp only [hi', ↓reduceIte]
      exact inst.sum_opWeight A C σ hA0 hAC hC j i' (h0 i') (hβC i')
  simp_rw [h_factor]
  simp

lemma bigOp_contains_interval (α C : ℝ) (σ : inst.Op → ℝ)
    (hA0 : ∀ x ∈ inst.bigTimes α σ, 0 ≤ x)
    (hAC : ∀ x ∈ inst.bigTimes α σ, x ≤ C)
    (hC : 0 ≤ C)
    {o : inst.Op} (ho : o.1 ∈ inst.bigJobs α) {k : ℕ}
    (hproc : inst.ProcessedIn (inst.bigTimes α σ) C σ o k) :
    σ o ≤ breakpoint (inst.bigTimes α σ) C k ∧
      breakpoint (inst.bigTimes α σ) C (k + 1) ≤ σ o + inst.proc o := by
  let A := inst.bigTimes α σ
  have ho_filter : o ∈ Finset.univ.filter (fun x : inst.Op => x.1 ∈ inst.bigJobs α) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ o, ho⟩
  have h_start_mem : σ o ∈ A :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem σ ho_filter)
  have h_end_mem : σ o + inst.proc o ∈ A :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem (fun x => σ x + inst.proc x) ho_filter)
  rcases mem_A_eq_breakpoint A C h_start_mem with ⟨m₁, _, _, hm₁⟩
  rcases mem_A_eq_breakpoint A C h_end_mem with ⟨m₂, _, _, hm₂⟩
  unfold Instance.ProcessedIn at hproc
  have hlt1 : σ o < breakpoint A C (k + 1) :=
    lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hproc (min_le_right _ _))
  have hlt2 : breakpoint A C k < σ o + inst.proc o :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hproc (min_le_left _ _))
  constructor
  · by_cases hm : m₁ ≤ k
    · rw [← hm₁]
      exact breakpoint_monotone A C hA0 hAC hC hm
    · have hge : k + 1 ≤ m₁ := by omega
      have hle := breakpoint_monotone A C hA0 hAC hC hge
      rw [hm₁] at hle
      linarith
  · by_cases hm : k + 1 ≤ m₂
    · rw [← hm₂]
      exact breakpoint_monotone A C hA0 hAC hC hm
    · have hle_idx : m₂ ≤ k := by omega
      have hle := breakpoint_monotone A C hA0 hAC hC hle_idx
      rw [hm₂] at hle
      linarith

end Instance

/-- Lemma 1 (§2.2, p. 292): for `C = C̃*_max`, the linear program (3)–(5) has a feasible
solution for some feasible restricted schedule `σ` of the big operations. -/
theorem lemma1_interval_lp_feasible {m n : ℕ} (inst : Instance m n) (ε α : ℝ)
    (hm : 2 ≤ m) (hμ : 1 ≤ inst.maxOps) (hε : 0 < ε) (hε1 : ε < 1)
    (hα_lo : ε ^ ⌈(m : ℝ) / ε⌉₊ ≤ α) (hα_hi : α ≤ ε) (hP : 0 < inst.Pmax) :
    ∃ σ : inst.Op → ℝ, inst.IsBigSchedule ε α σ ∧
      inst.LPFeasible ε α σ (inst.restrictedOpt ε α) := by
  obtain ⟨h_ex, h_opt1, h_opt2⟩ :=
    restrictedOpt_le inst ε α hm hμ hε hε1 hα_lo hα_hi hP
  obtain ⟨σ, hσ_feas, hσ_rest, hσ_mk⟩ :=
    inst.exists_optimal_restricted ε α h_ex
  let J_BT := inst.bigJobs α ∪ inst.tinyJobs ε α
  let C := inst.restrictedOpt ε α
  let A := inst.bigTimes α σ
  have hC0 : 0 ≤ C := by
    change 0 ≤ inst.restrictedOpt ε α
    rw [← hσ_mk]
    exact inst.makespan_nonneg hσ_feas
  have hA0 : ∀ x ∈ A, 0 ≤ x := by
    intro x hx
    simp only [A, Instance.bigTimes, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    rcases hx with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
    · exact hσ_feas.start_nonneg o (Finset.mem_union_left _ ho)
    · have h1 := hσ_feas.start_nonneg o (Finset.mem_union_left _ ho)
      have h2 : 0 ≤ inst.proc o := inst.p_nonneg o.1 o.2
      linarith
  have hAC : ∀ x ∈ A, x ≤ C := by
    intro x hx
    simp only [A, Instance.bigTimes, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    rcases hx with ⟨o, ho, rfl⟩ | ⟨o, ho, rfl⟩
    · have h1 : 0 ≤ inst.proc o := inst.p_nonneg o.1 o.2
      have h2 := inst.finish_le_makespan J_BT σ o (Finset.mem_union_left _ ho)
      linarith
    · have h2 := inst.finish_le_makespan J_BT σ o (Finset.mem_union_left _ ho)
      linarith
  refine ⟨σ, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_⟩, hσ_rest⟩
    · intro o ho
      exact hσ_feas.start_nonneg o (Finset.mem_union_left _ ho)
    · intro j hj i i' hii'
      exact hσ_feas.precedence j (Finset.mem_union_left _ hj) i i' hii'
    · intro o o' ho ho' hne hmach
      exact hσ_feas.machine_disjoint o o'
        (Finset.mem_union_left _ ho) (Finset.mem_union_left _ ho') hne hmach
  · refine ⟨?_, ?_, ?_⟩
    · calc breakpoint A C A.card
        _ ≤ breakpoint A C (A.card + 1) := breakpoint_step_le A C hA0 hAC hC0 A.card
        _ = C := breakpoint_card_add_one A C
    · have h_ub : inst.optMakespan Finset.univ ≤ (m : ℝ) * inst.Pmax :=
        optMakespan_le_m_mul_Pmax inst
      have h_coeff : 0 ≤ 1 + (inst.maxOps : ℝ) * (m : ℝ) * ε := by positivity
      have h_mul : (1 + (inst.maxOps : ℝ) * (m : ℝ) * ε) * inst.optMakespan Finset.univ ≤
          (1 + (inst.maxOps : ℝ) * (m : ℝ) * ε) * ((m : ℝ) * inst.Pmax) :=
        mul_le_mul_of_nonneg_left h_ub h_coeff
      unfold Instance.horizon
      linarith
    · let x : (j : Fin n) → (Fin (inst.μ j) → Fin (A.card + 1)) → ℝ :=
        fun j K => ∏ i : Fin (inst.μ j), inst.opWeight A C σ j i (K i)
      refine ⟨x, ?_, ?_, ?_⟩
      · intro j hj
        have hj_BT : j ∈ J_BT := Finset.mem_union_right _ hj
        have h_sub : ∑ K ∈ inst.monotoneTuples A j, x j K =
            ∑ K : Fin (inst.μ j) → Fin (A.card + 1), x j K := by
          refine Finset.sum_subset (Finset.subset_univ _) (fun K _ hK => ?_)
          exact inst.prod_opWeight_eq_zero_of_not_mono A C σ hA0 hAC hC0 hσ_feas hj_BT K hK
        rw [h_sub]
        dsimp [x]
        rw [← Fintype.prod_sum]
        have h_one : ∀ i : Fin (inst.μ j), ∑ k : Fin (A.card + 1), inst.opWeight A C σ j i k = 1 := by
          intro i
          refine inst.sum_opWeight A C σ hA0 hAC hC0 j i
            (hσ_feas.start_nonneg ⟨j, i⟩ hj_BT) ?_
          change σ ⟨j, i⟩ + inst.p j i ≤ inst.restrictedOpt ε α
          rw [← hσ_mk]
          exact inst.finish_le_makespan J_BT σ ⟨j, i⟩ hj_BT
        simp [h_one]
      · intro t k
        have h_per_job : ∀ j ∈ inst.tinyJobs ε α,
            (∑ K ∈ inst.monotoneTuples A j,
              ∑ i ∈ Finset.univ.filter (fun i => K i = k ∧ inst.π j i = t), inst.p j i * x j K) =
            ∑ i ∈ Finset.univ.filter (fun i : Fin (inst.μ j) => inst.π j i = t),
              overlap (σ ⟨j, i⟩) (σ ⟨j, i⟩ + inst.p j i)
                (breakpoint A C k.val) (breakpoint A C (k.val + 1)) := by
          intro j hj
          have hj_BT : j ∈ J_BT := Finset.mem_union_right _ hj
          have h_sub : (∑ K ∈ inst.monotoneTuples A j,
              ∑ i ∈ Finset.univ.filter (fun i => K i = k ∧ inst.π j i = t), inst.p j i * x j K) =
              ∑ K : Fin (inst.μ j) → Fin (A.card + 1),
                ∑ i ∈ Finset.univ.filter (fun i => K i = k ∧ inst.π j i = t), inst.p j i * x j K := by
            refine Finset.sum_subset (Finset.subset_univ _) (fun K _ hK => ?_)
            have hx0 : x j K = 0 :=
              inst.prod_opWeight_eq_zero_of_not_mono A C σ hA0 hAC hC0 hσ_feas hj_BT K hK
            simp [hx0]
          rw [h_sub]
          have h_inner : ∀ K : Fin (inst.μ j) → Fin (A.card + 1),
              (∑ i ∈ Finset.univ.filter (fun i => K i = k ∧ inst.π j i = t), inst.p j i * x j K) =
              ∑ i ∈ Finset.univ.filter (fun i : Fin (inst.μ j) => inst.π j i = t),
                inst.p j i * (if K i = k then x j K else 0) := by
            intro K
            simp only [Finset.sum_filter, mul_ite, mul_zero]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            split_ifs <;> tauto
          simp_rw [h_inner]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.mul_sum]
          have h0_all : ∀ i' : Fin (inst.μ j), 0 ≤ σ ⟨j, i'⟩ :=
            fun i' => hσ_feas.start_nonneg ⟨j, i'⟩ hj_BT
          have hβC_all : ∀ i' : Fin (inst.μ j), σ ⟨j, i'⟩ + inst.p j i' ≤ C := by
            intro i'
            change σ ⟨j, i'⟩ + inst.p j i' ≤ inst.restrictedOpt ε α
            rw [← hσ_mk]
            exact inst.finish_le_makespan J_BT σ ⟨j, i'⟩ hj_BT
          rw [inst.sum_ite_prod_opWeight A C σ hA0 hAC hC0 j h0_all hβC_all i k]
          exact inst.mul_opWeight A C σ j i k
        rw [Finset.sum_congr rfl h_per_job]
        let S_tk : Finset inst.Op :=
          (inst.tinyJobs ε α).sigma (fun j => Finset.univ.filter (fun i : Fin (inst.μ j) => inst.π j i = t))
        have h_sigma : (∑ j ∈ inst.tinyJobs ε α,
            ∑ i ∈ Finset.univ.filter (fun i : Fin (inst.μ j) => inst.π j i = t),
              overlap (σ ⟨j, i⟩) (σ ⟨j, i⟩ + inst.p j i)
                (breakpoint A C k.val) (breakpoint A C (k.val + 1))) =
            ∑ o ∈ S_tk,
              overlap (σ o) (σ o + inst.proc o)
                (breakpoint A C k.val) (breakpoint A C (k.val + 1)) := by
          exact (Finset.sum_sigma (inst.tinyJobs ε α)
            (fun j => Finset.univ.filter (fun i : Fin (inst.μ j) => inst.π j i = t))
            (fun o => overlap (σ o) (σ o + inst.proc o)
              (breakpoint A C k.val) (breakpoint A C (k.val + 1)))).symm
        rw [h_sigma]
        unfold Instance.availableLength
        split_ifs with h_big
        · rcases h_big with ⟨o_B, ho_B_big, ho_B_mach, ho_B_proc⟩
          have h_cont := inst.bigOp_contains_interval α C σ hA0 hAC hC0 ho_B_big ho_B_proc
          have h_zero_sum : ∀ o ∈ S_tk,
              overlap (σ o) (σ o + inst.proc o)
                (breakpoint A C k.val) (breakpoint A C (k.val + 1)) = 0 := by
            intro o ho
            simp only [S_tk, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at ho
            have ho_tiny : o.1 ∈ inst.tinyJobs ε α := ho.1
            have ho_mach : inst.mach o = t := ho.2
            have hα_pos : 0 < α := lt_of_lt_of_le (pow_pos hε _) hα_lo
            have h_ne_job : o.1 ≠ o_B.1 := by
              intro heq
              have h_tiny_le : inst.jobLength o.1 ≤ α * ε * inst.Pmax :=
                (Finset.mem_filter.mp ho_tiny).2
              have h_big_le : α * inst.Pmax ≤ inst.jobLength o_B.1 :=
                (Finset.mem_filter.mp ho_B_big).2
              rw [heq] at h_tiny_le
              have hαP : 0 < α * inst.Pmax := mul_pos hα_pos hP
              have h_strict : α * ε * inst.Pmax < α * inst.Pmax := by
                calc α * ε * inst.Pmax = ε * (α * inst.Pmax) := by ring
                  _ < 1 * (α * inst.Pmax) := mul_lt_mul_of_pos_right hε1 hαP
                  _ = α * inst.Pmax := one_mul _
              linarith
            have h_ne_op : o ≠ o_B := fun h => h_ne_job (congrArg Sigma.fst h)
            have h_disj := hσ_feas.machine_disjoint o o_B
              (Finset.mem_union_right _ ho_tiny) (Finset.mem_union_left _ ho_B_big)
              h_ne_op (by rw [ho_mach, ho_B_mach])
            rcases h_disj with h_left | h_right
            · exact overlap_eq_zero_of_le_left (le_trans h_left h_cont.1)
            · exact overlap_eq_zero_of_le_right (le_trans h_cont.2 h_right)
          rw [Finset.sum_eq_zero h_zero_sum]
        · unfold intervalLength
          let a := breakpoint A C k.val
          let b := breakpoint A C (k.val + 1)
          have hab : a ≤ b := breakpoint_step_le A C hA0 hAC hC0 k.val
          let u : inst.Op → ℝ := fun o => min b (max a (σ o))
          let v : inst.Op → ℝ := fun o => min b (max a (σ o + inst.proc o))
          have h_clamp : ∀ o ∈ S_tk,
              overlap (σ o) (σ o + inst.proc o) a b = v o - u o := by
            intro o _
            have h_p : σ o ≤ σ o + inst.proc o := le_add_of_nonneg_right (inst.p_nonneg o.1 o.2)
            exact overlap_eq_clamp_right h_p hab
          rw [Finset.sum_congr rfl h_clamp]
          refine sum_disjoint_intervals_le S_tk u v a b hab ?_ ?_
          · intro o _
            have h_p : σ o ≤ σ o + inst.proc o := le_add_of_nonneg_right (inst.p_nonneg o.1 o.2)
            dsimp [u, v]
            refine ⟨?_, ?_, min_le_left _ _⟩
            · exact le_min hab (le_max_left _ _)
            · exact min_le_min_left b (max_le_max_left a h_p)
          · intro o₁ ho₁ o₂ ho₂ hne
            simp only [S_tk, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at ho₁ ho₂
            have h_mach_eq : inst.mach o₁ = inst.mach o₂ := by
              change inst.π o₁.1 o₁.2 = inst.π o₂.1 o₂.2
              rw [ho₁.2, ho₂.2]
            have h_disj := hσ_feas.machine_disjoint o₁ o₂
              (Finset.mem_union_right _ ho₁.1) (Finset.mem_union_right _ ho₂.1)
              hne h_mach_eq
            rcases h_disj with h1 | h2
            · left
              exact min_le_min_left b (max_le_max_left a h1)
            · right
              exact min_le_min_left b (max_le_max_left a h2)
      · intro j _ K _
        exact Finset.prod_nonneg (fun i _ => inst.opWeight_nonneg A C σ j i (K i))

end JobShopLTAS.Core

theorem solution {m n : ℕ} (inst : JobShopLTAS.Core.Instance m n) (ε α : ℝ)
    (hm : 2 ≤ m) (hμ : 1 ≤ inst.maxOps) (hε : 0 < ε) (hε1 : ε < 1)
    (hα_lo : ε ^ ⌈(m : ℝ) / ε⌉₊ ≤ α) (hα_hi : α ≤ ε) (hP : 0 < inst.Pmax) :
    ∃ σ : inst.Op → ℝ, inst.IsBigSchedule ε α σ ∧
      inst.LPFeasible ε α σ (inst.restrictedOpt ε α) :=
  JobShopLTAS.Core.lemma1_interval_lp_feasible inst ε α hm hμ hε hε1 hα_lo hα_hi hP

