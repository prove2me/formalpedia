-- Prove2me | solution 1 for KelsoCrawford.FirmOptimal.salary_adjustment_firm_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T17:25:00.7599+00:00
-- url     : https://prove2.me/submissions/5fc7a3bc-ef87-4ba3-9db5-b4b71eb58b3d

import Mathlib
import Definitions.Def_KelsoCrawford_FirmOptimal_Model
import Definitions.Def_KelsoCrawford_FirmOptimal_Process
import Definitions.Def_KelsoCrawford_FirmOptimal_NoTies

set_option autoImplicit false

namespace KCFO338

open KelsoCrawford.FirmOptimal
open KelsoCrawford.Process (profit IsDemanded GrossSubstitutesOn)

section Generic

variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

set_option linter.unusedSectionVars false

structure RunFacts (M : Market W F) (δ : ℝ) (ρ : Run W F) : Prop where
  sal0 : ρ.sal 0 = M.σ
  off0 : ρ.offers 0 = fun _ => Finset.univ
  dem : ∀ t j, IsDemanded (M.y j) (fun i => ρ.sal (t + 1) i j) (ρ.offers (t + 1) j)
  keep : ∀ t j i, i ∈ ρ.offers t j → ¬ ρ.Rejects t i j → i ∈ ρ.offers (t + 1) j
  choice_mem : ∀ t i, (∃ j, i ∈ ρ.offers t j) → i ∈ ρ.offers t (ρ.choice t i)
  choice_max : ∀ t i k, i ∈ ρ.offers t k →
    M.u i k (ρ.sal t i k) ≤ M.u i (ρ.choice t i) (ρ.sal t i (ρ.choice t i))
  salR : ∀ t i j, ρ.Rejects t i j → ρ.sal (t + 1) i j = ρ.sal t i j + δ
  salN : ∀ t i j, ¬ ρ.Rejects t i j → ρ.sal (t + 1) i j = ρ.sal t i j

theorem rejects_iff (ρ : Run W F) (t : ℕ) (i : W) (j : F) :
    ρ.Rejects t i j ↔ i ∈ ρ.offers t j ∧ ρ.choice t i ≠ j := Iff.rfl

theorem RunFacts.of {M : Market W F} {δ : ℝ} {ρ : Run W F} (h : M.IsRun δ ρ) :
    RunFacts M δ ρ := by
  unfold Market.IsRun Market.IsRunFrom at h
  obtain ⟨⟨h0, ho0⟩, hdem, hch, hsal⟩ := h
  refine ⟨h0, ho0, fun t j => (hdem t j).1, ?_, fun t i hi => (hch t i hi).1, ?_, ?_, ?_⟩
  · intro t j i hi hr
    classical
    exact (hdem t j).2 (Finset.mem_filter.mpr ⟨hi, hr⟩)
  · intro t i k hk
    exact (hch t i ⟨k, hk⟩).2 k hk
  · intro t i j hr
    rw [hsal t i j, if_pos hr]
  · intro t i j hr
    rw [hsal t i j, if_neg hr]

/-- utility of the offer a worker holds at round `t` -/
def held (ρ : Run W F) (M : Market W F) (t : ℕ) (i : W) : ℝ :=
  M.u i (ρ.choice t i) (ρ.sal t i (ρ.choice t i))

theorem has_offer [Nonempty F] {M : Market W F} {δ : ℝ} {ρ : Run W F}
    (R : RunFacts M δ ρ) : ∀ t i, ∃ j, i ∈ ρ.offers t j := by
  intro t
  induction t with
  | zero =>
    intro i
    obtain ⟨j⟩ := ‹Nonempty F›
    exact ⟨j, by rw [R.off0]; exact Finset.mem_univ _⟩
  | succ t ih =>
    intro i
    refine ⟨ρ.choice t i, R.keep t _ i (R.choice_mem t i (ih i)) ?_⟩
    intro h
    exact ((rejects_iff ρ t i _).mp h).2 rfl

theorem sal_grid {M : Market W F} {δ : ℝ} {ρ : Run W F} (R : RunFacts M δ ρ) :
    ∀ t i j, ∃ n : ℕ, ρ.sal t i j = M.σ i j + n * δ := by
  intro t
  induction t with
  | zero => intro i j; exact ⟨0, by rw [R.sal0]; simp⟩
  | succ t ih =>
    intro i j
    obtain ⟨n, hn⟩ := ih i j
    by_cases hr : ρ.Rejects t i j
    · exact ⟨n + 1, by rw [R.salR t i j hr, hn]; push_cast; ring⟩
    · exact ⟨n, by rw [R.salN t i j hr, hn]⟩

theorem sal_le_succ {M : Market W F} {δ : ℝ} {ρ : Run W F} (hδ : 0 < δ)
    (R : RunFacts M δ ρ) (t : ℕ) (i : W) (j : F) : ρ.sal t i j ≤ ρ.sal (t + 1) i j := by
  by_cases hr : ρ.Rejects t i j
  · rw [R.salR t i j hr]; linarith
  · rw [R.salN t i j hr]

theorem sigma_le_sal {M : Market W F} {δ : ℝ} {ρ : Run W F} (hδ : 0 < δ)
    (R : RunFacts M δ ρ) (t : ℕ) (i : W) (j : F) : M.σ i j ≤ ρ.sal t i j := by
  obtain ⟨n, hn⟩ := sal_grid R t i j
  rw [hn]
  have : (0 : ℝ) ≤ n * δ := by positivity
  linarith

theorem held_le_succ [Nonempty F] {M : Market W F} {δ : ℝ} {ρ : Run W F}
    (R : RunFacts M δ ρ) (t : ℕ) (i : W) : held ρ M t i ≤ held ρ M (t + 1) i := by
  have hmem := R.choice_mem t i (has_offer R t i)
  have hnr : ¬ ρ.Rejects t i (ρ.choice t i) := fun h => ((rejects_iff ρ t i _).mp h).2 rfl
  have h1 := R.keep t _ i hmem hnr
  have h2 := R.choice_max (t + 1) i (ρ.choice t i) h1
  rw [R.salN t i _ hnr] at h2
  exact h2

theorem grid_step {s0 δ r s : ℝ} (hδ : 0 < δ) {a b : ℕ} (hr : r = s0 + a * δ)
    (hs : s = s0 + b * δ) (h : r < s) : r + δ ≤ s := by
  have hab : (a : ℝ) < b := by
    by_contra hc
    push Not at hc
    have : (b : ℝ) * δ ≤ a * δ := mul_le_mul_of_nonneg_right hc hδ.le
    linarith
  have hab' : a + 1 ≤ b := by exact_mod_cast hab
  have hab'' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab'
  have : ((a : ℝ) + 1) * δ ≤ b * δ := mul_le_mul_of_nonneg_right hab'' hδ.le
  rw [hr, hs]
  nlinarith

theorem grid_cases {s0 δ r s : ℝ} (hδ : 0 < δ) {a b : ℕ} (hr : r = s0 + a * δ)
    (hs : s = s0 + b * δ) (h : r < s + δ) : r < s ∨ r = s := by
  rcases lt_trichotomy r s with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · have := grid_step hδ hs hr h1
    linarith

theorem rej_bound [Nonempty F] {M : Market W F} {δ : ℝ} {ρ : Run W F} (hδ : 0 < δ)
    (R : RunFacts M δ ρ) : ∀ t i j r, r ∈ M.grid δ i j → r < ρ.sal t i j →
      M.u i j r ≤ held ρ M t i := by
  intro t
  induction t with
  | zero =>
    intro i j r hr hlt
    exfalso
    obtain ⟨k, hk⟩ := hr
    rw [R.sal0] at hlt
    have : (0 : ℝ) ≤ k * δ := by positivity
    linarith
  | succ t ih =>
    intro i j r hr hlt
    have hmono := held_le_succ R t i
    by_cases hrj : ρ.Rejects t i j
    · rw [R.salR t i j hrj] at hlt
      obtain ⟨a, ha⟩ := hr
      obtain ⟨b, hb⟩ := sal_grid R t i j
      rcases grid_cases hδ ha hb hlt with h | h
      · exact (ih i j r ⟨a, ha⟩ h).trans hmono
      · rw [h]
        exact (R.choice_max t i j ((rejects_iff ρ t i j).mp hrj).1).trans hmono
    · rw [R.salN t i j hrj] at hlt
      exact (ih i j r hr hlt).trans hmono

theorem profit_le_insert (y : Finset W → ℝ) (s : W → ℝ) (C : Finset W) (a : W) (ha : a ∉ C)
    (hMP : 0 ≤ y (insert a C) - y C - s a) : profit y C s ≤ profit y (insert a C) s := by
  unfold profit
  rw [Finset.sum_insert ha]
  linarith

theorem univ_demanded {M : Market W F} (hMP : M.MP) (j : F) :
    IsDemanded (M.y j) (fun i => M.σ i j) Finset.univ := by
  intro C
  have key : ∀ D : Finset W, profit (M.y j) C (fun i => M.σ i j) ≤
      profit (M.y j) (C ∪ D) (fun i => M.σ i j) := by
    intro D
    induction D using Finset.induction_on with
    | empty => simp
    | @insert a D haD ih =>
      rw [Finset.union_insert]
      by_cases hmem : a ∈ C ∪ D
      · rwa [Finset.insert_eq_of_mem hmem]
      · exact ih.trans (profit_le_insert _ _ _ a hmem (hMP a j _ hmem))
  have := key Finset.univ
  rwa [Finset.union_eq_right.mpr (Finset.subset_univ C)] at this

theorem dem_all {M : Market W F} {δ : ℝ} {ρ : Run W F} (hMP : M.MP)
    (R : RunFacts M δ ρ) : ∀ t j, IsDemanded (M.y j) (fun i => ρ.sal t i j) (ρ.offers t j)
  | 0, j => by
    have h1 : ρ.offers 0 j = Finset.univ := by rw [R.off0]
    have h2 : (fun i => ρ.sal 0 i j) = fun i => M.σ i j := by rw [R.sal0]
    rw [h1, h2]
    exact univ_demanded hMP j
  | t + 1, j => R.dem t j

theorem stopped_iff [Nonempty F] {M : Market W F} {δ : ℝ} {ρ : Run W F}
    (R : RunFacts M δ ρ) {T : ℕ} (hT : ρ.Stopped T) (i : W) (j : F) :
    i ∈ ρ.offers T j ↔ ρ.choice T i = j := by
  constructor
  · intro hi
    by_contra hne
    exact hT i j ((rejects_iff ρ T i j).mpr ⟨hi, hne⟩)
  · rintro rfl
    exact R.choice_mem T i (has_offer R T i)

theorem hired_eq [Nonempty F] {M : Market W F} {δ : ℝ} {ρ : Run W F}
    (R : RunFacts M δ ρ) {T : ℕ} (hT : ρ.Stopped T) (j : F) :
    (ρ.outcome T).hired j = ρ.offers T j := by
  ext i
  rw [stopped_iff R hT i j]
  simp only [Allocation.hired, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem outcome_profit [Nonempty F] {M : Market W F} {δ : ℝ} {ρ : Run W F}
    (R : RunFacts M δ ρ) {T : ℕ} (hT : ρ.Stopped T) (j : F) :
    profit (M.y j) ((ρ.outcome T).hired j) (ρ.outcome T).sal =
      profit (M.y j) (ρ.offers T j) (fun i => ρ.sal T i j) := by
  rw [hired_eq R hT j]
  unfold profit
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have h := (stopped_iff R hT i j).mp hi
  show ρ.sal T i (ρ.choice T i) = ρ.sal T i j
  rw [h]

theorem outcome_core [Nonempty F] {M : Market W F} {δ : ℝ} {ρ : Run W F} (hδ : 0 < δ)
    (hMP : M.MP) (hNFL : M.NFL) (R : RunFacts M δ ρ) {T : ℕ} (hT : ρ.Stopped T) :
    M.IsCore (M.grid δ) (ρ.outcome T) := by
  refine ⟨⟨fun i => sigma_le_sal hδ R T i _, fun j => ?_⟩, fun i => ?_, ?_⟩
  · rw [outcome_profit R hT j]
    have h := dem_all hMP R T j ∅
    have h0 : profit (M.y j) ∅ (fun i => ρ.sal T i j) = 0 := by
      simp [profit, hNFL j]
    linarith
  · obtain ⟨n, hn⟩ := sal_grid R T i (ρ.choice T i)
    exact ⟨n, hn⟩
  · rintro ⟨j, C, r, hrC, hu, hp⟩
    rw [outcome_profit R hT j] at hp
    have hge : ∀ i ∈ C, ρ.sal T i j ≤ r i := by
      intro i hi
      by_contra hlt
      push Not at hlt
      have h1 := rej_bound hδ R T i j (r i) (hrC i hi) hlt
      have h2 := hu i hi
      have h3 : M.u i ((ρ.outcome T).assign i) ((ρ.outcome T).sal i) = held ρ M T i := rfl
      linarith
    have h1 : profit (M.y j) C r ≤ profit (M.y j) C (fun i => ρ.sal T i j) := by
      unfold profit
      have := Finset.sum_le_sum hge
      linarith
    have h2 := dem_all hMP R T j C
    linarith

theorem sal_le_marg {M : Market W F} {δ : ℝ} {ρ : Run W F} (hMP : M.MP) (R : RunFacts M δ ρ)
    (t : ℕ) (i : W) (j : F) (hi : i ∈ ρ.offers t j) :
    ρ.sal t i j ≤ ∑ C : Finset W, |M.y j C - M.y j (C.erase i)| := by
  have h := dem_all hMP R t j ((ρ.offers t j).erase i)
  unfold profit at h
  have h2 := Finset.add_sum_erase (ρ.offers t j) (fun k => ρ.sal t k j) hi
  have h3 : M.y j (ρ.offers t j) - M.y j ((ρ.offers t j).erase i) ≤
      ∑ C : Finset W, |M.y j C - M.y j (C.erase i)| :=
    (le_abs_self _).trans (Finset.single_le_sum
      (f := fun C : Finset W => |M.y j C - M.y j (C.erase i)|)
      (fun C _ => abs_nonneg _) (Finset.mem_univ _))
  linarith

/-- an a priori bound on every permitted salary of a run -/
def bnd (M : Market W F) (δ : ℝ) (i : W) (j : F) : ℝ :=
  |M.σ i j| + (∑ C : Finset W, |M.y j C - M.y j (C.erase i)|) + δ

theorem sal_bound {M : Market W F} {δ : ℝ} {ρ : Run W F} (hδ : 0 < δ) (hMP : M.MP)
    (R : RunFacts M δ ρ) : ∀ t i j, ρ.sal t i j ≤ bnd M δ i j := by
  intro t
  induction t with
  | zero =>
    intro i j
    rw [R.sal0]
    unfold bnd
    have h1 := le_abs_self (M.σ i j)
    have h2 : 0 ≤ ∑ C : Finset W, |M.y j C - M.y j (C.erase i)| :=
      Finset.sum_nonneg (fun C _ => abs_nonneg _)
    linarith
  | succ t ih =>
    intro i j
    by_cases hr : ρ.Rejects t i j
    · rw [R.salR t i j hr]
      have h1 := sal_le_marg hMP R t i j ((rejects_iff ρ t i j).mp hr).1
      unfold bnd
      have h2 := abs_nonneg (M.σ i j)
      linarith
    · rw [R.salN t i j hr]
      exact ih i j

/-- total of all permitted salaries at round `t` -/
noncomputable def Phi (ρ : Run W F) (t : ℕ) : ℝ := ∑ p : W × F, ρ.sal t p.1 p.2

theorem exists_stopped {M : Market W F} {δ : ℝ} {ρ : Run W F} (hδ : 0 < δ) (hMP : M.MP)
    (R : RunFacts M δ ρ) : ∃ T, ρ.Stopped T := by
  by_contra hne
  push Not at hne
  have hstep : ∀ t, Phi ρ t + δ ≤ Phi ρ (t + 1) := by
    intro t
    have hns := hne t
    unfold Run.Stopped at hns
    push Not at hns
    obtain ⟨i, j, hij⟩ := hns
    have hp : ∀ p : W × F, ρ.sal (t + 1) p.1 p.2 =
        ρ.sal t p.1 p.2 + (if ρ.Rejects t p.1 p.2 then δ else 0) := by
      intro p
      by_cases hr : ρ.Rejects t p.1 p.2
      · rw [R.salR t _ _ hr, if_pos hr]
      · rw [R.salN t _ _ hr, if_neg hr, add_zero]
    have hge : δ ≤ ∑ p : W × F, (if ρ.Rejects t p.1 p.2 then δ else 0) := by
      calc δ = (fun p : W × F => if ρ.Rejects t p.1 p.2 then δ else 0) (i, j) := by
              simp [hij]
        _ ≤ _ := Finset.single_le_sum
              (f := fun p : W × F => if ρ.Rejects t p.1 p.2 then δ else 0)
              (fun p _ => by by_cases h : ρ.Rejects t p.1 p.2 <;> simp [h, hδ.le])
              (Finset.mem_univ (i, j))
    unfold Phi
    rw [Finset.sum_congr rfl (fun p _ => hp p), Finset.sum_add_distrib]
    linarith
  have hlow : ∀ t : ℕ, Phi ρ 0 + t * δ ≤ Phi ρ t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := hstep t
      push_cast
      linarith
  have hup : ∀ t, Phi ρ t ≤ ∑ p : W × F, bnd M δ p.1 p.2 := by
    intro t
    exact Finset.sum_le_sum (fun p _ => sal_bound hδ hMP R t p.1 p.2)
  obtain ⟨n, hn⟩ := exists_nat_gt ((∑ p : W × F, bnd M δ p.1 p.2 - Phi ρ 0) / δ)
  have h1 := hlow n
  have h2 := hup n
  rw [div_lt_iff₀ hδ] at hn
  linarith

/-! ### Firm optimality and strict core (Theorem 4) -/

theorem marg_bound (y : Finset W → ℝ) (p : W → ℝ) (C : Finset W) (hC : IsDemanded y p C)
    (l : W) (hl : l ∈ C) : p l ≤ ∑ D : Finset W, |y D - y (D.erase l)| := by
  have h := hC (C.erase l)
  unfold profit at h
  have h2 := Finset.add_sum_erase C p hl
  have h3 : y C - y (C.erase l) ≤ ∑ D : Finset W, |y D - y (D.erase l)| :=
    (le_abs_self _).trans (Finset.single_le_sum
      (f := fun D : Finset W => |y D - y (D.erase l)|)
      (fun D _ => abs_nonneg _) (Finset.mem_univ _))
  linarith

/-- a permitted salary above every a priori bound -/
noncomputable def hiN (M : Market W F) (δ : ℝ) (x : W) (k : F) : ℕ :=
  ⌈(bnd M δ x k - M.σ x k) / δ⌉₊

theorem hi_ge {M : Market W F} {δ : ℝ} (hδ : 0 < δ) (x : W) (k : F) :
    bnd M δ x k ≤ M.σ x k + (hiN M δ x k : ℝ) * δ := by
  have h := Nat.le_ceil ((bnd M δ x k - M.σ x k) / δ)
  rw [div_le_iff₀ hδ] at h
  unfold hiN
  linarith

theorem outcome_strict_core [Nonempty F] {M : Market W F} {δ : ℝ} {ρ : Run W F} (hδ : 0 < δ)
    (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL) (hNTW : M.NTW δ) (hNTF : M.NTF δ)
    (R : RunFacts M δ ρ) {T : ℕ} (hT : ρ.Stopped T) :
    M.IsStrictCore (M.grid δ) (ρ.outcome T) := by
  have hcore := outcome_core hδ hMP hNFL R hT
  refine ⟨hcore.1, hcore.2.1, ?_⟩
  rintro ⟨j, C, r, hrC, hwu, hp, hstrict⟩
  have hA : ∀ i, M.u i ((ρ.outcome T).assign i) ((ρ.outcome T).sal i) = held ρ M T i :=
    fun i => rfl
  have hge : ∀ i ∈ C, ρ.sal T i j ≤ r i := by
    intro i hi
    by_contra hlt
    push Not at hlt
    have h1 := rej_bound hδ R T i j (r i) (hrC i hi) hlt
    have h2 := hwu i hi
    rw [hA] at h2
    have heq : M.u i j (r i) = held ρ M T i := le_antisymm h1 h2
    by_cases hc : ρ.choice T i = j
    · have h3 : held ρ M T i = M.u i j (ρ.sal T i j) := by unfold held; rw [hc]
      have hsm := (hu i j).1 hlt
      linarith
    · exact hNTW _ hcore i j (Ne.symm hc) (r i) (hrC i hi) heq.symm
  have h1 : profit (M.y j) C r ≤ profit (M.y j) C (fun i => ρ.sal T i j) := by
    unfold profit
    have := Finset.sum_le_sum hge
    linarith
  have h2 := dem_all hMP R T j C
  have h3 := outcome_profit R hT j
  rw [h3] at hp hstrict
  have heqp : profit (M.y j) C r = profit (M.y j) C (fun i => ρ.sal T i j) := by linarith
  have hsum : ∑ i ∈ C, ρ.sal T i j = ∑ i ∈ C, r i := by
    unfold profit at heqp
    linarith
  have hreq : ∀ i ∈ C, ρ.sal T i j = r i := (Finset.sum_eq_sum_iff_of_le hge).mp hsum
  rcases hstrict with ⟨i, hi, hlt⟩ | hlt
  · rw [hA, ← hreq i hi] at hlt
    by_cases hc : ρ.choice T i = j
    · unfold held at hlt
      rw [hc] at hlt
      exact lt_irrefl _ hlt
    · have hiC : i ∉ ρ.offers T j := fun h => hc ((stopped_iff R hT i j).mp h)
      have hne : C ≠ (ρ.outcome T).hired j := by
        intro hE
        rw [hE, hired_eq R hT j] at hi
        exact hiC hi
      have hgrid : (fun x => ρ.sal T x j) ∈ M.gridVectors δ j := fun x => sal_grid R T x j
      apply hNTF _ hcore j C ⟨i, hi⟩ hne _ hgrid
      rw [outcome_profit R hT j]
      linarith
  · linarith

theorem strict_to_core {M : Market W F} {δ : ℝ} {A' : Allocation W F}
    (hA' : M.IsStrictCore (M.grid δ) A') : M.IsCore (M.grid δ) A' :=
  ⟨hA'.1, hA'.2.1, fun ⟨j, C, r, h1, h2, h3⟩ =>
    hA'.2.2 ⟨j, C, r, h1, fun i hi => (h2 i hi).le, h3.le, Or.inr h3⟩⟩

theorem fo_inv [Nonempty F] {M : Market W F} {δ : ℝ} {ρ : Run W F} (hδ : 0 < δ)
    (hMP : M.MP) (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j))
    (hNTW : M.NTW δ) (R : RunFacts M δ ρ) (A' : Allocation W F)
    (hA' : M.IsStrictCore (M.grid δ) A') :
    ∀ t i, ρ.sal t i (A'.assign i) ≤ A'.sal i := by
  have hA'core := strict_to_core hA'
  intro t
  induction t with
  | zero => intro i; rw [R.sal0]; exact hA'.1.1 i
  | succ t ih =>
    intro i
    by_cases hr : ρ.Rejects t i (A'.assign i)
    swap
    · rw [R.salN t i _ hr]; exact ih i
    rw [R.salR t i _ hr]
    obtain ⟨a, ha⟩ := sal_grid R t i (A'.assign i)
    obtain ⟨b, hb⟩ := hA'.2.1 i
    rcases lt_or_eq_of_le (ih i) with hlt | heq
    · exact grid_step hδ ha hb hlt
    exfalso
    obtain ⟨hij, hk⟩ := (rejects_iff ρ t i (A'.assign i)).mp hr
    have hik0 := R.choice_mem t i ⟨A'.assign i, hij⟩
    have hu1 := R.choice_max t i (A'.assign i) hij
    obtain ⟨k, hkdef⟩ : ∃ k, ρ.choice t i = k := ⟨_, rfl⟩
    rw [hkdef] at hik0 hu1 hk
    have hstr : M.u i (A'.assign i) (A'.sal i) < M.u i k (ρ.sal t i k) := by
      have hne := hNTW A' hA'core i k hk (ρ.sal t i k) (sal_grid R t i k)
      rw [← heq] at hne ⊢
      exact lt_of_le_of_ne hu1 hne
    let p : W → ℝ := fun x => ρ.sal t x k
    let p' : W → ℝ := fun x => if A'.assign x = k then A'.sal x else
      if x = i then ρ.sal t x k else M.σ x k + (hiN M δ x k : ℝ) * δ
    have hp : p ∈ M.gridVectors δ k := fun x => sal_grid R t x k
    have hp' : p' ∈ M.gridVectors δ k := by
      intro x
      by_cases h1 : A'.assign x = k
      · have := hA'.2.1 x
        rw [h1] at this
        simp only [p', if_pos h1]
        exact this
      · by_cases h2 : x = i
        · simp only [p', if_neg h1, if_pos h2]
          exact sal_grid R t x k
        · simp only [p', if_neg h1, if_neg h2]
          exact ⟨hiN M δ x k, rfl⟩
    have hle : p ≤ p' := by
      intro x
      by_cases h1 : A'.assign x = k
      · simp only [p', p, if_pos h1]
        have := ih x
        rw [h1] at this
        exact this
      · by_cases h2 : x = i
        · simp only [p', p, if_neg h1, if_pos h2]
          exact le_rfl
        · simp only [p', p, if_neg h1, if_neg h2]
          exact (sal_bound hδ hMP R t x k).trans (hi_ge hδ x k)
    obtain ⟨C', hC', hsub⟩ := hGS k p hp p' hp' hle _ (dem_all hMP R t k)
    have hiA : A'.assign i ≠ k := fun h => hk h.symm
    have hp'i : p' i = p i := by simp only [p', p, if_neg hiA, if_true]
    have hiC' : i ∈ C' := hsub (Finset.mem_filter.mpr ⟨hik0, hp'i⟩)
    have hC'sub : ∀ x ∈ C', A'.assign x = k ∨ x = i := by
      intro x hx
      by_contra hc
      push Not at hc
      have h1 := marg_bound (M.y k) p' C' hC' x hx
      have h2 : p' x = M.σ x k + (hiN M δ x k : ℝ) * δ := by
        simp only [p', if_neg hc.1, if_neg hc.2]
      have h3 := hi_ge (M := M) hδ x k
      have h4 : (∑ D : Finset W, |M.y k D - M.y k (D.erase x)|) + δ ≤ bnd M δ x k := by
        unfold bnd
        have := abs_nonneg (M.σ x k)
        linarith
      linarith
    apply hA'.2.2
    refine ⟨k, C', p', fun x _ => hp' x, ?_, ?_, Or.inl ⟨i, hiC', ?_⟩⟩
    · intro x hx
      rcases hC'sub x hx with h1 | h1
      · have h5 : p' x = A'.sal x := by simp only [p', if_pos h1]
        exact le_of_eq (by rw [h5, h1])
      · subst h1
        rw [hp'i]
        exact hstr.le
    · have hA'p : profit (M.y k) (A'.hired k) A'.sal = profit (M.y k) (A'.hired k) p' := by
        unfold profit
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        have h1 : A'.assign x = k := by simpa [Allocation.hired] using hx
        simp only [p', if_pos h1]
      rw [hA'p]
      exact hC' _
    · rw [hp'i]
      exact hstr

theorem fo_profit [Nonempty F] {M : Market W F} {δ : ℝ} {ρ : Run W F} (hδ : 0 < δ)
    (hMP : M.MP) (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j))
    (hNTW : M.NTW δ) (R : RunFacts M δ ρ) (A' : Allocation W F)
    (hA' : M.IsStrictCore (M.grid δ) A') {T : ℕ} (hT : ρ.Stopped T) (j : F) :
    profit (M.y j) (A'.hired j) A'.sal ≤
      profit (M.y j) ((ρ.outcome T).hired j) (ρ.outcome T).sal := by
  rw [outcome_profit R hT j]
  have hinv := fo_inv hδ hMP hGS hNTW R A' hA' T
  have h1 : profit (M.y j) (A'.hired j) A'.sal ≤
      profit (M.y j) (A'.hired j) (fun x => ρ.sal T x j) := by
    unfold profit
    have : ∑ x ∈ A'.hired j, ρ.sal T x j ≤ ∑ x ∈ A'.hired j, A'.sal x := by
      apply Finset.sum_le_sum
      intro x hx
      have h1 : A'.assign x = j := by simpa [Allocation.hired] using hx
      have := hinv x
      rw [h1] at this
      exact this
    linarith
  exact h1.trans (dem_all hMP R T j _)

end Generic

end KCFO338

open KelsoCrawford.FirmOptimal in
theorem solution
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) (M.gridVectors δ j))
    (hNTW : M.NTW δ) (hNTF : M.NTF δ) :
    ∀ ρ : Run W F, M.IsRun δ ρ →
      (∃ T, ρ.Stopped T) ∧
      ∀ T, ρ.Stopped T →
        M.IsStrictCore (M.grid δ) (ρ.outcome T) ∧
        ∀ A' : Allocation W F, M.IsStrictCore (M.grid δ) A' →
          ∀ j, KelsoCrawford.Process.profit (M.y j) (A'.hired j) A'.sal ≤
            KelsoCrawford.Process.profit (M.y j) ((ρ.outcome T).hired j) (ρ.outcome T).sal := by
  intro ρ hρ
  have R := KCFO338.RunFacts.of hρ
  exact ⟨KCFO338.exists_stopped hδ hMP R, fun T hT =>
    ⟨KCFO338.outcome_strict_core hδ hu hMP hNFL hNTW hNTF R hT,
      fun A' hA' j => KCFO338.fo_profit hδ hMP hGS hNTW R A' hA' hT j⟩⟩
