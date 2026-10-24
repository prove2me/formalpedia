-- Prove2me | solution 1 for KelsoCrawford.Process.salary_adjustment_converges_to_discrete_core
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T01:40:25.291817+00:00
-- url     : https://prove2.me/submissions/33f23881-4d79-4667-9404-5d0d615a9fd0

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model
import Definitions.Def_KelsoCrawford_Process_Process

set_option autoImplicit false

namespace KCP197e

open KelsoCrawford.Process

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

/-! ### A run exists -/

/-- R3 tie-breaking: a favourite among the offers held, if any. -/
noncomputable def chooseFav [Nonempty F] (M : Market W F) (s : W → F → ℝ) (O : F → Finset W)
    (i : W) : F :=
  if h : (Finset.univ.filter (fun j => i ∈ O j)).Nonempty then
    Classical.choose (Finset.exists_max_image _ (fun j => M.u i j (s i j)) h)
  else Classical.arbitrary F

theorem chooseFav_spec [Nonempty F] (M : Market W F) (s : W → F → ℝ) (O : F → Finset W) (i : W)
    (h : ∃ j, i ∈ O j) :
    i ∈ O (chooseFav M s O i) ∧ ∀ k, i ∈ O k →
      M.u i k (s i k) ≤ M.u i (chooseFav M s O i) (s i (chooseFav M s O i)) := by
  have hne : (Finset.univ.filter (fun j => i ∈ O j)).Nonempty := by
    obtain ⟨j, hj⟩ := h
    exact ⟨j, by simp [hj]⟩
  have hs := Classical.choose_spec (Finset.exists_max_image _ (fun j => M.u i j (s i j)) hne)
  have hc : chooseFav M s O i =
      Classical.choose (Finset.exists_max_image _ (fun j => M.u i j (s i j)) hne) := by
    unfold chooseFav
    rw [dif_pos hne]
  rw [hc]
  exact ⟨(Finset.mem_filter.mp hs.1).2, fun k hk => hs.2 k (by simp [hk])⟩

noncomputable def nextSal (δ : ℝ) (s : W → F → ℝ) (O : F → Finset W) (c : W → F) :
    W → F → ℝ :=
  fun i j => if i ∈ O j ∧ c i ≠ j then s i j + δ else s i j

noncomputable def nextOffers (M : Market W F) (s' : W → F → ℝ) (O : F → Finset W) (c : W → F) :
    F → Finset W := fun j =>
  Classical.epsilon (fun C : Finset W => IsDemanded (M.y j) (fun i => s' i j) C ∧
    (O j).filter (fun i => ¬ (i ∈ O j ∧ c i ≠ j)) ⊆ C)

noncomputable def step [Nonempty F] (M : Market W F) (δ : ℝ)
    (st : (W → F → ℝ) × (F → Finset W)) : (W → F → ℝ) × (F → Finset W) :=
  (nextSal δ st.1 st.2 (chooseFav M st.1 st.2),
   nextOffers M (nextSal δ st.1 st.2 (chooseFav M st.1 st.2)) st.2 (chooseFav M st.1 st.2))

noncomputable def stateSeq [Nonempty F] (M : Market W F) (δ : ℝ) :
    ℕ → (W → F → ℝ) × (F → Finset W)
  | 0 => (M.σ, fun _ => Finset.univ)
  | t + 1 => step M δ (stateSeq M δ t)

noncomputable def theRun [Nonempty F] (M : Market W F) (δ : ℝ) : Run W F :=
  ⟨fun t => (stateSeq M δ t).1, fun t => (stateSeq M δ t).2,
   fun t => chooseFav M (stateSeq M δ t).1 (stateSeq M δ t).2⟩

theorem theRun_sal [Nonempty F] (M : Market W F) (δ : ℝ) (t : ℕ) (i : W) (j : F) :
    (theRun M δ).sal (t + 1) i j =
      if i ∈ (theRun M δ).offers t j ∧ (theRun M δ).choice t i ≠ j then
        (theRun M δ).sal t i j + δ else (theRun M δ).sal t i j := rfl

theorem theRun_offers [Nonempty F] (M : Market W F) (δ : ℝ) (t : ℕ) :
    (theRun M δ).offers (t + 1) =
      nextOffers M ((theRun M δ).sal (t + 1)) ((theRun M δ).offers t) ((theRun M δ).choice t) :=
  rfl

theorem theRun_inv [Nonempty F] (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hMP : M.MP)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) : ∀ t, ∀ j,
    (IsDemanded (M.y j) (fun i => (theRun M δ).sal t i j) ((theRun M δ).offers t j) ∧
      (fun i => (theRun M δ).sal t i j) ∈ M.gridVectors δ j) ∧
    (IsDemanded (M.y j) (fun i => (theRun M δ).sal (t + 1) i j) ((theRun M δ).offers (t + 1) j) ∧
      ((theRun M δ).offers t j).filter
        (fun i => ¬ (i ∈ (theRun M δ).offers t j ∧ (theRun M δ).choice t i ≠ j)) ⊆
        (theRun M δ).offers (t + 1) j) := by
  -- the step property, from the invariant at `t`
  have hstep : ∀ t j,
      (IsDemanded (M.y j) (fun i => (theRun M δ).sal t i j) ((theRun M δ).offers t j) ∧
        (fun i => (theRun M δ).sal t i j) ∈ M.gridVectors δ j) →
      ((fun i => (theRun M δ).sal (t + 1) i j) ∈ M.gridVectors δ j ∧
      (IsDemanded (M.y j) (fun i => (theRun M δ).sal (t + 1) i j) ((theRun M δ).offers (t + 1) j) ∧
      ((theRun M δ).offers t j).filter
        (fun i => ¬ (i ∈ (theRun M δ).offers t j ∧ (theRun M δ).choice t i ≠ j)) ⊆
        (theRun M δ).offers (t + 1) j)) := by
    intro t j ⟨hd, hg⟩
    have hg' : (fun i => (theRun M δ).sal (t + 1) i j) ∈ M.gridVectors δ j := by
      simp only [Market.gridVectors, Set.mem_ofPred_eq] at hg ⊢
      intro i
      obtain ⟨k, hk⟩ := hg i
      rw [theRun_sal]
      split_ifs
      · exact ⟨k + 1, by rw [hk]; push_cast; ring⟩
      · exact ⟨k, hk⟩
    have hle : (fun i => (theRun M δ).sal t i j) ≤ (fun i => (theRun M δ).sal (t + 1) i j) := by
      intro i
      show (theRun M δ).sal t i j ≤ (theRun M δ).sal (t + 1) i j
      rw [theRun_sal]
      split_ifs <;> linarith
    obtain ⟨C', hC', hsub⟩ := hGS j _ hg _ hg' hle _ hd
    have hex : ∃ C, IsDemanded (M.y j) (fun i => (theRun M δ).sal (t + 1) i j) C ∧
        ((theRun M δ).offers t j).filter
          (fun i => ¬ (i ∈ (theRun M δ).offers t j ∧ (theRun M δ).choice t i ≠ j)) ⊆ C := by
      refine ⟨C', hC', fun i hi => hsub ?_⟩
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, ?_⟩
      show (theRun M δ).sal (t + 1) i j = (theRun M δ).sal t i j
      rw [theRun_sal, if_neg hi.2]
    refine ⟨hg', ?_⟩
    rw [theRun_offers]
    exact Classical.epsilon_spec hex
  have hinv : ∀ t j,
      IsDemanded (M.y j) (fun i => (theRun M δ).sal t i j) ((theRun M δ).offers t j) ∧
        (fun i => (theRun M δ).sal t i j) ∈ M.gridVectors δ j := by
    intro t
    induction t with
    | zero =>
      intro j
      refine ⟨univ_demanded hMP j, ?_⟩
      simp only [Market.gridVectors, Set.mem_ofPred_eq]
      intro i
      exact ⟨0, by show M.σ i j = M.σ i j + ((0 : ℕ) : ℝ) * δ; simp⟩
    | succ t ih =>
      intro j
      have := hstep t j (ih j)
      exact ⟨this.2.1, this.1⟩
  intro t j
  exact ⟨hinv t j, (hstep t j (hinv t j)).2⟩

theorem theRun_isRun [Nonempty F] (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hMP : M.MP)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) : M.IsRun δ (theRun M δ) := by
  have hinv := theRun_inv M δ hδ hMP hGS
  unfold Market.IsRun Market.IsRunFrom
  refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro t j
    refine ⟨((hinv t j).2).1, ?_⟩
    intro i hi
    apply ((hinv t j).2).2
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2⟩
  · intro t i h
    exact chooseFav_spec M _ _ i h
  · intro t i j
    rw [theRun_sal]
    rfl

end Generic

end KCP197e

open KelsoCrawford.Process in
theorem solution
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) :
    (∃ ρ : Run W F, M.IsRun δ ρ) ∧
      ∀ ρ : Run W F, M.IsRun δ ρ →
        (∃ T : ℕ, ρ.Stopped T) ∧ ∀ T : ℕ, ρ.Stopped T → M.IsCore (M.grid δ) (ρ.outcome T) := by
  refine ⟨⟨KCP197e.theRun M δ, KCP197e.theRun_isRun M δ hδ hMP hGS⟩, fun ρ hρ => ?_⟩
  have R := KCP197e.RunFacts.of hρ
  exact ⟨KCP197e.exists_stopped hδ hMP R, fun T hT => KCP197e.outcome_core hδ hMP hNFL R hT⟩
