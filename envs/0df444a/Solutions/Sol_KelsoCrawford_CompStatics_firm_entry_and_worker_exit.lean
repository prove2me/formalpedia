-- Prove2me | solution 1 for KelsoCrawford.CompStatics.firm_entry_and_worker_exit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T09:32:40.29299+00:00
-- url     : https://prove2.me/submissions/67778fe1-28db-40a0-b79a-a2adf534476c

import Mathlib
import Definitions.Def_KelsoCrawford_CompStatics_Process

set_option autoImplicit false

namespace KCFA0cd

open KelsoCrawford.CompStatics
open KelsoCrawford.OneSided (profit IsDemanded GrossSubstitutesOn)

section Generic

variable {W F : Type} [Fintype W] [DecidableEq W]

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
  obtain ⟨h0, ho0, hdem, hch, hsal⟩ := h
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

theorem dem_in_hired [Nonempty F] {M : Market W F} {δ : ℝ} {ρ : Run W F} (hδ : 0 < δ)
    (h4 : M.Theorem4Conditions δ) (R : RunFacts M δ ρ) {T : ℕ} (hT : ρ.Stopped T)
    (k : F) (C : Finset W) (hC : IsDemanded (M.y k) (fun x => ρ.sal T x k) C)
    (i : W) (hi : i ∈ C) : ρ.choice T i = k := by
  obtain ⟨_, hMP, hNFL, _, _, hNTF⟩ := h4
  have hcore := outcome_core hδ hMP hNFL R hT
  by_contra hne
  have hCne : C ≠ (ρ.outcome T).hired k := by
    intro hEq
    rw [hEq, hired_eq R hT, stopped_iff R hT] at hi
    exact hne hi
  have hgrid : (fun x => ρ.sal T x k) ∈ M.gridVectors δ k := by
    intro x
    exact sal_grid R T x k
  apply hNTF _ hcore k C ⟨i, hi⟩ hCne _ hgrid
  rw [outcome_profit R hT k]
  exact le_antisymm (hC _) (dem_all hMP R T k C)

theorem below_lt [Nonempty F] {M : Market W F} {δ : ℝ} {ρ : Run W F} (hδ : 0 < δ)
    (h4 : M.Theorem4Conditions δ) (R : RunFacts M δ ρ) {T : ℕ} (hT : ρ.Stopped T)
    (i : W) (k : F) (hk : ρ.choice T i ≠ k) (r : ℝ) (hr : r ∈ M.grid δ i k)
    (hlt : r < ρ.sal T i k) : M.u i k r < held ρ M T i := by
  obtain ⟨_, hMP, hNFL, _, hNTW, _⟩ := h4
  have hcore := outcome_core hδ hMP hNFL R hT
  have h1 := rej_bound hδ R T i k r hr hlt
  have h2 := hNTW _ hcore i k (Ne.symm hk) r hr
  exact lt_of_le_of_ne h1 (fun h => h2 h.symm)

end Generic

section Cross

variable {W F : Type} [Fintype W] [DecidableEq W] [Nonempty F]

set_option linter.unusedSectionVars false

theorem fa_L1 {M : Market W F} {Mp : Market W (Option F)} {δ : ℝ} (hδ : 0 < δ)
    (hAug : IsFirmAugmentation M Mp) (hM : M.Theorem4Conditions δ)
    (hP : Mp.Theorem4Conditions δ) {ρ : Run W F} {ρp : Run W (Option F)}
    (R : RunFacts M δ ρ) (Rp : RunFacts Mp δ ρp) {Tp : ℕ} (hTp : ρp.Stopped Tp)
    (t : ℕ) (k : F) (IH : ∀ x, ρ.sal t x k ≤ ρp.sal Tp x (some k)) (i : W)
    (hi : i ∈ ρ.offers t k) (heq : ρ.sal t i k = ρp.sal Tp i (some k)) :
    ρp.choice Tp i = some k := by
  have hGS := hM.2.2.2.1 k
  have hs : (fun x => ρ.sal t x k) ∈ M.gridVectors δ k := by
    intro x; exact sal_grid R t x k
  have hs' : (fun x => ρp.sal Tp x (some k)) ∈ M.gridVectors δ k := by
    intro x
    obtain ⟨n, hn⟩ := sal_grid Rp Tp x (some k)
    exact ⟨n, by show ρp.sal Tp x (some k) = _; rw [hn, hAug.2.2 x k]⟩
  have hle : (fun x => ρ.sal t x k) ≤ (fun x => ρp.sal Tp x (some k)) := fun x => IH x
  obtain ⟨C', hC', hsub⟩ := hGS _ hs _ hs' hle _ (dem_all hM.2.1 R t k)
  have hiC' : i ∈ C' := hsub (Finset.mem_filter.mpr ⟨hi, heq.symm⟩)
  have hC'p : IsDemanded (Mp.y (some k)) (fun x => ρp.sal Tp x (some k)) C' := by
    rw [hAug.2.1 k]; exact hC'
  exact dem_in_hired hδ hP Rp hTp (some k) C' hC'p i hiC'

theorem fa_inv {M : Market W F} {Mp : Market W (Option F)} {δ : ℝ} (hδ : 0 < δ)
    (hAug : IsFirmAugmentation M Mp) (hM : M.Theorem4Conditions δ)
    (hP : Mp.Theorem4Conditions δ) {ρ : Run W F} {ρp : Run W (Option F)}
    (R : RunFacts M δ ρ) (Rp : RunFacts Mp δ ρp) {Tp : ℕ} (hTp : ρp.Stopped Tp) :
    ∀ t i j, ρ.sal t i j ≤ ρp.sal Tp i (some j) := by
  intro t
  induction t with
  | zero =>
    intro i j
    rw [R.sal0]
    have := sigma_le_sal hδ Rp Tp i (some j)
    rwa [hAug.2.2 i j] at this
  | succ t ih =>
    intro i j
    by_cases hrj : ρ.Rejects t i j
    · rw [R.salR t i j hrj]
      obtain ⟨hij, hcj⟩ := (rejects_iff ρ t i j).mp hrj
      have hlt : ρ.sal t i j < ρp.sal Tp i (some j) := by
        rcases (ih i j).lt_or_eq with h | h
        · exact h
        · exfalso
          have hA : ρp.choice Tp i = some j :=
            fa_L1 hδ hAug hM hP R Rp hTp t j (fun x => ih x j) i hij h
          obtain ⟨k, hk⟩ : ∃ k, ρ.choice t i = k := ⟨_, rfl⟩
          have hkj : k ≠ j := by rw [← hk]; exact hcj
          have hik : i ∈ ρ.offers t k := by rw [← hk]; exact R.choice_mem t i (has_offer R t i)
          have hne : ρp.choice Tp i ≠ some k := by
            rw [hA]; intro h'; exact hkj (Option.some_inj.mp h').symm
          have hlt2 : ρ.sal t i k < ρp.sal Tp i (some k) := by
            rcases (ih i k).lt_or_eq with h' | h'
            · exact h'
            · exact absurd (fa_L1 hδ hAug hM hP R Rp hTp t k (fun x => ih x k) i hik h') hne
          have hgr : ρ.sal t i k ∈ Mp.grid δ i (some k) := by
            obtain ⟨n, hn⟩ := sal_grid R t i k
            exact ⟨n, by rw [hn, hAug.2.2 i k]⟩
          have h3 := below_lt hδ hP Rp hTp i (some k) hne _ hgr hlt2
          have h4 : held ρp Mp Tp i = M.u i j (ρ.sal t i j) := by
            unfold held; rw [hA, hAug.1, ← h]
          have h5 := R.choice_max t i j hij
          rw [hk] at h5
          rw [hAug.1, h4] at h3
          linarith
      obtain ⟨a, ha⟩ := sal_grid R t i j
      obtain ⟨b, hb⟩ := sal_grid Rp Tp i (some j)
      rw [hAug.2.2 i j] at hb
      exact grid_step hδ ha hb hlt
    · rw [R.salN t i j hrj]; exact ih i j

theorem fa_final {M : Market W F} {Mp : Market W (Option F)} {δ : ℝ} (hδ : 0 < δ)
    (hAug : IsFirmAugmentation M Mp) (hM : M.Theorem4Conditions δ)
    (hP : Mp.Theorem4Conditions δ) {ρ : Run W F} {ρp : Run W (Option F)}
    (R : RunFacts M δ ρ) (Rp : RunFacts Mp δ ρp) {Tp : ℕ} (hTp : ρp.Stopped Tp)
    {T : ℕ} (hT : ρ.Stopped T) (i : W) :
    M.u i ((ρ.outcome T).assign i) ((ρ.outcome T).sal i) ≤
      Mp.u i ((ρp.outcome Tp).assign i) ((ρp.outcome Tp).sal i) := by
  have hinv := fa_inv hδ hAug hM hP R Rp hTp
  obtain ⟨k, hk⟩ : ∃ k, ρ.choice T i = k := ⟨_, rfl⟩
  have hik : i ∈ ρ.offers T k := by rw [← hk]; exact R.choice_mem T i (has_offer R T i)
  have hL : M.u i ((ρ.outcome T).assign i) ((ρ.outcome T).sal i) = M.u i k (ρ.sal T i k) := by
    show M.u i (ρ.choice T i) (ρ.sal T i (ρ.choice T i)) = _
    rw [hk]
  have hR : Mp.u i ((ρp.outcome Tp).assign i) ((ρp.outcome Tp).sal i) = held ρp Mp Tp i := rfl
  rw [hL, hR]
  by_cases hA : ρp.choice Tp i = some k
  · have h1 : held ρp Mp Tp i = M.u i k (ρp.sal Tp i (some k)) := by
      unfold held; rw [hA, hAug.1]
    rw [h1]
    exact (hM.1 i k).1.monotone (hinv T i k)
  · rcases (hinv T i k).lt_or_eq with h | h
    · have hgr : ρ.sal T i k ∈ Mp.grid δ i (some k) := by
        obtain ⟨n, hn⟩ := sal_grid R T i k
        exact ⟨n, by rw [hn, hAug.2.2 i k]⟩
      have h3 := below_lt hδ hP Rp hTp i (some k) hA _ hgr h
      rw [hAug.1] at h3
      exact h3.le
    · exact absurd (fa_L1 hδ hAug hM hP R Rp hTp T k (fun x => hinv T x k) i hik h) hA

theorem wd_L1 {M : Market W F} {w₀ : W} {δ : ℝ} (hδ : 0 < δ) (hM : M.Theorem4Conditions δ)
    (hN : (M.withoutWorker w₀).Theorem4Conditions δ) {ρ : Run W F}
    {ρm : Run {i : W // i ≠ w₀} F}
    (R : RunFacts M δ ρ) (Rm : RunFacts (M.withoutWorker w₀) δ ρm) {Tm : ℕ}
    (hTm : ρm.Stopped Tm) (t : ℕ) (k : F)
    (IH : ∀ x (hx : x ≠ w₀), ρ.sal t x k ≤ ρm.sal Tm ⟨x, hx⟩ k) (i : W) (hiw : i ≠ w₀)
    (hi : i ∈ ρ.offers t k) (heq : ρ.sal t i k = ρm.sal Tm ⟨i, hiw⟩ k) :
    ρm.choice Tm ⟨i, hiw⟩ = k := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ C : Finset W, |M.y k (insert w₀ C) - M.y k C| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; exact Finset.sum_nonneg (fun C _ => abs_nonneg _)
  obtain ⟨N, hN0⟩ := exists_nat_gt ((|M.σ w₀ k| + B + |ρ.sal t w₀ k|) / δ)
  have hNδ : |M.σ w₀ k| + B + |ρ.sal t w₀ k| < N * δ := by
    rwa [div_lt_iff₀ hδ] at hN0
  let s' : W → ℝ := fun x => if h : x = w₀ then M.σ w₀ k + N * δ else ρm.sal Tm ⟨x, h⟩ k
  have hs'w : s' w₀ = M.σ w₀ k + N * δ := dif_pos rfl
  have hs'x : ∀ x (hx : x ≠ w₀), s' x = ρm.sal Tm ⟨x, hx⟩ k := fun x hx => dif_neg hx
  have hs : (fun x => ρ.sal t x k) ∈ M.gridVectors δ k := by
    intro x; exact sal_grid R t x k
  have hs' : s' ∈ M.gridVectors δ k := by
    intro x
    by_cases hx : x = w₀
    · rw [hx]; exact ⟨N, hs'w⟩
    · obtain ⟨n, hn⟩ := sal_grid Rm Tm ⟨x, hx⟩ k
      exact ⟨n, (hs'x x hx).trans hn⟩
  have hle : (fun x => ρ.sal t x k) ≤ s' := by
    intro x
    by_cases hx : x = w₀
    · show ρ.sal t x k ≤ s' x
      rw [hx, hs'w]
      have h1 := le_abs_self (ρ.sal t w₀ k)
      have h2 := neg_abs_le (M.σ w₀ k)
      linarith
    · show ρ.sal t x k ≤ s' x
      rw [hs'x x hx]
      exact IH x hx
  obtain ⟨C', hC', hsub⟩ := hM.2.2.2.1 k _ hs _ hs' hle _ (dem_all hM.2.1 R t k)
  have hiC' : i ∈ C' := hsub (Finset.mem_filter.mpr ⟨hi, by rw [hs'x i hiw]; exact heq.symm⟩)
  have hw : w₀ ∉ C' := by
    intro hw
    have h1 := hC' (C'.erase w₀)
    have hterm : M.y k (insert w₀ (C'.erase w₀)) - M.y k (C'.erase w₀) ≤ B := by
      rw [hB]
      exact (le_abs_self _).trans (Finset.single_le_sum
        (f := fun C => |M.y k (insert w₀ C) - M.y k C|) (fun C _ => abs_nonneg _)
        (Finset.mem_univ (C'.erase w₀)))
    rw [Finset.insert_erase hw] at hterm
    have hsum := Finset.add_sum_erase C' s' hw
    have h2 := neg_abs_le (M.σ w₀ k)
    have h3 := abs_nonneg (ρ.sal t w₀ k)
    unfold profit at h1
    rw [← hsum, hs'w] at h1
    linarith
  have hDmap : (C'.subtype (fun x => x ≠ w₀)).map (Function.Embedding.subtype _) = C' := by
    rw [Finset.subtype_map]
    exact Finset.filter_true_of_mem (fun x hx hxw => hw (hxw ▸ hx))
  have hprof : ∀ E : Finset {x : W // x ≠ w₀},
      profit ((M.withoutWorker w₀).y k) E (fun x => ρm.sal Tm x k) =
        profit (M.y k) (E.map (Function.Embedding.subtype _)) s' := by
    intro E
    have hy : (M.withoutWorker w₀).y k E = M.y k (E.map (Function.Embedding.subtype _)) := rfl
    have hsm : ∑ x ∈ E, ρm.sal Tm x k =
        ∑ x ∈ E.map (Function.Embedding.subtype _), s' x := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro x _
      rw [Function.Embedding.coe_subtype, hs'x x.1 x.2]
    unfold profit
    rw [hy, hsm]
  have hDdem : IsDemanded ((M.withoutWorker w₀).y k) (fun x => ρm.sal Tm x k)
      (C'.subtype (fun x => x ≠ w₀)) := by
    intro E
    rw [hprof E, hprof, hDmap]
    exact hC' _
  have hiD : (⟨i, hiw⟩ : {x : W // x ≠ w₀}) ∈ C'.subtype (fun x => x ≠ w₀) :=
    Finset.mem_subtype.mpr hiC'
  exact dem_in_hired hδ hN Rm hTm k _ hDdem _ hiD

theorem wd_inv {M : Market W F} {w₀ : W} {δ : ℝ} (hδ : 0 < δ) (hM : M.Theorem4Conditions δ)
    (hN : (M.withoutWorker w₀).Theorem4Conditions δ) {ρ : Run W F}
    {ρm : Run {i : W // i ≠ w₀} F}
    (R : RunFacts M δ ρ) (Rm : RunFacts (M.withoutWorker w₀) δ ρm) {Tm : ℕ}
    (hTm : ρm.Stopped Tm) :
    ∀ t x (hx : x ≠ w₀) j, ρ.sal t x j ≤ ρm.sal Tm ⟨x, hx⟩ j := by
  intro t
  induction t with
  | zero =>
    intro x hx j
    rw [R.sal0]
    exact sigma_le_sal hδ Rm Tm ⟨x, hx⟩ j
  | succ t ih =>
    intro i hiw j
    by_cases hrj : ρ.Rejects t i j
    · rw [R.salR t i j hrj]
      obtain ⟨hij, hcj⟩ := (rejects_iff ρ t i j).mp hrj
      have hlt : ρ.sal t i j < ρm.sal Tm ⟨i, hiw⟩ j := by
        rcases (ih i hiw j).lt_or_eq with h | h
        · exact h
        · exfalso
          have hA : ρm.choice Tm ⟨i, hiw⟩ = j :=
            wd_L1 hδ hM hN R Rm hTm t j (fun x hx => ih x hx j) i hiw hij h
          obtain ⟨k, hk⟩ : ∃ k, ρ.choice t i = k := ⟨_, rfl⟩
          have hkj : k ≠ j := by rw [← hk]; exact hcj
          have hik : i ∈ ρ.offers t k := by rw [← hk]; exact R.choice_mem t i (has_offer R t i)
          have hne : ρm.choice Tm ⟨i, hiw⟩ ≠ k := by rw [hA]; exact hkj.symm
          have hlt2 : ρ.sal t i k < ρm.sal Tm ⟨i, hiw⟩ k := by
            rcases (ih i hiw k).lt_or_eq with h' | h'
            · exact h'
            · exact absurd (wd_L1 hδ hM hN R Rm hTm t k (fun x hx => ih x hx k) i hiw hik h') hne
          have hgr : ρ.sal t i k ∈ (M.withoutWorker w₀).grid δ ⟨i, hiw⟩ k := by
            obtain ⟨n, hn⟩ := sal_grid R t i k
            exact ⟨n, hn⟩
          have h3 := below_lt hδ hN Rm hTm ⟨i, hiw⟩ k hne _ hgr hlt2
          have h4 : held ρm (M.withoutWorker w₀) Tm ⟨i, hiw⟩ = M.u i j (ρ.sal t i j) := by
            unfold held; rw [hA, ← h]; try rfl
          have h5 := R.choice_max t i j hij
          rw [hk] at h5
          have h6 : (M.withoutWorker w₀).u ⟨i, hiw⟩ k (ρ.sal t i k) = M.u i k (ρ.sal t i k) := rfl
          rw [h6, h4] at h3
          linarith
      obtain ⟨a, ha⟩ := sal_grid R t i j
      obtain ⟨b, hb⟩ := sal_grid Rm Tm ⟨i, hiw⟩ j
      exact grid_step hδ ha hb hlt
    · rw [R.salN t i j hrj]; exact ih i hiw j

theorem wd_final {M : Market W F} {w₀ : W} {δ : ℝ} (hδ : 0 < δ) (hM : M.Theorem4Conditions δ)
    (hN : (M.withoutWorker w₀).Theorem4Conditions δ) {ρ : Run W F}
    {ρm : Run {i : W // i ≠ w₀} F}
    (R : RunFacts M δ ρ) (Rm : RunFacts (M.withoutWorker w₀) δ ρm) {Tm : ℕ}
    (hTm : ρm.Stopped Tm) {T : ℕ} (hT : ρ.Stopped T) (j : F) :
    profit ((M.withoutWorker w₀).y j) ((ρm.outcome Tm).hired j) (ρm.outcome Tm).sal ≤
      profit (M.y j) ((ρ.outcome T).hired j) (ρ.outcome T).sal := by
  rw [outcome_profit Rm hTm j, outcome_profit R hT j]
  have hinv := wd_inv hδ hM hN R Rm hTm
  have h1 := dem_all hM.2.1 R T j ((ρm.offers Tm j).map (Function.Embedding.subtype _))
  refine le_trans ?_ h1
  have hy : (M.withoutWorker w₀).y j (ρm.offers Tm j) =
      M.y j ((ρm.offers Tm j).map (Function.Embedding.subtype _)) := rfl
  unfold profit
  rw [hy, Finset.sum_map]
  have h2 : ∑ x ∈ ρm.offers Tm j, ρ.sal T ((Function.Embedding.subtype _) x) j ≤
      ∑ x ∈ ρm.offers Tm j, ρm.sal Tm x j := by
    apply Finset.sum_le_sum
    intro x _
    exact hinv T x.1 x.2 j
  linarith

end Cross

end KCFA0cd

open KelsoCrawford.CompStatics in
theorem solution
    {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (M : Market W F) (Mplus : Market W (Option F))
    (w₀ : W) (δ : ℝ)
    (hδ : 0 < δ) (hAug : IsFirmAugmentation M Mplus)
    (hM : M.Theorem4Conditions δ)
    (hPlus : Mplus.Theorem4Conditions δ)
    (hMinus : (M.withoutWorker w₀).Theorem4Conditions δ)
    (ρ : Run W F) (ρplus : Run W (Option F))
    (ρminus : Run {i : W // i ≠ w₀} F)
    (hρ : M.IsRun δ ρ) (hρplus : Mplus.IsRun δ ρplus)
    (hρminus : (M.withoutWorker w₀).IsRun δ ρminus)
    (T Tplus Tminus : ℕ)
    (hT : ρ.Stopped T) (hTplus : ρplus.Stopped Tplus)
    (hTminus : ρminus.Stopped Tminus) :
    (∀ i : W,
      M.u i ((ρ.outcome T).assign i) ((ρ.outcome T).sal i) ≤
        Mplus.u i ((ρplus.outcome Tplus).assign i)
          ((ρplus.outcome Tplus).sal i)) ∧
    (∀ j : F,
      KelsoCrawford.OneSided.profit ((M.withoutWorker w₀).y j)
          ((ρminus.outcome Tminus).hired j) (ρminus.outcome Tminus).sal ≤
        KelsoCrawford.OneSided.profit (M.y j) ((ρ.outcome T).hired j) (ρ.outcome T).sal) := by
  have R := KCFA0cd.RunFacts.of hρ
  have Rp := KCFA0cd.RunFacts.of hρplus
  have Rm := KCFA0cd.RunFacts.of hρminus
  exact ⟨fun i => KCFA0cd.fa_final hδ hAug hM hPlus R Rp hTplus hT i,
    fun j => KCFA0cd.wd_final hδ hM hMinus R Rm hTminus hT j⟩
