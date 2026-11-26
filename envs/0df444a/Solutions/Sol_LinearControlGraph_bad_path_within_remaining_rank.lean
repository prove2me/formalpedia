-- Prove2me | solution 1 for LinearControlGraph.bad_path_within_remaining_rank
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T20:02:21.289296+00:00
-- url     : https://prove2.me/submissions/0b51852c-5942-4cfc-adf5-25c4a8aeadbd

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LinearControlGraph

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Each edge is always available at its source control location.
The register update may vary with the chosen edge. -/
abbrev Graph (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  ι → ι → Set (Module.End K V)

def levels (edge : Graph K V ι) (seed : ι → Set V) : ℕ → ι → Set V
  | 0 => seed
  | n+1 => fun j => levels edge seed n j ∪
      ⋃ i, ⋃ f : edge i j, f.val '' levels edge seed n i

def advance (edge : Graph K V ι) (spaces : ι → Submodule K V) : ι → Submodule K V :=
  fun j => spaces j ⊔ ⨆ i, ⨆ f : edge i j, (spaces i).map f.val

def summaries (edge : Graph K V ι) (seed : ι → Set V) : ℕ → ι → Submodule K V
  | 0 => fun i => Submodule.span K (seed i)
  | n+1 => advance edge (summaries edge seed n)

theorem summaries_exact (edge : Graph K V ι) (seed : ι → Set V) (n : ℕ) (i : ι) :
    summaries edge seed n i = Submodule.span K (levels edge seed n i) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [summaries, advance, levels, Submodule.span_union, Submodule.span_iUnion,
      ← Submodule.map_span, ih]

theorem advance_increasing (edge : Graph K V ι) (spaces : ι → Submodule K V) :
    spaces ≤ advance edge spaces :=
  fun _ => le_sup_left

theorem summaries_increasing (edge : Graph K V ι) (seed : ι → Set V) (n : ℕ) :
    summaries edge seed n ≤ summaries edge seed (n+1) :=
  advance_increasing edge _

theorem fixed_iff (edge : Graph K V ι) (spaces : ι → Submodule K V) :
    advance edge spaces = spaces ↔ ∀ i j f, f ∈ edge i j → (spaces i).map f ≤ spaces j := by
  constructor
  · intro fixed i j f occurs
    let entry : edge i j := ⟨f, occurs⟩
    have inner : (spaces i).map f ≤ ⨆ g : edge i j, (spaces i).map g.val :=
      by simpa only [entry] using le_iSup (fun g : edge i j => (spaces i).map g.val) entry
    have all : (spaces i).map f ≤ ⨆ b, ⨆ g : edge b j, (spaces b).map g.val :=
      le_iSup_of_le i inner
    have here : (spaces i).map f ≤ advance edge spaces j := all.trans le_sup_right
    rwa [fixed] at here
  · intro closed
    apply le_antisymm ?_ (advance_increasing edge spaces)
    intro j
    unfold advance
    exact sup_le le_rfl (iSup_le fun i => iSup_le fun f => closed i j f.val f.prop)

theorem summaries_stable (edge : Graph K V ι) (seed : ι → Set V) {n : ℕ}
    (fixed : summaries edge seed (n+1) = summaries edge seed n) (extra : ℕ) :
    summaries edge seed (n+extra) = summaries edge seed n := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    change advance edge (summaries edge seed (n+extra)) = _
    rw [ih]
    exact fixed

section FiniteDimensional

variable [Fintype ι] [FiniteDimensional K V]

noncomputable def totalRank (spaces : ι → Submodule K V) : ℕ :=
  ∑ i, Module.finrank K (spaces i)

theorem totalRank_le (spaces : ι → Submodule K V) :
    totalRank spaces ≤ Fintype.card ι * Module.finrank K V := by
  calc
    totalRank spaces ≤ ∑ _ : ι, Module.finrank K V :=
      Finset.sum_le_sum fun _ _ => Submodule.finrank_le _
    _ = _ := by simp

theorem totalRank_strict {spaces more : ι → Submodule K V} (mono : spaces ≤ more)
    (different : spaces ≠ more) : totalRank spaces < totalRank more := by
  classical
  obtain ⟨i, unequal⟩ : ∃ i, spaces i ≠ more i := by
    by_contra! every
    exact different (funext every)
  apply Finset.sum_lt_sum
  · exact fun j _ => Submodule.finrank_mono (mono j)
  · exact ⟨i, Finset.mem_univ i, Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne (mono i) unequal)⟩

end FiniteDimensional

def Certificate {W : Type*} [AddCommGroup W] [Module K W]
    (edge : Graph K V ι) (seed : ι → Set V) (probe : ι → V →ₗ[K] W)
    (spaces : ι → Submodule K V) : Prop :=
  (∀ i, seed i ⊆ spaces i) ∧
  (∀ i j f, f ∈ edge i j → (spaces i).map f ≤ spaces j) ∧
  (∀ i, spaces i ≤ LinearMap.ker (probe i))

theorem certificate_sound {W : Type*} [AddCommGroup W] [Module K W]
    {edge : Graph K V ι} {seed : ι → Set V} {probe : ι → V →ₗ[K] W}
    {spaces : ι → Submodule K V} (checked : Certificate edge seed probe spaces)
    (n : ℕ) (i : ι) {x : V} (reach : x ∈ levels edge seed n i) : probe i x = 0 := by
  have inside (time : ℕ) : summaries edge seed time ≤ spaces := by
    induction time with
    | zero => exact fun j => Submodule.span_le.mpr (checked.1 j)
    | succ time ih =>
      intro j
      change advance edge (summaries edge seed time) j ≤ spaces j
      unfold advance
      apply sup_le (ih j)
      exact iSup_le fun b => iSup_le fun f =>
        (Submodule.map_mono (ih b)).trans (checked.2.1 b j f.val f.prop)
  have mem : x ∈ summaries edge seed n i := by
    rw [summaries_exact]
    exact Submodule.subset_span reach
  exact checked.2.2 i (inside n i mem)

end LinearControlGraph

namespace LinearControlGraph.RankSlack

open LinearControlGraph

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype ι] [FiniteDimensional K V]

/-- Count only the dimensions that can still be added to the initial
spaces. Each strict propagation round consumes at least one. -/
theorem fixed_at_rank_slack (edge : Graph K V ι) (seed : ι → Set V) :
    let full := Fintype.card ι * Module.finrank K V
    let initial := totalRank (summaries edge seed 0)
    let slack := full - initial
    summaries edge seed (slack+1) = summaries edge seed slack := by
  let full := Fintype.card ι * Module.finrank K V
  let initial := totalRank (summaries edge seed 0)
  let slack := full - initial
  change summaries edge seed (slack+1) = summaries edge seed slack
  by_contra different
  have step (n : ℕ) (early : n ≤ slack) :
      totalRank (summaries edge seed n) < totalRank (summaries edge seed (n+1)) := by
    apply totalRank_strict (summaries_increasing edge seed n)
    intro same
    have first : n + (slack-n) = slack := Nat.add_sub_of_le early
    have second : n + (slack+1-n) = slack+1 := Nat.add_sub_of_le (by omega)
    have atBound := summaries_stable edge seed same.symm (slack-n)
    have afterBound := summaries_stable edge seed same.symm (slack+1-n)
    rw [first] at atBound
    rw [second] at afterBound
    exact different (afterBound.trans atBound.symm)
  have rank (n : ℕ) (early : n ≤ slack+1) : initial+n ≤ totalRank (summaries edge seed n) := by
    induction n with
    | zero => simp [initial]
    | succ n ih =>
      have prev := ih (by omega)
      have grow := step n (by omega)
      omega
  have count := rank (slack+1) le_rfl
  have initialFits : initial ≤ full := totalRank_le (summaries edge seed 0)
  have nextFits : totalRank (summaries edge seed (slack+1)) ≤ full := totalRank_le _
  dsimp only [slack] at count nextFits
  omega

omit [Fintype ι] [FiniteDimensional K V] in
theorem certificate_at_fixed_level {W : Type*} [AddCommGroup W] [Module K W]
    (edge : Graph K V ι) (seed : ι → Set V) (probe : ι → V →ₗ[K] W) (bound : ℕ)
    (fixed : summaries edge seed (bound+1) = summaries edge seed bound)
    (safe : ∀ i x, x ∈ levels edge seed bound i → probe i x = 0) :
    Certificate edge seed probe (summaries edge seed bound) := by
  refine ⟨?_, (fixed_iff edge _).mp fixed, ?_⟩
  · intro i x hx
    have chain : Monotone (summaries edge seed) :=
      monotone_nat_of_le_succ (summaries_increasing edge seed)
    exact chain (Nat.zero_le bound) i (Submodule.subset_span hx)
  · intro i
    rw [summaries_exact]
    exact Submodule.span_le.mpr (fun x reached => safe i x reached)

theorem zero_initial_safe {W : Type*} [AddCommGroup W] [Module K W]
    (edge : Graph K V ι) (seed : ι → Set V) (probe : ι → V →ₗ[K] W)
    (zero : totalRank (summaries edge seed 0) = 0) :
    Certificate edge seed probe (fun _ => ⊥) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i x hx
    have one : Module.finrank K (summaries edge seed 0 i) ≤ totalRank (summaries edge seed 0) := by
      unfold totalRank
      exact Finset.single_le_sum (f := fun j : ι => Module.finrank K (summaries edge seed 0 j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have rankZero : Module.finrank K (summaries edge seed 0 i) = 0 := by omega
    have small := Submodule.finrank_eq_zero.1 rankZero
    have included : x ∈ summaries edge seed 0 i := Submodule.subset_span hx
    rwa [small] at included
  · intro i j f _
    simp
  · intro i
    exact bot_le

/-- A violation has a witness by one less than the total ambient
dimension. If the initial span is nonzero, its rank tightens the bound. -/
theorem bad_within_rank_slack {W : Type*} [AddCommGroup W] [Module K W]
    (edge : Graph K V ι) (seed : ι → Set V) (probe : ι → V →ₗ[K] W) :
    (∃ n i x, x ∈ levels edge seed n i ∧ probe i x ≠ 0) ↔
      ∃ i x, x ∈ levels edge seed
        (Fintype.card ι * Module.finrank K V - max 1 (totalRank (summaries edge seed 0))) i ∧
        probe i x ≠ 0 := by
  classical
  constructor
  · rintro ⟨n, i, x, reached, nonzero⟩
    have positive : 1 ≤ totalRank (summaries edge seed 0) := by
      by_contra! small
      exact nonzero (certificate_sound (zero_initial_safe edge seed probe (by omega)) n i reached)
    rw [max_eq_right positive]
    by_contra! safe
    have fixed := fixed_at_rank_slack edge seed
    have certificate := certificate_at_fixed_level edge seed probe _ fixed safe
    exact nonzero (certificate_sound certificate n i reached)
  · rintro ⟨i, x, reached, nonzero⟩
    exact ⟨_, i, x, reached, nonzero⟩

end LinearControlGraph.RankSlack

theorem solution {K V W ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [Fintype ι]
    (edge : ι → ι → Set (Module.End K V)) (seed : ι → Set V)
    (probe : ι → V →ₗ[K] W) :
    let reachable : ℕ → ι → Set V :=
      Nat.rec seed (fun _ previous j =>
        previous j ∪ ⋃ i, ⋃ f : edge i j, f.val '' previous i)
    let initialRank := ∑ i, Module.finrank K (Submodule.span K (seed i))
    (∃ n i x, x ∈ reachable n i ∧ probe i x ≠ 0) ↔
      ∃ i x, x ∈ reachable (Fintype.card ι * Module.finrank K V - max 1 initialRank) i ∧
        probe i x ≠ 0 := by
  intro reachable initialRank
  have eq : reachable = LinearControlGraph.levels edge seed := by
    funext n
    induction n with
    | zero => rfl
    | succ n ih =>
      dsimp only [reachable, LinearControlGraph.levels] at ih ⊢
      rw [ih]
  rw [eq]
  exact LinearControlGraph.RankSlack.bad_within_rank_slack edge seed probe

#print axioms solution
