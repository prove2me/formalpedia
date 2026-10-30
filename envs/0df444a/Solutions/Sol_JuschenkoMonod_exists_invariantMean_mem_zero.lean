-- Prove2me | solution 1 for JuschenkoMonod.exists_invariantMean_mem_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:28:38.04178+00:00
-- url     : https://prove2.me/submissions/238253bc-5688-436a-beba-f81853febb9e

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod
import Theorems.Thm_JuschenkoDeLaSalle_isAmenableAction_lamplighter_wobbling_of_isRecurrentSpace_and_isRecurrentSpace_of_coarseEmbedding_and_not_of_containsLipschitzBinaryTree

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open scoped ENNReal Pointwise
open Garrido

namespace JuschenkoMonod

section FA

variable {X : Type*} {m : Set X → ℝ≥0∞}

theorem fa_mono (hm : IsFinitelyAdditiveMeasure m) {S T : Set X} (h : S ⊆ T) : m S ≤ m T := by
  have := hm.2 S (T \ S) Set.disjoint_sdiff_right
  rw [Set.union_sdiff_cancel h] at this
  rw [this]; exact le_self_add

theorem fa_sum (hm : IsFinitelyAdditiveMeasure m) {ι : Type*} (s : Finset ι) (S : ι → Set X)
    (hd : (s : Set ι).PairwiseDisjoint S) : m (⋃ i ∈ s, S i) = ∑ i ∈ s, m (S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hm.1
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha, hm.2, ih (hd.subset (by simp))]
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hd (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))

end FA


section Bary

open Classical

variable {Y : Type*} [Nonempty Y]

noncomputable def sig (F : Finset (Set Y)) (y : Y) : Finset (Set Y) := F.filter (fun B => y ∈ B)

def atom (F : Finset (Set Y)) (σ : Finset (Set Y)) : Set Y := {y | sig F y = σ}

noncomputable def rep (F : Finset (Set Y)) (σ : Finset (Set Y)) : Y :=
  if h : (atom F σ).Nonempty then h.choose else Classical.arbitrary Y

theorem rep_mem {F : Finset (Set Y)} {σ : Finset (Set Y)} (h : (atom F σ).Nonempty) :
    rep F σ ∈ atom F σ := by
  unfold rep; rw [dif_pos h]; exact h.choose_spec

theorem sig_mem (F : Finset (Set Y)) (y : Y) : sig F y ∈ F.powerset := by
  simp [sig]

theorem atom_disjoint (F : Finset (Set Y)) :
    ((F.powerset : Finset (Finset (Set Y))) : Set (Finset (Set Y))).PairwiseDisjoint (atom F) := by
  intro σ _ σ' _ hne
  rw [Function.onFun, Set.disjoint_left]
  intro y h h'
  exact hne (h.symm.trans h')

theorem iUnion_atom (F : Finset (Set Y)) : ⋃ σ ∈ F.powerset, atom F σ = Set.univ := by
  ext y; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨sig F y, sig_mem F y, rfl⟩

theorem mem_iff_of_atom {F : Finset (Set Y)} {σ : Finset (Set Y)} {y y' : Y} (hy : y ∈ atom F σ)
    (hy' : y' ∈ atom F σ) {B : Set Y} (hB : B ∈ F) : y ∈ B ↔ y' ∈ B := by
  have h1 : sig F y = sig F y' := hy.trans hy'.symm
  have : B ∈ sig F y ↔ B ∈ sig F y' := by rw [h1]
  simpa [sig, hB] using this

variable (μ : Set Y → ℝ≥0∞)

/-- exact formula: a function with level sets in `F` -/
theorem sum_atom_level (hμ : IsFinitelyAdditiveMeasure μ) (F : Finset (Set Y)) (n : ℕ)
    (q : Y → ℕ) (hq : ∀ y, q y ≤ n) (hF : ∀ j ∈ Finset.range (n + 1), {y | q y = j} ∈ F) :
    ∑ σ ∈ F.powerset, μ (atom F σ) * (q (rep F σ) : ℝ≥0∞) =
      ∑ j ∈ Finset.range (n + 1), (j : ℝ≥0∞) * μ {y | q y = j} := by
  -- q is constant on atoms
  have hconst : ∀ σ y, y ∈ atom F σ → q y = q (rep F σ) := by
    intro σ y hy
    have hne : (atom F σ).Nonempty := ⟨y, hy⟩
    have hr := rep_mem hne
    have := mem_iff_of_atom hy hr (hF (q y) (Finset.mem_range.2 (Nat.lt_succ_of_le (hq y))))
    exact (this.1 rfl).symm
  have hlevel : ∀ j, {y | q y = j} = ⋃ σ ∈ F.powerset.filter (fun σ => q (rep F σ) = j), atom F σ := by
    intro j; ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · intro h
      exact ⟨sig F y, ⟨sig_mem F y, by rw [← hconst (sig F y) y rfl, h]⟩, rfl⟩
    · rintro ⟨σ, ⟨_, h⟩, hy⟩
      rw [hconst σ y hy, h]
  have hmu : ∀ j, μ {y | q y = j} = ∑ σ ∈ F.powerset.filter (fun σ => q (rep F σ) = j), μ (atom F σ) := by
    intro j
    rw [hlevel j, fa_sum hμ]
    exact (atom_disjoint F).subset (by intro σ hσ; simpa using (Finset.mem_filter.1 hσ).1)
  simp_rw [hmu, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := F.powerset) (t := Finset.range (n + 1))
      (g := fun σ => q (rep F σ)) (fun σ _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hq _)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2, mul_comm]

end Bary

theorem real_bounds {ι : Type*} (s : Finset ι) (w g : ι → ℝ) (q : ι → ℕ) (n : ℕ) (hn : 0 < n)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (h1 : ∀ i, (q i : ℝ) ≤ n * g i)
    (h2 : ∀ i, (n : ℝ) * g i < q i + 1) :
    (1 / n) * ∑ i ∈ s, w i * q i ≤ ∑ i ∈ s, w i * g i ∧
      ∑ i ∈ s, w i * g i ≤ (1 / n) * ∑ i ∈ s, w i * q i + 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := h1 i
    have h3 : (1 / (n : ℝ)) * q i ≤ g i := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn']; linarith
    calc 1 / (n : ℝ) * (w i * q i) = w i * (1 / n * q i) := by ring
      _ ≤ w i * g i := mul_le_mul_of_nonneg_left h3 (hw i)
  · have : (1 / (n : ℝ)) = ∑ i ∈ s, w i * (1 / n) := by rw [← Finset.sum_mul, hsum, one_mul]
    rw [Finset.mul_sum]
    nth_rewrite 2 [this]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := h2 i
    have h3 : g i ≤ 1 / (n : ℝ) * q i + 1 / n := by
      have : g i < (q i + 1) / n := by rw [lt_div_iff₀ hn']; linarith
      calc g i ≤ (q i + 1) / n := this.le
        _ = 1 / (n : ℝ) * q i + 1 / n := by ring
    calc w i * g i ≤ w i * (1 / (n : ℝ) * q i + 1 / n) := mul_le_mul_of_nonneg_left h3 (hw i)
      _ = 1 / (n : ℝ) * (w i * q i) + w i * (1 / n) := by ring

section Main

open Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [MulAction H X] [Nonempty Y]

noncomputable def mF (μ : Set Y → ℝ≥0∞) (Φ : Y → Set X → ℝ≥0∞) (F : Finset (Set Y)) (A : Set X) :
    ℝ≥0∞ :=
  ∑ σ ∈ F.powerset, μ (atom F σ) * Φ (rep F σ) A

variable {μ : Set Y → ℝ≥0∞} {Φ : Y → Set X → ℝ≥0∞}

theorem sum_atom_mu (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (F : Finset (Set Y)) : ∑ σ ∈ F.powerset, μ (atom F σ) = 1 := by
  rw [← fa_sum hμ _ _ (atom_disjoint F), iUnion_atom, hμ1]

theorem mu_ne_top (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1) (S : Set Y) :
    μ S ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hμ1 ▸ fa_mono hμ (Set.subset_univ S))

theorem mF_empty (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y)) (F : Finset (Set Y)) :
    mF μ Φ F ∅ = 0 := by
  simp [mF, (hΦ _).1]

theorem mF_union (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y)) (F : Finset (Set Y)) (A B : Set X)
    (h : Disjoint A B) : mF μ Φ F (A ∪ B) = mF μ Φ F A + mF μ Φ F B := by
  simp only [mF, (hΦ _).2 A B h, mul_add, Finset.sum_add_distrib]

theorem mF_univ (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (hΦ1 : ∀ y, Φ y Set.univ = 1) (F : Finset (Set Y)) : mF μ Φ F Set.univ = 1 := by
  simp only [mF, hΦ1, mul_one]; exact sum_atom_mu hμ hμ1 F

theorem toReal_mF (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y)) (hΦ1 : ∀ y, Φ y Set.univ = 1) (F : Finset (Set Y))
    (A : Set X) :
    (mF μ Φ F A).toReal = ∑ σ ∈ F.powerset, (μ (atom F σ)).toReal * (Φ (rep F σ) A).toReal := by
  unfold mF
  rw [ENNReal.toReal_sum]
  · simp [ENNReal.toReal_mul]
  · intro σ _
    refine ENNReal.mul_ne_top (mu_ne_top hμ hμ1 _) ?_
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (hΦ1 _ ▸ fa_mono (hΦ _) (Set.subset_univ A))

theorem mF_close (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (hμi : IsInvariant H μ) (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y))
    (hΦ1 : ∀ y, Φ y Set.univ = 1)
    (hΦk : ∀ (k : H) (y : Y) (A : Set X), Φ (k • y) (k • A) = Φ y A) (k : H) (A : Set X)
    (n : ℕ) (hn : 0 < n) :
    ∃ F₀ : Finset (Set Y), ∀ F, F₀ ⊆ F →
      |(mF μ Φ F (k • A)).toReal - (mF μ Φ F A).toReal| ≤ 1 / n := by
  have hΦle : ∀ y (B : Set X), (Φ y B).toReal ≤ 1 := fun y B => by
    have : Φ y B ≤ 1 := hΦ1 y ▸ fa_mono (hΦ y) (Set.subset_univ B)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top this
  set f : Y → ℝ := fun y => (Φ y A).toReal with hfdef
  have hf0 : ∀ y, 0 ≤ f y := fun y => ENNReal.toReal_nonneg
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set q : Y → ℕ := fun y => ⌊(n : ℝ) * f y⌋₊ with hqdef
  have hq : ∀ y, q y ≤ n := fun y => Nat.floor_le_of_le (by
    have := hΦle y A
    nlinarith [hf0 y])
  have hfk : ∀ y, (Φ y (k • A)).toReal = f (k⁻¹ • y) := fun y => by
    have := hΦk k (k⁻¹ • y) A
    rw [smul_inv_smul] at this
    simp [hfdef, this]
  let Lj : ℕ → Set Y := fun j => {y | q y = j}
  refine ⟨(Finset.range (n + 1)).image Lj ∪ (Finset.range (n + 1)).image (fun j => k • Lj j), ?_⟩
  intro F hF
  have hF1 : ∀ j ∈ Finset.range (n + 1), {y | q y = j} ∈ F := fun j hj =>
    hF (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj))
  have hset : ∀ j, {y | q (k⁻¹ • y) = j} = k • Lj j := by
    intro j; ext y
    simp [Lj, Set.mem_smul_set_iff_inv_smul_mem]
  have hF2 : ∀ j ∈ Finset.range (n + 1), {y | q (k⁻¹ • y) = j} ∈ F := fun j hj => by
    rw [hset]; exact hF (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
  have E1 := sum_atom_level μ hμ F n q hq hF1
  have E2 := sum_atom_level μ hμ F n (fun y => q (k⁻¹ • y)) (fun y => hq _) hF2
  have hE : ∑ σ ∈ F.powerset, μ (atom F σ) * (q (rep F σ) : ℝ≥0∞) =
      ∑ σ ∈ F.powerset, μ (atom F σ) * (q (k⁻¹ • rep F σ) : ℝ≥0∞) := by
    rw [E1, E2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hset, hμi k]
  have hw : ∀ σ, 0 ≤ (μ (atom F σ)).toReal := fun σ => ENNReal.toReal_nonneg
  have hsum : ∑ σ ∈ F.powerset, (μ (atom F σ)).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun σ _ => mu_ne_top hμ hμ1 _), sum_atom_mu hμ hμ1]; simp
  have hE' : ∑ σ ∈ F.powerset, (μ (atom F σ)).toReal * (q (rep F σ) : ℝ) =
      ∑ σ ∈ F.powerset, (μ (atom F σ)).toReal * (q (k⁻¹ • rep F σ) : ℝ) := by
    have := congrArg ENNReal.toReal hE
    rw [ENNReal.toReal_sum, ENNReal.toReal_sum] at this
    · simpa [ENNReal.toReal_mul] using this
    · intro σ _; exact ENNReal.mul_ne_top (mu_ne_top hμ hμ1 _) (by simp)
    · intro σ _; exact ENNReal.mul_ne_top (mu_ne_top hμ hμ1 _) (by simp)
  have B1 := real_bounds F.powerset (fun σ => (μ (atom F σ)).toReal) (fun σ => f (rep F σ))
    (fun σ => q (rep F σ)) n hn hw hsum
    (fun σ => by simpa [hqdef] using Nat.floor_le (mul_nonneg hnr.le (hf0 (rep F σ))))
    (fun σ => by simpa [hqdef] using Nat.lt_floor_add_one ((n : ℝ) * f (rep F σ)))
  have B2 := real_bounds F.powerset (fun σ => (μ (atom F σ)).toReal) (fun σ => f (k⁻¹ • rep F σ))
    (fun σ => q (k⁻¹ • rep F σ)) n hn hw hsum
    (fun σ => by simpa [hqdef] using Nat.floor_le (mul_nonneg hnr.le (hf0 (k⁻¹ • rep F σ))))
    (fun σ => by simpa [hqdef] using Nat.lt_floor_add_one ((n : ℝ) * f (k⁻¹ • rep F σ)))
  rw [toReal_mF hμ hμ1 hΦ hΦ1, toReal_mF hμ hμ1 hΦ hΦ1]
  simp only [hfk]
  have e1 : ∑ σ ∈ F.powerset, (μ (atom F σ)).toReal * (Φ (rep F σ) A).toReal =
      ∑ σ ∈ F.powerset, (μ (atom F σ)).toReal * f (rep F σ) := rfl
  rw [e1, abs_le]
  rw [hE'] at B1
  constructor <;> linarith [B1.1, B1.2, B2.1, B2.2]

theorem le_add_ofReal_of_toReal {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : a.toReal ≤ b.toReal + δ) : a ≤ b + ENNReal.ofReal δ := by
  calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    _ ≤ ENNReal.ofReal (b.toReal + δ) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal b.toReal + ENNReal.ofReal δ := ENNReal.ofReal_add ENNReal.toReal_nonneg hδ
    _ = b + ENNReal.ofReal δ := by rw [ENNReal.ofReal_toReal hb]


theorem mF_ge (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1) (F : Finset (Set Y))
    (B : Set Y) (hB : B ∈ F) (A : Set X) (c₁ c₂ : ℝ≥0∞) (h1 : ∀ y ∈ B, c₁ ≤ Φ y A)
    (h2 : ∀ y, y ∉ B → c₂ ≤ Φ y A) : c₁ * μ B + c₂ * μ Bᶜ ≤ mF μ Φ F A := by
  have hB1 : B = ⋃ σ ∈ F.powerset.filter (fun σ => B ∈ σ), atom F σ := by
    ext y
    simp only [Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · intro hy
      exact ⟨sig F y, ⟨sig_mem F y, by simp [sig, hB, hy]⟩, rfl⟩
    · rintro ⟨σ, ⟨_, hσ⟩, hy⟩
      have : B ∈ sig F y := by rw [hy]; exact hσ
      simpa [sig, hB] using this
  have hB2 : Bᶜ = ⋃ σ ∈ F.powerset.filter (fun σ => B ∉ σ), atom F σ := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · intro hy
      exact ⟨sig F y, ⟨sig_mem F y, by simp [sig, hB, hy]⟩, rfl⟩
    · rintro ⟨σ, ⟨_, hσ⟩, hy⟩ hyB
      have : B ∈ sig F y := by simp [sig, hB, hyB]
      rw [hy] at this; exact hσ this
  have dis : ∀ (p : Finset (Set Y) → Prop) [DecidablePred p],
      ((F.powerset.filter p : Finset (Finset (Set Y))) :
      Set (Finset (Set Y))).PairwiseDisjoint (atom F) := fun p _ =>
    (atom_disjoint F).subset (by intro σ hσ; simpa using (Finset.mem_filter.1 hσ).1)
  have e1 : μ B = ∑ σ ∈ F.powerset.filter (fun σ => B ∈ σ), μ (atom F σ) := by
    conv_lhs => rw [hB1]
    exact fa_sum hμ _ _ (dis _)
  have e2 : μ Bᶜ = ∑ σ ∈ F.powerset.filter (fun σ => B ∉ σ), μ (atom F σ) := by
    conv_lhs => rw [hB2]
    exact fa_sum hμ _ _ (dis _)
  rw [e1, e2, Finset.mul_sum, Finset.mul_sum]
  unfold mF
  rw [← Finset.sum_filter_add_sum_filter_not F.powerset (fun σ => B ∈ σ)]
  refine add_le_add (Finset.sum_le_sum fun σ hσ => ?_) (Finset.sum_le_sum fun σ hσ => ?_)
  · rw [mul_comm c₁]
    by_cases hne : (atom F σ).Nonempty
    · have hr := rep_mem hne
      have hrB : rep F σ ∈ B := by
        have : B ∈ sig F (rep F σ) := by rw [hr]; exact (Finset.mem_filter.1 hσ).2
        simpa [sig, hB] using this
      gcongr; exact h1 _ hrB
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, hμ.1]; simp
  · rw [mul_comm c₂]
    by_cases hne : (atom F σ).Nonempty
    · have hr := rep_mem hne
      have hrB : rep F σ ∉ B := by
        intro hb
        have : B ∈ sig F (rep F σ) := by simp [sig, hB, hb]
        rw [hr] at this; exact (Finset.mem_filter.1 hσ).2 this
      gcongr; exact h2 _ hrB
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, hμ.1]; simp

theorem exists_invariant_of_barycenter (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (hμi : IsInvariant H μ) (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y))
    (hΦ1 : ∀ y, Φ y Set.univ = 1)
    (hΦk : ∀ (k : H) (y : Y) (A : Set X), Φ (k • y) (k • A) = Φ y A) :
    ∃ m : Set X → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧ IsInvariant H m ∧
      ∀ (B : Set Y) (A : Set X) (c₁ c₂ : ℝ≥0∞), (∀ y ∈ B, c₁ ≤ Φ y A) → (∀ y, y ∉ B → c₂ ≤ Φ y A) →
        c₁ * μ B + c₂ * μ Bᶜ ≤ m A := by
  haveI : (Filter.atTop : Filter (Finset (Set Y))).NeBot := Filter.atTop_neBot
  let U : Ultrafilter (Finset (Set Y)) := Ultrafilter.of Filter.atTop
  have hU : (U : Filter (Finset (Set Y))) ≤ Filter.atTop := Ultrafilter.of_le _
  have hlim : ∀ A : Set X, ∃ L : ℝ≥0∞, Filter.Tendsto (fun F => mF μ Φ F A) U (nhds L) := by
    intro A
    obtain ⟨L, -, hL⟩ := isCompact_univ.ultrafilter_le_nhds (U.map (fun F => mF μ Φ F A)) (by simp)
    exact ⟨L, hL⟩
  choose L hL using hlim
  have hFA : ∀ F, IsFinitelyAdditiveMeasure (mF μ Φ F) := fun F => ⟨mF_empty hΦ F, mF_union hΦ F⟩
  have hfin : ∀ F A, mF μ Φ F A ≠ ⊤ := fun F A =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (mF_univ hμ hμ1 hΦ1 F ▸ fa_mono (hFA F) (Set.subset_univ A))
  refine ⟨L, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact tendsto_nhds_unique (hL ∅) (by simpa [mF_empty hΦ] using tendsto_const_nhds (x := (0 : ℝ≥0∞)))
  · intro A B hAB
    refine tendsto_nhds_unique (hL _) ?_
    simp only [mF_union hΦ _ A B hAB]
    exact (hL A).add (hL B)
  · exact tendsto_nhds_unique (hL _) (by simpa [mF_univ hμ hμ1 hΦ1] using tendsto_const_nhds (x := (1 : ℝ≥0∞)))
  · intro k A
    have key : ∀ (A B : Set X) (k : H), (∀ n : ℕ, 0 < n → ∃ F₀ : Finset (Set Y), ∀ F, F₀ ⊆ F →
        |(mF μ Φ F B).toReal - (mF μ Φ F A).toReal| ≤ 1 / n) → L B ≤ L A := by
      intro A B k h
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε by exact_mod_cast hε)
      obtain ⟨F₀, hF₀⟩ := h (n + 1) (Nat.succ_pos n)
      have hev : ∀ᶠ F in (U : Filter (Finset (Set Y))), mF μ Φ F B ≤ mF μ Φ F A + ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)) := by
        filter_upwards [hU (Filter.eventually_ge_atTop F₀)] with F hF
        refine le_add_ofReal_of_toReal (hfin _ _) (hfin _ _) (by positivity) ?_
        have := hF₀ F hF
        rw [abs_le] at this; linarith
      have := le_of_tendsto_of_tendsto (hL B) ((hL A).add tendsto_const_nhds) hev
      refine this.trans (add_le_add_right ?_ _)
      have hc : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
      calc ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)) ≤ ENNReal.ofReal (ε : ℝ) :=
            ENNReal.ofReal_le_ofReal (by rw [hc]; exact hn.le)
        _ = ε := ENNReal.ofReal_coe_nnreal
    exact le_antisymm (key A (k • A) k fun n hn => by
        obtain ⟨F₀, h⟩ := mF_close hμ hμ1 hμi hΦ hΦ1 hΦk k A n hn; exact ⟨F₀, h⟩)
      (key (k • A) A k fun n hn => by
        obtain ⟨F₀, h⟩ := mF_close hμ hμ1 hμi hΦ hΦ1 hΦk k A n hn
        exact ⟨F₀, fun F hF => by rw [abs_sub_comm]; exact h F hF⟩)
  · intro B A c₁ c₂ h1 h2
    refine ge_of_tendsto (hL A) ?_
    filter_upwards [hU (Filter.eventually_ge_atTop {B})] with F hF
    exact mF_ge hμ hμ1 F B (hF (Finset.mem_singleton_self B)) A c₁ c₂ h1 h2

end Main


open IntervalExchange

theorem boundedGeometry_int : HasBoundedGeometry ℤ := by
  intro R hR
  refine ⟨⌈2 * R + 1⌉₊, fun x => ⟨?_, ?_⟩⟩
  · rw [Int.closedBall_eq_Icc]; exact Set.finite_Icc _ _
  · rw [Int.closedBall_eq_Icc, ← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]
    have h1 := Int.floor_le ((x : ℝ) + R)
    have h2 := Int.le_ceil ((x : ℝ) - R)
    have h3 : (⌊(x : ℝ) + R⌋ + 1 - ⌈(x : ℝ) - R⌉ : ℤ) ≤ ⌈2 * R + 1⌉₊ := by
      have h4 := Int.lt_floor_add_one ((x : ℝ) + R)
      have h5 := Int.ceil_lt_add_one ((x : ℝ) - R)
      have h6 := Nat.le_ceil (2 * R + 1)
      have : ((⌊(x : ℝ) + R⌋ + 1 - ⌈(x : ℝ) - R⌉ : ℤ) : ℝ) ≤ ((⌈2 * R + 1⌉₊ : ℕ) : ℝ) := by
        push_cast; linarith
      have : ((⌊(x : ℝ) + R⌋ + 1 - ⌈(x : ℝ) - R⌉ : ℤ) : ℝ) ≤ (((⌈2 * R + 1⌉₊ : ℕ) : ℤ) : ℝ) := by
        simpa using this
      exact_mod_cast this
    omega

theorem dist_embed_int (x y : ℤ) :
    id (dist x y) ≤ dist (![x, 0] : Fin 2 → ℤ) ![y, 0] ∧
      dist (![x, 0] : Fin 2 → ℤ) ![y, 0] ≤ id (dist x y) := by
  have : dist (![x, 0] : Fin 2 → ℤ) ![y, 0] = dist x y := by
    apply le_antisymm
    · refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
      fin_cases i <;> simp
    · simpa using dist_le_pi_dist (![x, 0] : Fin 2 → ℤ) ![y, 0] 0
  simp [this]

theorem lamp_mean_int :
    ∃ m : Set (Multiplicative (ℤ →₀ ZMod 2)) → ℝ≥0∞,
      Garrido.IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧
        Garrido.IsInvariant (Lamplighter ↥(wobbling ℤ) ℤ) m := by
  have h := (JuschenkoDeLaSalle.isAmenableAction_lamplighter_wobbling_of_isRecurrentSpace_and_isRecurrentSpace_of_coarseEmbedding_and_not_of_containsLipschitzBinaryTree
    boundedGeometry_int)
  exact h.1 0 (h.2.1 (fun x => ![x, 0]) id id monotone_id monotone_id Filter.tendsto_id
    dist_embed_int 0)


abbrev Zc := Multiplicative (ℤ →₀ ZMod 2)

/-- the support of a lamp configuration, as a finite set -/
def lampSupp (f : Zc) : Finset ℤ := (Multiplicative.toAdd f).support

/-- the indicator configuration of a finite set -/
noncomputable def indicZ (F : Finset ℤ) : Zc :=
  Multiplicative.ofAdd (Finsupp.onFinset F (fun x => if x ∈ F then (1 : ZMod 2) else 0)
    (fun x hx => by by_contra h; exact hx (by simp [h])))

theorem lampSupp_indicZ (F : Finset ℤ) : lampSupp (indicZ F) = F := by
  ext x; simp [lampSupp, indicZ]

theorem lampSupp_mul (f g : Zc) : lampSupp (f * g) = symmDiff (lampSupp f) (lampSupp g) := by
  ext x
  have key : ∀ a b : ZMod 2, a + b ≠ 0 ↔ ((a ≠ 0 ∧ b = 0) ∨ (b ≠ 0 ∧ a = 0)) := by decide
  simp only [lampSupp, Finsupp.mem_support_iff, toAdd_mul, Finsupp.add_apply,
    Finset.mem_symmDiff]
  rw [key]
  tauto

theorem lampSupp_lampAut (w : ↥(wobbling ℤ)) (f : Zc) :
    lampSupp (lampAut ↥(wobbling ℤ) ℤ w f) = (lampSupp f).image (fun x => (w : Equiv.Perm ℤ) x) := by
  have hinj : Function.Injective (fun x : ℤ => w • x) := fun a b h => (MulAction.injective w) h
  unfold lampSupp
  show (Finsupp.mapDomain (fun x => w • x) (Multiplicative.toAdd f)).support = _
  rw [Finsupp.mapDomain_support_of_injective hinj]
  rfl

theorem lampSupp_smul (F : Finset ℤ) (w : ↥(wobbling ℤ)) (f : Zc) :
    lampSupp ((⟨indicZ F, w⟩ : Lamplighter ↥(wobbling ℤ) ℤ) • f) =
      symmDiff F ((lampSupp f).image (fun x => (w : Equiv.Perm ℤ) x)) := by
  show lampSupp (indicZ F * lampAut ↥(wobbling ℤ) ℤ w f) = _
  rw [lampSupp_mul, lampSupp_indicZ, lampSupp_lampAut]



open IntervalExchange

section TheoremC

abbrev WG := ↥(wobbling ℤ)

theorem finset_smul_eq (g : WG) (E : Finset ℤ) : g • E = E.image (fun x => (g : Equiv.Perm ℤ) x) := by
  ext x
  simp only [Finset.mem_smul_finset, Finset.mem_image]
  rfl

theorem lampSupp_smul_empty (w : WG) (f : Zc) :
    lampSupp ((⟨indicZ ∅, w⟩ : Lamplighter WG ℤ) • f) = w • lampSupp f := by
  rw [lampSupp_smul, finset_smul_eq]
  simp

/-- the mean on finite subsets of `ℤ` obtained from a lamplighter-invariant mean on the lamp group -/
noncomputable def meanFin (m : Set Zc → ℝ≥0∞) (S : Set (Finset ℤ)) : ℝ≥0∞ := m (lampSupp ⁻¹' S)

theorem meanFin_inv (m : Set Zc → ℝ≥0∞) (hm : IsInvariant (Lamplighter WG ℤ) m) (g : WG)
    (S : Set (Finset ℤ)) : meanFin m (g • S) = meanFin m S := by
  have : lampSupp ⁻¹' (g • S) = (⟨indicZ ∅, g⁻¹⟩ : Lamplighter WG ℤ)⁻¹ • (lampSupp ⁻¹' S) := by
    rw [← Set.preimage_smul]
    ext f
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, lampSupp_smul_empty]
  unfold meanFin
  rw [this]
  exact hm _ _

theorem meanFin_half (m : Set Zc → ℝ≥0∞) (hfa : IsFinitelyAdditiveMeasure m) (hm1 : m Set.univ = 1)
    (hm : IsInvariant (Lamplighter WG ℤ) m) :
    meanFin m {E | (0 : ℤ) ∈ E} = 2⁻¹ := by
  let A : Set Zc := lampSupp ⁻¹' {E | (0 : ℤ) ∈ E}
  let p : Lamplighter WG ℤ := ⟨indicZ {0}, 1⟩
  have hpre : (fun f => p • f) ⁻¹' A = Aᶜ := by
    ext f
    simp only [Set.mem_preimage, Set.mem_compl_iff, A, Set.mem_setOf_eq]
    show (0 : ℤ) ∈ lampSupp ((⟨indicZ {0}, 1⟩ : Lamplighter WG ℤ) • f) ↔ _
    rw [lampSupp_smul]
    simp [Finset.mem_symmDiff]
  have h1 : m Aᶜ = m A := by
    have h' := hm p⁻¹ A
    have : p⁻¹ • A = Aᶜ := by rw [← Set.preimage_smul]; exact hpre
    rwa [this] at h'
  have h2 := hfa.2 A Aᶜ disjoint_compl_right
  rw [Set.union_compl_self, hm1, h1] at h2
  show m A = 2⁻¹
  have h3 : m A * 2 = 1 := by rw [mul_two]; exact h2.symm
  exact ENNReal.eq_inv_of_mul_eq_one_left h3


theorem step_union (μ : Set (Finset ℤ) → ℝ≥0∞) (hμ : IsFinitelyAdditiveMeasure μ)
    (hμ1 : μ Set.univ = 1) (hμi : IsInvariant WG μ) (hμB : μ {E | (0 : ℤ) ∈ E} = 2⁻¹)
    (M : Set (Finset ℤ) → ℝ≥0∞) (hM : IsFinitelyAdditiveMeasure M) (hM1 : M Set.univ = 1)
    (hMi : IsInvariant WG M) (δ : ℝ≥0∞) (hδ : 1 ≤ M {E | (0 : ℤ) ∈ E} + δ) :
    ∃ M' : Set (Finset ℤ) → ℝ≥0∞, IsFinitelyAdditiveMeasure M' ∧ M' Set.univ = 1 ∧
      IsInvariant WG M' ∧ 1 ≤ M' {E | (0 : ℤ) ∈ E} + δ * 2⁻¹ := by
  classical
  let Φ : Finset ℤ → Set (Finset ℤ) → ℝ≥0∞ := fun E S => M {E' | E ∪ E' ∈ S}
  have hΦ : ∀ E, IsFinitelyAdditiveMeasure (Φ E) := fun E => by
    refine ⟨by simpa [Φ] using hM.1, fun S T hST => ?_⟩
    simp only [Φ, Set.preimage_union]
    have : {E' | E ∪ E' ∈ S ∪ T} = {E' | E ∪ E' ∈ S} ∪ {E' | E ∪ E' ∈ T} := by ext; simp
    rw [this]
    exact hM.2 _ _ (Set.disjoint_left.2 fun x hxS hxT => Set.disjoint_left.1 hST hxS hxT)
  have hΦ1 : ∀ E, Φ E Set.univ = 1 := fun E => by simpa [Φ] using hM1
  have hΦk : ∀ (g : WG) (E : Finset ℤ) (S : Set (Finset ℤ)), Φ (g • E) (g • S) = Φ E S := by
    intro g E S
    simp only [Φ]
    have : {E' | g • E ∪ E' ∈ g • S} = g • {E'' | E ∪ E'' ∈ S} := by
      ext E'
      simp only [Set.mem_setOf_eq, Set.mem_smul_set_iff_inv_smul_mem]
      rw [Finset.smul_finset_union, inv_smul_smul]
    rw [this, hMi]
  obtain ⟨m', hm'fa, hm'1, hm'i, hge⟩ :=
    exists_invariant_of_barycenter (H := WG) (Y := Finset ℤ) (X := Finset ℤ) hμ hμ1 hμi hΦ hΦ1 hΦk
  refine ⟨m', hm'fa, hm'1, hm'i, ?_⟩
  have hB := hge {E | (0 : ℤ) ∈ E} {E | (0 : ℤ) ∈ E} 1 (M {E | (0 : ℤ) ∈ E})
    (fun E hE => by
      have : {E' | E ∪ E' ∈ {E : Finset ℤ | (0 : ℤ) ∈ E}} = Set.univ := by
        ext E'; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, Finset.mem_union]
        exact Or.inl hE
      simp only [Φ, this, hM1, le_refl])
    (fun E hE => by
      have : {E' | E ∪ E' ∈ {E : Finset ℤ | (0 : ℤ) ∈ E}} = {E' | (0 : ℤ) ∈ E'} := by
        ext E'; simp only [Set.mem_setOf_eq, Finset.mem_union]
        have : (0 : ℤ) ∉ E := hE
        tauto
      simp only [Φ, this, le_refl])
  have hBc : μ {E | (0 : ℤ) ∈ E}ᶜ = 2⁻¹ := by
    have h := hμ.2 _ _ (disjoint_compl_right : Disjoint {E : Finset ℤ | (0 : ℤ) ∈ E} _)
    rw [Set.union_compl_self, hμ1, hμB] at h
    exact (ENNReal.add_right_inj (by simp)).1 (h.symm.trans ENNReal.inv_two_add_inv_two.symm)
  rw [hμB, hBc, one_mul] at hB
  calc (1 : ℝ≥0∞) = 2⁻¹ + 1 * 2⁻¹ := by rw [one_mul, ENNReal.inv_two_add_inv_two]
    _ ≤ 2⁻¹ + (M {E | (0 : ℤ) ∈ E} + δ) * 2⁻¹ := by gcongr
    _ = (2⁻¹ + M {E | (0 : ℤ) ∈ E} * 2⁻¹) + δ * 2⁻¹ := by rw [add_mul, add_assoc]
    _ ≤ m' {E | (0 : ℤ) ∈ E} + δ * 2⁻¹ := by gcongr


theorem exists_invariantMean_mem_zero_dev :
    ∃ m : Set (Finset ℤ) → ℝ≥0∞, IsInvariantMean (wobbling ℤ) m ∧ m {E | (0 : ℤ) ∈ E} = 1 := by
  obtain ⟨m, hmfa, hm1, hmi⟩ := lamp_mean_int
  have h0fa : IsFinitelyAdditiveMeasure (meanFin m) :=
    ⟨by simpa [meanFin] using hmfa.1, fun S T hST => by
      simp only [meanFin, Set.preimage_union]
      exact hmfa.2 _ _ (hST.preimage lampSupp)⟩
  have h01 : meanFin m Set.univ = 1 := by simpa [meanFin] using hm1
  have h0i : IsInvariant WG (meanFin m) := fun g S => meanFin_inv m hmi g S
  have h0B := meanFin_half m hmfa hm1 hmi
  have hseq : ∀ k : ℕ, ∃ M : Set (Finset ℤ) → ℝ≥0∞, IsFinitelyAdditiveMeasure M ∧ M Set.univ = 1 ∧
      IsInvariant WG M ∧ 1 ≤ M {E | (0 : ℤ) ∈ E} + 2⁻¹ ^ k := by
    intro k
    induction k with
    | zero => exact ⟨meanFin m, h0fa, h01, h0i, by simp⟩
    | succ k ih =>
      obtain ⟨M, hM, hM1, hMi, hMk⟩ := ih
      obtain ⟨M', h1, h2, h3, h4⟩ :=
        step_union (meanFin m) h0fa h01 h0i h0B M hM hM1 hMi _ hMk
      exact ⟨M', h1, h2, h3, by rwa [← pow_succ] at h4⟩
  choose M hM using hseq
  haveI : (Filter.atTop : Filter ℕ).NeBot := Filter.atTop_neBot
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : (U : Filter ℕ) ≤ Filter.atTop := Ultrafilter.of_le _
  have hlim : ∀ S : Set (Finset ℤ), ∃ L : ℝ≥0∞, Filter.Tendsto (fun k => M k S) U (nhds L) := by
    intro S
    obtain ⟨L, -, hL⟩ := isCompact_univ.ultrafilter_le_nhds (U.map (fun k => M k S)) (by simp)
    exact ⟨L, hL⟩
  choose L hL using hlim
  have hLfa : IsFinitelyAdditiveMeasure L := by
    refine ⟨?_, fun S T hST => ?_⟩
    · refine tendsto_nhds_unique (hL ∅) ?_
      have : (fun k => M k ∅) = fun _ => 0 := funext fun k => (hM k).1.1
      rw [this]; exact tendsto_const_nhds
    · refine tendsto_nhds_unique (hL _) ?_
      simp only [fun k => (hM k).1.2 S T hST]
      exact (hL S).add (hL T)
  have hL1 : L Set.univ = 1 :=
    tendsto_nhds_unique (hL _) (by simpa [(hM _).2.1] using tendsto_const_nhds (x := (1 : ℝ≥0∞)))
  have hLi : IsInvariant WG L := by
    intro g S
    refine tendsto_nhds_unique (hL _) ?_
    simp only [fun k => (hM k).2.2.1 g S]
    exact hL S
  refine ⟨L, ⟨hLfa, hL1, hLi⟩, ?_⟩
  have hge : 1 ≤ L {E | (0 : ℤ) ∈ E} := by
    have hz : Filter.Tendsto (fun k : ℕ => (2⁻¹ : ℝ≥0∞) ^ k) U (nhds 0) :=
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by simp)).mono_left hU
    have := le_of_tendsto_of_tendsto' tendsto_const_nhds ((hL _).add hz) (fun k => (hM k).2.2.2)
    simpa using this
  exact le_antisymm (hL1 ▸ fa_mono hLfa (Set.subset_univ _)) hge

end TheoremC

end JuschenkoMonod

open scoped ENNReal Pointwise in
theorem solution :
    ∃ m : Set (Finset ℤ) → ℝ≥0∞, JuschenkoMonod.IsInvariantMean (IntervalExchange.wobbling ℤ) m ∧
      m {E | (0 : ℤ) ∈ E} = 1 :=
  JuschenkoMonod.exists_invariantMean_mem_zero_dev
