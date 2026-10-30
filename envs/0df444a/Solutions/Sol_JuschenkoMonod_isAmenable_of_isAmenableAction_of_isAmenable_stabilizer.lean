-- Prove2me | solution 1 for JuschenkoMonod.isAmenable_of_isAmenableAction_of_isAmenable_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:46:16.323802+00:00
-- url     : https://prove2.me/submissions/3fdc6637-d315-4a27-ac51-917a3c08bafa

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_IntervalExchange

open scoped ENNReal Pointwise
open Garrido

set_option linter.unusedSectionVars false
set_option linter.deprecated false

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

variable {H Y : Type*} [Group H] [MulAction H Y] [Nonempty Y]

noncomputable def mF (μ : Set Y → ℝ≥0∞) (Φ : Y → Set H → ℝ≥0∞) (F : Finset (Set Y)) (A : Set H) :
    ℝ≥0∞ :=
  ∑ σ ∈ F.powerset, μ (atom F σ) * Φ (rep F σ) A

variable {μ : Set Y → ℝ≥0∞} {Φ : Y → Set H → ℝ≥0∞}

theorem sum_atom_mu (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (F : Finset (Set Y)) : ∑ σ ∈ F.powerset, μ (atom F σ) = 1 := by
  rw [← fa_sum hμ _ _ (atom_disjoint F), iUnion_atom, hμ1]

theorem mu_ne_top (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1) (S : Set Y) :
    μ S ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hμ1 ▸ fa_mono hμ (Set.subset_univ S))

theorem mF_empty (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y)) (F : Finset (Set Y)) :
    mF μ Φ F ∅ = 0 := by
  simp [mF, (hΦ _).1]

theorem mF_union (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y)) (F : Finset (Set Y)) (A B : Set H)
    (h : Disjoint A B) : mF μ Φ F (A ∪ B) = mF μ Φ F A + mF μ Φ F B := by
  simp only [mF, (hΦ _).2 A B h, mul_add, Finset.sum_add_distrib]

theorem mF_univ (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (hΦ1 : ∀ y, Φ y Set.univ = 1) (F : Finset (Set Y)) : mF μ Φ F Set.univ = 1 := by
  simp only [mF, hΦ1, mul_one]; exact sum_atom_mu hμ hμ1 F

theorem toReal_mF (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y)) (hΦ1 : ∀ y, Φ y Set.univ = 1) (F : Finset (Set Y))
    (A : Set H) :
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
    (hΦk : ∀ (k : H) (y : Y) (A : Set H), Φ (k • y) (k • A) = Φ y A) (k : H) (A : Set H)
    (n : ℕ) (hn : 0 < n) :
    ∃ F₀ : Finset (Set Y), ∀ F, F₀ ⊆ F →
      |(mF μ Φ F (k • A)).toReal - (mF μ Φ F A).toReal| ≤ 1 / n := by
  have hΦle : ∀ y (B : Set H), (Φ y B).toReal ≤ 1 := fun y B => by
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

theorem exists_invariant_of_barycenter (hμ : IsFinitelyAdditiveMeasure μ) (hμ1 : μ Set.univ = 1)
    (hμi : IsInvariant H μ) (hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y))
    (hΦ1 : ∀ y, Φ y Set.univ = 1)
    (hΦk : ∀ (k : H) (y : Y) (A : Set H), Φ (k • y) (k • A) = Φ y A) :
    ∃ m : Set H → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧ IsInvariant H m := by
  haveI : (Filter.atTop : Filter (Finset (Set Y))).NeBot := Filter.atTop_neBot
  let U : Ultrafilter (Finset (Set Y)) := Ultrafilter.of Filter.atTop
  have hU : (U : Filter (Finset (Set Y))) ≤ Filter.atTop := Ultrafilter.of_le _
  have hlim : ∀ A : Set H, ∃ L : ℝ≥0∞, Filter.Tendsto (fun F => mF μ Φ F A) U (nhds L) := by
    intro A
    obtain ⟨L, -, hL⟩ := isCompact_univ.ultrafilter_le_nhds (U.map (fun F => mF μ Φ F A)) (by simp)
    exact ⟨L, hL⟩
  choose L hL using hlim
  have hFA : ∀ F, IsFinitelyAdditiveMeasure (mF μ Φ F) := fun F => ⟨mF_empty hΦ F, mF_union hΦ F⟩
  have hfin : ∀ F A, mF μ Φ F A ≠ ⊤ := fun F A =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (mF_univ hμ hμ1 hΦ1 F ▸ fa_mono (hFA F) (Set.subset_univ A))
  refine ⟨L, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact tendsto_nhds_unique (hL ∅) (by simpa [mF_empty hΦ] using tendsto_const_nhds (x := (0 : ℝ≥0∞)))
  · intro A B hAB
    refine tendsto_nhds_unique (hL _) ?_
    simp only [mF_union hΦ _ A B hAB]
    exact (hL A).add (hL B)
  · exact tendsto_nhds_unique (hL _) (by simpa [mF_univ hμ hμ1 hΦ1] using tendsto_const_nhds (x := (1 : ℝ≥0∞)))
  · intro k A
    have key : ∀ (A B : Set H) (k : H), (∀ n : ℕ, 0 < n → ∃ F₀ : Finset (Set Y), ∀ F, F₀ ⊆ F →
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

end Main

section Lemma32

open Classical

variable {H Y : Type*} [Group H] [MulAction H Y]

noncomputable def Mp (ν : ∀ z : Y, Set (MulAction.stabilizer H z) → ℝ≥0∞) (z : Y) (h : H)
    (A : Set H) : ℝ≥0∞ :=
  ν z {s | h * (s : H) ∈ A}

variable {ν : ∀ z : Y, Set (MulAction.stabilizer H z) → ℝ≥0∞}

theorem Mp_congr (z z' : Y) (e : z = z') (h : H) (A : Set H) : Mp ν z h A = Mp ν z' h A := by
  subst e; rfl

theorem Mp_smul (z : Y) (k h : H) (A : Set H) : Mp ν z (k * h) (k • A) = Mp ν z h A := by
  unfold Mp
  congr 1
  ext s
  simp [Set.mem_smul_set_iff_inv_smul_mem, mul_assoc]

theorem Mp_stab (hν : ∀ z, IsInvariant (MulAction.stabilizer H z) (ν z)) (z : Y) (h : H)
    (t : MulAction.stabilizer H z) (A : Set H) : Mp ν z (h * t) A = Mp ν z h A := by
  unfold Mp
  rw [← hν z t⁻¹ {s | h * (s : H) ∈ A}]
  congr 1
  ext s
  simp [Set.mem_smul_set_iff_inv_smul_mem, mul_assoc]

theorem lemma32_dev (H Y : Type*) [Group H] [MulAction H Y]
    (hY : ∃ m : Set Y → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧ m Set.univ = 1 ∧ IsInvariant H m)
    (hstab : ∀ y : Y, IsAmenable (MulAction.stabilizer H y)) : IsAmenable H := by
  obtain ⟨μ, hμ, hμ1, hμi⟩ := hY
  haveI : Nonempty Y := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : μ Set.univ = μ ∅ := by congr 1; exact Set.eq_empty_of_isEmpty _
    rw [hμ.1, hμ1] at this; exact one_ne_zero this
  choose ν hν using fun z : Y => hstab z
  -- hν z : FA ∧ univ = 1 ∧ invariant
  letI : Setoid Y := MulAction.orbitRel H Y
  let ρ : Y → Y := fun y => (Quotient.mk (MulAction.orbitRel H Y) y).out
  have hρ : ∀ y, ρ y ≈ y := fun y => Quotient.exact (Quotient.out_eq _)
  have hρk : ∀ (k : H) y, ρ (k • y) = ρ y := fun k y => by
    have : Quotient.mk (MulAction.orbitRel H Y) (k • y) = Quotient.mk (MulAction.orbitRel H Y) y :=
      Quotient.sound (by show k • y ∈ MulAction.orbit H y; exact MulAction.mem_orbit y k)
    simp only [ρ, this]
  have hex : ∀ y, ∃ h : H, h • ρ y = y := fun y => by
    have : ρ y ∈ MulAction.orbit H y := hρ y
    obtain ⟨g, hg⟩ := this
    exact ⟨g⁻¹, by rw [← hg, smul_smul]; simp⟩
  let hh : Y → H := fun y => Classical.choose (hex y)
  have hhs : ∀ y, hh y • ρ y = y := fun y => Classical.choose_spec (hex y)
  let Φ : Y → Set H → ℝ≥0∞ := fun y A => Mp ν (ρ y) (hh y) A
  have hΦ : ∀ y, IsFinitelyAdditiveMeasure (Φ y) := fun y => by
    refine ⟨?_, fun A B hAB => ?_⟩
    · simpa [Φ, Mp] using (hν (ρ y)).1.1
    · simp only [Φ, Mp]
      have : {s : MulAction.stabilizer H (ρ y) | (hh y) * (s : H) ∈ A ∪ B} =
          {s : MulAction.stabilizer H (ρ y) | (hh y) * (s : H) ∈ A} ∪
            {s : MulAction.stabilizer H (ρ y) | (hh y) * (s : H) ∈ B} := by ext; simp
      rw [this]
      exact (hν (ρ y)).1.2 _ _ (Set.disjoint_left.2 fun s hsA hsB => Set.disjoint_left.1 hAB hsA hsB)
  have hΦ1 : ∀ y, Φ y Set.univ = 1 := fun y => by simpa [Φ, Mp] using (hν (ρ y)).2.1
  have hΦk : ∀ (k : H) (y : Y) (A : Set H), Φ (k • y) (k • A) = Φ y A := by
    intro k y A
    simp only [Φ]
    rw [Mp_congr (ρ (k • y)) (ρ y) (hρk k y)]
    have ht : (k * hh y)⁻¹ * hh (k • y) ∈ MulAction.stabilizer H (ρ y) := by
      rw [MulAction.mem_stabilizer_iff, mul_smul]
      have h1 : hh (k • y) • ρ y = k • y := by
        have := hhs (k • y); rwa [hρk] at this
      rw [h1, inv_smul_eq_iff, mul_smul, hhs]
    have : hh (k • y) = (k * hh y) * ((k * hh y)⁻¹ * hh (k • y)) := by group
    rw [this]
    rw [Mp_stab (fun z => (hν z).2.2) (ρ y) (k * hh y) ⟨(k * hh y)⁻¹ * hh (k • y), ht⟩, Mp_smul]
  exact exists_invariant_of_barycenter hμ hμ1 hμi hΦ hΦ1 hΦk

end Lemma32

end JuschenkoMonod

theorem solution (H Y : Type*) [Group H] [MulAction H Y] (hY : IntervalExchange.IsAmenableAction H Y)
    (hstab : ∀ y : Y, Garrido.IsAmenable (MulAction.stabilizer H y)) : Garrido.IsAmenable H :=
  JuschenkoMonod.lemma32_dev H Y hY hstab
