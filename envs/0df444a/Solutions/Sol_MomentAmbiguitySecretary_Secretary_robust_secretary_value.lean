-- Prove2me | solution 1 for MomentAmbiguitySecretary.Secretary.robust_secretary_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:17:57.479835+00:00
-- url     : https://prove2.me/submissions/a550f18a-a861-4a6b-836d-b4f68c0bbafd

import Mathlib
import Definitions.Def_MomentAmbiguitySecretary_Secretary_Values
import Theorems.Thm_MomentAmbiguitySecretary_Secretary_ramsey_secretary_grid
import Theorems.Thm_MomentAmbiguitySecretary_Secretary_n_way_separator
import Theorems.Thm_MomentAmbiguitySecretary_Secretary_first_atom_concentration

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary.Dev.SecLower

section Comb
open Equiv

variable {m : ℕ} {L : Type} [LinearOrder L]

def Rec (k : Fin m → L) (σ : Perm (Fin m)) (t : Fin m) : Prop :=
  ∀ s : Fin m, s < t → k (σ s) < k (σ t)

def Cond (r : ℕ) (k : Fin m → L) (σ : Perm (Fin m)) (t : Fin m) : Prop :=
  r ≤ t.val ∧ Rec k σ t

def Good (r : ℕ) (k : Fin m → L) (σ : Perm (Fin m)) (t : Fin m) : Prop :=
  Cond r k σ t ∧ ∀ j, j < t → ¬ Cond r k σ j

lemma Good_unique (r : ℕ) (k : Fin m → L) (σ : Perm (Fin m)) {t t' : Fin m}
    (h : Good r k σ t) (h' : Good r k σ t') : t = t' := by
  rcases lt_trichotomy t t' with hl | he | hg
  · exact absurd h'.1 (h'.2 t hl |> fun x => by exact fun hc => x h.1)
  · exact he
  · exact absurd h.1 (h.2 t' hg |> fun x => by exact fun hc => x h'.1)

open Classical in
noncomputable def stopT (r : ℕ) (k : Fin m → L) (σ : Perm (Fin m)) : Option (Fin m) :=
  if h : ∃ t, Good r k σ t then some (Classical.choose h) else none

lemma stopT_eq_some_iff (r : ℕ) (k : Fin m → L) (σ : Perm (Fin m)) (t : Fin m) :
    stopT r k σ = some t ↔ Good r k σ t := by
  classical
  unfold stopT
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl; exact Classical.choose_spec h
    · intro ht; exact Good_unique r k σ (Classical.choose_spec h) ht
  · simp only [reduceCtorEq, false_iff]
    exact fun ht => h ⟨t, ht⟩

def Nn (M t : Fin m) : ℕ := (Finset.univ.filter fun σ : Perm (Fin m) => σ t = M).card

lemma N_eq (M t t' : Fin m) : Nn M t = Nn M t' := by
  classical
  unfold Nn
  refine Finset.card_nbij' (fun σ => σ * swap t t') (fun σ => σ * swap t t') ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    simpa [Perm.mul_apply] using hσ
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    simpa [Perm.mul_apply] using hσ
  · intro σ _; simp [mul_assoc]
  · intro σ _; simp [mul_assoc]

lemma sum_N (M : Fin m) : ∑ t, Nn M t = m.factorial := by
  classical
  unfold Nn
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ σ : Perm (Fin m), ∑ t : Fin m, (if σ t = M then 1 else 0) = 1 := by
    intro σ
    rw [Finset.sum_eq_single (σ.symm M)]
    · simp
    · intro b _ hb
      have : σ b ≠ M := fun h => hb (by rw [← h]; simp)
      simp [this]
    · simp
  simp [this, Fintype.card_perm]

lemma m_mul_N (hm : 0 < m) (M t : Fin m) : m * Nn M t = m.factorial := by
  rw [← sum_N M]
  have : ∀ t', Nn M t' = Nn M t := fun t' => N_eq M t' t
  simp [this]

def Fs (k : Fin m → L) (M t j : Fin m) : Finset (Perm (Fin m)) :=
  open Classical in
  Finset.univ.filter fun σ => σ t = M ∧ ∀ s, s < t → s ≠ j → k (σ s) < k (σ j)

lemma mem_Fs (k : Fin m → L) (M t j : Fin m) (σ : Perm (Fin m)) :
    σ ∈ Fs k M t j ↔ σ t = M ∧ ∀ s, s < t → s ≠ j → k (σ s) < k (σ j) := by
  classical
  simp [Fs]

lemma F_map (k : Fin m → L) (M t j j' : Fin m) (hj : j < t) (hj' : j' < t) (σ : Perm (Fin m))
    (hσ : σ ∈ Fs k M t j) : σ * swap j j' ∈ Fs k M t j' := by
  classical
  rw [mem_Fs] at hσ ⊢
  obtain ⟨h1, h2⟩ := hσ
  refine ⟨?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hj.ne' hj'.ne']; exact h1
  · intro s hs hsj'
    rw [Perm.mul_apply, Perm.mul_apply, swap_apply_right]
    by_cases hsj : s = j
    · rw [hsj, swap_apply_left]
      rw [hsj] at hsj'
      exact h2 j' hj' (fun h => hsj' h.symm)
    · rw [swap_apply_of_ne_of_ne hsj hsj']
      exact h2 s hs hsj

lemma F_card_eq (k : Fin m → L) (M t j j' : Fin m) (hj : j < t) (hj' : j' < t) :
    (Fs k M t j).card = (Fs k M t j').card := by
  have h1 : ∀ a b : Fin m, a < t → b < t → (Fs k M t a).card ≤ (Fs k M t b).card := by
    intro a b ha hb
    refine Finset.card_le_card_of_injOn (fun σ => σ * swap a b) ?_ ?_
    · intro σ hσ; exact F_map k M t a b ha hb σ hσ
    · intro σ _ τ _ h; exact mul_right_cancel h
  exact le_antisymm (h1 _ _ hj hj') (h1 _ _ hj' hj)

lemma F_disjoint (k : Fin m → L) (hk : Function.Injective k) (M t : Fin m) :
    Set.PairwiseDisjoint (↑(Finset.Iio t) : Set (Fin m)) (Fs k M t) := by
  classical
  intro j hj j' hj' hne
  show Disjoint (Fs k M t j) (Fs k M t j')
  rw [Finset.disjoint_left]
  intro σ h1 h2
  rw [mem_Fs] at h1 h2
  simp only [Finset.coe_Iio, Set.mem_Iio] at hj hj'
  have a := h1.2 j' hj' (Ne.symm hne)
  have b := h2.2 j hj hne
  exact absurd (a.trans b) (lt_irrefl _)

lemma N_eq_sum (k : Fin m → L) (hk : Function.Injective k) (M t : Fin m) (ht : 0 < t.val) :
    Nn M t = ∑ j ∈ Finset.Iio t, (Fs k M t j).card := by
  classical
  rw [← Finset.card_biUnion (F_disjoint k hk M t)]
  unfold Nn
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_Iio,
    mem_Fs]
  constructor
  · intro h
    have hne : (Finset.Iio t).Nonempty := ⟨⟨0, by omega⟩, by
      simp only [Finset.mem_Iio]; exact Fin.mk_lt_of_lt_val ht⟩
    obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.Iio t) (fun s => k (σ s)) hne
    refine ⟨j, Finset.mem_Iio.mp hj, h, ?_⟩
    intro s hs hsj
    refine lt_of_le_of_ne (hmax s (Finset.mem_Iio.mpr hs)) ?_
    intro he
    exact hsj (σ.injective (hk he))
  · rintro ⟨j, _, h, _⟩; exact h

lemma t_mul_F (k : Fin m → L) (hk : Function.Injective k) (M t j : Fin m) (hj : j < t) :
    t.val * (Fs k M t j).card = Nn M t := by
  have ht : 0 < t.val := lt_of_le_of_lt (Nat.zero_le _) hj
  rw [N_eq_sum k hk M t ht]
  rw [Finset.sum_congr rfl (fun j' hj' => F_card_eq k M t j' j (Finset.mem_Iio.mp hj') hj)]
  simp

def Es (k : Fin m → L) (r : ℕ) (hr : r < m) (M t : Fin m) : Finset (Perm (Fin m)) :=
  (Finset.Iio (⟨r, hr⟩ : Fin m)).biUnion (Fs k M t)

lemma E_card (k : Fin m → L) (hk : Function.Injective k) (r : ℕ) (hr : r < m) (M t : Fin m)
    (hrt : r ≤ t.val) : (Es k r hr M t).card * t.val = r * Nn M t := by
  classical
  have hdis : Set.PairwiseDisjoint (↑(Finset.Iio (⟨r, hr⟩ : Fin m)) : Set (Fin m)) (Fs k M t) :=
    (F_disjoint k hk M t).subset (by
      intro j hj
      simp only [Finset.coe_Iio, Set.mem_Iio] at hj ⊢
      exact Fin.lt_def.mpr (by have := Fin.lt_def.mp hj; simp only at this; omega))
  unfold Es
  rw [Finset.card_biUnion hdis, Finset.sum_mul]
  have : ∀ j ∈ Finset.Iio (⟨r, hr⟩ : Fin m), (Fs k M t j).card * t.val = Nn M t := by
    intro j hj
    rw [Finset.mem_Iio, Fin.lt_def] at hj
    rw [mul_comm]
    exact t_mul_F k hk M t j (Fin.lt_def.mpr (by simp only at hj; omega))
  rw [Finset.sum_congr rfl this]
  simp

open Classical in
noncomputable def SuccS (k : Fin m → L) (M : Fin m) (r : ℕ) : Finset (Perm (Fin m)) :=
  Finset.univ.filter fun σ => ∃ t, stopT r k σ = some t ∧ σ t = M

lemma SuccS_zero (hm : 0 < m) (k : Fin m → L) (M : Fin m) :
    (SuccS k M 0).card = Nn M ⟨0, hm⟩ := by
  classical
  unfold SuccS Nn
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hs : stopT 0 k σ = some ⟨0, hm⟩ := by
    rw [stopT_eq_some_iff]
    refine ⟨⟨le_rfl, fun s hs => absurd (Fin.lt_def.mp hs) (Nat.not_lt_zero _)⟩, ?_⟩
    intro j hj; exact absurd (Fin.lt_def.mp hj) (Nat.not_lt_zero _)
  constructor
  · rintro ⟨t, ht, h⟩
    rw [hs] at ht
    cases ht
    exact h
  · intro h; exact ⟨_, hs, h⟩

lemma stop_of_E (k : Fin m → L) (hk : Function.Injective k) (M : Fin m) (hM : ∀ i, k i ≤ k M)
    (r : ℕ) (hr : r < m) (t : Fin m) (hrt : r ≤ t.val) (σ : Perm (Fin m))
    (hσ : σ ∈ Es k r hr M t) : stopT r k σ = some t := by
  classical
  unfold Es at hσ
  simp only [Finset.mem_biUnion, Finset.mem_Iio, mem_Fs] at hσ
  obtain ⟨j, hj, hσt, hrest⟩ := hσ
  have hjr : j.val < r := Fin.lt_def.mp hj
  rw [stopT_eq_some_iff]
  refine ⟨⟨hrt, ?_⟩, ?_⟩
  · intro s hs
    rw [hσt]
    refine lt_of_le_of_ne (hM _) ?_
    intro he
    have := σ.injective (hk (he.trans (by rw [hσt])))
    exact hs.ne this
  · rintro j' hj' ⟨hj'r, hrec⟩
    have h1 : j < j' := Fin.lt_def.mpr (by omega)
    have h2 := hrec j h1
    have h3 := hrest j' hj' (ne_of_gt h1)
    exact lt_asymm h2 h3

lemma sumT (g : ℕ → ℝ) (r m : ℕ) :
    ∑ t ∈ (Finset.univ.filter fun t : Fin m => r ≤ t.val), g t.val
      = ∑ n ∈ Finset.Ico r m, g n := by
  classical
  rw [Finset.sum_filter]
  have := Fin.sum_univ_eq_sum_range (fun n => if r ≤ n then g n else 0) m
  rw [this, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

theorem count_ge (k : Fin m → L) (hk : Function.Injective k) (M : Fin m) (hM : ∀ i, k i ≤ k M)
    (r : ℕ) (hr1 : 1 ≤ r) (hr : r < m) :
    (m.factorial : ℝ) * (r * ∑ n ∈ Finset.Ico r m, 1 / (n : ℝ)) ≤ m * (SuccS k M r).card := by
  classical
  have hm : 0 < m := by omega
  set T : Finset (Fin m) := Finset.univ.filter fun t : Fin m => r ≤ t.val with hT
  have hEt : ∀ t, ∀ σ ∈ Es k r hr M t, σ t = M := by
    intro t σ hσ
    unfold Es at hσ
    simp only [Finset.mem_biUnion, Finset.mem_Iio, mem_Fs] at hσ
    obtain ⟨j, _, h, _⟩ := hσ
    exact h
  have hdis : Set.PairwiseDisjoint (↑T : Set (Fin m)) (Es k r hr M) := by
    intro t _ t' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro σ h1 h2
    exact hne (σ.injective ((hEt t σ h1).trans (hEt t' σ h2).symm))
  have hsub : T.biUnion (Es k r hr M) ⊆ SuccS k M r := by
    intro σ hσ
    simp only [Finset.mem_biUnion, hT, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨t, hrt, h⟩ := hσ
    unfold SuccS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨t, stop_of_E k hk M hM r hr t hrt σ h, hEt t σ h⟩
  have hcard : ∑ t ∈ T, (Es k r hr M t).card ≤ (SuccS k M r).card := by
    rw [← Finset.card_biUnion hdis]; exact Finset.card_le_card hsub
  have hterm : ∀ t ∈ T, (m : ℝ) * (Es k r hr M t).card
      = r * m.factorial * (1 / (t.val : ℝ)) := by
    intro t ht
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have h1 := E_card k hk r hr M t ht
    have h2 := m_mul_N hm M t
    have h1' : ((Es k r hr M t).card : ℝ) * t.val = r * Nn M t := by exact_mod_cast h1
    have h2' : (m : ℝ) * Nn M t = m.factorial := by exact_mod_cast h2
    have htpos : (0 : ℝ) < t.val := by exact_mod_cast (by omega : 0 < t.val)
    field_simp
    calc (m : ℝ) * (Es k r hr M t).card * t.val
        = m * (((Es k r hr M t).card : ℝ) * t.val) := by ring
      _ = m * (r * Nn M t) := by rw [h1']
      _ = r * (m * Nn M t) := by ring
      _ = r * m.factorial := by rw [h2']
  have hsum : ∑ t ∈ T, (1 / ((t.val : ℕ) : ℝ)) = ∑ n ∈ Finset.Ico r m, 1 / (n : ℝ) :=
    sumT (fun n => 1 / (n : ℝ)) r m
  calc (m.factorial : ℝ) * (r * ∑ n ∈ Finset.Ico r m, 1 / (n : ℝ))
      = ∑ t ∈ T, (r * m.factorial * (1 / (t.val : ℝ))) := by
        rw [← hsum, ← Finset.mul_sum]; ring
    _ = ∑ t ∈ T, (m : ℝ) * (Es k r hr M t).card :=
        Finset.sum_congr rfl (fun t ht => (hterm t ht).symm)
    _ = (m : ℝ) * ∑ t ∈ T, ((Es k r hr M t).card : ℝ) := by rw [← Finset.mul_sum]
    _ ≤ m * (SuccS k M r).card := by
        gcongr
        exact_mod_cast hcard

end Comb

section Prob
open Equiv

variable {m : ℕ}

def key (v : Fin m → ℝ≥0) : Fin m → ℝ≥0 ×ₗ Fin m := fun i => toLex (v i, i)

lemma key_injective (v : Fin m → ℝ≥0) : Function.Injective (key v) := by
  intro a b h
  have := congrArg (fun x => (ofLex x).2) h
  simpa [key] using this

lemma key_lt_iff (v : Fin m → ℝ≥0) (a b : Fin m) :
    key v a < key v b ↔ v a < v b ∨ (v a = v b ∧ a < b) := by
  simp only [key, Prod.Lex.toLex_lt_toLex]

lemma key_le_imp (v : Fin m → ℝ≥0) (a b : Fin m) (h : key v a ≤ key v b) : v a ≤ v b := by
  rcases h.lt_or_eq with h | h
  · rcases (key_lt_iff v a b).1 h with h | h
    · exact h.le
    · exact h.1.le
  · have := congrArg (fun x => (ofLex x).1) h
    simpa [key] using this.le

noncomputable def tauP (r : ℕ) (p : Path m) : Option (Fin m) := stopT r (key p.2) p.1

lemma measurable_good (r : ℕ) (σ : Perm (Fin m)) (t : Fin m) :
    Measurable fun v : Fin m → ℝ≥0 => Good r (key v) σ t := by
  have hlt : ∀ a b : Fin m, Measurable fun v : Fin m → ℝ≥0 => key v a < key v b := by
    intro a b
    simp_rw [key_lt_iff]
    refine Measurable.or ?_ (Measurable.and ?_ measurable_const)
    · exact measurableSet_setOfPred.1 (measurableSet_lt (measurable_pi_apply a) (measurable_pi_apply b))
    · exact measurableSet_setOfPred.1 (measurableSet_eq_fun (measurable_pi_apply a) (measurable_pi_apply b))
  unfold Good Cond Rec
  refine Measurable.and (Measurable.and measurable_const ?_) ?_
  · exact Measurable.forall fun s => Measurable.imp measurable_const (hlt _ _)
  · exact Measurable.forall fun j => Measurable.imp measurable_const
      (Measurable.not (Measurable.and measurable_const
        (Measurable.forall fun s => Measurable.imp measurable_const (hlt _ _))))

lemma measurable_tau (r : ℕ) : Measurable (tauP (m := m) r) := by
  have hσ : ∀ σ : Perm (Fin m), Measurable fun v : Fin m → ℝ≥0 => stopT r (key v) σ := by
    intro σ
    refine measurable_to_countable' (fun x => ?_)
    cases x with
    | some t =>
      have : (fun v : Fin m → ℝ≥0 => stopT r (key v) σ) ⁻¹' {some t}
          = {v | Good r (key v) σ t} := by
        ext v; simp [stopT_eq_some_iff]
      rw [this]; exact (measurable_good r σ t).setOf
    | none =>
      have : (fun v : Fin m → ℝ≥0 => stopT r (key v) σ) ⁻¹' {none}
          = {v | ∀ t, ¬ Good r (key v) σ t} := by
        ext v
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Option.eq_none_iff_forall_ne_some,
          ne_eq, stopT_eq_some_iff]
        rfl
      rw [this]
      exact (Measurable.forall fun t => (measurable_good r σ t).not).setOf
  exact measurable_from_prod_countable_right (f := fun p : Path m => stopT r (key p.2) p.1) hσ

noncomputable def pol (D : Type) [MeasurableSpace D] (m r : ℕ) : Policy D m where
  kernel := Kernel.deterministic (fun x : D × Path m => tauP r x.2)
    ((measurable_tau r).comp measurable_snd)
  markov := inferInstance
  causal := by
    intro d p q t h
    have hk : ∀ i, i ≤ t → key p.2 (p.1 i) = key q.2 (q.1 i) := by
      intro i hi
      have := h i hi
      simp only [observation, Prod.mk.injEq] at this
      simp only [key]
      rw [this.2, this.1]
    have hG : Good r (key p.2) p.1 t ↔ Good r (key q.2) q.1 t := by
      unfold Good Cond Rec
      apply and_congr
      · apply and_congr Iff.rfl
        apply forall_congr'; intro s; apply imp_congr_right; intro hs
        rw [hk s hs.le, hk t le_rfl]
      · apply forall_congr'; intro j; apply imp_congr_right; intro hj
        apply not_congr; apply and_congr Iff.rfl
        apply forall_congr'; intro s; apply imp_congr_right; intro hs
        rw [hk s (hs.trans hj).le, hk j hj.le]
    have : tauP r p = some t ↔ tauP r q = some t := by
      unfold tauP; rw [stopT_eq_some_iff, stopT_eq_some_iff]; exact hG
    show Measure.dirac (tauP r p) {some t} = Measure.dirac (tauP r q) {some t}
    rw [Measure.dirac_apply' _ (measurableSet_singleton _),
      Measure.dirac_apply' _ (measurableSet_singleton _)]
    by_cases hp : tauP r p = some t
    · have hq := this.1 hp
      simp [hp, hq]
    · have hq : ¬ tauP r q = some t := fun h => hp (this.2 h)
      simp [hp, hq]

end Prob

section Final
open Equiv

lemma cutoff_le {m : ℕ} {L : Type} [LinearOrder L] (r : ℕ) (hr1 : 1 ≤ r) (hrm : r ≤ m)
    (k : Fin m → L) (hk : Function.Injective k) (M : Fin m) (hM : ∀ i, k i ≤ k M) :
    cutoffProbability m r ≤ ((SuccS k M (r - 1)).card : ℝ) / m.factorial := by
  have hm : 0 < m := by omega
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [le_div_iff₀ hfac]
  unfold cutoffProbability
  by_cases h1 : r = 1
  · subst h1
    simp only [if_true]
    have e : SuccS k M (1 - 1) = SuccS k M 0 := rfl
    rw [e, SuccS_zero hm]
    have h2 := m_mul_N hm M ⟨0, hm⟩
    have h2' : (m : ℝ) * Nn M ⟨0, hm⟩ = m.factorial := by exact_mod_cast h2
    rw [← h2']
    field_simp
    exact le_rfl
  · simp only [h1, if_false]
    have hr2 : 1 ≤ r - 1 := by omega
    have H := count_ge k hk M hM (r - 1) hr2 (by omega)
    have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub hr1]; simp
    rw [hcast] at H
    have hS : ∑ t ∈ Finset.Icc r m, 1 / ((t : ℝ) - 1)
        = ∑ n ∈ Finset.Ico (r - 1) m, 1 / (n : ℝ) := by
      refine Finset.sum_nbij' (fun t => t - 1) (fun n => n + 1) ?_ ?_ ?_ ?_ ?_
      · intro a ha; simp only [Finset.mem_Icc, Finset.mem_Ico] at ha ⊢; omega
      · intro a ha; simp only [Finset.mem_Icc, Finset.mem_Ico] at ha ⊢; omega
      · intro a ha; simp only [Finset.mem_Icc] at ha; omega
      · intro a ha; simp
      · intro a ha
        simp only [Finset.mem_Icc] at ha
        rw [Nat.cast_sub (by omega)]; simp
    rw [hS]
    have e : ((r : ℝ) - 1) / m * (∑ n ∈ Finset.Ico (r - 1) m, 1 / (n : ℝ)) * m.factorial
        = (m.factorial * (((r : ℝ) - 1) * ∑ n ∈ Finset.Ico (r - 1) m, 1 / (n : ℝ))) / m := by
      field_simp
    rw [e, div_le_iff₀ hmpos]
    linarith

lemma success_ge {m : ℕ} (D : Type) [MeasurableSpace D] (r : ℕ) (hr1 : 1 ≤ r) (hrm : r ≤ m)
    (d : D) (μ : Fin m → Distribution) :
    cutoffProbability m r ≤ success (pol D m (r - 1)) d μ := by
  classical
  have hm : 0 < m := by omega
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  set π := pol D m (r - 1) with hπ
  set A : Set (Path m) := (fun p => (p, tauP (r - 1) p)) ⁻¹' successEvent m with hA
  have hAmeas : MeasurableSet A :=
    (measurable_id.prodMk (measurable_tau _)) (successEvent_measurable m)
  have h1 : ((outcomeLaw π d μ : ProbabilityMeasure _) : Measure _) (successEvent m)
      = (experiment μ : Measure (Path m)) A := by
    show ((experiment μ : Measure (Path m)) ⊗ₘ fixedKernel π d) (successEvent m) = _
    rw [Measure.compProd_apply (successEvent_measurable m)]
    have : ∀ p : Path m, fixedKernel π d p (Prod.mk p ⁻¹' successEvent m) = A.indicator 1 p := by
      intro p
      show Measure.dirac (tauP (r - 1) p) _ = _
      rw [Measure.dirac_apply' _ (measurable_prodMk_left (successEvent_measurable m))]
      rfl
    simp_rw [this]
    exact lintegral_indicator_one hAmeas
  have h2 : (experiment μ : Measure (Path m)) A
      = ∫⁻ v, (uniformPermutation m : Measure _) ((fun σ => (σ, v)) ⁻¹' A)
          ∂(Measure.pi fun i => (μ i : Measure ℝ≥0)) := by
    show ((uniformPermutation m : Measure _).prod (Measure.pi fun i => (μ i : Measure ℝ≥0))) A = _
    rw [Measure.prod_apply_symm hAmeas]
  have h3 : ∀ v : Fin m → ℝ≥0, ENNReal.ofReal (cutoffProbability m r)
      ≤ (uniformPermutation m : Measure _) ((fun σ => (σ, v)) ⁻¹' A) := by
    intro v
    obtain ⟨M, -, hM⟩ := Finset.exists_max_image Finset.univ (key v)
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    have hsub : (↑(SuccS (key v) M (r - 1)) : Set (Perm (Fin m))) ⊆ (fun σ => (σ, v)) ⁻¹' A := by
      intro σ hσ
      have hσ' : σ ∈ SuccS (key v) M (r - 1) := hσ
      simp only [SuccS, Finset.mem_filter, Finset.mem_univ, true_and] at hσ'
      obtain ⟨t, ht, hσt⟩ := hσ'
      refine ⟨t, ht, fun i => ?_⟩
      show v i ≤ v (σ t)
      rw [hσt]
      exact key_le_imp v _ _ (hM i (Finset.mem_univ _))
    refine le_trans ?_ (measure_mono hsub)
    have hU : (uniformPermutation m : Measure (Perm (Fin m))) ↑(SuccS (key v) M (r - 1))
        = ((SuccS (key v) M (r - 1)).card : ℝ≥0∞) * (m.factorial : ℝ≥0∞)⁻¹ := by
      show (PMF.uniformOfFintype (Perm (Fin m))).toMeasure _ = _
      rw [PMF.toMeasure_apply_finset]
      simp [PMF.uniformOfFintype_apply, Fintype.card_perm]
    rw [hU]
    have hc := cutoff_le r hr1 hrm (key v) (key_injective v) M (fun i => hM i (Finset.mem_univ _))
    have e : ENNReal.ofReal (((SuccS (key v) M (r - 1)).card : ℝ) / m.factorial)
        = ((SuccS (key v) M (r - 1)).card : ℝ≥0∞) * (m.factorial : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_div_of_pos hfac, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
        div_eq_mul_inv]
    rw [← e]
    exact ENNReal.ofReal_le_ofReal hc
  have h4 : ENNReal.ofReal (cutoffProbability m r) ≤ (experiment μ : Measure (Path m)) A := by
    rw [h2]
    calc ENNReal.ofReal (cutoffProbability m r)
        = ∫⁻ _ : Fin m → ℝ≥0, ENNReal.ofReal (cutoffProbability m r)
            ∂(Measure.pi fun i => (μ i : Measure ℝ≥0)) := by simp
      _ ≤ _ := lintegral_mono h3
  unfold success
  rw [h1]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 h4

/-- Lower bound (classical skip-then-record rule with continuous tie-breakers): independent of D. -/
lemma lower_generic (D : Type) [MeasurableSpace D] (m : ℕ) (hm : 1 ≤ m) :
    ∃ π : Policy D m, ∀ (d : D) (μ : Fin m → Distribution),
      classicalValue m ≤ success π d μ := by
  obtain ⟨r, hr, hsup⟩ := Finset.exists_mem_eq_sup'
    (⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hm⟩⟩ : (Finset.Icc 1 m).Nonempty) (cutoffProbability m)
  have hcv : classicalValue m = cutoffProbability m r := by
    unfold classicalValue; rw [dif_pos hm]; exact hsup
  refine ⟨pol D m (r - 1), fun d μ => ?_⟩
  rw [hcv]
  obtain ⟨hr1, hrm⟩ := Finset.mem_Icc.mp hr
  exact success_ge D r hr1 hrm d μ

end Final

end MomentAmbiguitySecretary.Secretary.Dev.SecLower
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary.Dev.SecUpper

open MomentAmbiguitySecretary.Secretary

section PiSplit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

lemma pi_split (μ ρ : ∀ i, Measure (α i)) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, IsFiniteMeasure (ρ i)] :
    Measure.pi (fun i => μ i + ρ i) =
      ∑ S : Finset ι, Measure.pi (fun i => if i ∈ S then μ i else ρ i) := by
  refine Measure.pi_eq (μ := fun i => μ i + ρ i) ?_
  intro s hs
  haveI : ∀ S : Finset ι, ∀ i, SigmaFinite (if i ∈ S then μ i else ρ i) := fun S i => by
    split_ifs <;> infer_instance
  rw [Measure.finsetSum_apply]
  have : ∀ S : Finset ι, Measure.pi (fun i => if i ∈ S then μ i else ρ i) (Set.pi univ s)
      = (∏ i ∈ S, μ i (s i)) * ∏ i ∈ Finset.univ \ S, ρ i (s i) := by
    intro S
    rw [Measure.pi_pi]
    have h2 : ∀ i, (if i ∈ S then μ i else ρ i) (s i) = if i ∈ S then μ i (s i) else ρ i (s i) :=
      fun i => by split_ifs <;> rfl
    simp_rw [h2]
    rw [Finset.prod_ite]
    congr 2
    · ext; simp
    · ext; simp
  simp_rw [this]
  simp only [Measure.add_apply]
  rw [Finset.prod_add]
  simp [Finset.powerset_univ]

lemma pi_mono (μ ν : ∀ i, Measure (α i)) [∀ i, IsFiniteMeasure (μ i)]
    [∀ i, IsFiniteMeasure (ν i)] (h : ∀ i, μ i ≤ ν i) :
    Measure.pi μ ≤ Measure.pi ν := by
  have hρ : ∀ i, IsFiniteMeasure (ν i - μ i) := fun i => inferInstance
  have hν : ν = fun i => μ i + (ν i - μ i) := by
    funext i; rw [add_comm]; exact (Measure.sub_add_cancel_of_le (h i)).symm
  have := pi_split μ (fun i => ν i - μ i)
  rw [← hν] at this
  rw [this]
  refine le_trans ?_ (Finset.single_le_sum (f := fun S : Finset ι =>
    Measure.pi (fun i => if i ∈ S then μ i else (ν i - μ i))) (fun _ _ => Measure.zero_le _)
    (Finset.mem_univ Finset.univ))
  simp

end PiSplit


section CompProd

lemma compProd_le_add {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (κ : Kernel X Y) [IsMarkovKernel κ] (P Q R : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q] [IsFiniteMeasure R] (hP : R ≤ P) (hQ : R ≤ Q) (S : Set (X × Y)) :
    (P ⊗ₘ κ) S ≤ (Q ⊗ₘ κ) S + (P univ - R univ) := by
  have e1 : P = (P - R) + R := (Measure.sub_add_cancel_of_le hP).symm
  have e2 : Q = (Q - R) + R := (Measure.sub_add_cancel_of_le hQ).symm
  have h1 : (P ⊗ₘ κ) S = ((P - R) ⊗ₘ κ) S + (R ⊗ₘ κ) S := by
    conv_lhs => rw [e1]
    rw [Measure.compProd_add_left, Measure.add_apply]
  have h2 : (Q ⊗ₘ κ) S = ((Q - R) ⊗ₘ κ) S + (R ⊗ₘ κ) S := by
    conv_lhs => rw [e2]
    rw [Measure.compProd_add_left, Measure.add_apply]
  have h3 : ((P - R) ⊗ₘ κ) S ≤ P univ - R univ := by
    calc ((P - R) ⊗ₘ κ) S ≤ ((P - R) ⊗ₘ κ) univ := measure_mono (subset_univ _)
      _ = (P - R) univ := Measure.compProd_apply_univ
      _ = P univ - R univ := Measure.sub_apply MeasurableSet.univ hP
  rw [h1, h2]
  calc ((P - R) ⊗ₘ κ) S + (R ⊗ₘ κ) S ≤ (P univ - R univ) + (R ⊗ₘ κ) S := by gcongr
    _ ≤ _ := by
      rw [add_comm]
      gcongr
      exact le_add_self

end CompProd


section Mix

variable {N : ℕ}

noncomputable def mix (k : ℕ) (H : Finset (Fin N)) (μ : Fin N → Measure ℝ≥0) : Measure ℝ≥0 :=
  ∑ h ∈ H, (k : ℝ≥0∞)⁻¹ • μ h

lemma mix_univ (k : ℕ) (H : Finset (Fin N)) (hk : H.card = k) (hk0 : 0 < k)
    (μ : Fin N → Measure ℝ≥0) (hμ : ∀ h, IsProbabilityMeasure (μ h)) :
    mix k H μ univ = 1 := by
  simp only [mix, Measure.finsetSum_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one, Finset.sum_const, nsmul_eq_mul, hk]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast hk0.ne') (by simp)

lemma mix_integrable (k : ℕ) (hk0 : 0 < k) (H : Finset (Fin N)) (μ : Fin N → Measure ℝ≥0) (f : ℝ≥0 → ℝ)
    (hf : ∀ h, Integrable f (μ h)) : Integrable f (mix k H μ) := by
  unfold mix
  rw [integrable_finset_sum_measure]
  intro h _
  exact (hf h).smul_measure (by simpa using hk0.ne')

lemma mix_integral (k : ℕ) (H : Finset (Fin N)) (hk : H.card = k) (hk0 : 0 < k)
    (μ : Fin N → Measure ℝ≥0) (f : ℝ≥0 → ℝ) (hf : ∀ h, Integrable f (μ h)) (c : ℝ)
    (hc : ∀ h, ∫ x, f x ∂(μ h) = c) : ∫ x, f x ∂(mix k H μ) = c := by
  unfold mix
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, hc, smul_eq_mul]
    rw [← Finset.sum_mul, Finset.sum_const, hk, nsmul_eq_mul]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    field_simp
  · intro h _
    exact (hf h).smul_measure (by simpa using hk0.ne')

end Mix

section Succ

lemma succ_le {m : ℕ} (π : IIDPolicy m) (d : Disclosure) (ψ g : Distribution)
    (ψ₀ : Measure ℝ≥0) [IsFiniteMeasure ψ₀]
    (h1 : ψ₀ ≤ (ψ : Measure ℝ≥0)) (h2 : ψ₀ ≤ (g : Measure ℝ≥0)) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmass : 1 - δ ≤ (ψ₀ univ).toReal) :
    success π d (fun _ : Fin m => ψ) ≤ success π d (fun _ : Fin m => g) + m * δ := by
  set U : Measure (Equiv.Perm (Fin m)) := (uniformPermutation m).toMeasure with hU
  haveI : IsProbabilityMeasure U := inferInstance
  have hexp : ∀ g' : Distribution, (experiment (fun _ : Fin m => g') : Measure (Path m)) =
      U.prod (Measure.pi fun _ : Fin m => (g' : Measure ℝ≥0)) := fun _ => rfl
  have hR : IsFiniteMeasure (Measure.pi fun _ : Fin m => ψ₀) := inferInstance
  have hRP : U.prod (Measure.pi fun _ : Fin m => ψ₀) ≤
      U.prod (Measure.pi fun _ : Fin m => (ψ : Measure ℝ≥0)) :=
    Measure.prod_mono le_rfl (pi_mono _ _ (fun _ => h1))
  have hRQ : U.prod (Measure.pi fun _ : Fin m => ψ₀) ≤
      U.prod (Measure.pi fun _ : Fin m => (g : Measure ℝ≥0)) :=
    Measure.prod_mono le_rfl (pi_mono _ _ (fun _ => h2))
  have key := compProd_le_add (fixedKernel π d) _ _ _ hRP hRQ (successEvent m)
  have hPu : (U.prod (Measure.pi fun _ : Fin m => (ψ : Measure ℝ≥0))) univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.pi_univ]; simp
  have hRu : (U.prod (Measure.pi fun _ : Fin m => ψ₀)) univ = (ψ₀ univ) ^ m := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.pi_univ]; simp
  rw [hPu, hRu] at key
  have hs : ∀ g' : Distribution, success π d (fun _ : Fin m => g') =
      ((U.prod (Measure.pi fun _ : Fin m => (g' : Measure ℝ≥0)) ⊗ₘ fixedKernel π d)
        (successEvent m)).toReal := fun _ => rfl
  rw [hs, hs]
  have hfin : (U.prod (Measure.pi fun _ : Fin m => (g : Measure ℝ≥0)) ⊗ₘ fixedKernel π d)
      (successEvent m) ≠ ∞ := measure_ne_top _ _
  have ha1 : ψ₀ univ ≤ 1 := by
    calc ψ₀ univ ≤ (ψ : Measure ℝ≥0) univ := h1 _
      _ = 1 := by simp
  have hpow1 : (ψ₀ univ) ^ m ≤ 1 := pow_le_one₀ (zero_le) ha1
  have h3 := ENNReal.toReal_mono (by simp [ENNReal.add_eq_top, hfin, hpow1, ENNReal.sub_eq_top_iff]) key
  rw [ENNReal.toReal_add hfin (by simp), ENNReal.toReal_sub_of_le hpow1 (by simp),
    ENNReal.toReal_pow] at h3
  have ha : 1 - δ ≤ (ψ₀ univ).toReal := hmass
  have hb : (1 - δ) ^ m ≤ (ψ₀ univ).toReal ^ m := pow_le_pow_left₀ (by linarith) ha m
  have hc : 1 + (m : ℝ) * (-δ) ≤ (1 + (-δ)) ^ m := one_add_mul_le_pow (by linarith) m
  simp only [ENNReal.toReal_one] at h3
  have : (1 - δ) = 1 + (-δ) := by ring
  rw [this] at hb
  nlinarith

end Succ


section Fix

/-- An iid policy with its disclosure fixed is a cardinal policy. -/
noncomputable def fixPolicy {m : ℕ} (π : IIDPolicy m) (d : Disclosure) : CardinalPolicy m where
  kernel := π.kernel.comap (fun x : Unit × Path m => (d, x.2)) (by fun_prop)
  markov := by infer_instance
  causal := by
    intro _ p q t h
    exact π.causal d p q t h

end Fix

section MixLemmas

variable {N : ℕ}

lemma mix_mono (k : ℕ) (H : Finset (Fin N)) (ν μ : Fin N → Measure ℝ≥0)
    (h : ∀ i, ν i ≤ μ i) : mix k H ν ≤ mix k H μ := by
  rw [Measure.le_iff']
  intro s
  simp only [mix, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (h i s)

lemma restrict_le_dirac (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (x : ℝ≥0) :
    μ.restrict {x} ≤ Measure.dirac x := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.restrict_apply hs]
  by_cases hx : x ∈ s
  · rw [Measure.dirac_apply_of_mem hx]; exact prob_le_one
  · have : s ∩ {x} = ∅ := by
      ext y; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false]
      rintro ⟨h1, rfl⟩; exact hx h1
    rw [this]; simp

end MixLemmas


lemma upper_core (m : ℕ) (hm : 1 ≤ m) (π : IIDPolicy m) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    iidGuarantee π ≤ classicalValue m + ε := by
  have hm0 : 0 < m := hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  -- choice of k
  obtain ⟨k, hkm, hk⟩ : ∃ k : ℕ, m ≤ k ∧ (Nat.choose m 2 : ℝ) / k ≤ ε / 3 := by
    refine ⟨max m ⌈3 * (m : ℝ) ^ 2 / ε⌉₊, le_max_left _ _, ?_⟩
    have hk1 : 3 * (m : ℝ) ^ 2 / ε ≤ (max m ⌈3 * (m : ℝ) ^ 2 / ε⌉₊ : ℕ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    have hkpos : (0 : ℝ) < (max m ⌈3 * (m : ℝ) ^ 2 / ε⌉₊ : ℕ) := by
      have : 0 < max m ⌈3 * (m : ℝ) ^ 2 / ε⌉₊ := lt_of_lt_of_le hm0 (le_max_left _ _)
      exact_mod_cast this
    have hch : (Nat.choose m 2 : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow m 2
    rw [div_le_iff₀ hkpos]
    rw [div_le_iff₀ hε] at hk1
    nlinarith
  have hk0 : 0 < k := lt_of_lt_of_le hm0 hkm
  obtain ⟨N₀, hkN₀, hR⟩ := ramsey_secretary_grid m k hm hkm (ε / 3) (by positivity)
  set N : ℕ := max 2 N₀ with hNdef
  have hN : 2 ≤ N := le_max_left _ _
  have hNN : N₀ ≤ N := le_max_right _ _
  set δ : ℝ := ε / (3 * m) with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hmδ : (m : ℝ) * δ = ε / 3 := by rw [hδdef]; field_simp
  obtain ⟨B, hB2, hBfa⟩ : ∃ B : ℕ, 2 ≤ B ∧ 1 - δ < minimumFirstAtom B N := by
    have h2 : ∀ᶠ B : ℕ in atTop, 1 - δ < minimumFirstAtom B N :=
      (first_atom_concentration N hN).eventually (lt_mem_nhds (by linarith))
    exact ((eventually_ge_atTop 2).and h2).exists
  obtain ⟨-, -, -, -, hE, -, hG, -⟩ := n_way_separator B N hB2 hN
  let μh : Fin N → Distribution := fun h => ⟨residueMeasure B N h.val, (hE h).1⟩
  have hμh : ∀ h, (μh h : Measure ℝ≥0) = residueMeasure B N h.val := fun h => rfl
  have hmom : ∀ h, HasAllMoments (μh h) := fun h t => (hE h).2.2.2 t
  let h0 : Fin N := ⟨0, by omega⟩
  let d₀ : Disclosure := disclose ⟨μh h0, hmom h0⟩
  have hint : ∀ h t, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ t) (μh h : Measure ℝ≥0) :=
    fun h t => hmom h t
  -- the grid
  let v : Fin N → ℝ≥0 := fun h => (B : ℝ≥0) ^ h.val
  have hv : StrictMono v := by
    intro a b hab
    have hB : (1 : ℝ≥0) < B := by exact_mod_cast hB2
    exact pow_lt_pow_right₀ hB hab
  obtain ⟨H, hHk, hHs⟩ := hR N hNN v hv (fixPolicy π d₀)
  -- the mixture
  have hHne : H.Nonempty := Finset.card_pos.1 (hHk ▸ hk0)
  have hprob : IsProbabilityMeasure (mix k H (fun h => (μh h : Measure ℝ≥0))) :=
    ⟨mix_univ k H hHk hk0 _ (fun h => inferInstance)⟩
  let ψ : Distribution := ⟨mix k H (fun h => (μh h : Measure ℝ≥0)), hprob⟩
  have hψm : HasAllMoments ψ := fun t =>
    mix_integrable k hk0 H _ _ (fun h => hint h t)
  let ψL : Law := ⟨ψ, hψm⟩
  have hψmom : moments ψ = moments (μh h0) := by
    funext t
    exact mix_integral k H hHk hk0 _ _ (fun h => hint h t) _
      (fun h => hG h h0 t)
  have hdisc : disclose ψL = d₀ := Subtype.ext hψmom
  -- compare with the grid
  have hgrid : (gridDistribution v H : Measure ℝ≥0) =
      mix k H (fun h => Measure.dirac (v h)) := by
    simp [gridDistribution, hHne, hHk, mix]
  let ψ₀ : Measure ℝ≥0 := mix k H (fun h => (μh h : Measure ℝ≥0).restrict {v h})
  have hψ₀ψ : ψ₀ ≤ (ψ : Measure ℝ≥0) :=
    mix_mono k H _ _ (fun h => Measure.restrict_le_self)
  have hψ₀g : ψ₀ ≤ (gridDistribution v H : Measure ℝ≥0) := by
    rw [hgrid]
    exact mix_mono k H _ _ (fun h => restrict_le_dirac _ _)
  haveI : IsFiniteMeasure ψ₀ := by
    refine ⟨lt_of_le_of_lt (hψ₀ψ _) ?_⟩
    simp
  have hmass : 1 - δ ≤ (ψ₀ univ).toReal := by
    have hatom : ∀ h : Fin N, 1 - δ ≤ ((μh h : Measure ℝ≥0) {v h}).toReal := by
      intro h
      refine hBfa.le.trans ?_
      unfold minimumFirstAtom
      rw [dif_pos (by omega)]
      exact Finset.inf'_le (fun h : Fin N => (residueMeasure B N h.val {((B : ℝ≥0) ^ h.val)}).toReal)
        (Finset.mem_univ h)
    simp only [ψ₀, mix, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply MeasurableSet.univ, univ_inter]
    rw [ENNReal.toReal_sum (fun h _ => ENNReal.mul_ne_top (by simpa using hk0.ne') (measure_ne_top _ _))]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    calc 1 - δ = ∑ h ∈ H, (k : ℝ)⁻¹ * (1 - δ) := by
          rw [Finset.sum_const, hHk, nsmul_eq_mul]; field_simp
      _ ≤ _ := Finset.sum_le_sum fun h _ => by
          have := hatom h
          gcongr
  have h1 := succ_le π d₀ ψ (gridDistribution v H) ψ₀ hψ₀ψ hψ₀g δ hδ.le hδ1 hmass
  have h2 : iidGuarantee π ≤ success π d₀ (fun _ : Fin m => ψ) := by
    have hb : BddBelow (Set.range (iidSuccess π)) :=
      ⟨0, by rintro _ ⟨μ, rfl⟩; exact (success_mem_unit π _ _).1⟩
    refine (ciInf_le hb ψL).trans ?_
    unfold iidSuccess
    rw [hdisc]
  have h3 : success π d₀ (fun _ : Fin m => gridDistribution v H) ≤
      classicalValue m + ε / 3 + (Nat.choose m 2 : ℝ) / k := hHs
  linarith


/-- Upper bound (Ramsey grid + N-way separator mixtures). -/
lemma upper_iid (m : ℕ) (hm : 1 ≤ m) (π : IIDPolicy m) (ε : ℝ) (hε : 0 < ε) :
    iidGuarantee π ≤ classicalValue m + ε := by
  have := upper_core m hm π (min ε 1) (lt_min hε one_pos) (min_le_right _ _)
  linarith [min_le_left ε 1]

end MomentAmbiguitySecretary.Secretary.Dev.SecUpper

end

section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary.Dev.GoalBP

/-- An independent policy gives an iid policy. -/
noncomputable def toIID {m : ℕ} (π : IndependentPolicy m) : IIDPolicy m where
  kernel := π.kernel.comap (fun x => ((fun _ => x.1 : Fin m → Disclosure), x.2))
    (by fun_prop)
  markov := by infer_instance
  causal := by
    intro d p q t h
    exact π.causal _ p q t h

lemma indepGuarantee_le {m : ℕ} (π : IndependentPolicy m) : independentGuarantee π ≤ iidGuarantee (toIID π) := by
  apply le_ciInf
  intro μ
  refine (ciInf_le ?_ (fun _ => μ)).trans ?_
  · exact ⟨0, by rintro _ ⟨ν, rfl⟩; exact (success_mem_unit _ _ _).1⟩
  · apply le_of_eq
    simp only [independentSuccess, iidSuccess, success, outcomeLaw, fixedKernel, toIID]
    rfl

end MomentAmbiguitySecretary.Secretary.Dev.GoalBP

namespace MomentAmbiguitySecretary.Secretary
open Dev.GoalBP in
theorem chk_robust_secretary_value (m : ℕ) (hm : 1 ≤ m) :
    independentValue m = classicalValue m ∧ iidValue m = classicalValue m := by
  have hup : ∀ π : IIDPolicy m, iidGuarantee π ≤ classicalValue m := fun π =>
    le_of_forall_pos_le_add fun ε hε => Dev.SecUpper.upper_iid m hm π ε hε
  have hlow : ∀ D : Type, ∀ _ : MeasurableSpace D, ∀ π : Policy D m, True := fun _ _ _ => trivial
  constructor
  · apply le_antisymm
    · apply ciSup_le
      intro π
      exact (indepGuarantee_le π).trans (hup _)
    · obtain ⟨π, hπ⟩ := Dev.SecLower.lower_generic (Fin m → Disclosure) m hm
      refine le_trans ?_ (le_ciSup ⟨1, by rintro _ ⟨π, rfl⟩; exact (independentGuarantee_mem_unit π).2⟩ π)
      exact le_ciInf fun μ => hπ _ _
  · apply le_antisymm
    · exact ciSup_le hup
    · obtain ⟨π, hπ⟩ := Dev.SecLower.lower_generic Disclosure m hm
      refine le_trans ?_ (le_ciSup ⟨1, by rintro _ ⟨π, rfl⟩; exact (iidGuarantee_mem_unit π).2⟩ π)
      exact le_ciInf fun μ => hπ _ _
end MomentAmbiguitySecretary.Secretary
end

theorem solution : type_of% @MomentAmbiguitySecretary.Secretary.chk_robust_secretary_value := @MomentAmbiguitySecretary.Secretary.chk_robust_secretary_value
