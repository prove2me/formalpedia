-- Prove2me | solution 1 for NegativeDP.Stationary.lemma21
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T11:21:34.594039+00:00
-- url     : https://prove2.me/submissions/f51b08a4-230b-4d5f-b8c6-2cad4ad4fb7d

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Classical

/-! Strauch Lemma 2.1 (N). Selection from a Borel set `B ⊆ X × Y` whose sections have positive
kernel mass (Blackwell / Ryll-Nardzewski): refine the Polish topology on `X × Y` so that `B` is
closed, then pick a nested sequence of small Borel cells of positive section mass greedily. -/

namespace NegativeDP.Stationary.L21Sel

section Core

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MetricSpace (X × Y)] [BorelSpace (X × Y)]
  (B : Set (X × Y)) (z : ℕ → X × Y) (κ : Kernel X Y)

/-- Radius at level `n`. -/
noncomputable def rad (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

lemma rad_pos (n : ℕ) : 0 < rad n := by unfold rad; positivity

lemma rad_succ_le (n : ℕ) : rad (n + 1) ≤ rad n := by
  unfold rad
  have hk : 0 < (1 / 2 : ℝ) ^ n := by positivity
  rw [pow_succ]
  linarith

/-- Cell predicate: `k` is a center within `rad n`, or no center is. -/
def CellP (n : ℕ) (p : X × Y) (k : ℕ) : Prop :=
  dist p (z k) < rad n ∨ ∀ m, ¬ dist p (z m) < rad n

lemma CellP_exists (n : ℕ) (p : X × Y) : ∃ k, CellP z n p k := by
  by_cases h : ∃ k, dist p (z k) < rad n
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Or.inl hk⟩
  · push_neg at h
    exact ⟨0, Or.inr fun m hm => absurd hm (not_lt.2 (h m))⟩

/-- Index of the first center within `rad n` of `p`. -/
noncomputable def cell (n : ℕ) (p : X × Y) : ℕ := Nat.find (CellP_exists z n p)

lemma measurable_cell (n : ℕ) : Measurable (cell z n) := by
  refine measurable_find (p := fun p k => CellP z n p k) (CellP_exists z n) fun k => ?_
  have h1 : ∀ m, MeasurableSet {p : X × Y | dist p (z m) < rad n} := fun m =>
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const).measurableSet
  have : {p : X × Y | CellP z n p k} =
      {p | dist p (z k) < rad n} ∪ ⋂ m, {p | dist p (z m) < rad n}ᶜ := by
    ext p
    simp [CellP]
  rw [this]
  exact (h1 k).union (MeasurableSet.iInter fun m => (h1 m).compl)

/-- Points of `B` whose first `l.length` cell indices are `l`. -/
def P (l : List ℕ) : Set (X × Y) := B ∩ {p | ∀ i < l.length, cell z i p = l.getD i 0}

lemma measurableSet_P (hB : MeasurableSet B) (l : List ℕ) : MeasurableSet (P B z l) := by
  refine hB.inter ?_
  simp only [setOf_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurable_cell z i (measurableSet_singleton (l.getD i 0))

lemma P_nil : P B z [] = B := by
  ext p
  simp [P]

lemma P_anti {l l' : List ℕ} (h : l <+: l') : P B z l' ⊆ P B z l := by
  obtain ⟨t, rfl⟩ := h
  rintro p ⟨hpB, hp⟩
  refine ⟨hpB, fun i hi => ?_⟩
  rw [hp i (by simp only [List.length_append]; omega), List.getD_append _ _ _ _ hi]

lemma P_subset_iUnion (l : List ℕ) : P B z l ⊆ ⋃ m, P B z (l ++ [m]) := by
  rintro p ⟨hpB, hp⟩
  refine mem_iUnion.2 ⟨cell z l.length p, hpB, fun i hi => ?_⟩
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
  · rw [List.getD_append _ _ _ _ hi]
    exact hp i hi
  · subst hi
    rw [List.getD_append_right _ _ _ _ le_rfl]
    simp

/-- Section mass of a cell. -/
noncomputable def mass (l : List ℕ) (x : X) : ℝ≥0∞ := κ x (Prod.mk x ⁻¹' P B z l)

/-- Greedy predicate: the child `n` has positive mass, or no child has. -/
def Pr (l : List ℕ) (x : X) (n : ℕ) : Prop :=
  mass B z κ (l ++ [n]) x ≠ 0 ∨ ∀ m, mass B z κ (l ++ [m]) x = 0

lemma Pr_exists (l : List ℕ) (x : X) : ∃ n, Pr B z κ l x n := by
  by_cases h : ∃ n, mass B z κ (l ++ [n]) x ≠ 0
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inl hn⟩
  · push_neg at h
    exact ⟨0, Or.inr h⟩

/-- Greedy prefixes. -/
noncomputable def pre (x : X) : ℕ → List ℕ
  | 0 => []
  | k + 1 => pre x k ++ [Nat.find (Pr_exists B z κ (pre x k) x)]

/-- The selected center index at level `i`. -/
noncomputable def sel (x : X) (i : ℕ) : ℕ := (pre B z κ x (i + 1)).getD i 0

lemma pre_succ (x : X) (k : ℕ) :
    pre B z κ x (k + 1) = pre B z κ x k ++ [Nat.find (Pr_exists B z κ (pre B z κ x k) x)] := rfl

lemma length_pre (x : X) (k : ℕ) : (pre B z κ x k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pre_succ]; simp [ih]

lemma prefix_pre (x : X) {k k' : ℕ} (h : k ≤ k') : pre B z κ x k <+: pre B z κ x k' := by
  induction k', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih => rw [pre_succ]; exact ih.trans (List.prefix_append _ _)

lemma mass_pre (x : X) (h0 : κ x (Prod.mk x ⁻¹' B) ≠ 0) :
    ∀ k, mass B z κ (pre B z κ x k) x ≠ 0 := by
  intro k
  induction k with
  | zero => simpa [mass, pre, P_nil] using h0
  | succ k ih =>
    rw [pre_succ]
    have hex : ∃ n, mass B z κ (pre B z κ x k ++ [n]) x ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply ih
      refine measure_mono_null (preimage_mono (P_subset_iUnion B z _)) ?_
      rw [preimage_iUnion]
      exact measure_iUnion_null hall
    rcases Nat.find_spec (Pr_exists B z κ (pre B z κ x k) x) with hs | hs
    · exact hs
    · obtain ⟨n, hn⟩ := hex
      exact absurd (hs n) hn

lemma dist_center (hz : ∀ p ∈ B, ∀ ε > 0, ∃ k, dist p (z k) < ε) (x : X) (k : ℕ)
    {p : X × Y} (hp : p ∈ P B z (pre B z κ x (k + 1))) :
    dist p (z (sel B z κ x k)) < rad k := by
  obtain ⟨hpB, hpc⟩ := hp
  have hc : cell z k p = sel B z κ x k := hpc k (by rw [length_pre]; omega)
  rw [← hc]
  rcases Nat.find_spec (CellP_exists z k p) with h | h
  · exact h
  · obtain ⟨m, hm⟩ := hz p hpB (rad k) (rad_pos k)
    exact absurd hm (h m)

lemma measurableSet_pre_eq [IsSFiniteKernel κ] (hB : MeasurableSet B) :
    ∀ k (l : List ℕ), MeasurableSet {x | pre B z κ x k = l} := by
  intro k
  induction k with
  | zero =>
    intro l
    show MeasurableSet {_x : X | ([] : List ℕ) = l}
    exact MeasurableSet.const _
  | succ k ih =>
    intro l
    have hfind : ∀ l' : List ℕ, Measurable fun x => Nat.find (Pr_exists B z κ l' x) := by
      intro l'
      refine measurable_find (p := fun x n => Pr B z κ l' x n) (Pr_exists B z κ l') fun n => ?_
      have hm : ∀ m, Measurable (mass B z κ (l' ++ [m])) := fun m =>
        Kernel.measurable_kernel_prodMk_left (measurableSet_P B z hB _)
      have : {x | Pr B z κ l' x n} =
          (mass B z κ (l' ++ [n]) ⁻¹' {0})ᶜ ∪ ⋂ m, mass B z κ (l' ++ [m]) ⁻¹' {0} := by
        ext x
        simp [Pr]
      rw [this]
      exact ((hm n) (measurableSet_singleton 0)).compl.union
        (MeasurableSet.iInter fun m => (hm m) (measurableSet_singleton 0))
    have : {x | pre B z κ x (k + 1) = l} = ⋃ l' : List ℕ, {x | pre B z κ x k = l'} ∩
        (fun x => Nat.find (Pr_exists B z κ l' x)) ⁻¹' {n | l' ++ [n] = l} := by
      ext x
      simp [pre_succ]
    rw [this]
    exact MeasurableSet.iUnion fun l' => (ih l').inter (hfind l' (MeasurableSet.of_discrete))

lemma measurable_sel [IsSFiniteKernel κ] (hB : MeasurableSet B) (k : ℕ) :
    Measurable fun x => sel B z κ x k := by
  refine measurable_to_countable' fun n => ?_
  have : (fun x => sel B z κ x k) ⁻¹' {n} =
      ⋃ l : List ℕ, {x | pre B z κ x (k + 1) = l} ∩ {_x | l.getD k 0 = n} := by
    ext x
    simp [sel]
  rw [this]
  exact MeasurableSet.iUnion fun l =>
    (measurableSet_pre_eq B z κ hB (k + 1) l).inter (MeasurableSet.const _)

theorem core [CompleteSpace (X × Y)] [IsSFiniteKernel κ] (hB : MeasurableSet B)
    (hBc : IsClosed B) (hfib : ∀ x : X, IsClosed {p : X × Y | p.1 = x})
    (hzB : ∀ k, z k ∈ B) (hz : ∀ p ∈ B, ∀ ε > 0, ∃ k, dist p (z k) < ε)
    (hpos : ∀ x, κ x (Prod.mk x ⁻¹' B) ≠ 0) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, (x, f x) ∈ B := by
  haveI : Nonempty (X × Y) := ⟨z 0⟩
  have hpt : ∀ x k, ∃ y, (x, y) ∈ P B z (pre B z κ x (k + 1)) := by
    intro x k
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero (mass_pre B z κ x (hpos x) (k + 1))
    exact ⟨y, hy⟩
  choose py hpy using hpt
  set w : X → ℕ → X × Y := fun x k => z (sel B z κ x k) with hw
  have hdw : ∀ x k, dist (x, py x k) (w x k) < rad k := fun x k =>
    dist_center B z κ hz x k (hpy x k)
  have hdw' : ∀ x k, dist (x, py x (k + 1)) (w x k) < rad k := fun x k =>
    dist_center B z κ hz x k (P_anti B z (prefix_pre B z κ x (by omega)) (hpy x (k + 1)))
  have hcauchy : ∀ x, CauchySeq (w x) := by
    intro x
    refine cauchySeq_of_le_geometric_two (C := 4) fun k => ?_
    have h1 := hdw' x k
    have h2 := hdw x (k + 1)
    have hr := rad_succ_le k
    rw [dist_comm] at h1
    calc dist (w x k) (w x (k + 1))
        ≤ dist (w x k) (x, py x (k + 1)) + dist (x, py x (k + 1)) (w x (k + 1)) :=
          dist_triangle _ _ _
      _ ≤ rad k + rad k := by linarith
      _ = 4 / 2 / 2 ^ k := by unfold rad; rw [div_pow, one_pow]; ring
  have hlim : ∀ x, Tendsto (w x) atTop (𝓝 (limUnder atTop (w x))) := fun x =>
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hcauchy x))
  set L : X → X × Y := fun x => limUnder atTop (w x) with hL
  have hLB : ∀ x, L x ∈ B := fun x =>
    hBc.mem_of_tendsto (hlim x) (Eventually.of_forall fun k => hzB _)
  have hrad : Tendsto rad atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hL1 : ∀ x, (L x).1 = x := by
    intro x
    have ht : Tendsto (fun k => ((x, py x k) : X × Y)) atTop (𝓝 (L x)) := by
      refine (hlim x).congr_dist ?_
      refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hrad
      rw [dist_comm]
      exact (hdw x k).le
    exact (hfib x).mem_of_tendsto ht (Eventually.of_forall fun k => rfl)
  have hwm : ∀ k, Measurable fun x => w x k := fun k =>
    measurable_from_nat.comp (measurable_sel B z κ hB k)
  have hLm : Measurable L := measurable_of_tendsto_metrizable hwm (tendsto_pi_nhds.2 hlim)
  refine ⟨fun x => (L x).2, measurable_snd.comp hLm, fun x => ?_⟩
  have : ((x, (L x).2) : X × Y) = L x := Prod.ext (hL1 x).symm rfl
  rw [this]
  exact hLB x

end Core

theorem core_polish {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [tZ : TopologicalSpace (X × Y)] [hP : PolishSpace (X × Y)] [hBor : BorelSpace (X × Y)]
    [Nonempty X] (B : Set (X × Y)) (hBc : IsClosed B)
    (hfib : ∀ x : X, IsClosed {p : X × Y | p.1 = x}) (κ : Kernel X Y) [IsSFiniteKernel κ]
    (hpos : ∀ x, κ x (Prod.mk x ⁻¹' B) ≠ 0) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, (x, f x) ∈ B := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable (X × Y)
  have hBne : B.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero (hpos x)
    exact ⟨_, hy⟩
  haveI : Nonempty B := hBne.to_subtype
  obtain ⟨z, hz⟩ := TopologicalSpace.exists_dense_seq B
  refine core B (fun k => (z k : X × Y)) κ hBc.measurableSet hBc hfib (fun k => (z k).2) ?_ hpos
  intro p hp ε hε
  obtain ⟨k, hk⟩ := hz.exists_dist_lt (⟨p, hp⟩ : B) hε
  exact ⟨k, hk⟩

end NegativeDP.Stationary.L21Sel

open MeasureTheory ProbabilityTheory Filter Topology NegativeDP.Stationary in
theorem solution {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (q : Kernel X Y) [IsMarkovKernel q] (u : X × Y → EReal) (hu : IsNegM u) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, kint q u x ≤ u (x, f x) := by
  have hum : Measurable fun p : X × Y => (-(u p)).toENNReal :=
    measurable_ereal_toENNReal.comp (continuous_neg.measurable.comp hu.1)
  have hgm : Measurable (kint q u) := by
    have h1 : Measurable fun x => ∫⁻ y, (-(u (x, y))).toENNReal ∂q x :=
      hum.lintegral_kernel_prod_right'
    exact continuous_neg.measurable.comp (measurable_coe_ennreal_ereal.comp h1)
  obtain ⟨B, hBdef⟩ : ∃ B : Set (X × Y), B = {p | kint q u p.1 ≤ u p} := ⟨_, rfl⟩
  have hBm : MeasurableSet B := by
    rw [hBdef]
    exact measurableSet_le (hgm.comp measurable_fst) hu.1
  have hpos : ∀ x, q x (Prod.mk x ⁻¹' B) ≠ 0 := by
    intro x h0
    obtain ⟨I, hI⟩ : ∃ I : ℝ≥0∞, I = ∫⁻ y, (-(u (x, y))).toENNReal ∂q x := ⟨_, rfl⟩
    have hk : kint q u x = -((I : ℝ≥0∞) : EReal) := by rw [hI]; rfl
    by_cases hItop : I = ⊤
    · have hgx : kint q u x = ⊥ := by rw [hk, hItop]; simp
      have hall : Prod.mk x ⁻¹' B = univ := by
        ext y
        simp [hBdef, hgx]
      rw [hall, measure_univ] at h0
      exact one_ne_zero h0
    · have hae : ∀ᵐ y ∂q x, u (x, y) < kint q u x := by
        rw [ae_iff]
        convert h0 using 2
        ext y
        simp [hBdef, not_lt]
      have hlt : ∀ᵐ y ∂q x, I < (-(u (x, y))).toENNReal := by
        filter_upwards [hae] with y hy
        rw [hk] at hy
        have h2 : ((I : ℝ≥0∞) : EReal) < -(u (x, y)) := EReal.lt_neg_comm.mp hy
        have h3 : (0 : EReal) ≤ -(u (x, y)) := by
          have := hu.2 (x, y)
          rw [EReal.neg_nonneg]
          exact this
        rw [← EReal.coe_toENNReal h3] at h2
        exact EReal.coe_ennreal_lt_coe_ennreal_iff.mp h2
      have hstrict := lintegral_strict_mono (μ := q x) (f := fun _ => I)
        (g := fun y => (-(u (x, y))).toENNReal)
        (IsProbabilityMeasure.ne_zero _) (hum.comp measurable_prodMk_left).aemeasurable
        (by rw [lintegral_const, measure_univ, mul_one]; exact hItop) hlt
      rw [lintegral_const, measure_univ, mul_one, ← hI] at hstrict
      exact lt_irrefl _ hstrict
  let _ := upgradeStandardBorel X
  let _ := upgradeStandardBorel Y
  have hPprod : PolishSpace (X × Y) := inferInstance
  have hBorprod : BorelSpace (X × Y) := inferInstance
  have hfib0 : ∀ x : X, IsClosed {p : X × Y | p.1 = x} := fun x =>
    isClosed_eq continuous_fst continuous_const
  obtain ⟨t', ht'le, ht'P, hBc', -⟩ := hBm.isClopenable
  have hbor : @BorelSpace (X × Y) t' _ := by
    refine ⟨?_⟩
    rw [borel_eq_borel_of_le (t := t') (t' := instTopologicalSpaceProd) ht'P hPprod ht'le]
    exact hBorprod.measurable_eq
  have hfib : ∀ x : X, IsClosed[t'] {p : X × Y | p.1 = x} := fun x => (hfib0 x).mono ht'le
  obtain ⟨f, hf, hfB⟩ :=
    L21Sel.core_polish (tZ := t') (hP := ht'P) (hBor := hbor) B hBc' hfib q hpos
  refine ⟨f, hf, fun x => ?_⟩
  have := hfB x
  rw [hBdef] at this
  exact this
