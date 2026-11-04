-- Prove2me | solution 1 for NegativeDP.Stationary.theorem83
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T00:03:24.091034+00:00
-- url     : https://prove2.me/submissions/890227e7-2661-4f16-b76c-b8427351629e

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model

set_option autoImplicit false
set_option linter.unusedSectionVars false

section L21

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
theorem NegativeDP.Stationary.L21Sel.lemma21_sel {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
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

end L21

section T83

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary.Red6dde

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Append `(a, t)` to a history (the map used in `historyLaw`). -/
def snoc {n : ℕ} (h : Hist S A n) (a : A) (t : S) : Hist S A (n + 1) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S × A) (Fin.last n)).symm
    ((h.2, a), h.1), t)

/-- Prepend the pair `(s, a)` to a history. -/
def consH (s : S) (a : A) {k : ℕ} (h : Hist S A k) : Hist S A (k + 1) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => S × A) 0).symm
    ((s, a), h.1), h.2)

/-- The empty history at state `s`. -/
def start (s : S) : Hist S A 0 := ((fun i : Fin 0 => Fin.elim0 i), s)

lemma measurable_snoc (n : ℕ) :
    Measurable (fun x : (Hist S A n × A) × S => snoc x.1.1 x.1.2 x.2) := by
  unfold snoc; fun_prop

lemma measurable_consH (s : S) (a : A) (k : ℕ) :
    Measurable (fun h : Hist S A k => consH s a h) := by
  unfold consH; fun_prop

lemma measurable_start : Measurable (fun s : S => (start s : Hist S A 0)) := by
  unfold start; fun_prop

lemma snoc_eq {n : ℕ} (h : Hist S A n) (a : A) (t : S) :
    snoc h a t = (Fin.snoc (α := fun _ => S × A) h.1 (h.2, a), t) := by
  show (Fin.insertNth (α := fun _ => S × A) (Fin.last n) (h.2, a) h.1, t) = _
  rw [Fin.insertNth_last']

lemma consH_eq (s : S) (a : A) {k : ℕ} (h : Hist S A k) :
    consH s a h = (Fin.cons (α := fun _ => S × A) (s, a) h.1, h.2) := by
  show (Fin.insertNth (α := fun _ => S × A) 0 (s, a) h.1, h.2) = _
  rw [Fin.insertNth_zero']

lemma snoc_consH (s : S) (a : A) {k : ℕ} (h : Hist S A k) (b : A) (t : S) :
    snoc (consH s a h) b t = consH s a (snoc h b t) := by
  rw [snoc_eq, consH_eq, consH_eq, snoc_eq]
  simp only [Fin.cons_snoc_eq_snoc_cons]
  rfl

lemma consH_start (s : S) (a : A) (t : S) :
    consH s a (start t : Hist S A 0) = snoc (start s) a t := by
  rw [snoc_eq, consH_eq]
  refine Prod.ext ?_ rfl
  funext i
  fin_cases i
  rfl

lemma historyLaw_succ (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    historyLaw P π s (n + 1) = (stageLaw P π s n).map (fun x => snoc x.1.1 x.1.2 x.2) := rfl

lemma historyLaw_zero (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    historyLaw P π s 0 = Measure.dirac (start s) := rfl

lemma isProb_historyLaw (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    ∀ n, IsProbabilityMeasure (historyLaw P π s n)
  | 0 => by rw [historyLaw_zero]; infer_instance
  | n + 1 => by
    haveI := isProb_historyLaw P π s n
    haveI := π.κ_markov n
    haveI := P.q_markov
    haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
    haveI : IsProbabilityMeasure (stageLaw P π s n) := by
      show IsProbabilityMeasure ((historyLaw P π s n ⊗ₘ π.κ n) ⊗ₘ nextKernel P n)
      infer_instance
    rw [historyLaw_succ]
    exact Measure.isProbabilityMeasure_map (measurable_snoc n).aemeasurable

lemma lintegral_stageLaw (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ)
    (G : (Hist S A n × A) × S → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂stageLaw P π s n =
      ∫⁻ h, ∫⁻ a, ∫⁻ t, G ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h ∂historyLaw P π s n := by
  haveI := π.κ_markov n
  haveI := P.q_markov
  haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
  haveI := isProb_historyLaw P π s n
  have hnk : ∀ ha : Hist S A n × A, nextKernel P n ha = P.q (ha.1.2, ha.2) := fun ha => by
    simp [nextKernel, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  show ∫⁻ x, G x ∂((historyLaw P π s n ⊗ₘ π.κ n) ⊗ₘ nextKernel P n) = _
  rw [Measure.lintegral_compProd hG,
    Measure.lintegral_compProd (f := fun ha => ∫⁻ t, G (ha, t) ∂nextKernel P n ha)
      hG.lintegral_kernel_prod_right']
  simp only [hnk]

lemma lintegral_historyLaw_succ (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S)
    (n : ℕ) (g : Hist S A (n + 1) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ h', g h' ∂historyLaw P π s (n + 1) =
      ∫⁻ h, ∫⁻ a, ∫⁻ t, g (snoc h a t) ∂P.q (h.2, a) ∂π.κ n h ∂historyLaw P π s n := by
  rw [historyLaw_succ, lintegral_map hg (measurable_snoc n)]
  exact lintegral_stageLaw P π s n _ (hg.comp (measurable_snoc n))

lemma measurable_loss (P : Problem S A) :
    Measurable (fun x : S × A × S => ENNReal.ofReal (-P.r x)) :=
  ENNReal.measurable_ofReal.comp P.r_measurable.neg

lemma stageLoss_eq (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    stageLoss P π s n = ∫⁻ h, ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t))
      ∂P.q (h.2, a) ∂π.κ n h ∂historyLaw P π s n :=
  lintegral_stageLaw P π s n (fun x => ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)))
    ((measurable_loss P).comp (by fun_prop))

lemma meas_inner (P : Problem S A) {n : ℕ} (X : (Hist S A n × A) × S → ℝ≥0∞)
    (hX : Measurable X) :
    Measurable (fun ha : Hist S A n × A => ∫⁻ t, X (ha, t) ∂P.q (ha.1.2, ha.2)) := by
  haveI := P.q_markov
  have hm : Measurable (fun ha : Hist S A n × A => (ha.1.2, ha.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  haveI : IsMarkovKernel (P.q.comap _ hm) := Kernel.IsMarkovKernel.comap _ hm
  exact hX.lintegral_kernel_prod_right' (κ := P.q.comap _ hm)

lemma triple_add (P : Problem S A) (π : Plan (S := S) (A := A)) {n : ℕ}
    (μ : Measure (Hist S A n)) (X Y : (Hist S A n × A) × S → ℝ≥0∞) (hX : Measurable X) :
    ∫⁻ h, ∫⁻ a, ∫⁻ t, X ((h, a), t) + Y ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h ∂μ =
      (∫⁻ h, ∫⁻ a, ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h ∂μ) +
      ∫⁻ h, ∫⁻ a, ∫⁻ t, Y ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h ∂μ := by
  haveI := P.q_markov
  haveI := π.κ_markov n
  have h1 := meas_inner P X hX
  have h2 : Measurable (fun h => ∫⁻ a, ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h) :=
    h1.lintegral_kernel_prod_right'
  have e3 : ∀ h a, ∫⁻ t, X ((h, a), t) + Y ((h, a), t) ∂P.q (h.2, a) =
      ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) + ∫⁻ t, Y ((h, a), t) ∂P.q (h.2, a) := fun h a =>
    lintegral_add_left (f := fun t => X ((h, a), t)) (hX.comp (by fun_prop)) _
  have e2 : ∀ h, ∫⁻ a, (∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) + ∫⁻ t, Y ((h, a), t) ∂P.q (h.2, a))
      ∂π.κ n h = ∫⁻ a, ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h +
        ∫⁻ a, ∫⁻ t, Y ((h, a), t) ∂P.q (h.2, a) ∂π.κ n h := fun h =>
    lintegral_add_left (f := fun a => ∫⁻ t, X ((h, a), t) ∂P.q (h.2, a))
      (h1.comp (measurable_const.prodMk measurable_id)) _
  simp_rw [e3, e2]
  exact lintegral_add_left h2 _

/-- Finite-horizon continuation loss: `N` more stages from a history at Lean stage `n`. -/
noncomputable def V (P : Problem S A) (π : Plan (S := S) (A := A)) :
    (N : ℕ) → (n : ℕ) → Hist S A n → ℝ≥0∞
  | 0, _, _ => 0
  | N + 1, n, h => ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) + V P π N (n + 1) (snoc h a t)
      ∂P.q (h.2, a) ∂π.κ n h

lemma measurable_V (P : Problem S A) (π : Plan (S := S) (A := A)) :
    ∀ N n, Measurable (V P π N n)
  | 0, n => measurable_const
  | N + 1, n => by
    haveI := π.κ_markov n
    have hX : Measurable (fun x : (Hist S A n × A) × S =>
        ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)) + V P π N (n + 1) (snoc x.1.1 x.1.2 x.2)) :=
      ((measurable_loss P).comp (by fun_prop)).add
        ((measurable_V P π N (n + 1)).comp (measurable_snoc n))
    exact (meas_inner P _ hX).lintegral_kernel_prod_right'

lemma V_le_succ (P : Problem S A) (π : Plan (S := S) (A := A)) :
    ∀ N n h, V P π N n h ≤ V P π (N + 1) n h
  | 0, n, h => by simp only [V]; exact bot_le
  | N + 1, n, h => by
    show ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) + V P π N (n + 1) (snoc h a t)
      ∂P.q (h.2, a) ∂π.κ n h ≤ ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) +
        V P π (N + 1) (n + 1) (snoc h a t) ∂P.q (h.2, a) ∂π.κ n h
    exact lintegral_mono fun a => lintegral_mono fun t =>
      add_le_add le_rfl (V_le_succ P π N (n + 1) (snoc h a t))

lemma V_mono (P : Problem S A) (π : Plan (S := S) (A := A)) (n : ℕ) (h : Hist S A n) :
    Monotone (fun N => V P π N n h) :=
  monotone_nat_of_le_succ fun N => V_le_succ P π N n h

lemma V_sum (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    ∀ N n, ∫⁻ h, V P π N n h ∂historyLaw P π s n =
      ∑ j ∈ Finset.range N, stageLoss P π s (n + j)
  | 0, n => by simp [V]
  | N + 1, n => by
    have hX : Measurable (fun x : (Hist S A n × A) × S =>
        ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2))) := (measurable_loss P).comp (by fun_prop)
    simp only [V]
    rw [triple_add P π _ (fun x => ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)))
      (fun x => V P π N (n + 1) (snoc x.1.1 x.1.2 x.2)) hX,
      ← stageLoss_eq, ← lintegral_historyLaw_succ P π s n _ (measurable_V P π N (n + 1)),
      V_sum P π s N (n + 1), Finset.sum_range_succ', add_comm]
    simp only [add_zero]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show n + 1 + j = n + (j + 1) by omega]

/-- The total expected loss of a plan, so that `I P π s = -(L P π s)`. -/
noncomputable def L (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) : ℝ≥0∞ :=
  ∑' n, stageLoss P π s n

lemma I_eq (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    I P π s = -((L P π s : ℝ≥0∞) : EReal) := rfl

lemma L_eq_iSup (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    L P π s = ⨆ N, V P π N 0 (start s) := by
  rw [L, ENNReal.tsum_eq_iSup_nat]
  refine iSup_congr fun N => ?_
  have := V_sum P π s N 0
  rw [historyLaw_zero, lintegral_dirac' _ (measurable_V P π N 0)] at this
  rw [this]
  simp

lemma measurable_L (P : Problem S A) (π : Plan (S := S) (A := A)) : Measurable (L P π) := by
  have : L P π = fun s => ⨆ N, V P π N 0 (start s) := funext (L_eq_iSup P π)
  rw [this]
  exact Measurable.iSup fun N => (measurable_V P π N 0).comp measurable_start

/-- The plan `π` seen after the first pair `(s, a)`. -/
noncomputable def shiftPlan (π : Plan (S := S) (A := A)) (s : S) (a : A) :
    Plan (S := S) (A := A) where
  κ k := (π.κ (k + 1)).comap (fun h => consH s a h) (measurable_consH s a k)
  κ_markov k := by
    haveI := π.κ_markov (k + 1)
    exact Kernel.IsMarkovKernel.comap _ _

lemma V_shift (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (a : A) :
    ∀ N k (h : Hist S A k), V P π N (k + 1) (consH s a h) = V P (shiftPlan π s a) N k h
  | 0, k, h => rfl
  | N + 1, k, h => by
    simp only [V, snoc_consH, V_shift P π s a N (k + 1)]
    rfl

lemma L_shift (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (a : A) (t : S) :
    L P (shiftPlan π s a) t = ⨆ N, V P π N 1 (snoc (start s) a t) := by
  rw [L_eq_iSup]
  refine iSup_congr fun N => ?_
  rw [← V_shift P π s a N 0, consH_start]

lemma V_succ (P : Problem S A) (π : Plan (S := S) (A := A)) (N n : ℕ) (h : Hist S A n) :
    V P π (N + 1) n h = ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (h.2, a, t)) +
      V P π N (n + 1) (snoc h a t) ∂P.q (h.2, a) ∂π.κ n h := rfl

/-- Step B: the first-stage decomposition inequality for an optimal plan. -/
lemma stepB (P : Problem S A) (π : Plan (S := S) (A := A)) (hπ : IsOptimal P π) (s : S) :
    ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (s, a, t)) + L P π t ∂P.q (s, a) ∂π.κ 0 (start s)
      ≤ L P π s := by
  haveI := P.q_markov
  haveI := π.κ_markov 0
  have hle : ∀ a t, L P π t ≤ ⨆ N, V P π N 1 (snoc (start s) a t) := by
    intro a t
    rw [← L_shift P π s a t]
    have h1 : I P (shiftPlan π s a) t ≤ I P π t :=
      (le_iSup (fun σ => I P σ t) (shiftPlan π s a)).trans (hπ t)
    rw [I_eq, I_eq, EReal.neg_le_neg_iff] at h1
    exact_mod_cast h1
  have hgm : ∀ N, Measurable (fun p : A × S => V P π N 1 (snoc (start s) p.1 p.2)) := fun N =>
    (measurable_V P π N 1).comp ((measurable_snoc 0).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
  have hXm : Measurable (fun p : A × S => ENNReal.ofReal (-P.r (s, p.1, p.2))) :=
    (measurable_loss P).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  have hsm : Measurable (fun a : A => (s, a)) := measurable_const.prodMk measurable_id
  haveI : IsMarkovKernel (P.q.comap _ hsm) := Kernel.IsMarkovKernel.comap _ hsm
  have hin : ∀ N, Measurable (fun a => ∫⁻ t, ENNReal.ofReal (-P.r (s, a, t)) +
      V P π N 1 (snoc (start s) a t) ∂P.q (s, a)) := fun N =>
    (hXm.add (hgm N)).lintegral_kernel_prod_right' (κ := P.q.comap _ hsm)
  have e1 : ∀ a, ∫⁻ t, ⨆ N, (ENNReal.ofReal (-P.r (s, a, t)) + V P π N 1 (snoc (start s) a t))
      ∂P.q (s, a) = ⨆ N, ∫⁻ t, ENNReal.ofReal (-P.r (s, a, t)) +
        V P π N 1 (snoc (start s) a t) ∂P.q (s, a) := fun a =>
    lintegral_iSup
      (f := fun N t => ENNReal.ofReal (-P.r (s, a, t)) + V P π N 1 (snoc (start s) a t))
      (fun N => (hXm.add (hgm N)).comp (measurable_const.prodMk measurable_id))
      (fun N M hNM t => add_le_add le_rfl (V_mono P π 1 _ hNM))
  have e2 : ∫⁻ a, ⨆ N, ∫⁻ t, ENNReal.ofReal (-P.r (s, a, t)) +
        V P π N 1 (snoc (start s) a t) ∂P.q (s, a) ∂π.κ 0 (start s) =
      ⨆ N, ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (s, a, t)) +
        V P π N 1 (snoc (start s) a t) ∂P.q (s, a) ∂π.κ 0 (start s) :=
    lintegral_iSup hin (fun N M hNM a =>
      lintegral_mono fun t => add_le_add le_rfl (V_mono P π 1 _ hNM))
  have e3 : (⨆ N, ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (s, a, t)) +
        V P π N 1 (snoc (start s) a t) ∂P.q (s, a) ∂π.κ 0 (start s)) =
      ⨆ N, V P π (N + 1) 0 (start s) :=
    iSup_congr fun N => (V_succ P π N 0 (start s)).symm
  calc ∫⁻ a, ∫⁻ t, ENNReal.ofReal (-P.r (s, a, t)) + L P π t ∂P.q (s, a) ∂π.κ 0 (start s)
      ≤ ∫⁻ a, ∫⁻ t, ⨆ N, (ENNReal.ofReal (-P.r (s, a, t)) + V P π N 1 (snoc (start s) a t))
          ∂P.q (s, a) ∂π.κ 0 (start s) := by
        refine lintegral_mono fun a => lintegral_mono fun t => ?_
        rw [← ENNReal.add_iSup]
        exact add_le_add le_rfl (hle a t)
    _ = ⨆ N, V P π (N + 1) 0 (start s) := by
        simp_rw [e1]
        rw [e2, e3]
    _ ≤ L P π s := by
        rw [L_eq_iSup]
        exact iSup_le fun N => le_iSup (fun N => V P π N 0 (start s)) (N + 1)

/-- Step C: a rule that does not increase `W = L π` makes `f^∞` at least as good. -/
lemma stepC (P : Problem S A) (W : S → ℝ≥0∞) (hW : Measurable W)
    (f : {g : S → A // Measurable g})
    (hf : ∀ s, ∫⁻ t, ENNReal.ofReal (-P.r (s, f.1 s, t)) + W t ∂P.q (s, f.1 s) ≤ W s)
    (s : S) : L P (MarkovPlan.toPlan (stationary f)) s ≤ W s := by
  set σ := MarkovPlan.toPlan (stationary f) with hσ
  have hκ : ∀ N (h : Hist S A N), σ.κ N h = Measure.dirac (f.1 h.2) := fun N h => by
    simp [hσ, MarkovPlan.toPlan, stationary, Kernel.deterministic_apply]
  have key : ∀ N, ∑ j ∈ Finset.range N, stageLoss P σ s j +
      ∫⁻ h, W h.2 ∂historyLaw P σ s N ≤ W s := by
    intro N
    induction N with
    | zero =>
      rw [historyLaw_zero, lintegral_dirac' _
        (show Measurable (fun h : Hist S A 0 => W h.2) from hW.comp measurable_snd)]
      simp [start]
    | succ N ih =>
      have hX : Measurable (fun x : (Hist S A N × A) × S =>
          ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2))) := (measurable_loss P).comp (by fun_prop)
      rw [Finset.sum_range_succ, add_assoc, stageLoss_eq,
        lintegral_historyLaw_succ P σ s N (fun h => W h.2) (hW.comp measurable_snd)]
      rw [← triple_add P σ _ (fun x => ENNReal.ofReal (-P.r (x.1.1.2, x.1.2, x.2)))
        (fun x => W (snoc x.1.1 x.1.2 x.2).2) hX]
      refine le_trans (add_le_add le_rfl ?_) ih
      refine lintegral_mono fun h => ?_
      rw [hκ, lintegral_dirac]
      exact hf h.2
  rw [L]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  exact le_trans le_self_add (key N)

/-- Theorem 8.3 (N), assuming Strauch's Lemma 2.1 (measurable selection) on `S × A`. -/
theorem main (P : Problem S A)
    (hsel : ∀ (q : Kernel S A) [IsMarkovKernel q] (u : S × A → EReal), IsNegM u →
      ∃ f : S → A, Measurable f ∧ ∀ x, kint q u x ≤ u (x, f x))
    (h : ∃ π : Plan (S := S) (A := A), IsOptimal P π) :
    ∃ f : {g : S → A // Measurable g}, IsOptimal P (MarkovPlan.toPlan (stationary f)) := by
  obtain ⟨π, hπ⟩ := h
  haveI := P.q_markov
  haveI := π.κ_markov 0
  set W : S → ℝ≥0∞ := L P π with hWdef
  have hWm : Measurable W := measurable_L P π
  set Wa : S × A → ℝ≥0∞ := fun p => ∫⁻ t, ENNReal.ofReal (-P.r (p.1, p.2, t)) + W t ∂P.q p
    with hWa
  have hWam : Measurable Wa :=
    Measurable.lintegral_kernel_prod_right' (κ := P.q)
      (f := fun x : (S × A) × S => ENNReal.ofReal (-P.r (x.1.1, x.1.2, x.2)) + W x.2)
      (((measurable_loss P).comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).add
        (hWm.comp measurable_snd))
  set κ0 : Kernel S A := (π.κ 0).comap (fun s => start s) measurable_start with hκ0
  haveI : IsMarkovKernel κ0 := Kernel.IsMarkovKernel.comap _ _
  set u : S × A → EReal := fun p => -((Wa p : ℝ≥0∞) : EReal) with hu
  have hun : IsNegM u := by
    refine ⟨(measurable_coe_ennreal_ereal.comp hWam).neg, fun p => ?_⟩
    simp only [hu]
    exact EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _)
  obtain ⟨f, hfm, hfsel⟩ := hsel κ0 u hun
  have hfle : ∀ s, Wa (s, f s) ≤ W s := by
    intro s
    have h1 := hfsel s
    simp only [kint, hu, neg_neg, EReal.toENNReal_coe, EReal.neg_le_neg_iff] at h1
    have h2 : Wa (s, f s) ≤ ∫⁻ a, Wa (s, a) ∂κ0 s := by exact_mod_cast h1
    exact h2.trans (stepB P π hπ s)
  refine ⟨⟨f, hfm⟩, fun s => ?_⟩
  have hC := stepC P W hWm ⟨f, hfm⟩ hfle s
  calc vstar P s ≤ I P π s := hπ s
    _ = -((W s : ℝ≥0∞) : EReal) := I_eq P π s
    _ ≤ -((L P (MarkovPlan.toPlan (stationary ⟨f, hfm⟩)) s : ℝ≥0∞) : EReal) := by
        rw [EReal.neg_le_neg_iff]; exact_mod_cast hC
    _ = I P (MarkovPlan.toPlan (stationary ⟨f, hfm⟩)) s := (I_eq P _ s).symm

end NegativeDP.Stationary.Red6dde

end T83

open NegativeDP.Stationary in open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary) in
theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (h : ∃ π : Plan (S := S) (A := A), IsOptimal P π) :
    ∃ f : {g : S → A // Measurable g}, IsOptimal P (MarkovPlan.toPlan (stationary f)) := by
  exact NegativeDP.Stationary.Red6dde.main P (fun q _ u hu => NegativeDP.Stationary.L21Sel.lemma21_sel q u hu) h
