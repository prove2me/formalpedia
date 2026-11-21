-- Prove2me | solution 1 for GreedyReusableNet.eq_12_part_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:32:46.566995+00:00
-- url     : https://prove2.me/submissions/36a5b808-85fc-4b63-93ed-acc5aab109c9

import Mathlib
import Definitions.Def_GreedyReusableNet_IndepSystemAssumption
import Definitions.Def_GreedyReusableNet_ActivatesWithinAction
import Definitions.Def_GreedyReusableNet_NonOverlappingActivation
import Definitions.Def_GreedyReusableNet_DecayingAvailability
import Definitions.Def_GreedyReusableNet_IsAdmissible
import Definitions.Def_GreedyReusableNet_Rew
import Definitions.Def_GreedyReusableNet_GRD
import Definitions.Def_GreedyReusableNet_coupledRun
import Definitions.Def_GreedyReusableNet_goodSet

open MeasureTheory

namespace Aux_GRN

open GreedyReusableNet

/-! ### Discrete measurability: measurable preimages of singletons -/

def DM {X Y : Type*} [MeasurableSpace X] (f : X → Y) : Prop := ∀ y, MeasurableSet (f ⁻¹' {y})

section DMlemmas

variable {X Y Z : Type*} [MeasurableSpace X]

lemma DM.preimage [Countable Y] {f : X → Y} (hf : DM f) (S : Set Y) :
    MeasurableSet (f ⁻¹' S) := by
  rw [← Set.biUnion_preimage_singleton]
  exact MeasurableSet.biUnion (Set.to_countable _) (fun y _ => hf y)

lemma DM.comp_fun [Countable Y] {f : X → Y} (hf : DM f) (G : Y → Z) :
    DM (fun x => G (f x)) := by
  intro z
  exact hf.preimage (G ⁻¹' {z})

lemma DM.measurable [Countable Y] {f : X → Y} (hf : DM f) {W : Type*} [MeasurableSpace W]
    (φ : Y → W) : Measurable (fun x => φ (f x)) := by
  intro S _
  exact hf.preimage (φ ⁻¹' S)

lemma DM.of_factor [Countable Z] {g : X → Z} (hg : DM g) {f : X → Y}
    (hfac : ∀ x x', g x = g x' → f x = f x') : DM f := by
  intro y
  have : f ⁻¹' {y} = g ⁻¹' (g '' (f ⁻¹' {y})) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', he⟩
      rw [hfac x x' he.symm]
      exact hx'
  rw [this]
  exact hg.preimage _

lemma DM.pair {f : X → Y} {g : X → Z} (hf : DM f) (hg : DM g) :
    DM (fun x => (f x, g x)) := by
  rintro ⟨a, b⟩
  have : (fun x => (f x, g x)) ⁻¹' {(a, b)} = f ⁻¹' {a} ∩ g ⁻¹' {b} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Prod.mk.injEq]
  rw [this]
  exact (hf a).inter (hg b)

lemma DM.const (c : Y) : DM (fun _ : X => c) := fun y => MeasurableSet.const _

lemma DM.comp_meas {W : Type*} [MeasurableSpace W] {f : W → Y} (hf : DM f) {k : X → W}
    (hk : Measurable k) : DM (fun x => f (k x)) := fun y => (hf y).preimage hk

lemma DM.bind [Countable Z] {D : X → Z} (hD : DM D) {F : Z → X → Y} (hF : ∀ z, DM (F z)) :
    DM (fun x => F (D x) x) := by
  intro y
  have : (fun x => F (D x) x) ⁻¹' {y} = ⋃ z, (D ⁻¹' {z} ∩ (F z) ⁻¹' {y}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨D x, rfl, h⟩
    · rintro ⟨z, rfl, h⟩
      exact h
  rw [this]
  exact MeasurableSet.iUnion fun z => (hD z).inter (hF z y)

lemma DM.of_pattern [Countable Z] {D : X → Z} (hD : DM D) {f : X → Y} (F : Z → X → Y)
    (hF : ∀ z, DM (F z)) (hfF : ∀ x, f x = F (D x) x) : DM f := by
  have : f = fun x => F (D x) x := funext hfF
  rw [this]
  exact DM.bind hD hF

lemma DM.pi {ι : Type*} [Countable ι] {f : ι → X → Y} (hf : ∀ i, DM (f i)) :
    DM (fun x i => f i x) := by
  intro v
  have : (fun x i => f i x) ⁻¹' {v} = ⋂ i, (f i) ⁻¹' {v i} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
    exact ⟨fun h i => congrFun h i, fun h => funext h⟩
  rw [this]
  exact MeasurableSet.iInter fun i => hf i (v i)

lemma DM.ofDecide {P : X → Prop} {_ : DecidablePred P} (hP : MeasurableSet {x | P x}) :
    DM (fun x => decide (P x)) := by
  intro b
  cases b with
  | false =>
    have : (fun x => decide (P x)) ⁻¹' {false} = {x | P x}ᶜ := by
      ext x
      simp
    rw [this]
    exact hP.compl
  | true =>
    have : (fun x => decide (P x)) ⁻¹' {true} = {x | P x} := by
      ext x
      simp
    rw [this]
    exact hP

end DMlemmas

/-! ### The primitive samplers -/

lemma sampleFin_congr {α : Type*} [Fintype α] (p : PMF α) (u v : ℝ)
    (h : ∀ k : Fin (Fintype.card α),
      (u < ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card α) => j ≤ k),
        (p ((Fintype.equivFin α).symm j)).toReal) ↔
      (v < ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card α) => j ≤ k),
        (p ((Fintype.equivFin α).symm j)).toReal)) :
    sampleFin p u = sampleFin p v := by
  classical
  unfold sampleFin
  try dsimp only
  have hs : (Finset.univ.filter fun k : Fin (Fintype.card α) =>
      p ((Fintype.equivFin α).symm k) ≠ 0 ∧
        u < ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card α) => j ≤ k),
          (p ((Fintype.equivFin α).symm j)).toReal) =
      (Finset.univ.filter fun k : Fin (Fintype.card α) =>
      p ((Fintype.equivFin α).symm k) ≠ 0 ∧
        v < ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card α) => j ≤ k),
          (p ((Fintype.equivFin α).symm j)).toReal) :=
    Finset.filter_congr (fun k _ => and_congr_right' (h k))
  first
    | rw [hs]
    | simp only [hs]

lemma sampleFin_DM {α : Type*} [Fintype α] (p : PMF α) : DM (sampleFin p) := by
  have hg : DM (fun u : ℝ => fun k : Fin (Fintype.card α) =>
      decide (u < ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card α) => j ≤ k),
        (p ((Fintype.equivFin α).symm j)).toReal)) :=
    DM.pi (fun k => DM.ofDecide measurableSet_Iio)
  refine DM.of_factor hg ?_
  intro u v huv
  apply sampleFin_congr
  intro k
  exact decide_eq_decide.mp (congrFun huv k)

noncomputable def cF (F : PMF ℕ) (x : ℕ) : ℝ := (F.toOuterMeasure (Set.Iic x)).toReal

lemma Finv_eq (F : PMF ℕ) (u : ℝ) : Finv F u = sInf {x : ℕ | u ≤ cF F x} := rfl

lemma Finv_DM (F : PMF ℕ) : DM (Finv F) := by
  intro m
  have key : Finv F ⁻¹' {m} =
      ((⋂ x : ℕ, {u : ℝ | cF F x < u}) ∩ {_u : ℝ | m = 0}) ∪
        ({u : ℝ | u ≤ cF F m} ∩ ⋂ x ∈ ({x : ℕ | x < m} : Set ℕ), {u : ℝ | cF F x < u}) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_iInter]
    rw [Finv_eq]
    constructor
    · intro h
      by_cases hS : ({x : ℕ | u ≤ cF F x}).Nonempty
      · right
        have hm := Nat.sInf_mem hS
        rw [h] at hm
        refine ⟨hm, fun x hx => ?_⟩
        have hx' : x < sInf {x : ℕ | u ≤ cF F x} := by rw [h]; exact hx
        have := Nat.notMem_of_lt_sInf hx'
        simp only [Set.mem_setOf_eq, not_le] at this
        exact this
      · left
        rw [Set.not_nonempty_iff_eq_empty] at hS
        refine ⟨fun x => ?_, ?_⟩
        · by_contra hx
          push_neg at hx
          have hmem : x ∈ ({x : ℕ | u ≤ cF F x}) := hx
          rw [hS] at hmem
          exact hmem
        · rw [← h, hS, Nat.sInf_empty]
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have hS : {x : ℕ | u ≤ cF F x} = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
          exact h1 x
        rw [hS, Nat.sInf_empty, h2]
      · apply le_antisymm (Nat.sInf_le (s := {x : ℕ | u ≤ cF F x}) h1)
        by_contra hlt
        push_neg at hlt
        have hmem := Nat.sInf_mem (s := {x : ℕ | u ≤ cF F x}) ⟨m, h1⟩
        have h3 := h2 _ hlt
        simp only [Set.mem_setOf_eq] at hmem
        linarith
  rw [key]
  refine ((MeasurableSet.iInter fun x => ?_).inter (MeasurableSet.const _)).union
    (MeasurableSet.inter ?_ (MeasurableSet.biInter (Set.to_countable _) fun x _ => ?_))
  · exact measurableSet_Ioi
  · exact measurableSet_Iic
  · exact measurableSet_Ioi

/-! ### One step of the history recursion -/

variable {N : ℕ}

lemma stepOf_eq (I : ProblemInstance N) (t : ℕ) (h : History N) (A : Finset (Finset (Fin N)))
    (uAct : ℝ) (U : Fin N → ℝ) :
    stepOf I t h A uAct U =
      (takenAction (I.period t) (freeArms h t) A,
        sampleFin ((I.period t).act (takenAction (I.period t) (freeArms h t) A) (counts h)) uAct,
        fun i => if i ∈ activatedArms (sampleFin ((I.period t).act
            (takenAction (I.period t) (freeArms h t) A) (counts h)) uAct)
          then Finv (I.block i (counts h i)) (U i) else 0) := rfl

lemma step_DM0 (I : ProblemInstance N) (t : ℕ) (h0 : History N) (A0 : Finset (Finset (Fin N)))
    {X : Type*} [MeasurableSpace X] (u : X → ℝ) (hu : Measurable u) (U : X → Fin N → ℝ)
    (hU : Measurable U) : DM (fun x => stepOf I t h0 A0 (u x) (U x)) := by
  have e : (fun x => stepOf I t h0 A0 (u x) (U x)) = fun x =>
      (takenAction (I.period t) (freeArms h0 t) A0,
        sampleFin ((I.period t).act (takenAction (I.period t) (freeArms h0 t) A0) (counts h0)) (u x),
        fun i => if i ∈ activatedArms (sampleFin ((I.period t).act
            (takenAction (I.period t) (freeArms h0 t) A0) (counts h0)) (u x))
          then Finv (I.block i (counts h0 i)) (U x i) else 0) :=
    funext fun x => stepOf_eq I t h0 A0 (u x) (U x)
  rw [e]
  refine DM.pair (DM.const _) (DM.pair ((sampleFin_DM _).comp_meas hu) ?_)
  refine DM.bind (D := fun x => sampleFin ((I.period t).act
      (takenAction (I.period t) (freeArms h0 t) A0) (counts h0)) (u x))
    ((sampleFin_DM _).comp_meas hu)
    (F := fun S x => fun i => if i ∈ activatedArms S
          then Finv (I.block i (counts h0 i)) (U x i) else 0) (fun S => ?_)
  apply DM.pi
  intro i
  by_cases hi : i ∈ activatedArms S
  · simp only [hi, ↓reduceIte]
    exact (Finv_DM _).comp_meas ((measurable_pi_apply i).comp hU)
  · simp only [hi, ↓reduceIte]
    exact DM.const _

lemma step_DM (I : ProblemInstance N) (t : ℕ) (h0 : History N)
    {X : Type*} [MeasurableSpace X] (A : X → Finset (Finset (Fin N))) (hA : DM A)
    (u : X → ℝ) (hu : Measurable u) (U : X → Fin N → ℝ)
    (hU : Measurable U) : DM (fun x => stepOf I t h0 (A x) (u x) (U x)) :=
  DM.bind (D := A) hA (F := fun A0 x => stepOf I t h0 A0 (u x) (U x))
    (fun A0 => step_DM0 I t h0 A0 u hu U hU)

lemma meas_coord {T : ℕ} (τ : Fin T) : Measurable (fun p : ℝ × Tape N T => p.2 τ) :=
  (measurable_pi_apply τ).comp measurable_snd

lemma run_DM {T : ℕ} (I : ProblemInstance N)
    (act : ℝ → ℕ → History N → ℝ → Finset (Finset (Fin N)))
    (hact : ∀ t h, DM (fun q : ℝ × ℝ => act q.1 t h q.2)) (t : ℕ) :
    DM (fun p : ℝ × Tape N T => run I (act p.1) p.2 t) := by
  induction t with
  | zero =>
    show DM (fun _ : ℝ × Tape N T => ([] : History N))
    exact DM.const _
  | succ t ih =>
    by_cases ht : t < T
    · have e : (fun p : ℝ × Tape N T => run I (act p.1) p.2 (t + 1)) = fun p =>
          run I (act p.1) p.2 t ++ [stepOf I t (run I (act p.1) p.2 t)
            (act p.1 t (run I (act p.1) p.2 t) (p.2 ⟨t, ht⟩).1) (p.2 ⟨t, ht⟩).2.1
            (p.2 ⟨t, ht⟩).2.2] := by
        funext p
        simp only [run, dif_pos ht]
      rw [e]
      refine DM.bind (D := fun p : ℝ × Tape N T => run I (act p.1) p.2 t) ih
        (F := fun h0 p => h0 ++ [stepOf I t h0 (act p.1 t h0 (p.2 ⟨t, ht⟩).1) (p.2 ⟨t, ht⟩).2.1
            (p.2 ⟨t, ht⟩).2.2]) (fun h0 => ?_)
      have hA : DM (fun p : ℝ × Tape N T => act p.1 t h0 (p.2 ⟨t, ht⟩).1) :=
        (hact t h0).comp_meas (k := fun p : ℝ × Tape N T => (p.1, (p.2 ⟨t, ht⟩).1))
          (measurable_fst.prodMk (meas_coord (N := N) ⟨t, ht⟩).fst)
      have hs := step_DM I t h0 _ hA _ (meas_coord (N := N) ⟨t, ht⟩).snd.fst _
        (meas_coord (N := N) ⟨t, ht⟩).snd.snd
      exact hs.comp_fun (fun s => h0 ++ [s])
    · have e : (fun p : ℝ × Tape N T => run I (act p.1) p.2 (t + 1)) = fun p =>
          run I (act p.1) p.2 t := by
        funext p
        simp only [run, dif_neg ht]
      rw [e]
      exact ih

lemma run_length {T : ℕ} (I : ProblemInstance N)
    (act : ℕ → History N → ℝ → Finset (Finset (Fin N))) (w : Tape N T) (t : ℕ) :
    (run I act w t).length = min t T := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
    by_cases ht : t < T
    · simp only [run, dif_pos ht, List.length_append, List.length_singleton, ih]
      rw [Nat.min_def, Nat.min_def]
      split_ifs <;> omega
    · simp only [run, dif_neg ht, ih]
      rw [Nat.min_def, Nat.min_def]
      split_ifs <;> omega

/-! ### The greedy action is discretely measurable -/

lemma sel_filter_DM (O : Oracle N) (d : PeriodData N) (f : Finset (Fin N) → ℝ) (n : Fin N → ℕ)
    (free : Finset (Fin N)) (P : Finset (Fin N) → Prop) {_ : DecidablePred P} :
    DM (fun q : ℝ × ℝ => (O.sel d f n free q.2).filter P) := by
  have h0 : DM (O.sel d f n free) := fun A => O.measurable_sel d f n free A
  exact (h0.comp_meas measurable_snd).comp_fun (fun S => S.filter P)

lemma greedy_congr (O : Oracle N) (sc : PeriodData N → Finset (Fin N) → (Fin N → ℕ) → ℝ)
    (r r' : ℝ) (d : PeriodData N) (n : Fin N → ℕ) (free : Finset (Fin N)) (u : ℝ)
    (h : ∀ B, r ≤ sc d B n ↔ r' ≤ sc d B n) :
    greedyStep O sc r d n free u = greedyStep O sc r' d n free u := by
  unfold greedyStep
  simp only [h]

noncomputable def patF (sc : PeriodData N → Finset (Fin N) → (Fin N → ℕ) → ℝ) (d : PeriodData N)
    (n : Fin N → ℕ) (r : ℝ) (B : Finset (Fin N)) : Bool := decide (r ≤ sc d B n)

noncomputable def repF (sc : PeriodData N → Finset (Fin N) → (Fin N → ℕ) → ℝ)
    (d : PeriodData N) (n : Fin N → ℕ) (z : Finset (Fin N) → Bool) : ℝ := by
  classical
  exact if h : ∃ r, patF sc d n r = z then h.choose else 0

lemma repF_spec (sc : PeriodData N → Finset (Fin N) → (Fin N → ℕ) → ℝ) (d : PeriodData N)
    (n : Fin N → ℕ) (r : ℝ) : patF sc d n (repF sc d n (patF sc d n r)) = patF sc d n r := by
  have hex : ∃ r', patF sc d n r' = patF sc d n r := ⟨r, rfl⟩
  have hrep : repF sc d n (patF sc d n r) = hex.choose := by
    unfold repF
    exact dif_pos hex
  rw [hrep]
  exact hex.choose_spec

lemma greedy_DM (O : Oracle N) (sc : PeriodData N → Finset (Fin N) → (Fin N → ℕ) → ℝ)
    (d : PeriodData N) (n : Fin N → ℕ) (free : Finset (Fin N)) :
    DM (fun q : ℝ × ℝ => greedyStep O sc q.1 d n free q.2) := by
  have hD0 : DM (fun r : ℝ => fun B : Finset (Fin N) => decide (r ≤ sc d B n)) :=
    DM.pi (fun B => DM.ofDecide measurableSet_Iic)
  have hD : DM (fun q : ℝ × ℝ => patF sc d n q.1) := hD0.comp_meas measurable_fst
  refine DM.of_pattern hD (fun z q => greedyStep O sc (repF sc d n z) d n free q.2) (fun z => ?_)
    (fun q => ?_)
  · show DM (fun q : ℝ × ℝ => greedyStep O sc (repF sc d n z) d n free q.2)
    unfold greedyStep
    exact sel_filter_DM O d _ n free _
  · show greedyStep O sc q.1 d n free q.2 =
      greedyStep O sc (repF sc d n (patF sc d n q.1)) d n free q.2
    apply greedy_congr
    intro B
    have hspec := congrFun (repF_spec sc d n q.1) B
    unfold patF at hspec
    exact (decide_eq_decide.mp hspec).symm

/-! ### Boundedness of the path sum -/

noncomputable def Mb (T : ℕ) (g : ℕ → Finset (Fin N) → (Fin N → ℕ) → ℝ) : ℝ :=
  ∑ k ∈ Finset.range T, ∑ B : Finset (Fin N),
    ∑ n ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (T + 1)), |g k B n|

lemma Mb_nonneg (T : ℕ) (g : ℕ → Finset (Fin N) → (Fin N → ℕ) → ℝ) : 0 ≤ Mb T g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    abs_nonneg _

lemma term_le (T : ℕ) (g : ℕ → Finset (Fin N) → (Fin N → ℕ) → ℝ) (k : ℕ) (hk : k < T)
    (B : Finset (Fin N)) (n : Fin N → ℕ) (hn : ∀ i, n i ≤ T) : |g k B n| ≤ Mb T g := by
  unfold Mb
  have hmem : n ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (T + 1)) :=
    Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (Nat.lt_succ_of_le (hn i))
  have h1 : |g k B n| ≤
      ∑ n' ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (T + 1)), |g k B n'| :=
    Finset.single_le_sum (f := fun n' => |g k B n'|) (fun n' _ => abs_nonneg _) hmem
  have h2 : (∑ n' ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (T + 1)), |g k B n'|) ≤
      ∑ B' : Finset (Fin N),
        ∑ n' ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (T + 1)), |g k B' n'| :=
    Finset.single_le_sum
      (f := fun B' => ∑ n' ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (T + 1)),
        |g k B' n'|)
      (fun B' _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ B)
  have h3 : (∑ B' : Finset (Fin N),
        ∑ n' ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (T + 1)), |g k B' n'|) ≤
      ∑ k' ∈ Finset.range T, ∑ B' : Finset (Fin N),
        ∑ n' ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (T + 1)), |g k' B' n'| :=
    Finset.single_le_sum
      (f := fun k' => ∑ B' : Finset (Fin N),
        ∑ n' ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (T + 1)), |g k' B' n'|)
      (fun k' _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 hk)
  exact h1.trans (h2.trans h3)

lemma pathSum_abs_le (T : ℕ) (h : History N) (g : ℕ → Finset (Fin N) → (Fin N → ℕ) → ℝ)
    (hT : h.length ≤ T) :
    |pathSum h g| ≤ T * ((Fintype.card (Finset (Fin N)) : ℝ) * Mb T g) := by
  unfold pathSum
  have hM := Mb_nonneg T g
  calc |∑ k : Fin h.length, ∑ B ∈ (h.get k).2.1, g k B (counts (h.take k))|
      ≤ ∑ k : Fin h.length, |∑ B ∈ (h.get k).2.1, g k B (counts (h.take k))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin h.length, ((Fintype.card (Finset (Fin N)) : ℝ) * Mb T g) := by
        apply Finset.sum_le_sum
        intro k _
        have hkT : (k : ℕ) < T := lt_of_lt_of_le k.isLt hT
        have hcnt : ∀ i, counts (h.take k) i ≤ T := by
          intro i
          unfold counts
          exact (List.length_filter_le _ _).trans ((List.length_take_le' _ _).trans hT)
        calc |∑ B ∈ (h.get k).2.1, g k B (counts (h.take k))|
            ≤ ∑ B ∈ (h.get k).2.1, |g k B (counts (h.take k))| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _B ∈ (h.get k).2.1, Mb T g :=
              Finset.sum_le_sum fun B _ => term_le T g k hkT B _ hcnt
          _ = ((h.get k).2.1.card : ℝ) * Mb T g := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Fintype.card (Finset (Fin N)) : ℝ) * Mb T g := by
              apply mul_le_mul_of_nonneg_right _ hM
              exact_mod_cast Finset.card_le_univ _
    _ = (h.length : ℝ) * ((Fintype.card (Finset (Fin N)) : ℝ) * Mb T g) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ T * ((Fintype.card (Finset (Fin N)) : ℝ) * Mb T g) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) hM)
        exact_mod_cast hT

/-! ### Measures -/

instance unif_prob : IsProbabilityMeasure unif :=
  ⟨by simp [unif, Real.volume_Icc]⟩

instance noise_prob : IsProbabilityMeasure (noiseLaw N) := by
  unfold noiseLaw
  infer_instance

instance tape_prob {T : ℕ} : IsProbabilityMeasure (tapeLaw N T) := by
  unfold tapeLaw
  infer_instance

/-! ### List and history lemmas -/

lemma sampleFin_mem {α : Type*} [Fintype α] (p : PMF α) (u : ℝ) : sampleFin p u ∈ p.support := by
  classical
  unfold sampleFin
  try dsimp only
  split_ifs with hg
  · have hmem := Finset.min'_mem _ hg
    rw [Finset.mem_filter] at hmem
    exact (PMF.mem_support_iff _ _).2 hmem.2.1
  · exact p.support_nonempty.choose_spec

def dur (h : History N) (k : ℕ) (i : Fin N) : ℕ := (h.getD k (∅, ∅, fun _ => 0)).2.2 i

lemma actAt_append_lt (h : History N) (s : Step N) {k : ℕ} (hk : k < h.length) :
    activatedAt (h ++ [s]) k = activatedAt h k := by
  unfold activatedAt
  rw [List.getD_append _ _ _ _ hk]

lemma actAt_append_len (h : History N) (s : Step N) :
    activatedAt (h ++ [s]) h.length = s.2.1 := by
  unfold activatedAt
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]

lemma actionAt_append_len (h : History N) (s : Step N) :
    actionAt (h ++ [s]) h.length = s.1 := by
  unfold actionAt
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]

lemma dur_append_lt (h : History N) (s : Step N) {k : ℕ} (hk : k < h.length) (i : Fin N) :
    dur (h ++ [s]) k i = dur h k i := by
  unfold dur
  rw [List.getD_append _ _ _ _ hk]

lemma dur_append_len (h : History N) (s : Step N) (i : Fin N) :
    dur (h ++ [s]) h.length i = s.2.2 i := by
  unfold dur
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]

lemma counts_append (h : History N) (s : Step N) (i : Fin N) :
    counts (h ++ [s]) i = counts h i + (if i ∈ activatedArms s.2.1 then 1 else 0) := by
  unfold counts
  rw [List.filter_append, List.length_append]
  by_cases hi : i ∈ activatedArms s.2.1 <;> simp [hi]

lemma counts_cons (s : Step N) (l : History N) (i : Fin N) :
    counts (s :: l) i = counts l i + (if i ∈ activatedArms s.2.1 then 1 else 0) := by
  unfold counts
  rw [List.filter_cons]
  by_cases hi : i ∈ activatedArms s.2.1 <;> simp [hi]

lemma counts_nil (i : Fin N) : counts ([] : History N) i = 0 := rfl

lemma take_append_le (h : History N) (s : Step N) {k : ℕ} (hk : k ≤ h.length) :
    (h ++ [s]).take k = h.take k := List.take_append_of_le_length hk

lemma counts_eq_sum (h : History N) (i : Fin N) :
    counts h i = ∑ t ∈ Finset.range h.length,
      (if i ∈ activatedArms (activatedAt h t) then 1 else 0) := by
  induction h with
  | nil => simp [counts_nil]
  | cons s l ih =>
    rw [List.length_cons, Finset.sum_range_succ', counts_cons, ih]
    have e0 : activatedAt (s :: l) 0 = s.2.1 := by
      unfold activatedAt
      rw [List.getD_cons_zero]
    have e1 : ∀ t, activatedAt (s :: l) (t + 1) = activatedAt l t := by
      intro t
      unfold activatedAt
      rw [List.getD_cons_succ]
    simp only [e0, e1]

lemma counts_take_succ (h : History N) (i : Fin N) {k : ℕ} (hk : k < h.length) :
    counts (h.take (k + 1)) i =
      counts (h.take k) i + (if i ∈ activatedArms (activatedAt h k) then 1 else 0) := by
  have e : h.take (k + 1) = h.take k ++ [h[k]] := by
    rw [List.take_succ, List.getElem?_eq_getElem hk]
    rfl
  rw [e, counts_append]
  unfold activatedAt
  rw [List.getD_eq_getElem _ _ hk]

lemma counts_take_mono (h : History N) (i : Fin N) (k m : ℕ) :
    counts (h.take k) i ≤ counts (h.take (k + m)) i := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    refine ih.trans ?_
    rcases Nat.lt_or_ge (k + m) h.length with hlt | hge
    · rw [show k + (m + 1) = (k + m) + 1 by omega, counts_take_succ h i hlt]
      omega
    · rw [List.take_of_length_le hge, List.take_of_length_le (by omega)]

lemma counts_lt_of_act (h : History N) (i : Fin N) {k k' : ℕ} (hkk : k < k') (hk : k < h.length)
    (hka : i ∈ activatedArms (activatedAt h k)) :
    counts (h.take k) i + 1 ≤ counts (h.take k') i := by
  have h1 := counts_take_succ h i hk
  rw [if_pos hka] at h1
  have h2 := counts_take_mono h i (k + 1) (k' - (k + 1))
  rw [show k + 1 + (k' - (k + 1)) = k' by omega] at h2
  omega

lemma counts_lt_of_act' (h : History N) (i : Fin N) {k : ℕ} (hk : k < h.length)
    (hka : i ∈ activatedArms (activatedAt h k)) :
    counts (h.take k) i + 1 ≤ counts h i := by
  have := counts_lt_of_act h i hk hk hka
  rwa [List.take_length] at this

lemma mem_freeArms (h : History N) (t : ℕ) (i : Fin N) :
    i ∈ freeArms h t ↔
      ∀ k < h.length, i ∈ activatedArms (activatedAt h k) → k + dur h k i < t := by
  unfold freeArms
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro H k hk
    have := H k hk
    unfold activatedAt dur
    rw [List.getD_eq_getElem _ _ hk]
    exact this
  · intro H k hk
    have := H k hk
    unfold activatedAt dur at this
    rw [List.getD_eq_getElem _ _ hk] at this
    exact this

lemma mem_goodSet (h h' : History N) (t : ℕ) (B : Finset (Fin N)) :
    B ∈ goodSet h h' t ↔ B ∈ actionAt h' t ∧
      ((∀ i ∈ B, counts (h.take t) i ≤ counts (h'.take t) i) ∧ B ⊆ freeArms (h.take t) t) := by
  unfold goodSet
  rw [Finset.mem_filter]

lemma takenAction_spec (d : PeriodData N) (free : Finset (Fin N)) (A : Finset (Finset (Fin N)))
    (h0 : ∅ ∈ d.actions) :
    takenAction d free A ∈ d.actions ∧ (∀ B ∈ takenAction d free A, B ⊆ free) ∧
      takenAction d free A ⊆ A := by
  unfold takenAction
  split_ifs with hA
  · have hA' : A ∈ d.actions ∧ ∀ B ∈ A, B ⊆ free := hA
    exact ⟨hA'.1, hA'.2, le_rfl⟩
  · exact ⟨h0, fun B hB => by simp at hB, Finset.empty_subset _⟩

lemma prefix_getD {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) {k : ℕ} (hk : k < l₁.length)
    (d : α) : l₂.getD k d = l₁.getD k d := by
  obtain ⟨l, rfl⟩ := h
  exact List.getD_append _ _ _ _ hk

lemma stepOf_dur (I : ProblemInstance N) (t : ℕ) (h : History N) (A : Finset (Finset (Fin N)))
    (u : ℝ) (U : Fin N → ℝ) (i : Fin N) (hi : i ∈ activatedArms (stepOf I t h A u U).2.1) :
    (stepOf I t h A u U).2.2 i = Finv (I.block i (counts h i)) (U i) := by
  rw [stepOf_eq] at hi ⊢
  exact if_pos hi

lemma stepOf_props {L T : ℕ} (I : ProblemInstance N) (h1 : IndepSystemAssumption I T L)
    (hact : ActivatesWithinAction I T) {t : ℕ} (ht : t < T) (h : History N)
    (A : Finset (Finset (Fin N))) (u : ℝ) (U : Fin N → ℝ) :
    (stepOf I t h A u U).2.1 ⊆ (stepOf I t h A u U).1 ∧
      (stepOf I t h A u U).1 ∈ (I.period t).actions ∧
      (∀ B ∈ (stepOf I t h A u U).1, B ⊆ freeArms h t) ∧ (stepOf I t h A u U).1 ⊆ A ∧
      (∀ B₁ ∈ (stepOf I t h A u U).2.1, ∀ B₂ ∈ (stepOf I t h A u U).2.1, B₁ ≠ B₂ →
        NonOverlappingActivation I T → Disjoint B₁ B₂) ∧
      (∀ B ∈ (stepOf I t h A u U).1, B.card ≤ L) := by
  rw [stepOf_eq]
  have hI := (h1 t ht).1
  unfold SubsamplingSM.Offline.IsIndepSystem at hI
  have h0 : ∅ ∈ (I.period t).actions := hI.1
  obtain ⟨hA1, hA2, hA3⟩ := takenAction_spec (I.period t) (freeArms h t) A h0
  have hsupp := sampleFin_mem ((I.period t).act (takenAction (I.period t) (freeArms h t) A)
    (counts h)) u
  refine ⟨hact t ht _ hA1 _ _ hsupp, hA1, hA2, hA3, ?_, ?_⟩
  · intro B₁ hB₁ B₂ hB₂ hne h3
    exact h3 t ht _ hA1 _ _ hsupp B₁ hB₁ B₂ hB₂ hne
  · intro B hB
    exact (h1 t ht).2.2 B ((h1 t ht).2.1 _ hA1 hB)

/-! ### Quantile monotonicity -/

lemma exists_cdf_ge (G : PMF ℕ) (v : ℝ) (hv : v < 1) :
    ∃ x : ℕ, v ≤ (G.toOuterMeasure (Set.Iic x)).toReal := by
  have hmono : Monotone (fun n : ℕ => Set.Iic n) := fun a b hab => Set.Iic_subset_Iic.2 hab
  have ht := tendsto_measure_iUnion_atTop (μ := G.toMeasure) hmono
  rw [Set.iUnion_Iic, measure_univ] at ht
  have hlt : ENNReal.ofReal v < 1 := ENNReal.ofReal_lt_one.2 hv
  obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hlt)).exists
  refine ⟨n, ?_⟩
  have e : G.toOuterMeasure (Set.Iic n) = G.toMeasure (Set.Iic n) :=
    (PMF.toMeasure_apply_eq_toOuterMeasure_apply G (MeasurableSet.of_discrete)).symm
  rw [e]
  have hne : G.toMeasure (Set.Iic n) ≠ ⊤ := measure_ne_top _ _
  exact (ENNReal.ofReal_le_iff_le_toReal hne).1 hn.le

lemma toOuter_ne_top (G : PMF ℕ) (s : Set ℕ) : G.toOuterMeasure s ≠ ⊤ := by
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply G (MeasurableSet.of_discrete)]
  exact measure_ne_top _ _

lemma Finv_mono (F G : PMF ℕ)
    (hFG : ∀ x : ℕ, G.toOuterMeasure (Set.Iic x) ≤ F.toOuterMeasure (Set.Iic x))
    (v : ℝ) (hv : v < 1) : Finv F v ≤ Finv G v := by
  obtain ⟨x0, hx0⟩ := exists_cdf_ge G v hv
  unfold Finv
  have hmem := Nat.sInf_mem (s := {x : ℕ | v ≤ (G.toOuterMeasure (Set.Iic x)).toReal}) ⟨x0, hx0⟩
  apply Nat.sInf_le
  simp only [Set.mem_setOf_eq] at hmem ⊢
  exact hmem.trans (ENNReal.toReal_mono (toOuter_ne_top F _) (hFG _))

/-! ### The per-arm queue invariant -/

def InvL (I : ProblemInstance N) (hA hO : History N) (Q : List ℝ) (i : Fin N) : Prop :=
  counts hA i ≤ Q.length + counts hO i ∧
  (∀ j < Q.length, ∃ k < hA.length, i ∈ activatedArms (activatedAt hA k) ∧
      counts (hA.take k) i + Q.length = counts hA i + j ∧ Q.getD j 0 < 1 ∧
      dur hA k i = Finv (I.block i (counts (hA.take k) i)) (Q.getD j 0)) ∧
  (∀ k < hA.length, i ∈ activatedArms (activatedAt hA k) →
      counts hA i ≤ Q.length + counts (hA.take k) i ∨
      ∃ k', k ≤ k' ∧ k' < hO.length ∧ i ∈ activatedArms (activatedAt hO k') ∧
        dur hA k i ≤ dur hO k' i)

lemma inv_nil (I : ProblemInstance N) (i : Fin N) : InvL I [] [] [] i := by
  refine ⟨?_, ?_, ?_⟩
  · simp [counts_nil]
  · intro j hj
    simp at hj
  · intro k hk
    simp at hk

lemma inv_push (I : ProblemInstance N) (hA hO : History N) (Q : List ℝ) (i : Fin N)
    (s : Step N) (x : ℝ) (hx : x < 1)
    (hs : i ∈ activatedArms s.2.1 → s.2.2 i = Finv (I.block i (counts hA i)) x)
    (H : InvL I hA hO Q i) :
    InvL I (hA ++ [s]) hO (if i ∈ activatedArms s.2.1 then Q ++ [x] else Q) i := by
  obtain ⟨H1, H3, HAB⟩ := H
  have hlen : (hA ++ [s]).length = hA.length + 1 := by simp
  by_cases ha : i ∈ activatedArms s.2.1
  · rw [if_pos ha]
    have hc : counts (hA ++ [s]) i = counts hA i + 1 := by rw [counts_append, if_pos ha]
    have hQl : (Q ++ [x]).length = Q.length + 1 := by simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hc, hQl]
      omega
    · intro j hj
      rw [hQl] at hj
      rcases Nat.lt_or_ge j Q.length with hjq | hjq
      · obtain ⟨k, hk, hka, hkc, hv, hd⟩ := H3 j hjq
        refine ⟨k, by rw [hlen]; omega, ?_, ?_, ?_, ?_⟩
        · rw [actAt_append_lt _ _ hk]
          exact hka
        · rw [take_append_le _ _ hk.le, hQl, hc]
          omega
        · rw [List.getD_append _ _ _ _ hjq]
          exact hv
        · rw [dur_append_lt _ _ hk, take_append_le _ _ hk.le, List.getD_append _ _ _ _ hjq]
          exact hd
      · have hjq' : j = Q.length := by omega
        subst hjq'
        refine ⟨hA.length, by rw [hlen]; omega, ?_, ?_, ?_, ?_⟩
        · rw [actAt_append_len]
          exact ha
        · rw [take_append_le _ _ le_rfl, List.take_length, hQl, hc]
          omega
        · rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          exact hx
        · rw [dur_append_len, take_append_le _ _ le_rfl, List.take_length,
            List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          exact hs ha
    · intro k hk hka
      rw [hlen] at hk
      rcases Nat.lt_or_ge k hA.length with hk' | hk'
      · rw [actAt_append_lt _ _ hk'] at hka
        rcases HAB k hk' hka with hA1 | ⟨k', hkk', hk'l, hk'a, hdur⟩
        · left
          rw [hc, hQl, take_append_le _ _ hk'.le]
          omega
        · right
          exact ⟨k', hkk', hk'l, hk'a, by rw [dur_append_lt _ _ hk']; exact hdur⟩
      · have hkl : k = hA.length := by omega
        subst hkl
        left
        rw [hc, hQl, take_append_le _ _ le_rfl, List.take_length]
        omega
  · rw [if_neg ha]
    have hc : counts (hA ++ [s]) i = counts hA i := by
      rw [counts_append, if_neg ha, Nat.add_zero]
    refine ⟨?_, ?_, ?_⟩
    · rw [hc]
      exact H1
    · intro j hj
      obtain ⟨k, hk, hka, hkc, hv, hd⟩ := H3 j hj
      refine ⟨k, by rw [hlen]; omega, ?_, ?_, hv, ?_⟩
      · rw [actAt_append_lt _ _ hk]
        exact hka
      · rw [take_append_le _ _ hk.le, hc]
        exact hkc
      · rw [dur_append_lt _ _ hk, take_append_le _ _ hk.le]
        exact hd
    · intro k hk hka
      rw [hlen] at hk
      rcases Nat.lt_or_ge k hA.length with hk' | hk'
      · rw [actAt_append_lt _ _ hk'] at hka
        rcases HAB k hk' hka with hA1 | ⟨k', hkk', hk'l, hk'a, hdur⟩
        · left
          rw [hc, take_append_le _ _ hk'.le]
          exact hA1
        · right
          exact ⟨k', hkk', hk'l, hk'a, by rw [dur_append_lt _ _ hk']; exact hdur⟩
      · have hkl : k = hA.length := by omega
        subst hkl
        rw [actAt_append_len] at hka
        exact absurd hka ha

lemma inv_pop (I : ProblemInstance N) (h53 : DecayingAvailability I) (hA hO : History N)
    (Q1 : List ℝ) (i : Fin N) (s : Step N) (y : ℝ) (hlen : hA.length = hO.length + 1)
    (hs : i ∈ activatedArms s.2.1 → s.2.2 i = Finv (I.block i (counts hO i)) (Q1.headD y))
    (H : InvL I hA hO Q1 i) :
    InvL I hA (hO ++ [s]) (if i ∈ activatedArms s.2.1 then Q1.tail else Q1) i := by
  obtain ⟨H1, H3, HAB⟩ := H
  have hlenO : (hO ++ [s]).length = hO.length + 1 := by simp
  by_cases ho : i ∈ activatedArms s.2.1
  · rw [if_pos ho]
    have hc : counts (hO ++ [s]) i = counts hO i + 1 := by rw [counts_append, if_pos ho]
    cases Q1 with
    | nil =>
      simp only [List.tail_nil, List.length_nil, Nat.zero_add] at H1 HAB ⊢
      refine ⟨?_, ?_, ?_⟩
      · rw [hc]
        omega
      · intro j hj
        simp at hj
      · intro k hk hka
        rcases HAB k hk hka with hA1 | ⟨k', hkk', hk'l, hk'a, hdur⟩
        · left
          simpa using hA1
        · right
          refine ⟨k', hkk', by rw [hlenO]; omega, ?_, ?_⟩
          · rw [actAt_append_lt _ _ hk'l]
            exact hk'a
          · rw [dur_append_lt _ _ hk'l]
            exact hdur
    | cons v rest =>
      simp only [List.tail_cons]
      simp only [List.length_cons] at H1 H3 HAB
      refine ⟨?_, ?_, ?_⟩
      · rw [hc]
        omega
      · intro j hj
        obtain ⟨k, hk, hka, hkc, hv, hd⟩ := H3 (j + 1) (by omega)
        rw [List.getD_cons_succ] at hv hd
        exact ⟨k, hk, hka, by omega, hv, hd⟩
      · intro k hk hka
        rcases HAB k hk hka with hA1 | ⟨k', hkk', hk'l, hk'a, hdur⟩
        · by_cases hstrict : counts hA i ≤ rest.length + counts (hA.take k) i
          · left
            exact hstrict
          · right
            obtain ⟨k0, hk0, hk0a, hk0c, hv0, hd0⟩ := H3 0 (by omega)
            rw [List.getD_cons_zero] at hv0 hd0
            have hck : counts (hA.take k0) i = counts (hA.take k) i := by omega
            have hkk0 : k0 = k := by
              rcases Nat.lt_trichotomy k0 k with h' | h' | h'
              · have := counts_lt_of_act hA i h' hk0 hk0a
                omega
              · exact h'
              · have := counts_lt_of_act hA i h' hk hka
                omega
            subst hkk0
            refine ⟨hO.length, by omega, by rw [hlenO]; omega, ?_, ?_⟩
            · rw [actAt_append_len]
              exact ho
            · rw [dur_append_len, hs ho, hd0]
              simp only [List.headD_cons]
              apply Finv_mono _ _ (fun x => h53 i x _ _ (by omega)) v hv0
        · right
          refine ⟨k', hkk', by rw [hlenO]; omega, ?_, ?_⟩
          · rw [actAt_append_lt _ _ hk'l]
            exact hk'a
          · rw [dur_append_lt _ _ hk'l]
            exact hdur
  · rw [if_neg ho]
    have hc : counts (hO ++ [s]) i = counts hO i := by
      rw [counts_append, if_neg ho, Nat.add_zero]
    refine ⟨?_, H3, ?_⟩
    · rw [hc]
      exact H1
    · intro k hk hka
      rcases HAB k hk hka with hA1 | ⟨k', hkk', hk'l, hk'a, hdur⟩
      · left
        exact hA1
      · right
        refine ⟨k', hkk', by rw [hlenO]; omega, ?_, ?_⟩
        · rw [actAt_append_lt _ _ hk'l]
          exact hk'a
        · rw [dur_append_lt _ _ hk'l]
          exact hdur

lemma bad_pop (I : ProblemInstance N) (hA hO : History N) (Q : List ℝ) (i : Fin N) (t : ℕ)
    (hlA : hA.length = t) (H : InvL I hA hO Q i) (hfreeO : i ∈ freeArms hO t)
    (hbad : counts hO i < counts hA i ∨ i ∉ freeArms hA t) (s : Step N) (x : ℝ) :
    (if i ∈ activatedArms s.2.1 then Q ++ [x] else Q) ≠ [] := by
  obtain ⟨H1, H3, HAB⟩ := H
  split_ifs with ha
  · simp
  · intro hQ
    subst hQ
    simp only [List.length_nil, Nat.zero_add] at H1 HAB
    rcases hbad with hlt | hnf
    · omega
    · rw [mem_freeArms] at hnf hfreeO
      push_neg at hnf
      obtain ⟨k, hk, hka, hkt⟩ := hnf
      rcases HAB k hk hka with hA1 | ⟨k', hkk', hk'l, hk'a, hdur⟩
      · have := counts_lt_of_act' hA i hk hka
        omega
      · have := hfreeO k' hk'l hk'a
        omega

/-! ### The coupled run -/

def wn {T : ℕ} (w : Tape N T) (t : ℕ) : Noise N := if ht : t < T then w ⟨t, ht⟩ else (0, 0, 0)

section Coupled

variable {T : ℕ} (I : ProblemInstance N)
  (actP actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (w w' : Tape N T)

noncomputable def stPf (t : ℕ) : Step N :=
  stepOf I t (coupledRun I actP actO w w' t).1
    (actP t (coupledRun I actP actO w w' t).1 (wn w t).1) (wn w t).2.1 (wn w t).2.2

noncomputable def SOf (t : ℕ) : Finset (Finset (Fin N)) :=
  sampleFin ((I.period t).act (takenAction (I.period t)
    (freeArms (coupledRun I actP actO w w' t).2.1 t)
    (actO t (coupledRun I actP actO w w' t).2.1 (wn w' t).1))
    (counts (coupledRun I actP actO w w' t).2.1)) (wn w' t).2.1

noncomputable def Q1f (t : ℕ) (i : Fin N) : List ℝ :=
  if i ∈ activatedArms (stPf I actP actO w w' t).2.1 then
    (coupledRun I actP actO w w' t).2.2.1 i ++ [(wn w t).2.2 i]
  else (coupledRun I actP actO w w' t).2.2.1 i

noncomputable def seedOf (t : ℕ) : Fin N → ℝ := fun i =>
  if i ∈ activatedArms (SOf I actP actO w w' t) then
    (Q1f I actP actO w w' t i).headD ((wn w' t).2.2 i) else 0

noncomputable def stOf (t : ℕ) : Step N :=
  stepOf I t (coupledRun I actP actO w w' t).2.1
    (actO t (coupledRun I actP actO w w' t).2.1 (wn w' t).1) (wn w' t).2.1
    (seedOf I actP actO w w' t)

lemma cr_zero : coupledRun I actP actO w w' 0 = ([], [], fun _ => [], []) := rfl

lemma cr_succ {t : ℕ} (ht : t < T) :
    coupledRun I actP actO w w' (t + 1) =
      ((coupledRun I actP actO w w' t).1 ++ [stPf I actP actO w w' t],
        (coupledRun I actP actO w w' t).2.1 ++ [stOf I actP actO w w' t],
        fun i => if i ∈ activatedArms (SOf I actP actO w w' t) then
          (Q1f I actP actO w w' t i).tail else Q1f I actP actO w w' t i,
        (coupledRun I actP actO w w' t).2.2.2 ++ [seedOf I actP actO w w' t]) := by
  have h1 : wn w t = w ⟨t, ht⟩ := dif_pos ht
  have h2 : wn w' t = w' ⟨t, ht⟩ := dif_pos ht
  rw [show coupledRun I actP actO w w' (t + 1) = coupledStep I t actP actO
      (coupledRun I actP actO w w' t) (w ⟨t, ht⟩) (w' ⟨t, ht⟩) by
    simp only [coupledRun, dif_pos ht]]
  unfold stOf seedOf Q1f SOf stPf
  rw [h1, h2]
  rfl

lemma cr_ge {t : ℕ} (ht : ¬ t < T) :
    coupledRun I actP actO w w' (t + 1) = coupledRun I actP actO w w' t := by
  simp only [coupledRun, dif_neg ht]

lemma cr1 {t : ℕ} (ht : t < T) :
    (coupledRun I actP actO w w' (t + 1)).1 =
      (coupledRun I actP actO w w' t).1 ++ [stPf I actP actO w w' t] := by
  rw [cr_succ I actP actO w w' ht]

lemma cr2 {t : ℕ} (ht : t < T) :
    (coupledRun I actP actO w w' (t + 1)).2.1 =
      (coupledRun I actP actO w w' t).2.1 ++ [stOf I actP actO w w' t] := by
  rw [cr_succ I actP actO w w' ht]

lemma cr3 {t : ℕ} (ht : t < T) (i : Fin N) :
    (coupledRun I actP actO w w' (t + 1)).2.2.1 i =
      if i ∈ activatedArms (SOf I actP actO w w' t) then
        (Q1f I actP actO w w' t i).tail else Q1f I actP actO w w' t i := by
  rw [cr_succ I actP actO w w' ht]

lemma stOf_fst (t : ℕ) : (stOf I actP actO w w' t).2.1 = SOf I actP actO w w' t := rfl

lemma cr_len (t : ℕ) : (coupledRun I actP actO w w' t).1.length = min t T ∧
    (coupledRun I actP actO w w' t).2.1.length = min t T := by
  induction t with
  | zero => simp [cr_zero]
  | succ t ih =>
    by_cases ht : t < T
    · rw [cr1 I actP actO w w' ht, cr2 I actP actO w w' ht]
      simp only [List.length_append, List.length_singleton, ih.1, ih.2]
      constructor <;> omega
    · rw [cr_ge I actP actO w w' ht]
      constructor <;> omega

lemma cr_len' {t : ℕ} (ht : t ≤ T) : (coupledRun I actP actO w w' t).1.length = t ∧
    (coupledRun I actP actO w w' t).2.1.length = t := by
  have := cr_len I actP actO w w' t
  constructor <;> omega

lemma cr_fst (t : ℕ) : (coupledRun I actP actO w w' t).1 = run I actP w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t < T
    · rw [cr1 I actP actO w w' ht]
      simp only [run, dif_pos ht]
      unfold stPf
      have h1 : wn w t = w ⟨t, ht⟩ := dif_pos ht
      rw [h1, ih]
    · rw [cr_ge I actP actO w w' ht, ih]
      simp only [run, dif_neg ht]

lemma cr_prefix (t m : ℕ) (htm : t + m ≤ T) :
    (coupledRun I actP actO w w' t).1 <+: (coupledRun I actP actO w w' (t + m)).1 ∧
    (coupledRun I actP actO w w' t).2.1 <+: (coupledRun I actP actO w w' (t + m)).2.1 := by
  induction m with
  | zero => exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | succ m ih =>
    have ih' := ih (by omega)
    have hlt : t + m < T := by omega
    rw [show t + (m + 1) = (t + m) + 1 by omega, cr1 I actP actO w w' hlt,
      cr2 I actP actO w w' hlt]
    exact ⟨ih'.1.trans (List.prefix_append _ _), ih'.2.trans (List.prefix_append _ _)⟩

lemma final_take {t : ℕ} (ht : t ≤ T) :
    (coupledRun I actP actO w w' T).1.take t = (coupledRun I actP actO w w' t).1 ∧
    (coupledRun I actP actO w w' T).2.1.take t = (coupledRun I actP actO w w' t).2.1 := by
  have hp := cr_prefix I actP actO w w' t (T - t) (by omega)
  rw [show t + (T - t) = T by omega] at hp
  have hl := cr_len' I actP actO w w' ht
  constructor
  · have := List.prefix_iff_eq_take.1 hp.1
    rw [hl.1] at this
    exact this.symm
  · have := List.prefix_iff_eq_take.1 hp.2
    rw [hl.2] at this
    exact this.symm

lemma final_at {t : ℕ} (ht : t < T) :
    activatedAt (coupledRun I actP actO w w' T).1 t = (stPf I actP actO w w' t).2.1 ∧
    activatedAt (coupledRun I actP actO w w' T).2.1 t = SOf I actP actO w w' t ∧
    actionAt (coupledRun I actP actO w w' T).2.1 t = (stOf I actP actO w w' t).1 ∧
    actionAt (coupledRun I actP actO w w' T).1 t = (stPf I actP actO w w' t).1 := by
  have hp := cr_prefix I actP actO w w' (t + 1) (T - (t + 1)) (by omega)
  rw [show t + 1 + (T - (t + 1)) = T by omega] at hp
  have hl := cr_len' I actP actO w w' (show t ≤ T by omega)
  have hl1 := cr_len' I actP actO w w' (show t + 1 ≤ T by omega)
  have g1 : (coupledRun I actP actO w w' T).1.getD t (∅, ∅, fun _ => 0) =
      stPf I actP actO w w' t := by
    rw [prefix_getD hp.1 (by omega), cr1 I actP actO w w' ht,
      List.getD_append_right _ _ _ _ (by omega), hl.1, Nat.sub_self, List.getD_cons_zero]
  have g2 : (coupledRun I actP actO w w' T).2.1.getD t (∅, ∅, fun _ => 0) =
      stOf I actP actO w w' t := by
    rw [prefix_getD hp.2 (by omega), cr2 I actP actO w w' ht,
      List.getD_append_right _ _ _ _ (by omega), hl.2, Nat.sub_self, List.getD_cons_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold activatedAt
    rw [g1]
  · unfold activatedAt
    rw [g2]
    rfl
  · unfold actionAt
    rw [g2]
  · unfold actionAt
    rw [g1]

lemma inv_all (h53 : DecayingAvailability I) (htape : ∀ τ i, (w τ).2.2 i < 1) (i : Fin N) :
    ∀ t ≤ T, InvL I (coupledRun I actP actO w w' t).1 (coupledRun I actP actO w w' t).2.1
      ((coupledRun I actP actO w w' t).2.2.1 i) i := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [cr_zero]
    exact inv_nil I i
  | succ t ih =>
    intro ht1
    have ht : t < T := by omega
    have H := ih (by omega)
    have hl := cr_len' I actP actO w w' (show t ≤ T by omega)
    rw [cr1 I actP actO w w' ht, cr2 I actP actO w w' ht, cr3 I actP actO w w' ht]
    have hx : (wn w t).2.2 i < 1 := by
      rw [show wn w t = w ⟨t, ht⟩ from dif_pos ht]
      exact htape _ _
    have Hmid : InvL I ((coupledRun I actP actO w w' t).1 ++ [stPf I actP actO w w' t])
        (coupledRun I actP actO w w' t).2.1 (Q1f I actP actO w w' t i) i :=
      inv_push I _ _ _ i (stPf I actP actO w w' t) ((wn w t).2.2 i) hx
        (fun ha => stepOf_dur _ _ _ _ _ _ _ ha) H
    have hs : i ∈ activatedArms (stOf I actP actO w w' t).2.1 →
        (stOf I actP actO w w' t).2.2 i =
          Finv (I.block i (counts (coupledRun I actP actO w w' t).2.1 i))
            ((Q1f I actP actO w w' t i).headD ((wn w' t).2.2 i)) := by
      intro ho
      have ho' : i ∈ activatedArms (SOf I actP actO w w' t) := ho
      unfold stOf at ho ⊢
      rw [stepOf_dur _ _ _ _ _ _ _ ho]
      simp only [seedOf, ho', ↓reduceIte]
    have Hfin := inv_pop I h53 _ _ (Q1f I actP actO w w' t i) i (stOf I actP actO w w' t)
      ((wn w' t).2.2 i) (by simp [hl.1, hl.2]) hs Hmid
    rw [stOf_fst] at Hfin
    exact Hfin

lemma pop_count (i : Fin N) : ∀ t ≤ T,
    (∑ s ∈ Finset.range t, (if i ∈ activatedArms (SOf I actP actO w w' s) ∧
        0 < (Q1f I actP actO w w' s i).length then 1 else 0)) +
      ((coupledRun I actP actO w w' t).2.2.1 i).length = counts (coupledRun I actP actO w w' t).1 i := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [cr_zero]
    simp [counts_nil]
  | succ t ih =>
    intro ht1
    have ht : t < T := by omega
    have ih' := ih (by omega)
    have hq : (Q1f I actP actO w w' t i).length =
        ((coupledRun I actP actO w w' t).2.2.1 i).length +
          (if i ∈ activatedArms (stPf I actP actO w w' t).2.1 then 1 else 0) := by
      unfold Q1f
      split_ifs <;> simp
    rw [Finset.sum_range_succ, cr1 I actP actO w w' ht, cr3 I actP actO w w' ht, counts_append]
    by_cases ho : i ∈ activatedArms (SOf I actP actO w w' t)
    · rw [if_pos ho, List.length_tail]
      simp only [ho, true_and]
      split_ifs at hq ⊢ <;> omega
    · rw [if_neg ho]
      simp only [ho, false_and, ↓reduceIte]
      split_ifs at hq ⊢ <;> omega

lemma bad_imp_pop {L : ℕ} (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (h53 : DecayingAvailability I) (htape : ∀ τ i, (w τ).2.2 i < 1) {t : ℕ} (ht : t < T)
    (B : Finset (Fin N)) (hB : B ∈ activatedAt (coupledRun I actP actO w w' T).2.1 t)
    (hbad : B ∉ goodSet (coupledRun I actP actO w w' T).1 (coupledRun I actP actO w w' T).2.1 t) :
    ∃ i ∈ B, i ∈ activatedArms (SOf I actP actO w w' t) ∧
      0 < (Q1f I actP actO w w' t i).length := by
  obtain ⟨fa1, fa2, fa3, fa4⟩ := final_at I actP actO w w' ht
  obtain ⟨ft1, ft2⟩ := final_take I actP actO w w' (show t ≤ T by omega)
  rw [fa2] at hB
  have hP := stepOf_props I h1 hact ht (coupledRun I actP actO w w' t).2.1
    (actO t (coupledRun I actP actO w w' t).2.1 (wn w' t).1) (wn w' t).2.1
    (seedOf I actP actO w w' t)
  have hBact : B ∈ (stOf I actP actO w w' t).1 := hP.1 hB
  have hBfree : B ⊆ freeArms (coupledRun I actP actO w w' t).2.1 t := hP.2.2.1 B hBact
  rw [mem_goodSet, fa3, ft1, ft2] at hbad
  have hl := cr_len' I actP actO w w' (show t ≤ T by omega)
  by_contra hno
  push_neg at hno
  apply hbad
  refine ⟨hBact, ?_, ?_⟩
  · intro i hiB
    by_contra hlt
    push_neg at hlt
    have hiS : i ∈ activatedArms (SOf I actP actO w w' t) := Finset.mem_biUnion.2 ⟨B, hB, hiB⟩
    have hne := bad_pop I _ _ _ i t hl.1 (inv_all I actP actO w w' h53 htape i t (by omega))
      (hBfree hiB) (Or.inl hlt) (stPf I actP actO w w' t) ((wn w t).2.2 i)
    have hpos : 0 < (Q1f I actP actO w w' t i).length := List.length_pos_iff.2 hne
    have := hno i hiB hiS
    omega
  · intro i hiB
    by_contra hnf
    have hiS : i ∈ activatedArms (SOf I actP actO w w' t) := Finset.mem_biUnion.2 ⟨B, hB, hiB⟩
    have hne := bad_pop I _ _ _ i t hl.1 (inv_all I actP actO w w' h53 htape i t (by omega))
      (hBfree hiB) (Or.inr hnf) (stPf I actP actO w w' t) ((wn w t).2.2 i)
    have hpos : 0 < (Q1f I actP actO w w' t i).length := List.length_pos_iff.2 hne
    have := hno i hiB hiS
    omega

theorem core_count {L : ℕ} (h1 : IndepSystemAssumption I T L)
    (hact : ActivatesWithinAction I T) (h3 : NonOverlappingActivation I T)
    (h53 : DecayingAvailability I) (htape : ∀ τ i, (w τ).2.2 i < 1) :
    (∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledRun I actP actO w w' T).2.1 t,
      (if B ∈ goodSet (coupledRun I actP actO w w' T).1 (coupledRun I actP actO w w' T).2.1 t
        then 0 else 1)) ≤
      ∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledRun I actP actO w w' T).1 t, B.card := by
  have hlT := cr_len' I actP actO w w' (le_refl T)
  calc (∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledRun I actP actO w w' T).2.1 t,
      (if B ∈ goodSet (coupledRun I actP actO w w' T).1 (coupledRun I actP actO w w' T).2.1 t
        then 0 else 1))
      ≤ ∑ t ∈ Finset.range T, ∑ i : Fin N,
          (if i ∈ activatedArms (SOf I actP actO w w' t) ∧
            0 < (Q1f I actP actO w w' t i).length then 1 else 0) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_range] at ht
        have hP := stepOf_props I h1 hact ht (coupledRun I actP actO w w' t).2.1
          (actO t (coupledRun I actP actO w w' t).2.1 (wn w' t).1) (wn w' t).2.1
          (seedOf I actP actO w w' t)
        have hdisj : (↑(activatedAt (coupledRun I actP actO w w' T).2.1 t) :
            Set (Finset (Fin N))).PairwiseDisjoint id := by
          intro B₁ hB₁ B₂ hB₂ hne
          rw [(final_at I actP actO w w' ht).2.1] at hB₁ hB₂
          exact hP.2.2.2.2.1 B₁ hB₁ B₂ hB₂ hne h3
        calc (∑ B ∈ activatedAt (coupledRun I actP actO w w' T).2.1 t,
            (if B ∈ goodSet (coupledRun I actP actO w w' T).1
              (coupledRun I actP actO w w' T).2.1 t then 0 else 1))
            ≤ ∑ B ∈ activatedAt (coupledRun I actP actO w w' T).2.1 t, ∑ i ∈ B,
                (if i ∈ activatedArms (SOf I actP actO w w' t) ∧
                  0 < (Q1f I actP actO w w' t i).length then 1 else 0) := by
              apply Finset.sum_le_sum
              intro B hB
              split_ifs with hg
              · exact Nat.zero_le _
              · obtain ⟨i, hiB, hp⟩ :=
                  bad_imp_pop I actP actO w w' h1 hact h53 htape ht B hB hg
                calc 1 = (if i ∈ activatedArms (SOf I actP actO w w' t) ∧
                      0 < (Q1f I actP actO w w' t i).length then 1 else 0) := by rw [if_pos hp]
                  _ ≤ _ := Finset.single_le_sum (f := fun i =>
                      (if i ∈ activatedArms (SOf I actP actO w w' t) ∧
                        0 < (Q1f I actP actO w w' t i).length then 1 else 0))
                      (fun _ _ => Nat.zero_le _) hiB
          _ = ∑ i ∈ (activatedAt (coupledRun I actP actO w w' T).2.1 t).biUnion id,
                (if i ∈ activatedArms (SOf I actP actO w w' t) ∧
                  0 < (Q1f I actP actO w w' t i).length then 1 else 0) :=
              (Finset.sum_biUnion hdisj).symm
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => Nat.zero_le _)
    _ = ∑ i : Fin N, ∑ t ∈ Finset.range T,
          (if i ∈ activatedArms (SOf I actP actO w w' t) ∧
            0 < (Q1f I actP actO w w' t i).length then 1 else 0) := Finset.sum_comm
    _ ≤ ∑ i : Fin N, counts (coupledRun I actP actO w w' T).1 i := by
        apply Finset.sum_le_sum
        intro i _
        have := pop_count I actP actO w w' i T le_rfl
        omega
    _ = ∑ i : Fin N, ∑ t ∈ Finset.range T,
          (if i ∈ activatedArms (activatedAt (coupledRun I actP actO w w' T).1 t) then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [counts_eq_sum, hlT.1]
    _ = ∑ t ∈ Finset.range T, ∑ i : Fin N,
          (if i ∈ activatedArms (activatedAt (coupledRun I actP actO w w' T).1 t) then 1 else 0) :=
        Finset.sum_comm
    _ ≤ ∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledRun I actP actO w w' T).1 t, B.card := by
        apply Finset.sum_le_sum
        intro t _
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
        unfold activatedArms
        exact Finset.card_biUnion_le

theorem core_count_real {L : ℕ} (h1 : IndepSystemAssumption I T L)
    (hact : ActivatesWithinAction I T) (h3 : NonOverlappingActivation I T)
    (h53 : DecayingAvailability I) (htape : ∀ τ i, (w τ).2.2 i < 1) :
    (∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledRun I actP actO w w' T).2.1 t,
      (if B ∈ goodSet (coupledRun I actP actO w w' T).1 (coupledRun I actP actO w w' T).2.1 t
        then (0 : ℝ) else 1)) ≤
      ∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledRun I actP actO w w' T).1 t,
        (B.card : ℝ) := by
  have h := core_count I actP actO w w' h1 hact h3 h53 htape
  have h' : ((∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledRun I actP actO w w' T).2.1 t,
      (if B ∈ goodSet (coupledRun I actP actO w w' T).1 (coupledRun I actP actO w w' T).2.1 t
        then 0 else 1) : ℕ) : ℝ) ≤
      ((∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledRun I actP actO w w' T).1 t,
        B.card : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

/-- Card bounds for activated bundles of both runs. -/
lemma card_le_L {L : ℕ} (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    {t : ℕ} (ht : t < T) :
    (∀ B ∈ activatedAt (coupledRun I actP actO w w' T).1 t, B.card ≤ L) ∧
    (∀ B ∈ activatedAt (coupledRun I actP actO w w' T).2.1 t, B.card ≤ L) := by
  obtain ⟨fa1, fa2, fa3, fa4⟩ := final_at I actP actO w w' ht
  have hP := stepOf_props I h1 hact ht (coupledRun I actP actO w w' t).1
    (actP t (coupledRun I actP actO w w' t).1 (wn w t).1) (wn w t).2.1 (wn w t).2.2
  have hO := stepOf_props I h1 hact ht (coupledRun I actP actO w w' t).2.1
    (actO t (coupledRun I actP actO w w' t).2.1 (wn w' t).1) (wn w' t).2.1
    (seedOf I actP actO w w' t)
  constructor
  · intro B hB
    rw [fa1] at hB
    exact hP.2.2.2.2.2 B (hP.1 hB)
  · intro B hB
    rw [fa2] at hB
    exact hO.2.2.2.2.2 B (hO.1 hB)

end Coupled

/-! ### Measure-theoretic glue -/

lemma unif_ae : ∀ᵐ u ∂unif, u < 1 := by
  rw [ae_iff]
  have hsub : {u : ℝ | ¬ u < 1} ∩ Set.Icc 0 1 ⊆ {1} := by
    intro u hu
    have h1 : ¬ u < 1 := hu.1
    have h2 : u ≤ 1 := hu.2.2
    push_neg at h1
    exact le_antisymm h2 h1
  unfold unif
  rw [Measure.restrict_apply' measurableSet_Icc]
  exact measure_mono_null hsub Real.volume_singleton

lemma noise_ae : ∀ᵐ x ∂(noiseLaw N), ∀ i, x.2.2 i < 1 := by
  rw [ae_all_iff]
  intro i
  have m1 : MeasurePreserving (fun x : Noise N => x.2) (noiseLaw N)
      (unif.prod (Measure.pi fun _ : Fin N => unif)) := measurePreserving_snd
  have m2 : MeasurePreserving (fun y : ℝ × (Fin N → ℝ) => y.2)
      (unif.prod (Measure.pi fun _ : Fin N => unif)) (Measure.pi fun _ : Fin N => unif) :=
    measurePreserving_snd
  have m3 : MeasurePreserving (fun f : Fin N → ℝ => f i) (Measure.pi fun _ : Fin N => unif) unif :=
    measurePreserving_eval (μ := fun _ : Fin N => unif) i
  have := (m3.comp (m2.comp m1)).quasiMeasurePreserving.ae unif_ae
  filter_upwards [this] with x hx
  exact hx

lemma tape_ae {T : ℕ} : ∀ᵐ w ∂(tapeLaw N T), ∀ τ i, (w τ).2.2 i < 1 := by
  rw [ae_all_iff]
  intro τ
  have m : MeasurePreserving (fun w : Tape N T => w τ) (tapeLaw N T) (noiseLaw N) :=
    measurePreserving_eval (μ := fun _ : Fin T => noiseLaw N) τ
  exact m.quasiMeasurePreserving.ae noise_ae

lemma coupled_ae {T : ℕ} (π π' : Rule N) [IsProbabilityMeasure π.seedLaw]
    [IsProbabilityMeasure π'.seedLaw] :
    ∀ᵐ ω ∂(coupledLaw T π π'), ∀ τ i, (ω.1.2 τ).2.2 i < 1 := by
  have m1 : MeasurePreserving (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => ω.1)
      (coupledLaw T π π') (π.seedLaw.prod (tapeLaw N T)) := measurePreserving_fst
  have m2 : MeasurePreserving (fun p : ℝ × Tape N T => p.2) (π.seedLaw.prod (tapeLaw N T))
      (tapeLaw N T) := measurePreserving_snd
  exact (m2.comp m1).quasiMeasurePreserving.ae tape_ae

instance coupled_prob {T : ℕ} (π π' : Rule N) [IsProbabilityMeasure π.seedLaw]
    [IsProbabilityMeasure π'.seedLaw] : IsProbabilityMeasure (coupledLaw T π π') := by
  unfold coupledLaw
  infer_instance

/-- Integral of a function of the first run against the coupled law. -/
lemma integral_fst {T : ℕ} (π π' : Rule N) [IsProbabilityMeasure π.seedLaw]
    [IsProbabilityMeasure π'.seedLaw] (F : ℝ × Tape N T → ℝ) (hF : Measurable F) :
    ∫ ω, F ω.1 ∂(coupledLaw T π π') = ∫ p, F p ∂(π.seedLaw.prod (tapeLaw N T)) := by
  have hmap : Measure.map Prod.fst (coupledLaw T π π') = π.seedLaw.prod (tapeLaw N T) :=
    (measurePreserving_fst : MeasurePreserving Prod.fst ((π.seedLaw.prod (tapeLaw N T)).prod
      (π'.seedLaw.prod (tapeLaw N T))) _).map_eq
  rw [← hmap, integral_map measurable_fst.aemeasurable]
  rw [hmap]
  exact hF.aestronglyMeasurable

/-- Measurability of a function of the first run. -/
lemma run_fst_measurable {T : ℕ} (I : ProblemInstance N) (π : Rule N)
    (hπ : ∀ (t : ℕ) (h : History N) (A : Finset (Finset (Fin N))),
      MeasurableSet {p : ℝ × ℝ | π.act p.1 t h p.2 = A}) (G : History N → ℝ) :
    Measurable (fun p : ℝ × Tape N T => G (run I (π.act p.1) p.2 T)) :=
  (run_DM (T := T) I π.act (fun t h A => hπ t h A) T).measurable G

lemma sumcard_bound (h : History N) (T : ℕ) :
    0 ≤ (∑ t ∈ Finset.range T, ∑ B ∈ activatedAt h t, (B.card : ℝ)) ∧
    (∑ t ∈ Finset.range T, ∑ B ∈ activatedAt h t, (B.card : ℝ)) ≤
      T * ((Fintype.card (Finset (Fin N)) : ℝ) * N) := by
  constructor
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  · calc (∑ t ∈ Finset.range T, ∑ B ∈ activatedAt h t, (B.card : ℝ))
        ≤ ∑ _t ∈ Finset.range T, ((Fintype.card (Finset (Fin N)) : ℝ) * N) := by
          apply Finset.sum_le_sum
          intro t _
          calc (∑ B ∈ activatedAt h t, (B.card : ℝ)) ≤ ∑ _B ∈ activatedAt h t, (N : ℝ) := by
                apply Finset.sum_le_sum
                intro B _
                have := Finset.card_le_univ B
                rw [Fintype.card_fin] at this
                exact_mod_cast this
            _ = ((activatedAt h t).card : ℝ) * N := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (Fintype.card (Finset (Fin N)) : ℝ) * N := by
                apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
                exact_mod_cast Finset.card_le_univ _
      _ = T * ((Fintype.card (Finset (Fin N)) : ℝ) * N) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma sumone_bound (h : History N) (T : ℕ) :
    0 ≤ (∑ t ∈ Finset.range T, ∑ _B ∈ activatedAt h t, (1 : ℝ)) ∧
    (∑ t ∈ Finset.range T, ∑ _B ∈ activatedAt h t, (1 : ℝ)) ≤
      T * (Fintype.card (Finset (Fin N)) : ℝ) := by
  constructor
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => zero_le_one
  · calc (∑ t ∈ Finset.range T, ∑ _B ∈ activatedAt h t, (1 : ℝ))
        ≤ ∑ _t ∈ Finset.range T, (Fintype.card (Finset (Fin N)) : ℝ) := by
          apply Finset.sum_le_sum
          intro t _
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast Finset.card_le_univ _
      _ = T * (Fintype.card (Finset (Fin N)) : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Greedy-specific facts -/

lemma greedy_DM_const (O : Oracle N) (sc : PeriodData N → Finset (Fin N) → (Fin N → ℕ) → ℝ)
    (r : ℝ) (d : PeriodData N) (n : Fin N → ℕ) (free : Finset (Fin N)) :
    DM (fun q : ℝ × ℝ => greedyStep O sc r d n free q.2) := by
  unfold greedyStep
  exact sel_filter_DM O d _ n free _

lemma pathSum_eq (h : History N) (g : ℕ → Finset (Fin N) → (Fin N → ℕ) → ℝ) :
    pathSum h g = ∑ t ∈ Finset.range h.length, ∑ B ∈ activatedAt h t,
      g t B (counts (h.take t)) := by
  unfold pathSum
  rw [← Fin.sum_univ_eq_sum_range (fun t => ∑ B ∈ activatedAt h t, g t B (counts (h.take t)))
    h.length]
  apply Finset.sum_congr rfl
  intro k _
  unfold activatedAt
  rw [List.getD_eq_getElem _ _ k.isLt]
  try rfl

lemma grd_reward {T L : ℕ} (I : ProblemInstance N) (O : Oracle N) (r : ℝ)
    (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (w w' : Tape N T) {t : ℕ} (ht : t < T)
    (B : Finset (Fin N))
    (hB : B ∈ activatedAt (coupledRun I (fun t h u => greedyStep O (fun d B n => d.reward B n) r
      (I.period t) (counts h) (freeArms h t) u) actO w w' T).1 t) :
    r ≤ (I.period t).reward B (counts ((coupledRun I (fun t h u => greedyStep O
      (fun d B n => d.reward B n) r (I.period t) (counts h) (freeArms h t) u) actO w w' T).1.take t)) := by
  obtain ⟨fa1, fa2, fa3, fa4⟩ := final_at I (fun t h u => greedyStep O (fun d B n => d.reward B n) r
      (I.period t) (counts h) (freeArms h t) u) actO w w' ht
  obtain ⟨ft1, ft2⟩ := final_take I (fun t h u => greedyStep O (fun d B n => d.reward B n) r
      (I.period t) (counts h) (freeArms h t) u) actO w w' (show t ≤ T by omega)
  rw [fa1] at hB
  rw [ft1]
  have hP := stepOf_props I h1 hact ht (coupledRun I (fun t h u => greedyStep O
      (fun d B n => d.reward B n) r (I.period t) (counts h) (freeArms h t) u) actO w w' t).1
    (greedyStep O (fun d B n => d.reward B n) r (I.period t)
      (counts (coupledRun I (fun t h u => greedyStep O (fun d B n => d.reward B n) r
        (I.period t) (counts h) (freeArms h t) u) actO w w' t).1)
      (freeArms (coupledRun I (fun t h u => greedyStep O (fun d B n => d.reward B n) r
        (I.period t) (counts h) (freeArms h t) u) actO w w' t).1 t) (wn w t).1)
    (wn w t).2.1 (wn w t).2.2
  have hB2 := hP.2.2.2.1 (hP.1 hB)
  unfold greedyStep at hB2
  rw [Finset.mem_filter] at hB2
  exact hB2.2

end Aux_GRN

open GreedyReusableNet in
theorem solution {N T L : ℕ} (I : ProblemInstance N)
    (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (h3 : NonOverlappingActivation I T) (h53 : DecayingAvailability I)
    (O : Oracle N) (r : ℝ) (hr : 0 < r) (π' : Rule N) (hπ' : IsAdmissible π') :
    ∫ ω, (∑ t ∈ Finset.range T,
        ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).2.1 t,
          if B ∉ goodSet (coupledFinal I T (GRD I O r) π' ω).1
                (coupledFinal I T (GRD I O r) π' ω).2.1 t ∧
              r ≤ (I.period t).reward B (counts ((coupledFinal I T (GRD I O r) π' ω).2.1.take t))
          then r else 0) ∂(coupledLaw T (GRD I O r) π') ≤
      (L : ℝ) * Rew I T (GRD I O r) := by
  haveI : IsProbabilityMeasure (GRD I O r).seedLaw := by
    show IsProbabilityMeasure (Measure.dirac (0 : ℝ))
    infer_instance
  haveI : IsProbabilityMeasure π'.seedLaw := hπ'.1
  have hadm : ∀ (t : ℕ) (h : History N) (A : Finset (Finset (Fin N))),
      MeasurableSet {p : ℝ × ℝ | (GRD I O r).act p.1 t h p.2 = A} := by
    intro t h A
    exact Aux_GRN.greedy_DM_const O (fun d B n => d.reward B n) r (I.period t) (counts h)
      (freeArms h t) A
  have hFm : Measurable (fun p : ℝ × Tape N T => pathSum (run I ((GRD I O r).act p.1) p.2 T)
      (fun t B n => (I.period t).reward B n)) :=
    Aux_GRN.run_fst_measurable (T := T) I (GRD I O r) hadm
      (fun h => pathSum h (fun t B n => (I.period t).reward B n))
  have hRew : Rew I T (GRD I O r) = ∫ ω, pathSum (run I ((GRD I O r).act ω.1.1) ω.1.2 T)
      (fun t B n => (I.period t).reward B n) ∂(coupledLaw T (GRD I O r) π') := by
    rw [Aux_GRN.integral_fst (T := T) (GRD I O r) π' (fun p => pathSum
      (run I ((GRD I O r).act p.1) p.2 T) (fun t B n => (I.period t).reward B n)) hFm]
    rfl
  have hint : Integrable (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
      pathSum (run I ((GRD I O r).act ω.1.1) ω.1.2 T) (fun t B n => (I.period t).reward B n))
      (coupledLaw T (GRD I O r) π') := by
    refine Integrable.of_bound (hFm.comp measurable_fst).aestronglyMeasurable
      (T * ((Fintype.card (Finset (Fin N)) : ℝ) *
        Aux_GRN.Mb T (fun t B n => (I.period t).reward B n)))
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    apply Aux_GRN.pathSum_abs_le
    rw [Aux_GRN.run_length]
    exact min_le_right _ _
  rw [hRew, ← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun t _ =>
      Finset.sum_nonneg fun B _ => by split_ifs <;> linarith
  · exact hint.const_mul _
  · filter_upwards [Aux_GRN.coupled_ae (T := T) (GRD I O r) π'] with ω hω
    try dsimp only
    have hc := Aux_GRN.core_count_real I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2
      h1 hact h3 h53 hω
    have hlen := (Aux_GRN.cr_len' I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2
      (le_refl T)).1
    have hF : pathSum (run I ((GRD I O r).act ω.1.1) ω.1.2 T)
        (fun t B n => (I.period t).reward B n) =
        ∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).1 t,
          (I.period t).reward B (counts ((coupledFinal I T (GRD I O r) π' ω).1.take t)) := by
      rw [← Aux_GRN.cr_fst I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2,
        Aux_GRN.pathSum_eq, hlen]
      rfl
    rw [hF]
    calc _ ≤ ∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).2.1 t,
            r * (if B ∈ goodSet (coupledFinal I T (GRD I O r) π' ω).1
              (coupledFinal I T (GRD I O r) π' ω).2.1 t then (0 : ℝ) else 1) := by
          apply Finset.sum_le_sum
          intro t _
          apply Finset.sum_le_sum
          intro B _
          split_ifs with ha hb hb
          · exact absurd hb ha.1
          · simp
          · simp
          · simpa using hr.le
      _ = r * ∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).2.1 t,
            (if B ∈ goodSet (coupledFinal I T (GRD I O r) π' ω).1
              (coupledFinal I T (GRD I O r) π' ω).2.1 t then (0 : ℝ) else 1) := by
          simp_rw [Finset.mul_sum]
      _ ≤ r * ∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).1 t,
            (B.card : ℝ) := mul_le_mul_of_nonneg_left hc hr.le
      _ = ∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).1 t,
            r * (B.card : ℝ) := by
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).1 t,
            (L : ℝ) * (I.period t).reward B
              (counts ((coupledFinal I T (GRD I O r) π' ω).1.take t)) := by
          apply Finset.sum_le_sum
          intro t ht
          rw [Finset.mem_range] at ht
          apply Finset.sum_le_sum
          intro B hB
          have hcard := (Aux_GRN.card_le_L I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2
            h1 hact ht).1 B hB
          have hrew := Aux_GRN.grd_reward I O r h1 hact (π'.act ω.2.1) ω.1.2 ω.2.2 ht B hB
          have hcard' : (B.card : ℝ) ≤ L := by exact_mod_cast hcard
          calc r * (B.card : ℝ) ≤ r * L := mul_le_mul_of_nonneg_left hcard' hr.le
            _ = (L : ℝ) * r := mul_comm _ _
            _ ≤ (L : ℝ) * (I.period t).reward B
                (counts ((coupledFinal I T (GRD I O r) π' ω).1.take t)) :=
                mul_le_mul_of_nonneg_left hrew (Nat.cast_nonneg _)
      _ = (L : ℝ) * ∑ t ∈ Finset.range T, ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).1 t,
            (I.period t).reward B (counts ((coupledFinal I T (GRD I O r) π' ω).1.take t)) := by
          simp_rw [Finset.mul_sum]
