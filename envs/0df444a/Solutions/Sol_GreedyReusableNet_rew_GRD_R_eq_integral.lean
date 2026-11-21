-- Prove2me | solution 1 for GreedyReusableNet.rew_GRD_R_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:57:33.522849+00:00
-- url     : https://prove2.me/submissions/5e20f1ad-5a82-4e88-8259-efe2e473044b

import Mathlib
import Definitions.Def_GreedyReusableNet_Rew
import Definitions.Def_GreedyReusableNet_GRD
import Definitions.Def_GreedyReusableNet_GRDbar
import Definitions.Def_GreedyReusableNet_GRD_R
import Definitions.Def_GreedyReusableNet_GRDbar_R
import Definitions.Def_GreedyReusableNet_thresholdLaw

open MeasureTheory

namespace Aux_GRN_int

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

lemma thr_finite (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : IsFiniteMeasure (thresholdLaw a b) := by
  constructor
  unfold thresholdLaw
  rw [Measure.add_apply, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · simp
  · have hL : 0 ≤ Real.log (b / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
    have hpos : 0 < (1 + Real.log (b / a)) * a := mul_pos (by linarith) ha
    calc ∫⁻ x, ENNReal.ofReal (1 / ((1 + Real.log (b / a)) * x)) ∂(volume.restrict (Set.Ioc a b))
        ≤ ∫⁻ _x, ENNReal.ofReal (1 / ((1 + Real.log (b / a)) * a))
            ∂(volume.restrict (Set.Ioc a b)) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          apply ENNReal.ofReal_le_ofReal
          apply one_div_le_one_div_of_le hpos
          exact mul_le_mul_of_nonneg_left hx.1.le (by linarith)
      _ < ⊤ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp [Real.volume_Ioc])

lemma main {T : ℕ} (I : ProblemInstance N) (O : Oracle N)
    (sc : PeriodData N → Finset (Fin N) → (Fin N → ℕ) → ℝ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ p : ℝ × Tape N T, pathSum (run I (fun t h u =>
        greedyStep O sc p.1 (I.period t) (counts h) (freeArms h t) u) p.2 T)
        (fun t B n => (I.period t).reward B n) ∂((thresholdLaw a b).prod (tapeLaw N T)) =
      ∫ r, (∫ p : ℝ × Tape N T, pathSum (run I (fun t h u =>
        greedyStep O sc r (I.period t) (counts h) (freeArms h t) u) p.2 T)
        (fun t B n => (I.period t).reward B n) ∂((Measure.dirac 0).prod (tapeLaw N T)))
        ∂(thresholdLaw a b) := by
  haveI := thr_finite a b ha hab
  set g : ℕ → Finset (Fin N) → (Fin N → ℕ) → ℝ := fun t B n => (I.period t).reward B n with hg
  have hrun := run_DM (T := T) I
    (fun r t h u => greedyStep O sc r (I.period t) (counts h) (freeArms h t) u)
    (fun t h => greedy_DM O sc (I.period t) (counts h) (freeArms h t))
  have hmeas : Measurable (fun p : ℝ × Tape N T => pathSum (run I (fun t h u =>
        greedyStep O sc p.1 (I.period t) (counts h) (freeArms h t) u) p.2 T) g) :=
    (hrun T).measurable (fun h => pathSum h g)
  have hint : Integrable (fun p : ℝ × Tape N T => pathSum (run I (fun t h u =>
        greedyStep O sc p.1 (I.period t) (counts h) (freeArms h t) u) p.2 T) g)
        ((thresholdLaw a b).prod (tapeLaw N T)) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable
      (T * ((Fintype.card (Finset (Fin N)) : ℝ) * Mb T g)) (Filter.Eventually.of_forall ?_)
    intro p
    rw [Real.norm_eq_abs]
    apply pathSum_abs_le
    rw [run_length]
    exact min_le_right _ _
  rw [integral_prod _ hint]
  congr 1
  funext r
  rw [Measure.dirac_prod, (measurableEmbedding_prodMk_left (0 : ℝ)).integral_map]
  try rfl

end Aux_GRN_int

open GreedyReusableNet in
theorem solution {N T : ℕ} (I : ProblemInstance N) (O : Oracle N)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Rew I T (GRD_R I O a b) = ∫ r, Rew I T (GRD I O r) ∂(thresholdLaw a b) ∧
      Rew I T (GRDbar_R I O a b) = ∫ r, Rew I T (GRDbar I O r) ∂(thresholdLaw a b) := by
  constructor
  · exact Aux_GRN_int.main I O (fun d B n => d.reward B n) a b ha hab
  · exact Aux_GRN_int.main I O avgReward a b ha hab
