-- Prove2me | solution 1 for GreedyReusableNet.eq_12_part_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:09:39.328115+00:00
-- url     : https://prove2.me/submissions/9ed00bfc-2b44-4d74-be87-c311534e97af

import Mathlib
import Definitions.Def_GreedyReusableNet_IndepSystemAssumption
import Definitions.Def_GreedyReusableNet_ActivatesWithinAction
import Definitions.Def_GreedyReusableNet_Substitutability
import Definitions.Def_GreedyReusableNet_DecayingReward
import Definitions.Def_GreedyReusableNet_DecayingProbability
import Definitions.Def_GreedyReusableNet_IsApproxOracle
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

end Coupled

/-! ### Measure-theoretic glue -/

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


/-! ### The law of `sampleFin` -/

section SampleLaw

variable {α : Type*} [Fintype α]

noncomputable def pP (p : PMF α) (j : Fin (Fintype.card α)) : ℝ :=
  (p ((Fintype.equivFin α).symm j)).toReal

noncomputable def cc (p : PMF α) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card α) => j.val < i), pP p j

lemma cc_zero (p : PMF α) : cc p 0 = 0 := by
  unfold cc
  rw [Finset.filter_false_of_mem (fun j _ => Nat.not_lt_zero _), Finset.sum_empty]

lemma cc_succ (p : PMF α) {i : ℕ} (hi : i < Fintype.card α) :
    cc p (i + 1) = cc p i + pP p ⟨i, hi⟩ := by
  unfold cc
  have e : Finset.univ.filter (fun j : Fin (Fintype.card α) => j.val < i + 1) =
      insert ⟨i, hi⟩ (Finset.univ.filter (fun j : Fin (Fintype.card α) => j.val < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [e, Finset.sum_insert (by simp)]
  ring

lemma cdf_eq (p : PMF α) (k : Fin (Fintype.card α)) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card α) => j ≤ k),
      (p ((Fintype.equivFin α).symm j)).toReal = cc p (k.val + 1) := by
  unfold cc pP
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val]
  omega

lemma cc_card (p : PMF α) : cc p (Fintype.card α) = 1 := by
  unfold cc pP
  rw [Finset.filter_true_of_mem (fun j _ => j.isLt)]
  rw [Equiv.sum_comp (Fintype.equivFin α).symm (fun a => (p a).toReal)]
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a)]
  have h : ∑ a, p a = 1 := by
    have := p.tsum_coe
    rwa [tsum_fintype] at this
  rw [h, ENNReal.toReal_one]

lemma pP_eq_zero (p : PMF α) (j : Fin (Fintype.card α)) :
    pP p j = 0 ↔ p ((Fintype.equivFin α).symm j) = 0 := by
  unfold pP
  rw [ENNReal.toReal_eq_zero_iff]
  simp [PMF.apply_ne_top]

lemma cc_const_after (p : PMF α) (jm : Fin (Fintype.card α))
    (hz : ∀ j : Fin (Fintype.card α), jm < j → p ((Fintype.equivFin α).symm j) = 0) :
    ∀ d, jm.val + 1 + d ≤ Fintype.card α → cc p (jm.val + 1 + d) = cc p (jm.val + 1) := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro hd
    rw [show jm.val + 1 + (d + 1) = (jm.val + 1 + d) + 1 by omega, cc_succ p (by omega),
      ih (by omega)]
    have : pP p ⟨jm.val + 1 + d, by omega⟩ = 0 := by
      rw [pP_eq_zero]
      apply hz
      rw [Fin.lt_iff_val_lt_val]
      show jm.val < jm.val + 1 + d
      omega
    rw [this, add_zero]

lemma min'_le_of {β : Type*} [LinearOrder β] (S : Finset β) (h : S.Nonempty) :
    ∀ x ∈ S, S.min' h ≤ x := fun x hx => Finset.min'_le S x hx

lemma sampleFin_spec (p : PMF α) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    cc p (Fintype.equivFin α (sampleFin p u)).val ≤ u ∧
      u < cc p ((Fintype.equivFin α (sampleFin p u)).val + 1) ∧ p (sampleFin p u) ≠ 0 := by
  classical
  have hsupp : ∃ j : Fin (Fintype.card α), p ((Fintype.equivFin α).symm j) ≠ 0 := by
    obtain ⟨a, ha⟩ := p.support_nonempty
    exact ⟨Fintype.equivFin α a, by simpa using (PMF.mem_support_iff p a).1 ha⟩
  have hsne : (Finset.univ.filter (fun j : Fin (Fintype.card α) =>
      p ((Fintype.equivFin α).symm j) ≠ 0)).Nonempty := by
    obtain ⟨j, hj⟩ := hsupp
    exact ⟨j, by simp [hj]⟩
  set jm := (Finset.univ.filter (fun j : Fin (Fintype.card α) =>
      p ((Fintype.equivFin α).symm j) ≠ 0)).max' hsne with hjm
  have hjm_mem : p ((Fintype.equivFin α).symm jm) ≠ 0 := by
    have := Finset.max'_mem _ hsne
    rw [← hjm] at this
    simpa using this
  have hz : ∀ j : Fin (Fintype.card α), jm < j → p ((Fintype.equivFin α).symm j) = 0 := by
    intro j hj
    by_contra hne
    have hle := Finset.le_max' (Finset.univ.filter (fun j : Fin (Fintype.card α) =>
      p ((Fintype.equivFin α).symm j) ≠ 0)) j (by simp [hne])
    rw [← hjm] at hle
    exact absurd hj (not_lt.2 hle)
  have hcj : cc p (jm.val + 1) = 1 := by
    have := cc_const_after p jm hz (Fintype.card α - (jm.val + 1)) (by omega)
    rw [show jm.val + 1 + (Fintype.card α - (jm.val + 1)) = Fintype.card α by omega,
      cc_card] at this
    exact this.symm
  unfold sampleFin
  try dsimp only
  split_ifs with hG
  · have hmem := Finset.min'_mem _ hG
    have hmin := min'_le_of _ hG
    simp only [Equiv.apply_symm_apply]
    generalize Finset.min' _ hG = K at hmem hmin ⊢
    rw [Finset.mem_filter] at hmem
    obtain ⟨_, hpk, huk⟩ := hmem
    refine ⟨?_, ?_, hpk⟩
    · have key : ∀ i, i ≤ K.val → cc p i ≤ u := by
        intro i
        induction i with
        | zero => intro _; rw [cc_zero]; exact hu0
        | succ i ih =>
          intro hi
          have hi' : i < Fintype.card α := by
            have := K.isLt
            omega
          rw [cc_succ p hi']
          by_cases hpi : p ((Fintype.equivFin α).symm ⟨i, hi'⟩) = 0
          · rw [(pP_eq_zero p _).2 hpi, add_zero]
            exact ih (by omega)
          · rw [← cc_succ p hi']
            by_contra hcon
            push_neg at hcon
            have hlt : u < ∑ j ∈ Finset.univ.filter
                (fun j : Fin (Fintype.card α) => j ≤ ⟨i, hi'⟩),
                (p ((Fintype.equivFin α).symm j)).toReal := by
              rw [cdf_eq]
              exact hcon
            have hle := hmin ⟨i, hi'⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hpi, hlt⟩)
            rw [Fin.le_iff_val_le_val] at hle
            have : K.val ≤ i := hle
            omega
      exact key _ le_rfl
    · rw [← cdf_eq]
      exact huk
  · exfalso
    apply hG
    refine ⟨jm, Finset.mem_filter.2 ⟨Finset.mem_univ _, hjm_mem, ?_⟩⟩
    rw [cdf_eq, hcj]
    exact hu1

lemma unif_sampleFin_le (p : PMF α) (a : α) : unif {u | sampleFin p u = a} ≤ p a := by
  set k := Fintype.equivFin α a with hk
  have hsub : {u : ℝ | sampleFin p u = a} ∩ Set.Icc 0 1 ⊆
      Set.Ico (cc p k.val) (cc p (k.val + 1)) ∪ {1} := by
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    simp only [Set.mem_setOf_eq] at h1
    rcases lt_or_eq_of_le h2.2 with hlt | heq
    · left
      have := sampleFin_spec p u h2.1 hlt
      rw [h1, ← hk] at this
      exact ⟨this.1, this.2.1⟩
    · right
      exact heq
  unfold unif
  rw [Measure.restrict_apply' measurableSet_Icc]
  calc volume ({u : ℝ | sampleFin p u = a} ∩ Set.Icc 0 1)
      ≤ volume (Set.Ico (cc p k.val) (cc p (k.val + 1)) ∪ {1}) := measure_mono hsub
    _ ≤ volume (Set.Ico (cc p k.val) (cc p (k.val + 1))) + volume ({1} : Set ℝ) :=
        measure_union_le _ _
    _ = p a := by
        rw [Real.volume_Ico, Real.volume_singleton, add_zero, cc_succ p k.isLt]
        have : pP p ⟨k.val, k.isLt⟩ = (p a).toReal := by
          unfold pP
          rw [hk]
          simp
        rw [show cc p k.val + pP p ⟨k.val, k.isLt⟩ - cc p k.val = pP p ⟨k.val, k.isLt⟩ by ring,
          this, ENNReal.ofReal_toReal (PMF.apply_ne_top p a)]

lemma unif_sampleFin (p : PMF α) (a : α) : unif {u | sampleFin p u = a} = p a := by
  have hmeas : ∀ b, MeasurableSet {u : ℝ | sampleFin p u = b} := fun b => sampleFin_DM p b
  have htot : ∑ b, unif {u : ℝ | sampleFin p u = b} = 1 := by
    have hU : (⋃ b, {u : ℝ | sampleFin p u = b}) = Set.univ := by
      ext u
      simp
    have := measure_iUnion (μ := unif) (f := fun b => {u : ℝ | sampleFin p u = b})
      (fun b c hbc => by
        rw [Function.onFun, Set.disjoint_left]
        intro u hu hu'
        exact hbc (hu.symm.trans hu')) hmeas
    rw [hU, measure_univ, tsum_fintype] at this
    exact this.symm
  have hp : ∑ b, p b = 1 := by
    have := p.tsum_coe
    rwa [tsum_fintype] at this
  have hle : ∀ b ∈ (Finset.univ : Finset α), (unif {u : ℝ | sampleFin p u = b}).toReal ≤
      (p b).toReal :=
    fun b _ => ENNReal.toReal_mono (PMF.apply_ne_top p b) (unif_sampleFin_le p b)
  have hsum : ∑ b, (unif {u : ℝ | sampleFin p u = b}).toReal = ∑ b, (p b).toReal := by
    rw [← ENNReal.toReal_sum (fun b _ => measure_ne_top _ _),
      ← ENNReal.toReal_sum (fun b _ => PMF.apply_ne_top p b), htot, hp]
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hsum a (Finset.mem_univ a)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (PMF.apply_ne_top p a)).1 heq

lemma integral_sampleFin (p : PMF α) (g : α → ℝ) :
    ∫ u, g (sampleFin p u) ∂unif = ∑ a, (p a).toReal * g a := by
  have hS : ∀ a, MeasurableSet {u : ℝ | sampleFin p u = a} := fun a => sampleFin_DM p a
  have e : (fun u => g (sampleFin p u)) =
      fun u => ∑ a, ({u | sampleFin p u = a} : Set ℝ).indicator (fun _ => g a) u := by
    funext u
    rw [Finset.sum_eq_single (sampleFin p u)]
    · simp [Set.indicator]
    · intro b _ hb
      simp [Set.indicator, Ne.symm hb]
    · simp
  rw [e, integral_finset_sum _ (fun a _ => (integrable_const (g a)).indicator (hS a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_indicator_const _ (hS a), smul_eq_mul]
  simp only [Measure.real, unif_sampleFin]

end SampleLaw

lemma integral_sample_sum {N : ℕ} (q : PMF (Finset (Finset (Fin N)))) (c : Finset (Fin N) → ℝ) :
    ∫ u, ∑ B ∈ sampleFin q u, c B ∂unif =
      ∑ B, c B * (q.toOuterMeasure {S | B ∈ S}).toReal := by
  rw [integral_sampleFin q (fun S => ∑ B ∈ S, c B)]
  calc ∑ S, (q S).toReal * ∑ B ∈ S, c B
      = ∑ S, ∑ B, (if B ∈ S then (q S).toReal * c B else 0) := by
        apply Finset.sum_congr rfl
        intro S _
        rw [Finset.mul_sum, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = ∑ B, ∑ S, (if B ∈ S then (q S).toReal * c B else 0) := Finset.sum_comm
    _ = ∑ B, c B * (q.toOuterMeasure {S | B ∈ S}).toReal := by
        apply Finset.sum_congr rfl
        intro B _
        rw [PMF.toOuterMeasure_apply, tsum_fintype,
          ENNReal.toReal_sum (fun S _ => by
            simp only [Set.indicator]
            split_ifs <;> simp [PMF.apply_ne_top]), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hBS : B ∈ S
        · rw [if_pos hBS, Set.indicator_of_mem (show S ∈ {S : Finset (Finset (Fin N)) | B ∈ S} from hBS)]
          ring
        · rw [if_neg hBS, Set.indicator_of_notMem (show S ∉ {S : Finset (Finset (Fin N)) | B ∈ S} from hBS)]
          simp

/-! ### Finite-range integrals over the noise -/

lemma integrable_finrange {X Z : Type*} [MeasurableSpace X] [Fintype Z] {μ : Measure X}
    [IsFiniteMeasure μ] {D : X → Z} (hD : DM D) (φ : Z → ℝ) :
    Integrable (fun x => φ (D x)) μ := by
  refine Integrable.of_bound (hD.measurable φ).aestronglyMeasurable (∑ z, |φ z|)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun z => |φ z|) (fun z _ => abs_nonneg _) (Finset.mem_univ (D x))

lemma noise_integral {N : ℕ} {Z : Type*} [Fintype Z] (D : ℝ × ℝ → Z) (hD : DM D) (φ : Z → ℝ) :
    ∫ b, φ (D (b.1, b.2.1)) ∂(noiseLaw N) = ∫ v, ∫ v1, φ (D (v, v1)) ∂unif ∂unif := by
  unfold noiseLaw
  have hm : Measurable (fun b : ℝ × ℝ × (Fin N → ℝ) => (b.1, b.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hint : Integrable (fun b : ℝ × ℝ × (Fin N → ℝ) => φ (D (b.1, b.2.1)))
      (unif.prod (unif.prod (Measure.pi fun _ : Fin N => unif))) :=
    integrable_finrange (hD.comp_meas hm) φ
  rw [integral_prod _ hint]
  apply integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hm2 : Measurable (fun q : ℝ × (Fin N → ℝ) => (v, q.1)) := measurable_const.prodMk measurable_fst
  have hint2 : Integrable (fun q : ℝ × (Fin N → ℝ) => φ (D (v, q.1)))
      (unif.prod (Measure.pi fun _ : Fin N => unif)) :=
    integrable_finrange (hD.comp_meas hm2) φ
  show ∫ q, φ (D (v, q.1)) ∂(unif.prod (Measure.pi fun _ : Fin N => unif)) =
    ∫ v1, φ (D (v, v1)) ∂unif
  rw [integral_prod _ hint2]
  simp

/-! ### One step of the greedy run against one step of the benchmark -/

section OneStep

variable {N : ℕ} (I : ProblemInstance N) (O : Oracle N) (r : ℝ) (t : ℕ)

noncomputable def fR (hA : History N) : Finset (Fin N) → ℝ :=
  fun B => (I.period t).reward B (counts hA) *
    (if r ≤ (I.period t).reward B (counts hA) then 1 else 0)

noncomputable def Aalg (hA : History N) (u : ℝ) : Finset (Finset (Fin N)) :=
  takenAction (I.period t) (freeArms hA t)
    (greedyStep O (fun d B n => d.reward B n) r (I.period t) (counts hA) (freeArms hA t) u)

noncomputable def Yfun (hA : History N) (a : Noise N) : ℝ :=
  ∑ B ∈ sampleFin ((I.period t).act (Aalg I O r t hA a.1) (counts hA)) a.2.1,
    (I.period t).reward B (counts hA)

noncomputable def Aopt (actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (hO : History N)
    (v : ℝ) : Finset (Finset (Fin N)) :=
  takenAction (I.period t) (freeArms hO t) (actO t hO v)

def goodP (hA hO : History N) (B : Finset (Fin N)) : Prop :=
  (∀ i ∈ B, counts hA i ≤ counts hO i) ∧ B ⊆ freeArms hA t

noncomputable def cA (hA hO : History N) (A : Finset (Finset (Fin N))) (B : Finset (Fin N)) : ℝ := by
  classical
  exact if (B ∈ A ∧ goodP t hA hO B) ∧ r ≤ (I.period t).reward B (counts hO) then r else 0

noncomputable def Xfun (actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (hA hO : History N)
    (b : Noise N) : ℝ :=
  ∑ B ∈ sampleFin ((I.period t).act (Aopt I t actO hO b.1) (counts hO)) b.2.1,
    cA I r t hA hO (Aopt I t actO hO b.1) B

lemma greedy_DM1 (hA : History N) :
    DM (fun u : ℝ => greedyStep O (fun d B n => d.reward B n) r (I.period t) (counts hA)
      (freeArms hA t) u) := by
  unfold greedyStep
  have h0 : DM (O.sel (I.period t) (fun B => (I.period t).reward B (counts hA) *
      (if r ≤ (I.period t).reward B (counts hA) then 1 else 0)) (counts hA) (freeArms hA t)) :=
    fun A => O.measurable_sel _ _ _ _ A
  exact h0.comp_fun _

lemma Aalg_DM (hA : History N) : DM (fun u : ℝ => Aalg I O r t hA u) := by
  unfold Aalg
  exact (greedy_DM1 I O r t hA).comp_fun _

lemma Aopt_DM (actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (hO : History N)
    (hactO : DM (fun v : ℝ => actO t hO v)) : DM (fun v : ℝ => Aopt I t actO hO v) := by
  unfold Aopt
  exact hactO.comp_fun _

lemma prob_nonneg' (d : PeriodData N) (B : Finset (Fin N)) (A : Finset (Finset (Fin N)))
    (n : Fin N → ℕ) : 0 ≤ prob d B A n := ENNReal.toReal_nonneg

lemma prob_zero_of_not_mem {T : ℕ} (hact : ActivatesWithinAction I T) (ht : t < T)
    (A : Finset (Finset (Fin N))) (hA : A ∈ (I.period t).actions) (n : Fin N → ℕ)
    (B : Finset (Fin N)) (hB : B ∉ A) : prob (I.period t) B A n = 0 := by
  unfold prob
  rw [(PMF.toOuterMeasure_apply_eq_zero_iff _ _).2, ENNReal.toReal_zero]
  rw [Set.disjoint_left]
  intro S hS hBS
  exact hB (hact t ht A hA n S hS hBS)

lemma takenAction_mem {L T : ℕ} (h1 : IndepSystemAssumption I T L) (ht : t < T)
    (free : Finset (Fin N)) (A : Finset (Finset (Fin N))) :
    takenAction (I.period t) free A ∈ (I.period t).actions ∧
      (∀ B ∈ takenAction (I.period t) free A, B ⊆ free) ∧ takenAction (I.period t) free A ⊆ A := by
  have hI := (h1 t ht).1
  unfold SubsamplingSM.Offline.IsIndepSystem at hI
  exact takenAction_spec (I.period t) free A hI.1

lemma Yint {L T : ℕ} (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (ht : t < T) (hA : History N) :
    ∫ a, Yfun I O r t hA a ∂(noiseLaw N) =
      ∫ u, objValue (I.period t) (fR I r t hA) (counts hA) (Aalg I O r t hA u) ∂unif := by
  have hD : DM (fun q : ℝ × ℝ => sampleFin ((I.period t).act (Aalg I O r t hA q.1) (counts hA)) q.2) :=
    DM.bind (D := fun q : ℝ × ℝ => Aalg I O r t hA q.1) ((Aalg_DM I O r t hA).comp_meas measurable_fst)
      (F := fun A q => sampleFin ((I.period t).act A (counts hA)) q.2)
      (fun A => (sampleFin_DM _).comp_meas measurable_snd)
  have e := noise_integral (N := N) _ hD (fun S => ∑ B ∈ S, (I.period t).reward B (counts hA))
  have e' : ∫ a, Yfun I O r t hA a ∂(noiseLaw N) =
      ∫ b, (fun S => ∑ B ∈ S, (I.period t).reward B (counts hA))
        ((fun q : ℝ × ℝ => sampleFin ((I.period t).act (Aalg I O r t hA q.1) (counts hA)) q.2)
          (b.1, b.2.1)) ∂(noiseLaw N) := rfl
  rw [e', e]
  apply integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show ∫ v1, ∑ B ∈ sampleFin ((I.period t).act (Aalg I O r t hA u) (counts hA)) v1,
      (I.period t).reward B (counts hA) ∂unif = _
  rw [integral_sample_sum]
  obtain ⟨hAm, _, hAsub⟩ := takenAction_mem I t h1 ht (freeArms hA t)
    (greedyStep O (fun d B n => d.reward B n) r (I.period t) (counts hA) (freeArms hA t) u)
  unfold objValue
  rw [← Finset.sum_subset (Finset.subset_univ (Aalg I O r t hA u))]
  · apply Finset.sum_congr rfl
    intro B hB
    have hBg := hAsub hB
    unfold greedyStep at hBg
    rw [Finset.mem_filter] at hBg
    unfold fR
    rw [if_pos hBg.2, mul_one]
    rfl
  · intro B _ hB
    have : prob (I.period t) B (Aalg I O r t hA u) (counts hA) = 0 :=
      prob_zero_of_not_mem I t hact ht _ hAm _ B hB
    unfold prob at this
    rw [this, mul_zero]

lemma Xint (actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (hA hO : History N)
    (hactO : DM (fun v : ℝ => actO t hO v)) :
    ∫ b, Xfun I r t actO hA hO b ∂(noiseLaw N) =
      ∫ v, ∑ B, cA I r t hA hO (Aopt I t actO hO v) B *
        prob (I.period t) B (Aopt I t actO hO v) (counts hO) ∂unif := by
  have hD : DM (fun q : ℝ × ℝ => (Aopt I t actO hO q.1,
      sampleFin ((I.period t).act (Aopt I t actO hO q.1) (counts hO)) q.2)) :=
    DM.bind (D := fun q : ℝ × ℝ => Aopt I t actO hO q.1)
      ((Aopt_DM I t actO hO hactO).comp_meas measurable_fst)
      (F := fun A q => (A, sampleFin ((I.period t).act A (counts hO)) q.2))
      (fun A => DM.pair (DM.const _) ((sampleFin_DM _).comp_meas measurable_snd))
  have e := noise_integral (N := N) _ hD
    (fun z : Finset (Finset (Fin N)) × Finset (Finset (Fin N)) => ∑ B ∈ z.2, cA I r t hA hO z.1 B)
  have e' : ∫ b, Xfun I r t actO hA hO b ∂(noiseLaw N) =
      ∫ b, (fun z : Finset (Finset (Fin N)) × Finset (Finset (Fin N)) =>
        ∑ B ∈ z.2, cA I r t hA hO z.1 B)
        ((fun q : ℝ × ℝ => (Aopt I t actO hO q.1,
          sampleFin ((I.period t).act (Aopt I t actO hO q.1) (counts hO)) q.2)) (b.1, b.2.1))
        ∂(noiseLaw N) := rfl
  rw [e', e]
  apply integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show ∫ v1, ∑ B ∈ sampleFin ((I.period t).act (Aopt I t actO hO v) (counts hO)) v1,
      cA I r t hA hO (Aopt I t actO hO v) B ∂unif = _
  rw [integral_sample_sum]
  rfl

lemma fR_nonneg (hr : 0 < r) (hA : History N) (B : Finset (Fin N)) : 0 ≤ fR I r t hA B := by
  unfold fR
  split_ifs with h
  · rw [mul_one]
    linarith
  · rw [mul_zero]

lemma objValue_nonneg (hr : 0 < r) (hA : History N) (A : Finset (Finset (Fin N))) :
    0 ≤ objValue (I.period t) (fR I r t hA) (counts hA) A :=
  Finset.sum_nonneg fun B _ => mul_nonneg (fR_nonneg I r t hr hA B) (prob_nonneg' _ _ _ _)

lemma avail_iff (d : PeriodData N) (free : Finset (Fin N)) (A : Finset (Finset (Fin N))) :
    IsAvailableSet d free A ↔ A ∈ d.actions ∧ ∀ B ∈ A, B ⊆ free := Iff.rfl

lemma pointwise_bound {L T : ℕ} (h1 : IndepSystemAssumption I T L)
    (h2 : Substitutability I T) (h51 : DecayingReward I T) (h52 : DecayingProbability I T)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hO : IsApproxOracle I T α β O) (hr : 0 < r) (ht : t < T)
    (hA hO' : History N) (A' : Finset (Finset (Fin N))) (hA'act : A' ∈ (I.period t).actions) :
    α * β * (∑ B, cA I r t hA hO' A' B * prob (I.period t) B A' (counts hO')) ≤
      ∫ u, objValue (I.period t) (fR I r t hA) (counts hA) (Aalg I O r t hA u) ∂unif := by
  classical
  have hIall := h1 t ht
  have hI := hIall.1
  unfold SubsamplingSM.Offline.IsIndepSystem at hI
  obtain ⟨G, hG⟩ : ∃ G : Finset (Finset (Fin N)),
      G = A'.filter (fun B => goodP t hA hO' B ∧ r ≤ (I.period t).reward B (counts hO')) :=
    ⟨_, rfl⟩
  have hmemG : ∀ B, B ∈ G ↔ B ∈ A' ∧ (goodP t hA hO' B ∧
      r ≤ (I.period t).reward B (counts hO')) := by
    intro B
    rw [hG, Finset.mem_filter]
  have hΨ : ∑ B, cA I r t hA hO' A' B * prob (I.period t) B A' (counts hO') =
      ∑ B ∈ G, r * prob (I.period t) B A' (counts hO') := by
    rw [← Finset.sum_subset (Finset.subset_univ G)]
    · apply Finset.sum_congr rfl
      intro B hB
      have hB' := (hmemG B).1 hB
      unfold cA
      rw [if_pos ⟨⟨hB'.1, hB'.2.1⟩, hB'.2.2⟩]
    · intro B _ hB
      unfold cA
      rw [if_neg, zero_mul]
      intro hc
      exact hB ((hmemG B).2 ⟨hc.1.1, hc.1.2, hc.2⟩)
  have hGsub : G ⊆ A' := by
    intro B hB
    exact ((hmemG B).1 hB).1
  have hGact : G ∈ (I.period t).actions := hI.2 G A' hGsub hA'act
  have hGavail : IsAvailableSet (I.period t) (freeArms hA t) G := by
    rw [avail_iff]
    exact ⟨hGact, fun B hB => ((hmemG B).1 hB).2.1.2⟩
  have hobjG : ∑ B ∈ G, r * prob (I.period t) B A' (counts hO') ≤
      objValue (I.period t) (fR I r t hA) (counts hA) G := by
    unfold objValue
    apply Finset.sum_le_sum
    intro B hB
    obtain ⟨hBA, ⟨hgood1, _⟩, hrR⟩ := (hmemG B).1 hB
    have hBb : B ∈ (I.period t).bundles := hIall.2.1 A' hA'act hBA
    have hRR : (I.period t).reward B (counts hO') ≤ (I.period t).reward B (counts hA) :=
      h51 t ht B hBb (counts hA) (counts hO') hgood1
    have hfR : fR I r t hA B = (I.period t).reward B (counts hA) := by
      unfold fR
      rw [if_pos (hrR.trans hRR), mul_one]
    have hp1 : prob (I.period t) B A' (counts hA) ≤ prob (I.period t) B G (counts hA) :=
      h2 t ht B hBb G A' hA'act hB hGsub (counts hA)
    have hp2 : prob (I.period t) B A' (counts hO') ≤ prob (I.period t) B A' (counts hA) :=
      h52 t ht B hBb A' hA'act (counts hA) (counts hO') hgood1
    rw [hfR]
    have hpG : 0 ≤ prob (I.period t) B G (counts hA) := prob_nonneg' _ _ _ _
    calc r * prob (I.period t) B A' (counts hO') ≤ r * prob (I.period t) B G (counts hA) :=
          mul_le_mul_of_nonneg_left (hp2.trans hp1) hr.le
      _ ≤ (I.period t).reward B (counts hA) * prob (I.period t) B G (counts hA) :=
          mul_le_mul_of_nonneg_right (hrR.trans hRR) hpG
  have hEβ := hO t ht (fR I r t hA) (fR_nonneg I r t hr hA) (counts hA) (freeArms hA t)
  obtain ⟨E, hE⟩ : ∃ E : Set ℝ, E = {u : ℝ | IsAvailableSet (I.period t) (freeArms hA t)
      (O.sel (I.period t) (fR I r t hA) (counts hA) (freeArms hA t) u) ∧
      ∀ A'' : Finset (Finset (Fin N)), IsAvailableSet (I.period t) (freeArms hA t) A'' →
        α * objValue (I.period t) (fR I r t hA) (counts hA) A'' ≤
          objValue (I.period t) (fR I r t hA) (counts hA)
            (O.sel (I.period t) (fR I r t hA) (counts hA) (freeArms hA t) u)} := ⟨_, rfl⟩
  rw [← hE] at hEβ
  have hEm : MeasurableSet E := by
    have hsel : DM (O.sel (I.period t) (fR I r t hA) (counts hA) (freeArms hA t)) :=
      fun A => O.measurable_sel _ _ _ _ A
    rw [hE]
    exact hsel.preimage {A | IsAvailableSet (I.period t) (freeArms hA t) A ∧
      ∀ A'' : Finset (Finset (Fin N)), IsAvailableSet (I.period t) (freeArms hA t) A'' →
        α * objValue (I.period t) (fR I r t hA) (counts hA) A'' ≤
          objValue (I.period t) (fR I r t hA) (counts hA) A}
  have hgE : ∀ u ∈ E, α * objValue (I.period t) (fR I r t hA) (counts hA) G ≤
      objValue (I.period t) (fR I r t hA) (counts hA) (Aalg I O r t hA u) := by
    intro u hu
    rw [hE] at hu
    obtain ⟨hav, hopt⟩ := hu
    have hS := (avail_iff _ _ _).1 hav
    obtain ⟨S, hSdef⟩ : ∃ S, S = O.sel (I.period t) (fR I r t hA) (counts hA) (freeArms hA t) u :=
      ⟨_, rfl⟩
    rw [← hSdef] at hS hopt
    obtain ⟨Sf, hSf⟩ : ∃ Sf, Sf = S.filter (fun B => r ≤ (I.period t).reward B (counts hA)) :=
      ⟨_, rfl⟩
    have hSfsub : Sf ⊆ S := by
      rw [hSf]
      exact Finset.filter_subset _ _
    have hSfavail : IsAvailableSet (I.period t) (freeArms hA t) Sf := by
      rw [avail_iff]
      exact ⟨hI.2 Sf S hSfsub hS.1, fun B hB => hS.2 B (hSfsub hB)⟩
    have hgs : greedyStep O (fun d B n => d.reward B n) r (I.period t) (counts hA)
        (freeArms hA t) u = Sf := by
      rw [hSf, hSdef]
      rfl
    have hAalg : Aalg I O r t hA u = Sf := by
      unfold Aalg
      rw [hgs]
      unfold takenAction
      rw [if_pos hSfavail]
    rw [hAalg]
    refine (hopt G hGavail).trans ?_
    unfold objValue
    have h0 : ∀ B ∈ S, B ∉ Sf → fR I r t hA B * prob (I.period t) B S (counts hA) = 0 := by
      intro B _ hB
      have hnot : ¬ r ≤ (I.period t).reward B (counts hA) := by
        intro hle
        apply hB
        rw [hSf, Finset.mem_filter]
        exact ⟨by assumption, hle⟩
      unfold fR
      rw [if_neg hnot, mul_zero, zero_mul]
    rw [← Finset.sum_subset hSfsub h0]
    apply Finset.sum_le_sum
    intro B hB
    have hBS := hSfsub hB
    have hBb : B ∈ (I.period t).bundles := hIall.2.1 S hS.1 hBS
    exact mul_le_mul_of_nonneg_left (h2 t ht B hBb Sf S hS.1 hB hSfsub (counts hA))
      (fR_nonneg I r t hr hA B)
  have hgi : Integrable (fun u => objValue (I.period t) (fR I r t hA) (counts hA)
      (Aalg I O r t hA u)) unif :=
    integrable_finrange (Aalg_DM I O r t hA)
      (fun A => objValue (I.period t) (fR I r t hA) (counts hA) A)
  have hind : ∫ u, E.indicator (fun _ => α * objValue (I.period t) (fR I r t hA) (counts hA) G) u
      ∂unif ≤ ∫ u, objValue (I.period t) (fR I r t hA) (counts hA) (Aalg I O r t hA u) ∂unif := by
    apply integral_mono ((integrable_const _).indicator hEm) hgi
    intro u
    by_cases hu : u ∈ E
    · rw [Set.indicator_of_mem hu]
      exact hgE u hu
    · rw [Set.indicator_of_notMem hu]
      exact objValue_nonneg I r t hr hA _
  rw [integral_indicator_const _ hEm, smul_eq_mul] at hind
  have hEr : β ≤ unif.real E := by
    unfold Measure.real
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hEβ
  have hΨ0 : 0 ≤ ∑ B ∈ G, r * prob (I.period t) B A' (counts hO') :=
    Finset.sum_nonneg fun B _ => mul_nonneg hr.le (prob_nonneg' _ _ _ _)
  rw [hΨ]
  have hobj0 : 0 ≤ objValue (I.period t) (fR I r t hA) (counts hA) G := hΨ0.trans hobjG
  have hk := mul_le_mul_of_nonneg_right hEr (mul_nonneg hα.le hobj0)
  calc α * β * ∑ B ∈ G, r * prob (I.period t) B A' (counts hO')
      ≤ α * β * objValue (I.period t) (fR I r t hA) (counts hA) G :=
        mul_le_mul_of_nonneg_left hobjG (by positivity)
    _ ≤ unif.real E * (α * objValue (I.period t) (fR I r t hA) (counts hA) G) := by
        nlinarith
    _ ≤ _ := hind

lemma local_ineq {L T : ℕ} (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (h2 : Substitutability I T) (h51 : DecayingReward I T) (h52 : DecayingProbability I T)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hO : IsApproxOracle I T α β O) (hr : 0 < r) (ht : t < T)
    (actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (hA hO' : History N)
    (hactO : DM (fun v : ℝ => actO t hO' v)) :
    α * β * ∫ b, Xfun I r t actO hA hO' b ∂(noiseLaw N) ≤ ∫ a, Yfun I O r t hA a ∂(noiseLaw N) := by
  rw [Xint I r t actO hA hO' hactO, Yint I O r t h1 hact ht hA]
  have hXi : Integrable (fun v => ∑ B, cA I r t hA hO' (Aopt I t actO hO' v) B *
      prob (I.period t) B (Aopt I t actO hO' v) (counts hO')) unif :=
    integrable_finrange (Aopt_DM I t actO hO' hactO)
      (fun A => ∑ B, cA I r t hA hO' A B * prob (I.period t) B A (counts hO'))
  have hpt : ∀ v, α * β * (∑ B, cA I r t hA hO' (Aopt I t actO hO' v) B *
      prob (I.period t) B (Aopt I t actO hO' v) (counts hO')) ≤
      ∫ u, objValue (I.period t) (fR I r t hA) (counts hA) (Aalg I O r t hA u) ∂unif := by
    intro v
    exact pointwise_bound I O r t h1 h2 h51 h52 α β hα hβ hO hr ht hA hO' _
      (takenAction_mem I t h1 ht (freeArms hO' t) (actO t hO' v)).1
  calc α * β * ∫ v, ∑ B, cA I r t hA hO' (Aopt I t actO hO' v) B *
        prob (I.period t) B (Aopt I t actO hO' v) (counts hO') ∂unif
      = ∫ v, α * β * ∑ B, cA I r t hA hO' (Aopt I t actO hO' v) B *
        prob (I.period t) B (Aopt I t actO hO' v) (counts hO') ∂unif :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ _v, (∫ u, objValue (I.period t) (fR I r t hA) (counts hA) (Aalg I O r t hA u) ∂unif)
        ∂unif := integral_mono (hXi.const_mul _) (integrable_const _) hpt
    _ = _ := by simp

end OneStep

/-! ### A countable-state description of the coupled histories -/

section Sym

variable {N T : ℕ} (I : ProblemInstance N)
  (actP actO : ℕ → History N → ℝ → Finset (Finset (Fin N)))

abbrev SState (N : ℕ) := History N × History N × (Fin N → List ℕ)

noncomputable def sStP (t : ℕ) (d : SState N) (wP : Noise N) : Step N :=
  stepOf I t d.1 (actP t d.1 wP.1) wP.2.1 wP.2.2

noncomputable def sS (t : ℕ) (d : SState N) (wO : Noise N) : Finset (Finset (Fin N)) :=
  sampleFin ((I.period t).act (takenAction (I.period t) (freeArms d.2.1 t) (actO t d.2.1 wO.1))
    (counts d.2.1)) wO.2.1

noncomputable def sQ1 (t : ℕ) (d : SState N) (wP : Noise N) (i : Fin N) : List ℕ :=
  if i ∈ activatedArms (sStP I actP t d wP).2.1 then d.2.2 i ++ [t] else d.2.2 i

noncomputable def sSeed (t : ℕ) (w : Tape N T) (d : SState N) (wP wO : Noise N) : Fin N → ℝ :=
  fun i => if i ∈ activatedArms (sS I actO t d wO) then
    ((sQ1 I actP t d wP i).head?).elim (wO.2.2 i) (fun τ => (wn w τ).2.2 i) else 0

noncomputable def sStep (t : ℕ) (w : Tape N T) (d : SState N) (wP wO : Noise N) : SState N :=
  (d.1 ++ [sStP I actP t d wP],
    d.2.1 ++ [stepOf I t d.2.1 (actO t d.2.1 wO.1) wO.2.1 (sSeed I actP actO t w d wP wO)],
    fun i => if i ∈ activatedArms (sS I actO t d wO) then (sQ1 I actP t d wP i).tail
      else sQ1 I actP t d wP i)

noncomputable def sRun (w w' : Tape N T) : ℕ → SState N
  | 0 => ([], [], fun _ => [])
  | t + 1 => if t < T then sStep I actP actO t w (sRun w w' t) (wn w t) (wn w' t)
      else sRun w w' t

lemma headD_map_eq (l : List ℕ) (f : ℕ → ℝ) (d : ℝ) :
    (l.map f).headD d = (l.head?).elim d f := by
  cases l <;> rfl

lemma sRun_eq (w w' : Tape N T) : ∀ t,
    (coupledRun I actP actO w w' t).1 = (sRun I actP actO w w' t).1 ∧
    (coupledRun I actP actO w w' t).2.1 = (sRun I actP actO w w' t).2.1 ∧
    ∀ i, (coupledRun I actP actO w w' t).2.2.1 i =
      ((sRun I actP actO w w' t).2.2 i).map (fun τ => (wn w τ).2.2 i) := by
  intro t
  induction t with
  | zero =>
    refine ⟨rfl, rfl, fun i => rfl⟩
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    by_cases ht : t < T
    · have hs : sRun I actP actO w w' (t + 1) =
          sStep I actP actO t w (sRun I actP actO w w' t) (wn w t) (wn w' t) := by
        simp only [sRun, if_pos ht]
      rw [cr1 I actP actO w w' ht, cr2 I actP actO w w' ht, hs]
      have hP : stPf I actP actO w w' t = sStP I actP t (sRun I actP actO w w' t) (wn w t) := by
        unfold stPf sStP
        rw [h1]
      have hS : SOf I actP actO w w' t = sS I actO t (sRun I actP actO w w' t) (wn w' t) := by
        unfold SOf sS
        rw [h2]
      have hQ : ∀ i, Q1f I actP actO w w' t i =
          (sQ1 I actP t (sRun I actP actO w w' t) (wn w t) i).map (fun τ => (wn w τ).2.2 i) := by
        intro i
        unfold Q1f sQ1
        rw [hP, h3 i]
        split_ifs
        · simp [List.map_append]
        · rfl
      have hseed : seedOf I actP actO w w' t =
          sSeed I actP actO t w (sRun I actP actO w w' t) (wn w t) (wn w' t) := by
        funext i
        simp only [seedOf, sSeed]
        rw [hS, hQ i, headD_map_eq]
      refine ⟨?_, ?_, fun i => ?_⟩
      · show (coupledRun I actP actO w w' t).1 ++ [stPf I actP actO w w' t] = _
        rw [h1, hP]
        rfl
      · show (coupledRun I actP actO w w' t).2.1 ++ [stOf I actP actO w w' t] = _
        unfold stOf
        rw [h2, hseed]
        rfl
      · rw [cr3 I actP actO w w' ht, hS, hQ i]
        show _ = (if i ∈ activatedArms (sS I actO t (sRun I actP actO w w' t) (wn w' t)) then
          (sQ1 I actP t (sRun I actP actO w w' t) (wn w t) i).tail
          else sQ1 I actP t (sRun I actP actO w w' t) (wn w t) i).map (fun τ => (wn w τ).2.2 i)
        split_ifs
        · rw [List.map_tail]
        · rfl
    · have hs : sRun I actP actO w w' (t + 1) = sRun I actP actO w w' t := by
        simp only [sRun, if_neg ht]
      rw [cr_ge I actP actO w w' ht, hs]
      exact ⟨h1, h2, h3⟩

end Sym

lemma meas_wn {N T : ℕ} (t : ℕ) : Measurable (fun w : Tape N T => wn w t) := by
  unfold wn
  by_cases ht : t < T
  · simp only [dif_pos ht]
    exact measurable_pi_apply _
  · simp only [dif_neg ht]
    exact measurable_const

lemma meas_bind {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Countable Z]
    {D : X → Z} (hD : DM D) {G : Z → X → Y} (hG : ∀ z, Measurable (G z)) :
    Measurable (fun x => G (D x) x) := by
  intro S hS
  have : (fun x => G (D x) x) ⁻¹' S = ⋃ z, (D ⁻¹' {z} ∩ (G z) ⁻¹' S) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨D x, rfl, h⟩
    · rintro ⟨z, rfl, h⟩
      exact h
  rw [this]
  exact MeasurableSet.iUnion fun z => (hD z).inter (hG z hS)

set_option maxHeartbeats 400000 in
/-- The symbolic coupled state is discretely measurable in all randomness. -/
lemma sRun_DM {N T : ℕ} (I : ProblemInstance N) (π π' : Rule N)
    (hπ : ∀ (t : ℕ) (h : History N) (A : Finset (Finset (Fin N))),
      MeasurableSet {p : ℝ × ℝ | π.act p.1 t h p.2 = A})
    (hπ' : ∀ (t : ℕ) (h : History N) (A : Finset (Finset (Fin N))),
      MeasurableSet {p : ℝ × ℝ | π'.act p.1 t h p.2 = A}) :
    ∀ t, DM (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
      sRun I (π.act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t) := by
  intro t
  induction t with
  | zero =>
    show DM (fun _ : (ℝ × Tape N T) × (ℝ × Tape N T) => (([], [], fun _ => []) : SState N))
    exact DM.const _
  | succ t ih =>
    by_cases ht : t < T
    · have e : (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
          sRun I (π.act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 (t + 1)) = fun ω =>
          sStep I (π.act ω.1.1) (π'.act ω.2.1) t ω.1.2
            (sRun I (π.act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t) (wn ω.1.2 t) (wn ω.2.2 t) := by
        funext ω
        simp only [sRun, if_pos ht]
      rw [e]
      refine DM.bind (D := fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
        sRun I (π.act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t) ih
        (F := fun d ω => sStep I (π.act ω.1.1) (π'.act ω.2.1) t ω.1.2 d (wn ω.1.2 t) (wn ω.2.2 t))
        (fun d => ?_)
      have hwP : Measurable (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => wn ω.1.2 t) :=
        (meas_wn t).comp (measurable_fst.snd)
      have hwO : Measurable (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => wn ω.2.2 t) :=
        (meas_wn t).comp (measurable_snd.snd)
      have hAP : DM (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => π.act ω.1.1 t d.1 (wn ω.1.2 t).1) :=
        (show DM (fun q : ℝ × ℝ => π.act q.1 t d.1 q.2) from fun A => hπ t d.1 A).comp_meas
          (k := fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => (ω.1.1, (wn ω.1.2 t).1))
          (measurable_fst.fst.prodMk hwP.fst)
      have hAO : DM (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => π'.act ω.2.1 t d.2.1 (wn ω.2.2 t).1) :=
        (show DM (fun q : ℝ × ℝ => π'.act q.1 t d.2.1 q.2) from fun A => hπ' t d.2.1 A).comp_meas
          (k := fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => (ω.2.1, (wn ω.2.2 t).1))
          (measurable_snd.fst.prodMk hwO.fst)
      have hP : DM (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
          sStP I (π.act ω.1.1) t d (wn ω.1.2 t)) :=
        step_DM I t d.1 _ hAP _ hwP.snd.fst _ hwP.snd.snd
      have hS : DM (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
          sS I (π'.act ω.2.1) t d (wn ω.2.2 t)) := by
        unfold sS
        exact DM.bind (D := fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
          π'.act ω.2.1 t d.2.1 (wn ω.2.2 t).1) hAO
          (F := fun A ω => sampleFin ((I.period t).act (takenAction (I.period t) (freeArms d.2.1 t) A)
            (counts d.2.1)) (wn ω.2.2 t).2.1)
          (fun A => (sampleFin_DM _).comp_meas hwO.snd.fst)
      have hPS : DM (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
          ((sStP I (π.act ω.1.1) t d (wn ω.1.2 t)).2.1, sS I (π'.act ω.2.1) t d (wn ω.2.2 t))) :=
        DM.pair (hP.comp_fun (fun s : Step N => s.2.1)) hS
      have hseed : Measurable (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
          sSeed I (π.act ω.1.1) (π'.act ω.2.1) t ω.1.2 d (wn ω.1.2 t) (wn ω.2.2 t)) := by
        apply measurable_pi_lambda
        intro i
        have hc : MeasurableSet {ω : (ℝ × Tape N T) × (ℝ × Tape N T) |
            i ∈ activatedArms (sS I (π'.act ω.2.1) t d (wn ω.2.2 t))} :=
          hS.preimage {S | i ∈ activatedArms S}
        have hH : DM (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
            (sQ1 I (π.act ω.1.1) t d (wn ω.1.2 t) i).head?) := by
          refine DM.of_factor hP ?_
          intro ω ω' h
          show (sQ1 I (π.act ω.1.1) t d (wn ω.1.2 t) i).head? =
            (sQ1 I (π.act ω'.1.1) t d (wn ω'.1.2 t) i).head?
          unfold sQ1
          rw [h]
        have hb : Measurable (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
            ((sQ1 I (π.act ω.1.1) t d (wn ω.1.2 t) i).head?).elim ((wn ω.2.2 t).2.2 i)
              (fun τ => (wn ω.1.2 τ).2.2 i)) := by
          refine meas_bind hH (G := fun z ω => z.elim ((wn ω.2.2 t).2.2 i)
            (fun τ => (wn ω.1.2 τ).2.2 i)) (fun z => ?_)
          cases z with
          | none =>
            have hc0 : Measurable (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => (wn ω.2.2 t).2.2 i) :=
              (measurable_pi_apply i).comp hwO.snd.snd
            exact hc0
          | some τ =>
            have hτ : Measurable (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => wn ω.1.2 τ) :=
              (meas_wn τ).comp measurable_fst.snd
            have hc1 : Measurable (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => (wn ω.1.2 τ).2.2 i) :=
              (measurable_pi_apply i).comp hτ.snd.snd
            exact hc1
        exact Measurable.ite hc hb measurable_const
      have hO2 : DM (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
          stepOf I t d.2.1 (π'.act ω.2.1 t d.2.1 (wn ω.2.2 t).1) (wn ω.2.2 t).2.1
            (sSeed I (π.act ω.1.1) (π'.act ω.2.1) t ω.1.2 d (wn ω.1.2 t) (wn ω.2.2 t))) :=
        step_DM I t d.2.1 _ hAO _ hwO.snd.fst _ hseed
      have hQ2 : DM (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
          fun i => if i ∈ activatedArms (sS I (π'.act ω.2.1) t d (wn ω.2.2 t)) then
            (sQ1 I (π.act ω.1.1) t d (wn ω.1.2 t) i).tail
            else sQ1 I (π.act ω.1.1) t d (wn ω.1.2 t) i) := by
        refine DM.of_factor hPS ?_
        intro ω ω' hω
        simp only [Prod.mk.injEq] at hω
        show (fun i => if i ∈ activatedArms (sS I (π'.act ω.2.1) t d (wn ω.2.2 t)) then
            (sQ1 I (π.act ω.1.1) t d (wn ω.1.2 t) i).tail
            else sQ1 I (π.act ω.1.1) t d (wn ω.1.2 t) i) =
          (fun i => if i ∈ activatedArms (sS I (π'.act ω'.2.1) t d (wn ω'.2.2 t)) then
            (sQ1 I (π.act ω'.1.1) t d (wn ω'.1.2 t) i).tail
            else sQ1 I (π.act ω'.1.1) t d (wn ω'.1.2 t) i)
        unfold sQ1
        rw [hω.1, hω.2]
      show DM (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
        sStep I (π.act ω.1.1) (π'.act ω.2.1) t ω.1.2 d (wn ω.1.2 t) (wn ω.2.2 t))
      have e2 : (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
          sStep I (π.act ω.1.1) (π'.act ω.2.1) t ω.1.2 d (wn ω.1.2 t) (wn ω.2.2 t)) =
          fun ω => (d.1 ++ [sStP I (π.act ω.1.1) t d (wn ω.1.2 t)],
            d.2.1 ++ [stepOf I t d.2.1 (π'.act ω.2.1 t d.2.1 (wn ω.2.2 t).1) (wn ω.2.2 t).2.1
              (sSeed I (π.act ω.1.1) (π'.act ω.2.1) t ω.1.2 d (wn ω.1.2 t) (wn ω.2.2 t))],
            fun i => if i ∈ activatedArms (sS I (π'.act ω.2.1) t d (wn ω.2.2 t)) then
              (sQ1 I (π.act ω.1.1) t d (wn ω.1.2 t) i).tail
              else sQ1 I (π.act ω.1.1) t d (wn ω.1.2 t) i) := rfl
      rw [e2]
      exact DM.pair (hP.comp_fun (fun s => d.1 ++ [s]))
        (DM.pair (hO2.comp_fun (fun s => d.2.1 ++ [s])) hQ2)
    · have e : (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
          sRun I (π.act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 (t + 1)) = fun ω =>
          sRun I (π.act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t := by
        funext ω
        simp only [sRun, if_neg ht]
      rw [e]
      exact ih

/-- The coupled state up to time `t` only depends on the second tape before time `t`. -/
lemma cr_congr {N T : ℕ} (I : ProblemInstance N)
    (actP actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (w w'₁ w'₂ : Tape N T) :
    ∀ t, (∀ s < t, wn w'₁ s = wn w'₂ s) →
      coupledRun I actP actO w w'₁ t = coupledRun I actP actO w w'₂ t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    by_cases ht : t < T
    · rw [cr_succ I actP actO w w'₁ ht, cr_succ I actP actO w w'₂ ht]
      have e := ih (fun s hs => h s (by omega))
      have e2 := h t (by omega)
      unfold stOf seedOf Q1f SOf stPf
      rw [e, e2]
    · rw [cr_ge I actP actO w w'₁ ht, cr_ge I actP actO w w'₂ ht]
      exact ih (fun s hs => h s (by omega))

lemma run_congr {N T : ℕ} (I : ProblemInstance N)
    (act : ℕ → History N → ℝ → Finset (Finset (Fin N))) (w₁ w₂ : Tape N T) :
    ∀ t, (∀ s < t, wn w₁ s = wn w₂ s) → run I act w₁ t = run I act w₂ t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    by_cases ht : t < T
    · have e := ih (fun s hs => h s (by omega))
      have e2 := h t (by omega)
      have h1 : wn w₁ t = w₁ ⟨t, ht⟩ := dif_pos ht
      have h2 : wn w₂ t = w₂ ⟨t, ht⟩ := dif_pos ht
      rw [h1, h2] at e2
      simp only [run, dif_pos ht]
      rw [e, e2]
    · simp only [run, dif_neg ht]
      exact ih (fun s hs => h s (by omega))

lemma wn_update {N T : ℕ} (w : Tape N T) (τ : Fin T) (b : Noise N) (s : ℕ) :
    wn (Function.update w τ b) s = if s = τ.val then b else wn w s := by
  unfold wn
  split_ifs with h1 h2 h2
  · subst h2
    simp
  · rw [Function.update_of_ne]
    intro h
    apply h2
    rw [← h]
  · exact absurd (h2 ▸ τ.isLt) h1
  · rfl

/-! ### Resampling one coordinate of a tape preserves the law -/

lemma mp_update {N T : ℕ} (τ : Fin T) :
    MeasurePreserving (fun p : Tape N T × Noise N => Function.update p.1 τ p.2)
      ((tapeLaw N T).prod (noiseLaw N)) (tapeLaw N T) := by
  refine ⟨measurable_update' (a := τ), ?_⟩
  symm
  unfold tapeLaw
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply (measurable_update' (a := τ)) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : Tape N T × Noise N => Function.update p.1 τ p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s τ Set.univ)) ×ˢ (s τ) := by
    ext ⟨w, a⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = τ
        · subst hi
          simp
        · rw [Function.update_of_ne hi]
          have := h i
          rwa [Function.update_of_ne hi] at this
      · have := h τ
        rwa [Function.update_self] at this
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = τ
      · subst hi
        rwa [Function.update_self]
      · rw [Function.update_of_ne hi]
        have := h1 i
        rwa [Function.update_of_ne hi] at this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun i => noiseLaw N (s i)) (Finset.mem_univ τ),
    ← Finset.mul_prod_erase Finset.univ (fun i => noiseLaw N (Function.update s τ Set.univ i))
      (Finset.mem_univ τ)]
  have hrest : ∏ i ∈ Finset.univ.erase τ, noiseLaw N (Function.update s τ Set.univ i) =
      ∏ i ∈ Finset.univ.erase τ, noiseLaw N (s i) :=
    Finset.prod_congr rfl (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
  simp only [Function.update_self, measure_univ, one_mul]
  rw [hrest]
  ring

lemma mp_assoc {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ρ : Measure γ) [SFinite μ] [SFinite ν] [SFinite ρ] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α × β) × γ ≃ᵐ α × β × γ)
      ((μ.prod ν).prod ρ) (μ.prod (ν.prod ρ)) :=
  ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩

lemma mp_update1 {N T : ℕ} (μs : Measure ℝ) [IsProbabilityMeasure μs] (τ : Fin T) :
    MeasurePreserving (fun q : (ℝ × Tape N T) × Noise N => (q.1.1, Function.update q.1.2 τ q.2))
      ((μs.prod (tapeLaw N T)).prod (noiseLaw N)) (μs.prod (tapeLaw N T)) := by
  have h1 := mp_assoc μs (tapeLaw N T) (noiseLaw N)
  have h2 := (MeasurePreserving.id μs).prod (mp_update (N := N) τ)
  exact h2.comp h1

lemma mp_update2 {N T : ℕ} (μ1 : Measure (ℝ × Tape N T)) [IsProbabilityMeasure μ1]
    (μs : Measure ℝ) [IsProbabilityMeasure μs] (τ : Fin T) :
    MeasurePreserving (fun q : ((ℝ × Tape N T) × (ℝ × Tape N T)) × Noise N =>
        (q.1.1, (q.1.2.1, Function.update q.1.2.2 τ q.2)))
      ((μ1.prod (μs.prod (tapeLaw N T))).prod (noiseLaw N)) (μ1.prod (μs.prod (tapeLaw N T))) := by
  have h1 := mp_assoc μ1 (μs.prod (tapeLaw N T)) (noiseLaw N)
  have h2 := (MeasurePreserving.id μ1).prod (mp_update1 (N := N) μs τ)
  exact h2.comp h1

lemma integral_resample {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    {ν : Measure Y} [IsFiniteMeasure μ] [IsProbabilityMeasure ν] {M : X × Y → X}
    (hM : MeasurePreserving M (μ.prod ν) μ) (F : X → ℝ) (hF : Measurable F) (C : ℝ)
    (hC : ∀ x, |F x| ≤ C) :
    ∫ x, F x ∂μ = ∫ x, ∫ y, F (M (x, y)) ∂ν ∂μ := by
  have hFi : Integrable (fun p => F (M p)) (μ.prod ν) :=
    Integrable.of_bound ((hF.comp hM.measurable).aestronglyMeasurable) C
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC _)
  rw [← integral_prod _ hFi]
  conv_lhs => rw [← hM.map_eq]
  rw [integral_map hM.measurable.aemeasurable hF.aestronglyMeasurable]

/-! ### Bounds -/

lemma counts_le_length {N : ℕ} (h : History N) (i : Fin N) : counts h i ≤ h.length := by
  unfold counts
  exact List.length_filter_le _ _

lemma Yfun_bound {N T : ℕ} (I : ProblemInstance N) (O : Oracle N) (r : ℝ) (t : ℕ) (hA : History N)
    (hl : hA.length ≤ T) (a : Noise N) :
    |Yfun I O r t hA a| ≤ ∑ B : Finset (Fin N),
      ∑ n ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (T + 1)), |(I.period t).reward B n| := by
  unfold Yfun
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hmem : counts hA ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (T + 1)) :=
    Fintype.mem_piFinset.2 fun i =>
      Finset.mem_range.2 (Nat.lt_succ_of_le ((counts_le_length hA i).trans hl))
  calc _ ≤ ∑ B : Finset (Fin N), |(I.period t).reward B (counts hA)| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)
    _ ≤ _ := Finset.sum_le_sum fun B _ =>
        Finset.single_le_sum (f := fun n => |(I.period t).reward B n|) (fun _ _ => abs_nonneg _) hmem

lemma Xfun_nonneg {N : ℕ} (I : ProblemInstance N) (r : ℝ) (hr : 0 < r) (t : ℕ)
    (actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (hA hO : History N) (b : Noise N) :
    0 ≤ Xfun I r t actO hA hO b := by
  unfold Xfun
  apply Finset.sum_nonneg
  intro B _
  unfold cA
  split_ifs <;> linarith

lemma Xfun_bound {N : ℕ} (I : ProblemInstance N) (r : ℝ) (hr : 0 < r) (t : ℕ)
    (actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (hA hO : History N) (b : Noise N) :
    |Xfun I r t actO hA hO b| ≤ ∑ _B : Finset (Fin N), r := by
  rw [abs_of_nonneg (Xfun_nonneg I r hr t actO hA hO b)]
  unfold Xfun
  calc _ ≤ ∑ _B ∈ sampleFin ((I.period t).act (Aopt I t actO hO b.1) (counts hO)) b.2.1, r := by
        apply Finset.sum_le_sum
        intro B _
        unfold cA
        split_ifs <;> linarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => hr.le)

/-! ### Per-period identities along the runs -/

lemma Xt_eq {N T : ℕ} (I : ProblemInstance N) (r : ℝ)
    (actP actO : ℕ → History N → ℝ → Finset (Finset (Fin N))) (w w' : Tape N T) {t : ℕ}
    (ht : t < T) :
    (∑ B ∈ activatedAt (coupledRun I actP actO w w' T).2.1 t,
      if B ∈ goodSet (coupledRun I actP actO w w' T).1 (coupledRun I actP actO w w' T).2.1 t ∧
        r ≤ (I.period t).reward B (counts ((coupledRun I actP actO w w' T).2.1.take t))
      then r else 0) =
    Xfun I r t actO (coupledRun I actP actO w w' t).1 (coupledRun I actP actO w w' t).2.1
      (wn w' t) := by
  obtain ⟨fa1, fa2, fa3, fa4⟩ := final_at I actP actO w w' ht
  obtain ⟨ft1, ft2⟩ := final_take I actP actO w w' (show t ≤ T by omega)
  rw [fa2, ft2]
  unfold Xfun
  apply Finset.sum_congr rfl
  intro B _
  have hiff : (B ∈ goodSet (coupledRun I actP actO w w' T).1 (coupledRun I actP actO w w' T).2.1 t ∧
      r ≤ (I.period t).reward B (counts (coupledRun I actP actO w w' t).2.1)) ↔
      ((B ∈ Aopt I t actO (coupledRun I actP actO w w' t).2.1 (wn w' t).1 ∧
        goodP t (coupledRun I actP actO w w' t).1 (coupledRun I actP actO w w' t).2.1 B) ∧
        r ≤ (I.period t).reward B (counts (coupledRun I actP actO w w' t).2.1)) := by
    rw [mem_goodSet, fa3, ft1, ft2]
    rfl
  unfold cA
  by_cases hc : (B ∈ Aopt I t actO (coupledRun I actP actO w w' t).2.1 (wn w' t).1 ∧
        goodP t (coupledRun I actP actO w w' t).1 (coupledRun I actP actO w w' t).2.1 B) ∧
        r ≤ (I.period t).reward B (counts (coupledRun I actP actO w w' t).2.1)
  · rw [if_pos (hiff.2 hc), if_pos hc]
  · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc]

lemma Yt_eq {N T : ℕ} (I : ProblemInstance N) (O : Oracle N) (r : ℝ) (s : ℝ) (w : Tape N T) :
    pathSum (run I ((GRD I O r).act s) w T) (fun t B n => (I.period t).reward B n) =
      ∑ t ∈ Finset.range T, Yfun I O r t (run I ((GRD I O r).act s) w t) (wn w t) := by
  have hT := cr_fst I ((GRD I O r).act s) ((GRD I O r).act s) w w T
  rw [← hT, pathSum_eq, (cr_len' I ((GRD I O r).act s) ((GRD I O r).act s) w w (le_refl T)).1]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_range] at ht
  obtain ⟨fa1, _, _, _⟩ := final_at I ((GRD I O r).act s) ((GRD I O r).act s) w w ht
  obtain ⟨ft1, _⟩ := final_take I ((GRD I O r).act s) ((GRD I O r).act s) w w (show t ≤ T by omega)
  rw [fa1, ft1, ← cr_fst I ((GRD I O r).act s) ((GRD I O r).act s) w w t]
  rfl

lemma Yfun_meas {N : ℕ} (I : ProblemInstance N) (O : Oracle N) (r : ℝ) (t : ℕ) (hA : History N) :
    Measurable (fun a : Noise N => Yfun I O r t hA a) := by
  have hD : DM (fun a : Noise N =>
      sampleFin ((I.period t).act (Aalg I O r t hA a.1) (counts hA)) a.2.1) :=
    DM.bind (D := fun a : Noise N => Aalg I O r t hA a.1)
      ((Aalg_DM I O r t hA).comp_meas measurable_fst)
      (F := fun A a => sampleFin ((I.period t).act A (counts hA)) a.2.1)
      (fun A => (sampleFin_DM _).comp_meas measurable_snd.fst)
  exact hD.measurable (fun S => ∑ B ∈ S, (I.period t).reward B (counts hA))

lemma Xfun_meas {N : ℕ} (I : ProblemInstance N) (r : ℝ) (t : ℕ) (π' : Rule N)
    (hπ' : ∀ (t : ℕ) (h : History N) (A : Finset (Finset (Fin N))),
      MeasurableSet {p : ℝ × ℝ | π'.act p.1 t h p.2 = A}) (hA hO : History N) :
    Measurable (fun q : ℝ × Noise N => Xfun I r t (π'.act q.1) hA hO q.2) := by
  have hact0 : DM (fun q : ℝ × Noise N => π'.act q.1 t hO q.2.1) :=
    (show DM (fun p : ℝ × ℝ => π'.act p.1 t hO p.2) from fun A => hπ' t hO A).comp_meas
      (k := fun q : ℝ × Noise N => (q.1, q.2.1)) (measurable_fst.prodMk measurable_snd.fst)
  have hAO : DM (fun q : ℝ × Noise N => Aopt I t (π'.act q.1) hO q.2.1) := by
    unfold Aopt
    exact hact0.comp_fun _
  have hD : DM (fun q : ℝ × Noise N => (Aopt I t (π'.act q.1) hO q.2.1,
      sampleFin ((I.period t).act (Aopt I t (π'.act q.1) hO q.2.1) (counts hO)) q.2.2.1)) :=
    DM.bind (D := fun q : ℝ × Noise N => Aopt I t (π'.act q.1) hO q.2.1) hAO
      (F := fun A q => (A, sampleFin ((I.period t).act A (counts hO)) q.2.2.1))
      (fun A => DM.pair (DM.const _) ((sampleFin_DM _).comp_meas measurable_snd.snd.fst))
  exact hD.measurable (fun z => ∑ B ∈ z.2, cA I r t hA hO z.1 B)

/-! ### The per-period terms as functions of the randomness -/


/-! ### The per-period terms as functions of the randomness -/

section Main

variable {N T : ℕ} (I : ProblemInstance N) (O : Oracle N) (r : ℝ) (π' : Rule N)

noncomputable def XtF (t : ℕ) (ω : (ℝ × Tape N T) × (ℝ × Tape N T)) : ℝ :=
  Xfun I r t (π'.act ω.2.1)
    (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).1
    (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).2.1 (wn ω.2.2 t)

noncomputable def XbF (t : ℕ) (ω : (ℝ × Tape N T) × (ℝ × Tape N T)) : ℝ :=
  ∫ b, Xfun I r t (π'.act ω.2.1)
    (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).1
    (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).2.1 b ∂(noiseLaw N)

noncomputable def YtF (t : ℕ) (p : ℝ × Tape N T) : ℝ :=
  Yfun I O r t (run I ((GRD I O r).act p.1) p.2 t) (wn p.2 t)

noncomputable def GF (t : ℕ) (p : ℝ × Tape N T) : ℝ :=
  ∫ a, Yfun I O r t (run I ((GRD I O r).act p.1) p.2 t) a ∂(noiseLaw N)

noncomputable def KY (t : ℕ) : ℝ := ∑ B : Finset (Fin N),
  ∑ n ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (T + 1)), |(I.period t).reward B n|

lemma grd_adm : ∀ (t : ℕ) (h : History N) (A : Finset (Finset (Fin N))),
    MeasurableSet {p : ℝ × ℝ | (GRD I O r).act p.1 t h p.2 = A} := by
  intro t h A
  exact greedy_DM_const O (fun d B n => d.reward B n) r (I.period t) (counts h) (freeArms h t) A

lemma run_len_le (s : ℝ) (w : Tape N T) (t : ℕ) : (run I ((GRD I O r).act s) w t).length ≤ T := by
  rw [run_length]
  exact min_le_right _ _

lemma XtF_bound (hr : 0 < r) (t : ℕ) (ω : (ℝ × Tape N T) × (ℝ × Tape N T)) :
    |XtF I O r π' t ω| ≤ ∑ _B : Finset (Fin N), r :=
  Xfun_bound I r hr t _ _ _ _

lemma YtF_bound (t : ℕ) (p : ℝ × Tape N T) : |YtF I O r t p| ≤ KY (T := T) I t :=
  Yfun_bound I O r t _ (run_len_le I O r _ _ _) _

lemma GF_bound (t : ℕ) (p : ℝ × Tape N T) : |GF I O r t p| ≤ KY (T := T) I t := by
  have := norm_integral_le_of_norm_le_const (μ := noiseLaw N)
    (f := fun a => Yfun I O r t (run I ((GRD I O r).act p.1) p.2 t) a)
    (Filter.Eventually.of_forall fun a => (show ‖Yfun I O r t (run I ((GRD I O r).act p.1) p.2 t) a‖ ≤
      KY (T := T) I t by
      rw [Real.norm_eq_abs]; exact Yfun_bound I O r t _ (run_len_le I O r _ _ _) a))
  rw [Real.norm_eq_abs] at this
  unfold GF
  simpa using this

lemma run_DM_grd (t : ℕ) : DM (fun p : ℝ × Tape N T => run I ((GRD I O r).act p.1) p.2 t) :=
  run_DM (T := T) I (GRD I O r).act (fun t h A => grd_adm I O r t h A) t

lemma YtF_meas (t : ℕ) : Measurable (fun p : ℝ × Tape N T => YtF I O r t p) := by
  unfold YtF
  have hw1 : Measurable (fun p : ℝ × Tape N T => wn p.2 t) := (meas_wn t).comp measurable_snd
  exact meas_bind (run_DM_grd I O r t) (G := fun h p => Yfun I O r t h (wn p.2 t))
    (fun h => (Yfun_meas I O r t h).comp hw1)

lemma GF_meas (t : ℕ) : Measurable (fun p : ℝ × Tape N T => GF I O r t p) := by
  unfold GF
  exact meas_bind (run_DM_grd I O r t) (G := fun h _ => ∫ a, Yfun I O r t h a ∂(noiseLaw N))
    (fun _ => measurable_const)

lemma hist_DM (hπ' : IsAdmissible π') (t : ℕ) : DM (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
    ((coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).1,
      (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).2.1)) := by
  have hs := sRun_DM (T := T) I (GRD I O r) π' (grd_adm I O r) hπ'.2 t
  have e : (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
      ((coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).1,
        (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).2.1)) = fun ω =>
      (fun d : SState N => (d.1, d.2.1))
        (sRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t) := by
    funext ω
    have := sRun_eq I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t
    rw [this.1, this.2.1]
  rw [e]
  exact hs.comp_fun (fun d : SState N => (d.1, d.2.1))

lemma XtF_meas (hπ' : IsAdmissible π') (t : ℕ) :
    Measurable (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => XtF I O r π' t ω) := by
  have hw2 : Measurable (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => wn ω.2.2 t) :=
    (meas_wn t).comp measurable_snd.snd
  have hg : Measurable (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) => (ω.2.1, wn ω.2.2 t)) :=
    measurable_snd.fst.prodMk hw2
  have h := meas_bind (D := fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
      ((coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).1,
        (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).2.1))
    (hist_DM I O r π' hπ' t)
    (G := fun (d : History N × History N) (ω : (ℝ × Tape N T) × (ℝ × Tape N T)) =>
      Xfun I r t (π'.act ω.2.1) d.1 d.2 (wn ω.2.2 t))
    (fun d => by
      have hX := (Xfun_meas I r t π' hπ'.2 d.1 d.2).comp hg
      exact hX)
  have e : (fun ω : (ℝ × Tape N T) × (ℝ × Tape N T) =>
      (fun (d : History N × History N) (ω : (ℝ × Tape N T) × (ℝ × Tape N T)) =>
        Xfun I r t (π'.act ω.2.1) d.1 d.2 (wn ω.2.2 t))
      ((coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).1,
        (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).2.1) ω) =
      fun ω => XtF I O r π' t ω := by
    funext ω
    dsimp only
    rfl
  rw [← e]
  exact h

lemma XtF_update (t : ℕ) (ht : t < T) (ω : (ℝ × Tape N T) × (ℝ × Tape N T)) (b : Noise N) :
    XtF I O r π' t (ω.1, (ω.2.1, Function.update ω.2.2 ⟨t, ht⟩ b)) =
      Xfun I r t (π'.act ω.2.1) (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).1
        (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).2.1 b := by
  have hc := cr_congr I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2
    (Function.update ω.2.2 ⟨t, ht⟩ b) ω.2.2 t
    (fun s hs => by rw [wn_update, if_neg (show ¬ s = t by omega)])
  have hw : wn (Function.update ω.2.2 ⟨t, ht⟩ b) t = b := by
    rw [wn_update, if_pos rfl]
  show Xfun I r t (π'.act ω.2.1)
    (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 (Function.update ω.2.2 ⟨t, ht⟩ b) t).1
    (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 (Function.update ω.2.2 ⟨t, ht⟩ b) t).2.1
    (wn (Function.update ω.2.2 ⟨t, ht⟩ b) t) = _
  rw [hc, hw]

lemma YtF_update (t : ℕ) (ht : t < T) (p : ℝ × Tape N T) (a : Noise N) :
    YtF I O r t (p.1, Function.update p.2 ⟨t, ht⟩ a) =
      Yfun I O r t (run I ((GRD I O r).act p.1) p.2 t) a := by
  have hc := run_congr I ((GRD I O r).act p.1) (Function.update p.2 ⟨t, ht⟩ a) p.2 t
    (fun s hs => by rw [wn_update, if_neg (show ¬ s = t by omega)])
  have hw : wn (Function.update p.2 ⟨t, ht⟩ a) t = a := by
    rw [wn_update, if_pos rfl]
  show Yfun I O r t (run I ((GRD I O r).act p.1) (Function.update p.2 ⟨t, ht⟩ a) t)
    (wn (Function.update p.2 ⟨t, ht⟩ a) t) = _
  rw [hc, hw]

lemma X_resample (hr : 0 < r) (hπ' : IsAdmissible π') [IsProbabilityMeasure π'.seedLaw]
    [IsProbabilityMeasure (GRD I O r).seedLaw] (t : ℕ) (ht : t < T) :
    ∫ ω, XtF I O r π' t ω ∂(coupledLaw T (GRD I O r) π') =
      ∫ ω, XbF I O r π' t ω ∂(coupledLaw T (GRD I O r) π') := by
  have hMX : MeasurePreserving (fun q : ((ℝ × Tape N T) × (ℝ × Tape N T)) × Noise N =>
        (q.1.1, (q.1.2.1, Function.update q.1.2.2 ⟨t, ht⟩ q.2)))
      ((coupledLaw T (GRD I O r) π').prod (noiseLaw N)) (coupledLaw T (GRD I O r) π') :=
    mp_update2 (N := N) ((GRD I O r).seedLaw.prod (tapeLaw N T)) π'.seedLaw ⟨t, ht⟩
  rw [integral_resample hMX (fun ω => XtF I O r π' t ω) (XtF_meas I O r π' hπ' t) _
    (XtF_bound I O r π' hr t)]
  apply integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show ∫ b, XtF I O r π' t (ω.1, (ω.2.1, Function.update ω.2.2 ⟨t, ht⟩ b)) ∂(noiseLaw N) = _
  unfold XbF
  congr 1
  funext b
  exact XtF_update I O r π' t ht ω b

lemma Y_resample [IsProbabilityMeasure (GRD I O r).seedLaw] (t : ℕ) (ht : t < T) :
    ∫ p, YtF I O r t p ∂((GRD I O r).seedLaw.prod (tapeLaw N T)) =
      ∫ p, GF I O r t p ∂((GRD I O r).seedLaw.prod (tapeLaw N T)) := by
  have hMY := mp_update1 (N := N) (GRD I O r).seedLaw ⟨t, ht⟩
  rw [integral_resample hMY (fun p => YtF I O r t p) (YtF_meas I O r t) _ (YtF_bound I O r t)]
  apply integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show ∫ a, YtF I O r t (p.1, Function.update p.2 ⟨t, ht⟩ a) ∂(noiseLaw N) = _
  unfold GF
  congr 1
  funext a
  exact YtF_update I O r t ht p a

lemma per_t_ineq {L : ℕ} (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (h2 : Substitutability I T) (h51 : DecayingReward I T) (h52 : DecayingProbability I T)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hO : IsApproxOracle I T α β O) (hr : 0 < r)
    (hπ' : IsAdmissible π') [IsProbabilityMeasure π'.seedLaw]
    [IsProbabilityMeasure (GRD I O r).seedLaw] (t : ℕ) (ht : t < T) :
    α * β * ∫ ω, XbF I O r π' t ω ∂(coupledLaw T (GRD I O r) π') ≤
      ∫ p, GF I O r t p ∂((GRD I O r).seedLaw.prod (tapeLaw N T)) := by
  rw [← integral_const_mul, ← integral_fst (T := T) (GRD I O r) π' (fun p => GF I O r t p)
    (GF_meas I O r t)]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun ω => mul_nonneg (by positivity)
      (integral_nonneg fun b => Xfun_nonneg I r hr t _ _ _ b)
  · exact Integrable.of_bound ((GF_meas I O r t).comp measurable_fst).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact GF_bound I O r t ω.1)
  · refine Filter.Eventually.of_forall fun ω => ?_
    have hrun : (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).1 =
        run I ((GRD I O r).act ω.1.1) ω.1.2 t :=
      cr_fst I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t
    have hloc := local_ineq I O r t h1 hact h2 h51 h52 α β hα hβ hO hr ht (π'.act ω.2.1)
      (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).1
      (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).2.1
      ((show DM (fun p : ℝ × ℝ => π'.act p.1 t
          (coupledRun I ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 t).2.1 p.2) from
        fun A => hπ'.2 t _ A).comp_meas (k := fun v : ℝ => (ω.2.1, v))
        (measurable_const.prodMk measurable_id))
    show α * β * XbF I O r π' t ω ≤ GF I O r t ω.1
    unfold XbF GF
    rw [← hrun]
    exact hloc

end Main

theorem eq12_main {N T L : ℕ} (I : ProblemInstance N)
    (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (h2 : Substitutability I T) (h51 : DecayingReward I T) (h52 : DecayingProbability I T)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (O : Oracle N) (hO : IsApproxOracle I T α β O)
    (r : ℝ) (hr : 0 < r) (π' : Rule N) (hπ' : IsAdmissible π') :
    α * β * ∫ ω, (∑ t ∈ Finset.range T,
        ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).2.1 t,
          if B ∈ goodSet (coupledFinal I T (GRD I O r) π' ω).1
                (coupledFinal I T (GRD I O r) π' ω).2.1 t ∧
              r ≤ (I.period t).reward B (counts ((coupledFinal I T (GRD I O r) π' ω).2.1.take t))
          then r else 0) ∂(coupledLaw T (GRD I O r) π') ≤
      Rew I T (GRD I O r) := by
  haveI hs1 : IsProbabilityMeasure (GRD I O r).seedLaw := by
    show IsProbabilityMeasure (Measure.dirac (0 : ℝ))
    infer_instance
  haveI hs2 : IsProbabilityMeasure π'.seedLaw := hπ'.1
  have hf : ∀ ω : (ℝ × Tape N T) × (ℝ × Tape N T), (∑ t ∈ Finset.range T,
        ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).2.1 t,
          if B ∈ goodSet (coupledFinal I T (GRD I O r) π' ω).1
                (coupledFinal I T (GRD I O r) π' ω).2.1 t ∧
              r ≤ (I.period t).reward B (counts ((coupledFinal I T (GRD I O r) π' ω).2.1.take t))
          then r else 0) = ∑ t ∈ Finset.range T, XtF I O r π' t ω := by
    intro ω
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    exact Xt_eq I r ((GRD I O r).act ω.1.1) (π'.act ω.2.1) ω.1.2 ω.2.2 ht
  have hXi : ∀ t, Integrable (fun ω => XtF I O r π' t ω) (coupledLaw T (GRD I O r) π') :=
    fun t => Integrable.of_bound (XtF_meas I O r π' hπ' t).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact XtF_bound I O r π' hr t ω)
  have hYi : ∀ t, Integrable (fun p => YtF I O r t p) ((GRD I O r).seedLaw.prod (tapeLaw N T)) :=
    fun t => Integrable.of_bound (YtF_meas I O r t).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact YtF_bound I O r t p)
  have hlhs : ∫ ω, (∑ t ∈ Finset.range T,
        ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).2.1 t,
          if B ∈ goodSet (coupledFinal I T (GRD I O r) π' ω).1
                (coupledFinal I T (GRD I O r) π' ω).2.1 t ∧
              r ≤ (I.period t).reward B (counts ((coupledFinal I T (GRD I O r) π' ω).2.1.take t))
          then r else 0) ∂(coupledLaw T (GRD I O r) π') =
      ∑ t ∈ Finset.range T, ∫ ω, XtF I O r π' t ω ∂(coupledLaw T (GRD I O r) π') := by
    rw [← integral_finset_sum _ (fun t _ => hXi t)]
    exact integral_congr_ae (Filter.Eventually.of_forall hf)
  have hrhs : Rew I T (GRD I O r) =
      ∑ t ∈ Finset.range T, ∫ p, YtF I O r t p ∂((GRD I O r).seedLaw.prod (tapeLaw N T)) := by
    rw [← integral_finset_sum _ (fun t _ => hYi t)]
    show ∫ p, pathSum (run I ((GRD I O r).act p.1) p.2 T) (fun t B n => (I.period t).reward B n)
      ∂((GRD I O r).seedLaw.prod (tapeLaw N T)) = _
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => Yt_eq I O r p.1 p.2)
  rw [hlhs, hrhs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.mem_range] at ht
  rw [X_resample I O r π' hr hπ' t ht, Y_resample I O r t ht]
  exact per_t_ineq I O r π' h1 hact h2 h51 h52 α β hα hβ hO hr hπ' t ht

end Aux_GRN

open GreedyReusableNet in
theorem solution {N T L : ℕ} (I : ProblemInstance N)
    (h1 : IndepSystemAssumption I T L) (hact : ActivatesWithinAction I T)
    (h2 : Substitutability I T) (h51 : DecayingReward I T) (h52 : DecayingProbability I T)
    (α β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (O : Oracle N) (hO : IsApproxOracle I T α β O)
    (r : ℝ) (hr : 0 < r) (π' : Rule N) (hπ' : IsAdmissible π') :
    α * β * ∫ ω, (∑ t ∈ Finset.range T,
        ∑ B ∈ activatedAt (coupledFinal I T (GRD I O r) π' ω).2.1 t,
          if B ∈ goodSet (coupledFinal I T (GRD I O r) π' ω).1
                (coupledFinal I T (GRD I O r) π' ω).2.1 t ∧
              r ≤ (I.period t).reward B (counts ((coupledFinal I T (GRD I O r) π' ω).2.1.take t))
          then r else 0) ∂(coupledLaw T (GRD I O r) π') ≤
      Rew I T (GRD I O r) :=
  Aux_GRN.eq12_main I h1 hact h2 h51 h52 α β hα hβ O hO r hr π' hπ'
