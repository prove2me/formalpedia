-- Prove2me | solution 1 for MatroidProphetKW.Single.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T04:22:37.385994+00:00
-- url     : https://prove2.me/submissions/84632533-2b2e-41b0-b04c-6adc2d66dfd1

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Online
import Definitions.Def_MatroidProphetKW_Single_Setting
import Definitions.Def_MatroidProphetKW_Single_Algorithm

/-
Apache-2.0. Independent proof of the complete native adaptive matroid prophet inequality.
Credit: accepted supports by fizzyinc3 (exchange bijection) and shivm (identity (9)=(10)) form part of the mission history; no accepted proof source was copied.
Actual native residual values, weighted rank profiles, threshold budgets, adaptive prefix coupling and product resampling are established below.
-/

-- BEGIN MPProof.RunBasics
section

namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

variable {α : Type*} [DecidableEq α]

lemma fold_step_history (M : Matroid α)
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (w : α → ℝ) (l : List α) (st : List α × Finset α) :
    (l.foldl (step M Thr w) st).1 = st.1 ++ l := by
  induction l generalizing st with
  | nil => simp
  | cons x l ih =>
      rw [List.foldl_cons, ih]
      simp [step, List.append_assoc]

open Classical in
lemma run_append_singleton (M : Matroid α)
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (w : α → ℝ) (l : List α) (x : α) :
    run M Thr (l ++ [x]) w =
      if M.Indep (↑(insert x (run M Thr l w)) : Set α) ∧
          Thr (run M Thr l w) l w x ≤ w x
      then insert x (run M Thr l w) else run M Thr l w := by
  classical
  have hh := fold_step_history M Thr w l ([], ∅)
  simp only [List.nil_append] at hh
  simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil, step]
  rw [hh]
  rfl

@[simp] lemma run_nil (M : Matroid α)
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ) (w : α → ℝ) :
    run M Thr [] w = ∅ := rfl

lemma fold_step_indep (M : Matroid α)
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (w : α → ℝ) (l : List α) (st : List α × Finset α)
    (hst : M.Indep (st.2 : Set α)) :
    M.Indep ((l.foldl (step M Thr w) st).2 : Set α) := by
  classical
  induction l generalizing st with
  | nil => exact hst
  | cons x l ih =>
      apply ih
      simp only [step]
      split_ifs with h
      · exact h.1
      · exact hst

lemma run_indep (M : Matroid α)
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (w : α → ℝ) (l : List α) : M.Indep (run M Thr l w : Set α) := by
  apply fold_step_indep
  simp

lemma run_subset_append (M : Matroid α)
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (w : α → ℝ) (l : List α) (x : α) :
    run M Thr l w ⊆ run M Thr (l ++ [x]) w := by
  rw [run_append_singleton]
  split_ifs
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.RunBasics

-- BEGIN MPProof.AdversaryOrder
section

namespace MatroidProphetKW.Single.MPFresh

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
lemma advPrefix_length (adv : List α → (α → ℝ) → α) (w : α → ℝ) (k : ℕ) :
    (advPrefix adv w k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [advPrefix, ih]

lemma exists_notMem_of_length_lt (l : List α) (h : l.length < Fintype.card α) :
    ∃ x, x ∉ l := by
  classical
  by_contra hn
  push Not at hn
  have he : l.toFinset = Finset.univ := by
    ext x
    simp [hn x]
  have hc := l.toFinset_card_le
  rw [he, Finset.card_univ] at hc
  omega

lemma advPrefix_nodup (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (w : α → ℝ) (k : ℕ) (hk : k ≤ Fintype.card α) :
    (advPrefix adv w k).Nodup := by
  induction k with
  | zero => simp [advPrefix]
  | succ k ih =>
      have hn := hadv.1 (advPrefix adv w k) w
        (exists_notMem_of_length_lt _ (by rw [advPrefix_length]; omega))
      apply List.nodup_append.mpr
      refine ⟨ih (by omega), by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      intro he
      exact hn (he ▸ ha)

lemma advOrder_isOrder (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (w : α → ℝ) : IsOrder (advOrder adv w) := by
  classical
  have hn := advPrefix_nodup adv hadv w (Fintype.card α) le_rfl
  refine ⟨hn, ?_⟩
  have hc : (advOrder adv w).toFinset.card = Fintype.card α := by
    change (advPrefix adv w (Fintype.card α)).toFinset.card = _
    rw [List.toFinset_card_of_nodup hn]
    exact advPrefix_length adv w _
  have he : (advOrder adv w).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ hc
  intro x
  have : x ∈ (advOrder adv w).toFinset := by rw [he]; exact Finset.mem_univ x
  simpa using this

omit [Fintype α] [DecidableEq α] in
lemma advPrefix_coupling (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (w w' : α → ℝ) (x : α) (hw : ∀ y, y ≠ x → w y = w' y)
    (k : ℕ) (hx : x ∉ advPrefix adv w k) :
    advPrefix adv w k = advPrefix adv w' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hxk : x ∉ advPrefix adv w k := by
        intro hm
        exact hx (List.mem_append_left _ hm)
      have he := ih hxk
      have ha : adv (advPrefix adv w k) w = adv (advPrefix adv w k) w' := by
        apply hadv.2.1
        intro y hy
        apply hw
        intro h
        subst y
        exact hxk hy
      simp only [advPrefix]
      rw [← he, ha]

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.AdversaryOrder

-- BEGIN MPProof.FirstArrival
section

namespace MatroidProphetKW.Single.MPFresh

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
lemma notMem_take_idxOf (x : α) (l : List α) : x ∉ l.take (l.idxOf x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : a = x
      · subst a; simp
      · simpa [List.idxOf_cons, h, Ne.symm h] using ih

omit [Fintype α] [DecidableEq α] in
lemma advPrefix_isPrefix (adv : List α → (α → ℝ) → α) (w : α → ℝ)
    (j k : ℕ) (hjk : j ≤ k) : (advPrefix adv w j).IsPrefix (advPrefix adv w k) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction q with
  | zero => exact List.prefix_refl _
  | succ q ih =>
      exact ih.trans ⟨[adv (advPrefix adv w (j + q)) w], rfl⟩

omit [Fintype α] [DecidableEq α] in
lemma advPrefix_eq_take (adv : List α → (α → ℝ) → α) (w : α → ℝ)
    (j k : ℕ) (hjk : j ≤ k) :
    advPrefix adv w j = (advPrefix adv w k).take j := by
  have h := List.prefix_iff_eq_take.mp (advPrefix_isPrefix adv w j k hjk)
  simpa only [advPrefix_length] using h

lemma next_at_idxOf (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (w : α → ℝ) (x : α) :
    adv (advPrefix adv w ((advOrder adv w).idxOf x)) w = x := by
  let j := (advOrder adv w).idxOf x
  have hj : j < Fintype.card α := by
    have h := List.idxOf_lt_length_of_mem ((advOrder_isOrder adv hadv w).2 x)
    simpa only [j, advOrder, advPrefix_length] using h
  have hpre := advPrefix_eq_take adv w j (Fintype.card α) (by omega)
  have hsucc := advPrefix_eq_take adv w (j + 1) (Fintype.card α) (by omega)
  change advPrefix adv w j ++ [adv (advPrefix adv w j) w] =
    (advOrder adv w).take (j + 1) at hsucc
  rw [List.take_succ_eq_append_getElem (by simpa [advOrder, advPrefix_length] using hj)] at hsucc
  rw [hpre] at hsucc
  have he := List.append_cancel_left hsucc
  rw [← hpre] at he
  have hjl : j < (advOrder adv w).length := by simpa only [advOrder, advPrefix_length] using hj
  have hget : (advOrder adv w)[j]'hjl = x := List.getElem_idxOf hjl
  exact (List.cons.inj he).1.trans hget

lemma first_arrival_coupling (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (w w' : α → ℝ) (x : α) (hw : ∀ y, y ≠ x → w y = w' y) :
    (advOrder adv w).take ((advOrder adv w).idxOf x) =
      (advOrder adv w').take ((advOrder adv w').idxOf x) := by
  let j := (advOrder adv w).idxOf x
  have hj : j < Fintype.card α := by
    have h := List.idxOf_lt_length_of_mem ((advOrder_isOrder adv hadv w).2 x)
    simpa only [j, advOrder, advPrefix_length] using h
  have ht := advPrefix_eq_take adv w j (Fintype.card α) (by omega)
  have hx : x ∉ advPrefix adv w j := by rw [ht]; exact notMem_take_idxOf x _
  have he := advPrefix_coupling adv hadv w w' x hw j hx
  have ha : adv (advPrefix adv w j) w = adv (advPrefix adv w j) w' := by
    apply hadv.2.1
    intro y hy
    apply hw
    intro h
    subst y
    exact hx hy
  have hnext : adv (advPrefix adv w' j) w' = x := by
    rw [← he, ← ha]
    exact next_at_idxOf adv hadv w x
  obtain ⟨tail, htail⟩ := advPrefix_isPrefix adv w' (j + 1) (Fintype.card α) (by omega)
  change (advPrefix adv w' j ++ [adv (advPrefix adv w' j) w']) ++ tail =
    advOrder adv w' at htail
  rw [hnext, List.append_assoc] at htail
  have hx' : x ∉ advPrefix adv w' j := he ▸ hx
  change advPrefix adv w j = (advOrder adv w).take j at ht
  change (advOrder adv w).take j = _
  rw [← ht, ← htail, List.idxOf_append, if_neg hx']
  simp only [List.singleton_append, List.idxOf_cons_self, zero_add, List.take_left]
  exact he

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.FirstArrival

-- BEGIN MPProof.RunCoupling
section

namespace MatroidProphetKW.Single.MPFresh

variable {α : Type*} [DecidableEq α]

lemma fold_constant_congr (M : Matroid α) (T : Finset α → α → ℝ)
    (w w' : α → ℝ) (l : List α) (st : List α × Finset α)
    (hw : ∀ x ∈ l, w x = w' x) :
    l.foldl (step M (fun A _ _ x => T A x) w) st =
      l.foldl (step M (fun A _ _ x => T A x) w') st := by
  induction l generalizing st with
  | nil => rfl
  | cons x l ih =>
      have hx := hw x (by simp)
      have hs : step M (fun A _ _ x => T A x) w st x =
          step M (fun A _ _ x => T A x) w' st x := by
        dsimp only [step]
        rw [hx]
      simp only [List.foldl_cons, hs]
      apply ih
      intro y hy
      exact hw y (List.mem_cons_of_mem x hy)

lemma run_constant_congr (M : Matroid α) (T : Finset α → α → ℝ)
    (w w' : α → ℝ) (l : List α) (hw : ∀ x ∈ l, w x = w' x) :
    run M (fun A _ _ x => T A x) l w = run M (fun A _ _ x => T A x) l w' := by
  exact congrArg Prod.snd (fold_constant_congr M T w w' l ([], ∅) hw)

variable [Fintype α]

noncomputable def beforeSet (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (w : α → ℝ) (x : α) : Finset α :=
  run M (fun A _ _ x => T A x)
    ((advOrder adv w).take ((advOrder adv w).idxOf x)) w

lemma beforeSet_coupling (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (w w' : α → ℝ) (x : α) (hw : ∀ y, y ≠ x → w y = w' y) :
    beforeSet M T adv w x = beforeSet M T adv w' x := by
  unfold beforeSet
  rw [← first_arrival_coupling adv hadv w w' x hw]
  apply run_constant_congr
  intro y hy
  apply hw
  intro he
  subst y
  exact notMem_take_idxOf x (advOrder adv w) hy

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.RunCoupling

-- BEGIN MPProof.RunMembership
section

namespace MatroidProphetKW.Single.MPFresh

variable {α : Type*} [DecidableEq α]

lemma run_append_fold (M : Matroid α)
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (w : α → ℝ) (l r : List α) :
    run M Thr (l ++ r) w = (r.foldl (step M Thr w) (l, run M Thr l w)).2 := by
  have hh := fold_step_history M Thr w l ([], ∅)
  simp only [List.nil_append] at hh
  have hs : l.foldl (step M Thr w) ([], ∅) = (l, run M Thr l w) := by
    apply Prod.ext
    · exact hh
    · rfl
  simp only [run, List.foldl_append]
  rw [hs]

lemma fold_step_notMem (M : Matroid α)
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (w : α → ℝ) (l : List α) (st : List α × Finset α) (x : α)
    (hx : x ∉ l) :
    x ∈ (l.foldl (step M Thr w) st).2 ↔ x ∈ st.2 := by
  classical
  induction l generalizing st with
  | nil => rfl
  | cons y l ih =>
      have hxy : x ≠ y := by intro h; exact hx (by simp [h])
      have hxl : x ∉ l := fun h => hx (List.mem_cons_of_mem y h)
      rw [List.foldl_cons, ih _ hxl]
      simp only [step]
      split_ifs <;> simp [hxy]

lemma run_notMem (M : Matroid α)
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (w : α → ℝ) (l : List α) (x : α) (hx : x ∉ l) : x ∉ run M Thr l w := by
  have h := fold_step_notMem M Thr w l ([], ∅) x hx
  simpa only [Finset.notMem_empty, iff_false, run] using h

lemma run_mem_decomposition (M : Matroid α) (T : Finset α → α → ℝ)
    (w : α → ℝ) (l r : List α) (x : α) (hxl : x ∉ l) (hxr : x ∉ r) :
    x ∈ run M (fun A _ _ x => T A x) (l ++ x :: r) w ↔
      M.Indep (↑(insert x (run M (fun A _ _ x => T A x) l w)) : Set α) ∧
        T (run M (fun A _ _ x => T A x) l w) x ≤ w x := by
  classical
  rw [show l ++ x :: r = (l ++ [x]) ++ r by simp, run_append_fold]
  rw [fold_step_notMem M _ w r _ x hxr, run_append_singleton]
  have hn := run_notMem M (fun A _ _ x => T A x) w l x hxl
  split_ifs with h
  · exact iff_of_true (Finset.mem_insert_self _ _) h
  · exact iff_of_false hn h

lemma fold_step_contains (M : Matroid α)
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (w : α → ℝ) (l : List α) (st : List α × Finset α) :
    st.2 ⊆ (l.foldl (step M Thr w) st).2 := by
  classical
  induction l generalizing st with
  | nil => exact Finset.Subset.refl _
  | cons x l ih =>
      apply Finset.Subset.trans (s₂ := (step M Thr w st x).2) _ (ih _)
      simp only [step]
      split_ifs
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _

lemma run_append_contains (M : Matroid α)
    (Thr : Finset α → List α → (α → ℝ) → α → ℝ)
    (w : α → ℝ) (l r : List α) : run M Thr l w ⊆ run M Thr (l ++ r) w := by
  rw [run_append_fold]
  exact fold_step_contains M Thr w r (l, run M Thr l w)

variable [Fintype α]

lemma beforeSet_indep (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (w : α → ℝ) (x : α) :
    M.Indep (beforeSet M T adv w x : Set α) :=
  run_indep M _ w _

lemma beforeSet_notMem (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (w : α → ℝ) (x : α) :
    x ∉ beforeSet M T adv w x :=
  run_notMem M _ w _ x (notMem_take_idxOf x _)

lemma beforeSet_subset_final (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (w : α → ℝ) (x : α) :
    beforeSet M T adv w x ⊆ run M (fun A _ _ x => T A x) (advOrder adv w) w := by
  have h := run_append_contains M (fun A _ _ x => T A x) w
    ((advOrder adv w).take ((advOrder adv w).idxOf x))
    ((advOrder adv w).drop ((advOrder adv w).idxOf x))
  simpa only [beforeSet, List.take_append_drop] using h

lemma actual_selected_iff (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (w : α → ℝ) (x : α) :
    x ∈ run M (fun A _ _ x => T A x) (advOrder adv w) w ↔
      M.Indep (↑(insert x (beforeSet M T adv w x)) : Set α) ∧
        T (beforeSet M T adv w x) x ≤ w x := by
  obtain ⟨l, r, he⟩ := List.mem_iff_append.mp ((advOrder_isOrder adv hadv w).2 x)
  have hn := (advOrder_isOrder adv hadv w).1
  rw [he, List.nodup_append] at hn
  have hxr : x ∉ r := (List.nodup_cons.mp hn.2.1).1
  have hxl : x ∉ l := by
    intro hx
    exact hn.2.2 x hx x (by simp) rfl
  have hp : (advOrder adv w).take ((advOrder adv w).idxOf x) = l := by
    rw [he, List.idxOf_append, if_neg hxl]
    simp
  unfold beforeSet
  rw [hp, he]
  exact run_mem_decomposition M T w l r x hxl hxr

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.RunMembership

-- BEGIN MPProof.DiscreteFibers
section

namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

variable {Ω β γ : Type*} [MeasurableSpace Ω]

def MeasurableFibers (f : Ω → β) : Prop :=
  ∀ b, MeasurableSet {ω | f ω = b}

lemma measurableFibers_const (b : β) : MeasurableFibers (fun _ : Ω => b) := by
  intro c
  by_cases h : b = c <;> simp [h]

lemma MeasurableFibers.bind [Countable β] {f : Ω → β} {g : β → Ω → γ}
    (hf : MeasurableFibers f) (hg : ∀ b, MeasurableFibers (g b)) :
    MeasurableFibers (fun ω => g (f ω) ω) := by
  intro c
  have he : {ω | g (f ω) ω = c} = ⋃ b, {ω | f ω = b} ∩ {ω | g b ω = c} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨f ω, rfl, h⟩
    · rintro ⟨b, hb, h⟩; simpa only [hb] using h
  rw [he]
  exact MeasurableSet.iUnion (fun b => (hf b).inter (hg b c))

lemma MeasurableFibers.comp [Countable β] {f : Ω → β} (hf : MeasurableFibers f)
    (g : β → γ) : MeasurableFibers (fun ω => g (f ω)) := by
  exact hf.bind (fun b => measurableFibers_const (g b))

lemma MeasurableFibers.pair {f : Ω → β} {g : Ω → γ}
    (hf : MeasurableFibers f) (hg : MeasurableFibers g) :
    MeasurableFibers (fun ω => (f ω, g ω)) := by
  intro b
  have he : {ω | (f ω, g ω) = b} = {ω | f ω = b.1} ∩ {ω | g ω = b.2} := by
    rcases b with ⟨b, c⟩
    ext ω
    simp
  rw [he]
  exact (hf b.1).inter (hg b.2)

lemma measurableFibers_ite (p : Ω → Prop) [DecidablePred p]
    (hp : MeasurableSet {ω | p ω}) (b c : β) :
    MeasurableFibers (fun ω => if p ω then b else c) := by
  intro d
  have he : {ω | (if p ω then b else c) = d} =
      ({ω | p ω} ∩ {ω | b = d}) ∪ ({ω | p ω}ᶜ ∩ {ω | c = d}) := by
    ext ω
    by_cases h : p ω <;> simp [h]
  rw [he]
  exact (hp.inter (measurableFibers_const b d)).union
    (hp.compl.inter (measurableFibers_const c d))

lemma MeasurableFibers.measurable_bind [Countable β] [MeasurableSpace γ]
    {f : Ω → β} {g : β → Ω → γ} (hf : MeasurableFibers f)
    (hg : ∀ b, Measurable (g b)) : Measurable (fun ω => g (f ω) ω) := by
  intro s hs
  have he : (fun ω => g (f ω) ω) ⁻¹' s =
      ⋃ b, {ω | f ω = b} ∩ (g b ⁻¹' s) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro h; exact ⟨f ω, rfl, h⟩
    · rintro ⟨b, hb, h⟩; simpa only [hb] using h
  rw [he]
  exact MeasurableSet.iUnion (fun b => (hf b).inter (hg b hs))

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.DiscreteFibers

-- BEGIN MPProof.RunMeasurability
section

namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma fold_constant_measurableFibers (M : Matroid α) (T : Finset α → α → ℝ)
    (l : List α) (st : List α × Finset α) :
    MeasurableFibers (fun w : α → ℝ =>
      l.foldl (step M (fun A _ _ x => T A x) w) st) := by
  classical
  induction l generalizing st with
  | nil => exact measurableFibers_const st
  | cons x l ih =>
      have hp : MeasurableSet {w : α → ℝ |
          M.Indep (↑(insert x st.2) : Set α) ∧ T st.2 x ≤ w x} := by
        by_cases h : M.Indep (↑(insert x st.2) : Set α)
        · simpa only [h, true_and] using
            measurableSet_le measurable_const (measurable_pi_apply x)
        · simp only [h, false_and]
          exact MeasurableSet.empty
      have hs : MeasurableFibers (fun w : α → ℝ =>
          step M (fun A _ _ x => T A x) w st x) := by
        exact (measurableFibers_const (st.1 ++ [x])).pair
          (measurableFibers_ite _ hp (insert x st.2) st.2)
      exact hs.bind (fun st' => ih st')

lemma run_constant_measurableFibers (M : Matroid α) (T : Finset α → α → ℝ)
    (l : List α) :
    MeasurableFibers (fun w : α → ℝ => run M (fun A _ _ x => T A x) l w) := by
  exact (fold_constant_measurableFibers M T l ([], ∅)).comp Prod.snd

omit [DecidableEq α] in
lemma advPrefix_measurableFibers (adv : List α → (α → ℝ) → α)
    (hadv : IsAdversary adv) (k : ℕ) :
    MeasurableFibers (fun w => advPrefix adv w k) := by
  induction k with
  | zero => exact measurableFibers_const []
  | succ k ih =>
      change MeasurableFibers (fun w => advPrefix adv w k ++ [adv (advPrefix adv w k) w])
      apply ih.bind (g := fun l w => l ++ [adv l w])
      intro l
      have hmf : MeasurableFibers (adv l) := hadv.2.2 l
      exact hmf.comp (fun x => l ++ [x])

omit [DecidableEq α] in
lemma advOrder_measurableFibers (adv : List α → (α → ℝ) → α)
    (hadv : IsAdversary adv) : MeasurableFibers (advOrder adv) :=
  advPrefix_measurableFibers adv hadv _

lemma beforeSet_measurableFibers (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv) (x : α) :
    MeasurableFibers (fun w => beforeSet M T adv w x) := by
  exact ((advOrder_measurableFibers adv hadv).comp
    (fun l => l.take (l.idxOf x))).bind (run_constant_measurableFibers M T)

lemma adaptive_run_measurableFibers (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv) :
    MeasurableFibers (fun w => run M (fun A _ _ x => T A x) (advOrder adv w) w) := by
  exact (advOrder_measurableFibers adv hadv).bind (run_constant_measurableFibers M T)

lemma before_threshold_measurable (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv) (x : α) :
    Measurable (fun w => T (beforeSet M T adv w x) x) := by
  exact (beforeSet_measurableFibers M T adv hadv x).measurable_bind
    (g := fun A (_ : α → ℝ) => T A x) (fun _ => measurable_const)

lemma before_feasible_measurableSet (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv) (x : α) :
    MeasurableSet {w | M.Indep (↑(insert x (beforeSet M T adv w x)) : Set α)} := by
  classical
  have h := (beforeSet_measurableFibers M T adv hadv x).comp
    (fun A => decide (M.Indep (↑(insert x A) : Set α))) true
  simpa only [decide_eq_true_eq] using h

lemma adaptive_reward_measurable (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv) :
    Measurable (fun w => wt w (run M (fun A _ _ x => T A x) (advOrder adv w) w)) := by
  apply (adaptive_run_measurableFibers M T adv hadv).measurable_bind
  intro A
  exact Finset.measurable_sum A (fun x _ => measurable_pi_apply x)

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.RunMeasurability

-- BEGIN MPProof.FiniteIntegrability
section

namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

lemma MeasurableFibers.integrable_bind {Ω β : Type*} [MeasurableSpace Ω] [Fintype β]
    (μ : Measure Ω) {f : Ω → β} {g : β → Ω → ℝ}
    (hf : MeasurableFibers f) (hgm : ∀ b, Measurable (g b))
    (hgi : ∀ b, Integrable (g b) μ) : Integrable (fun ω => g (f ω) ω) μ := by
  classical
  have hi : Integrable (fun ω => ∑ b, ‖g b ω‖) μ :=
    integrable_finsetSum _ (fun b _ => (hgi b).norm)
  apply hi.mono' (hf.measurable_bind hgm).aestronglyMeasurable
  filter_upwards [] with ω
  exact Finset.single_le_sum (fun b _ => norm_nonneg (g b ω)) (Finset.mem_univ (f ω))

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
omit [DecidableEq α] in
lemma weight_integrable (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hFi : ∀ x, Integrable id (F x)) (A : Finset α) :
    Integrable (fun w : α → ℝ => wt w A) (Measure.pi F) := by
  apply integrable_finsetSum
  intro x hx
  exact integrable_eval (hFi x)

lemma adaptive_reward_integrable (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hFi : ∀ x, Integrable id (F x)) :
    Integrable (fun w => wt w (run M (fun A _ _ x => T A x) (advOrder adv w) w))
      (Measure.pi F) := by
  apply (adaptive_run_measurableFibers M T adv hadv).integrable_bind
  · intro A
    exact Finset.measurable_sum A (fun x _ => measurable_pi_apply x)
  · exact weight_integrable F hFi

open Classical in
noncomputable def guardedSurplus (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (x : α) (w : α → ℝ) (t : ℝ) : ℝ :=
  if M.Indep (↑(insert x (beforeSet M T adv w x)) : Set α)
  then max (t - T (beforeSet M T adv w x) x) 0 else 0

lemma guardedSurplus_update (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (x : α) (w : α → ℝ) (t s : ℝ) :
    guardedSurplus M T adv x (Function.update w x t) s = guardedSurplus M T adv x w s := by
  have he := beforeSet_coupling M T adv hadv (Function.update w x t) w x
    (fun y hy => Function.update_of_ne hy t w)
  classical
  exact congrArg (fun A : Finset α =>
    if M.Indep (↑(insert x A) : Set α) then max (s - T A x) 0 else 0) he

lemma guardedSurplus_nonneg (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (x : α) (w : α → ℝ) (t : ℝ) :
    0 ≤ guardedSurplus M T adv x w t := by
  unfold guardedSurplus
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.FiniteIntegrability

-- BEGIN MPProof.CoordinateSwap
section

namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def coordinateSwapEquiv (x : α) :
    ((α → ℝ) × (α → ℝ)) ≃ᵐ ((α → ℝ) × (α → ℝ)) :=
  ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ α).symm.trans
    (MeasurableEquiv.piCongrRight (fun y =>
      if y = x then MeasurableEquiv.prodComm else MeasurableEquiv.refl (ℝ × ℝ)))).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ α)

omit [Fintype α] in
lemma coordinateSwapEquiv_apply (x : α) (w w' : α → ℝ) :
    coordinateSwapEquiv x (w, w') =
      (Function.update w x (w' x), Function.update w' x (w x)) := by
  ext y <;> by_cases h : y = x <;>
    simp [coordinateSwapEquiv, MeasurableEquiv.arrowProdEquivProdArrow,
      Equiv.arrowProdEquivProdArrow, MeasurableEquiv.piCongrRight, h]
  all_goals rfl

lemma coordinateSwap_measurePreserving (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (x : α) :
    MeasurePreserving (coordinateSwapEquiv x)
      ((Measure.pi F).prod (Measure.pi F)) ((Measure.pi F).prod (Measure.pi F)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ α
  have he := measurePreserving_arrowProdEquivProdArrow ℝ ℝ α F F
  have hp : MeasurePreserving
      (MeasurableEquiv.piCongrRight (fun y : α =>
        if y = x then MeasurableEquiv.prodComm else MeasurableEquiv.refl (ℝ × ℝ)))
      (Measure.pi (fun y => (F y).prod (F y)))
      (Measure.pi (fun y => (F y).prod (F y))) := by
    apply measurePreserving_pi
    intro y
    by_cases h : y = x
    · simp only [if_pos h]
      exact Measure.measurePreserving_swap
    · simp only [if_neg h]
      exact MeasurePreserving.id _
  exact he.comp (hp.comp (MeasurePreserving.symm e he))

lemma coordinate_resampling_integral (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (x : α)
    (f : (α → ℝ) → ℝ → ℝ)
    (hf : ∀ w t s, f (Function.update w x t) s = f w s) :
    (∫ z, f z.1 (z.1 x) ∂(Measure.pi F).prod (Measure.pi F)) =
      ∫ z, f z.1 (z.2 x) ∂(Measure.pi F).prod (Measure.pi F) := by
  have he := (coordinateSwap_measurePreserving F x).integral_comp
    (coordinateSwapEquiv x).measurableEmbedding (fun z => f z.1 (z.1 x))
  symm
  calc
    (∫ z, f z.1 (z.2 x) ∂(Measure.pi F).prod (Measure.pi F)) =
        ∫ z, f (coordinateSwapEquiv x z).1 ((coordinateSwapEquiv x z).1 x)
          ∂(Measure.pi F).prod (Measure.pi F) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rcases z with ⟨w, w'⟩
      simp [coordinateSwapEquiv_apply, hf]
    _ = _ := he

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.CoordinateSwap

-- BEGIN MPProof.GhostSurplus
section

namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

lemma MeasurableFibers.precomp {Ω Ω' β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {f : Ω → β} {g : Ω' → Ω} (hf : MeasurableFibers f) (hg : Measurable g) :
    MeasurableFibers (fun ω => f (g ω)) := by
  intro b
  exact (hf b).preimage hg

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma own_surplus_integrable (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hFi : ∀ x, Integrable id (F x)) (x : α) :
    Integrable (fun w => guardedSurplus M T adv x w (w x)) (Measure.pi F) := by
  classical
  have hi : Integrable (fun w : α → ℝ => w x) (Measure.pi F) := integrable_eval (hFi x)
  unfold guardedSurplus
  apply (beforeSet_measurableFibers M T adv hadv x).integrable_bind (Measure.pi F)
    (g := fun (A : Finset α) (w : α → ℝ) => if M.Indep (↑(insert x A) : Set α)
      then max (w x - T A x) 0 else 0)
  · intro A
    by_cases h : M.Indep (↑(insert x A) : Set α)
    · simp only [if_pos h]
      exact ((measurable_pi_apply x).sub measurable_const).max measurable_const
    · simp only [if_neg h]
      exact measurable_const
  · intro A
    by_cases h : M.Indep (↑(insert x A) : Set α)
    · simp only [if_pos h]
      exact (hi.sub (integrable_const _)).sup (integrable_const _)
    · simp only [if_neg h]
      exact integrable_const _

lemma ghost_surplus_integrable (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hFi : ∀ x, Integrable id (F x)) (x : α) :
    Integrable (fun z : (α → ℝ) × (α → ℝ) => guardedSurplus M T adv x z.1 (z.2 x))
      ((Measure.pi F).prod (Measure.pi F)) := by
  classical
  have hi : Integrable (fun w : α → ℝ => w x) (Measure.pi F) := integrable_eval (hFi x)
  unfold guardedSurplus
  apply ((beforeSet_measurableFibers M T adv hadv x).precomp
    (g := fun z : (α → ℝ) × (α → ℝ) => z.1) measurable_fst).integrable_bind
      ((Measure.pi F).prod (Measure.pi F))
      (g := fun (A : Finset α) (z : (α → ℝ) × (α → ℝ)) => if M.Indep (↑(insert x A) : Set α)
        then max (z.2 x - T A x) 0 else 0)
  · intro A
    by_cases h : M.Indep (↑(insert x A) : Set α)
    · simp only [if_pos h]
      exact (((measurable_pi_apply x).comp measurable_snd).sub measurable_const).max measurable_const
    · simp only [if_neg h]
      exact measurable_const
  · intro A
    by_cases h : M.Indep (↑(insert x A) : Set α)
    · simp only [if_pos h]
      exact ((hi.comp_snd (Measure.pi F)).sub
        (integrable_const _)).sup (integrable_const _)
    · simp only [if_neg h]
      exact integrable_const _

lemma actual_surplus_resampling (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hFi : ∀ x, Integrable id (F x)) (x : α) :
    (∫ w, guardedSurplus M T adv x w (w x) ∂Measure.pi F) =
      ∫ z, guardedSurplus M T adv x z.1 (z.2 x) ∂(Measure.pi F).prod (Measure.pi F) := by
  have hi := (own_surplus_integrable M T adv hadv F hFi x).comp_fst (Measure.pi F)
  have he := coordinate_resampling_integral F x (guardedSurplus M T adv x)
    (guardedSurplus_update M T adv hadv x)
  rw [integral_prod _ hi] at he
  simpa using he

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.GhostSurplus

-- BEGIN MPProof.RewardAccounting
section

namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def selectedRevenue (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (w : α → ℝ) : ℝ :=
  ∑ x ∈ run M (fun A _ _ x => T A x) (advOrder adv w) w,
    T (beforeSet M T adv w x) x

lemma reward_accounting (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv) (w : α → ℝ) :
    wt w (run M (fun A _ _ x => T A x) (advOrder adv w) w) =
      selectedRevenue M T adv w + ∑ x, guardedSurplus M T adv x w (w x) := by
  classical
  let A := run M (fun A _ _ x => T A x) (advOrder adv w) w
  have hp (x : α) : (if x ∈ A then w x else 0) =
      (if x ∈ A then T (beforeSet M T adv w x) x else 0) +
        guardedSurplus M T adv x w (w x) := by
    have hm := actual_selected_iff M T adv hadv w x
    change x ∈ A ↔ _ at hm
    unfold guardedSurplus
    by_cases hfe : M.Indep (↑(insert x (beforeSet M T adv w x)) : Set α)
    · by_cases ht : T (beforeSet M T adv w x) x ≤ w x
      · have hx := hm.mpr ⟨hfe, ht⟩
        rw [if_pos hx, if_pos hx, if_pos hfe, max_eq_left (sub_nonneg.mpr ht)]
        ring
      · have hx : x ∉ A := fun hx => ht (hm.mp hx).2
        rw [if_neg hx, if_neg hx, if_pos hfe, max_eq_right (by linarith)]
        simp
    · have hx : x ∉ A := fun hx => hfe (hm.mp hx).1
      simp only [if_neg hx, if_neg hfe, add_zero]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun x _ => hp x)
  simpa [wt, selectedRevenue, A, Finset.sum_add_distrib] using hs

lemma selectedRevenue_integrable (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)] :
    Integrable (selectedRevenue M T adv) (Measure.pi F) := by
  classical
  have hterm (x : α) : Integrable (fun w =>
      if x ∈ run M (fun A _ _ x => T A x) (advOrder adv w) w
      then T (beforeSet M T adv w x) x else 0) (Measure.pi F) := by
    apply ((adaptive_run_measurableFibers M T adv hadv).pair
      (beforeSet_measurableFibers M T adv hadv x)).integrable_bind (Measure.pi F)
        (g := fun (b : Finset α × Finset α) (_ : α → ℝ) =>
          if x ∈ b.1 then T b.2 x else 0)
    · intro b; exact measurable_const
    · intro b; exact integrable_const _
  have hs := integrable_finsetSum Finset.univ (fun x _ => hterm x)
  apply hs.congr
  filter_upwards [] with w
  simp [selectedRevenue]

lemma total_surplus_resampling (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hFi : ∀ x, Integrable id (F x)) :
    (∫ w, ∑ x, guardedSurplus M T adv x w (w x) ∂Measure.pi F) =
      ∫ z, ∑ x, guardedSurplus M T adv x z.1 (z.2 x)
        ∂(Measure.pi F).prod (Measure.pi F) := by
  rw [integral_finsetSum _ (fun x _ => own_surplus_integrable M T adv hadv F hFi x),
    integral_finsetSum _ (fun x _ => ghost_surplus_integrable M T adv hadv F hFi x)]
  exact Finset.sum_congr rfl (fun x _ => actual_surplus_resampling M T adv hadv F hFi x)

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.RewardAccounting

-- BEGIN MPProof.ChronologicalRevenue
section

namespace MatroidProphetKW.Single.MPFresh

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def listRevenue (M : Matroid α) (T : Finset α → α → ℝ)
    (l : List α) (w : α → ℝ) : ℝ :=
  ∑ x ∈ run M (fun A _ _ x => T A x) l w,
    T (run M (fun A _ _ x => T A x) (l.take (l.idxOf x)) w) x

omit [Fintype α] in
lemma take_idxOf_append_of_mem (l r : List α) (x : α) (hx : x ∈ l) :
    (l ++ r).take ((l ++ r).idxOf x) = l.take (l.idxOf x) := by
  rw [List.idxOf_append, if_pos hx, List.take_append]
  simp only [Nat.sub_eq_zero_of_le (List.idxOf_lt_length_of_mem hx).le,
    List.take_zero, List.append_nil]

omit [Fintype α] in
open Classical in
lemma listRevenue_append (M : Matroid α) (T : Finset α → α → ℝ)
    (w : α → ℝ) (l : List α) (x : α) (hx : x ∉ l) :
    listRevenue M T (l ++ [x]) w = listRevenue M T l w +
      if M.Indep (↑(insert x (run M (fun A _ _ x => T A x) l w)) : Set α) ∧
          T (run M (fun A _ _ x => T A x) l w) x ≤ w x
      then T (run M (fun A _ _ x => T A x) l w) x else 0 := by
  classical
  let A := run M (fun A _ _ x => T A x) l w
  have hxa : x ∉ A := run_notMem M _ w l x hx
  have hold (y : α) (hy : y ∈ A) :
      (l ++ [x]).take ((l ++ [x]).idxOf y) = l.take (l.idxOf y) := by
    apply take_idxOf_append_of_mem
    by_contra hyl
    exact run_notMem M _ w l y hyl hy
  have hnew : (l ++ [x]).take ((l ++ [x]).idxOf x) = l := by
    rw [List.idxOf_append, if_neg hx]
    simp
  unfold listRevenue
  rw [run_append_singleton]
  split_ifs with h
  · rw [Finset.sum_insert hxa, hnew]
    have he : (∑ y ∈ A, T (run M (fun A _ _ x => T A x)
        ((l ++ [x]).take ((l ++ [x]).idxOf y)) w) y) =
        ∑ y ∈ A, T (run M (fun A _ _ x => T A x) (l.take (l.idxOf y)) w) y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hold y hy]
    rw [he]
    exact add_comm _ _
  · simp only [add_zero]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hold y hy]

omit [Fintype α] in
lemma listRevenue_potential (M : Matroid α) (T : Finset α → α → ℝ)
    (V : Finset α → ℝ)
    (hT : ∀ (A : Finset α) (x : α), M.Indep (A : Set α) → x ∉ A →
      M.Indep (↑(insert x A) : Set α) → T A x = V A - V (insert x A))
    (w : α → ℝ) (l : List α) (hl : l.Nodup) :
    listRevenue M T l w = V ∅ - V (run M (fun A _ _ x => T A x) l w) := by
  classical
  induction l using List.reverseRecOn with
  | nil => simp [listRevenue]
  | append_singleton l x ih =>
      have hn := List.nodup_append.mp hl
      have hx : x ∉ l := by
        intro h
        exact hn.2.2 x h x (by simp) rfl
      rw [listRevenue_append M T w l x hx, ih hn.1, run_append_singleton]
      split_ifs with h
      · rw [hT _ x (run_indep M _ w l) (run_notMem M _ w l x hx) h.1]
        ring
      · ring

lemma selectedRevenue_potential (M : Matroid α) (T : Finset α → α → ℝ)
    (V : Finset α → ℝ)
    (hT : ∀ (A : Finset α) (x : α), M.Indep (A : Set α) → x ∉ A →
      M.Indep (↑(insert x A) : Set α) → T A x = V A - V (insert x A))
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv) (w : α → ℝ) :
    selectedRevenue M T adv w = V ∅ -
      V (run M (fun A _ _ x => T A x) (advOrder adv w) w) := by
  exact listRevenue_potential M T V hT w (advOrder adv w) (advOrder_isOrder adv hadv w).1

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.ChronologicalRevenue

-- BEGIN MPProof.GhostLowerBound
section

namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma ghost_surplus_lower (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (w w' : α → ℝ)
    (V : Finset α) (B : ℝ)
    (hV : M.Indep (↑(run M (fun A _ _ x => T A x) (advOrder adv w) w ∪ V) : Set α))
    (hbudget : (∑ x ∈ V, T (beforeSet M T adv w x) x) ≤ B) :
    wt w' V - B ≤ ∑ x, guardedSurplus M T adv x w (w' x) := by
  classical
  have hfe (x : α) (hx : x ∈ V) :
      M.Indep (↑(insert x (beforeSet M T adv w x)) : Set α) := by
    apply hV.subset
    intro y hy
    have hy' : y ∈ insert x (beforeSet M T adv w x) := hy
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · exact Finset.mem_union_right _ hx
    · exact Finset.mem_union_left _ (beforeSet_subset_final M T adv w x hy')
  have hsum : (∑ x ∈ V, (w' x - T (beforeSet M T adv w x) x)) ≤
      ∑ x ∈ V, guardedSurplus M T adv x w (w' x) := by
    apply Finset.sum_le_sum
    intro x hx
    simp only [guardedSurplus, if_pos (hfe x hx)]
    exact le_max_left _ _
  have hall : (∑ x ∈ V, guardedSurplus M T adv x w (w' x)) ≤
      ∑ x, guardedSurplus M T adv x w (w' x) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ V)
    intro x hx hnx
    exact guardedSurplus_nonneg M T adv x w (w' x)
  rw [Finset.sum_sub_distrib] at hsum
  change (∑ x ∈ V, w' x) - B ≤ _
  linarith

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.GhostLowerBound

-- BEGIN MPProof.SymmetricExchange
section

namespace MatroidProphetKW.Single.MPFresh

open Set

theorem symmetric_basis_exchange {α : Type*} (M : Matroid α) {B D : Set α}
    (hB : M.IsBase B) (hD : M.IsBase D) {e : α} (heD : e ∈ D) (heB : e ∉ B) :
    ∃ f ∈ B \ D, M.IsBase (insert e (B \ {f})) ∧ M.IsBase (insert f (D \ {e})) := by
  classical
  have heE := hD.subset_ground heD
  have hecl : e ∈ M.closure B := by rw [hB.closure_eq]; exact heE
  have hC := hB.indep.fundCircuit_isCircuit hecl heB
  have hex : ∃ f ∈ M.fundCircuit e B \ {e}, f ∉ M.closure (D \ {e}) := by
    by_contra hh
    push Not at hh
    have hs : M.fundCircuit e B \ {e} ⊆ M.closure (D \ {e}) := by
      intro f hf
      exact hh f hf
    have hc := M.closure_subset_closure hs
    rw [M.closure_closure] at hc
    exact hD.indep.notMem_closure_sdiff_of_mem heD
      (hc (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit e B)))
  obtain ⟨f, hfC, hfcl⟩ := hex
  have hfB : f ∈ B := by
    have := M.fundCircuit_subset_insert e B hfC.1
    exact this.resolve_left (by simpa using hfC.2)
  have hfD : f ∉ D := by
    intro hf
    apply hfcl
    exact M.mem_closure_of_mem ⟨hf, hfC.2⟩
  have hef : e ≠ f := by simpa [ne_comm] using hfC.2
  have hind : M.Indep (insert e (B \ {f})) := by
    simpa only [Set.insert_sdiff_singleton_comm hef] using
      (hB.indep.mem_fundCircuit_iff hecl heB).mp hfC.1
  exact ⟨f, ⟨hfB, hfD⟩, hB.exchange_isBase_of_indep heB hind,
    hD.exchange_base_of_notMem_closure heD hfcl (hB.subset_ground hfB)⟩

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.SymmetricExchange

-- BEGIN MPProof.MatroidFin
section

noncomputable section
namespace MatroidProphetKW.Single.MPFresh

open Set

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem wt_insert (w : α → ℝ) (A : Finset α) (x : α) (hx : x ∉ A) :
    wt w (insert x A) = w x + wt w A := by simp [wt, hx]

omit [Fintype α] in
theorem wt_erase (w : α → ℝ) (A : Finset α) (x : α) (hx : x ∈ A) :
    wt w (A.erase x) = wt w A - w x := by
  exact Finset.sum_erase_eq_sub hx

omit [Fintype α] in
theorem wt_union (w : α → ℝ) (A B : Finset α) (h : Disjoint A B) :
    wt w (A ∪ B) = wt w A + wt w B := by exact Finset.sum_union h

omit [DecidableEq α] in
theorem maxBase_isBase (M : Matroid α) (w : α → ℝ) :
    M.IsBase (maxBase M w : Set α) := by
  classical
  have h := (Finset.exists_max_image (bases M) (wt w) (bases_nonempty M)).choose_spec.1
  simpa only [maxBase, bases, Finset.mem_filter, Finset.mem_univ, true_and] using h

omit [DecidableEq α] in
theorem maxBase_weight (M : Matroid α) (w : α → ℝ) (B : Finset α)
    (hB : M.IsBase (B : Set α)) : wt w B ≤ wt w (maxBase M w) := by
  classical
  exact (Finset.exists_max_image (bases M) (wt w) (bases_nonempty M)).choose_spec.2 B
    (by simp [bases, hB])

open Classical in
def completions (M : Matroid α) (A : Finset α) : Finset (Finset α) :=
  Finset.univ.filter (fun R => Disjoint A R ∧ M.IsBase (↑(A ∪ R) : Set α))

theorem mem_completions (M : Matroid α) (A R : Finset α) :
    R ∈ completions M A ↔ Disjoint A R ∧ M.IsBase (↑(A ∪ R) : Set α) := by
  classical
  simp [completions]

theorem completions_nonempty (M : Matroid α) (A : Finset α)
    (hA : M.Indep (A : Set α)) : (completions M A).Nonempty := by
  classical
  obtain ⟨B, hB, hAB⟩ := hA.exists_isBase_superset
  let C := B.toFinite.toFinset
  have hAC : A ⊆ C := by simpa [C] using hAB
  refine ⟨C \ A, (mem_completions M A _).2 ⟨Finset.disjoint_sdiff, ?_⟩⟩
  rw [Finset.union_sdiff_of_subset hAC]
  simpa [C] using hB

end MatroidProphetKW.Single.MPFresh
end
end
-- END MPProof.MatroidFin

-- BEGIN MPProof.WeightedExchange
section

noncomputable section
namespace MatroidProphetKW.Single.MPFresh

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem weighted_basis_exchange (M : Matroid α) (w : α → ℝ) (B D : Finset α)
    (hB : M.IsBase (B : Set α)) (hD : M.IsBase (D : Set α))
    (hmax : ∀ C : Finset α, M.IsBase (C : Set α) → wt w C ≤ wt w B)
    (e : α) (heD : e ∈ D) (heB : e ∉ B) :
    ∃ f ∈ B \ D, w e ≤ w f ∧ M.IsBase (↑(insert f (D.erase e)) : Set α) := by
  classical
  obtain ⟨f, hf, hb, hd⟩ := symmetric_basis_exchange M hB hD heD heB
  have hfB : f ∈ B := hf.1
  have hfD : f ∉ D := hf.2
  have hb' : M.IsBase (↑(insert e (B.erase f)) : Set α) := by simpa using hb
  have hw := hmax (insert e (B.erase f)) hb'
  rw [wt_insert _ _ _ (by simp [heB]), wt_erase _ _ _ hfB] at hw
  refine ⟨f, Finset.mem_sdiff.mpr ⟨hfB, hfD⟩, by linarith, ?_⟩
  simpa using hd

theorem completion_improve (M : Matroid α) (w : α → ℝ) (A B R : Finset α)
    (hB : M.IsBase (B : Set α))
    (hmax : ∀ C : Finset α, M.IsBase (C : Set α) → wt w C ≤ wt w B)
    (hR : R ∈ completions M A) (e : α) (he : e ∈ R \ B) :
    ∃ R' ∈ completions M A, wt w R ≤ wt w R' ∧ (R' \ B).card < (R \ B).card := by
  classical
  obtain ⟨hd, hb⟩ := (mem_completions M A R).mp hR
  have heR := (Finset.mem_sdiff.mp he).1
  have heB := (Finset.mem_sdiff.mp he).2
  have heA : e ∉ A := by
    intro h
    exact Finset.disjoint_left.mp hd h heR
  obtain ⟨f, hf, hw, hnew⟩ := weighted_basis_exchange M w B (A ∪ R) hB hb hmax e
    (Finset.mem_union_right A heR) heB
  have hfB := (Finset.mem_sdiff.mp hf).1
  have hfAR := (Finset.mem_sdiff.mp hf).2
  have hfA : f ∉ A := fun h => hfAR (Finset.mem_union_left R h)
  have hfR : f ∉ R := fun h => hfAR (Finset.mem_union_right A h)
  let R' := insert f (R.erase e)
  have hu : A ∪ R' = insert f ((A ∪ R).erase e) := by
    ext x
    simp only [R', Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    aesop
  have hr' : R' ∈ completions M A := by
    apply (mem_completions M A R').2
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro x hxA hxR
      rcases Finset.mem_insert.mp hxR with hxf | hxR
      · exact hfA (hxf ▸ hxA)
      · exact Finset.disjoint_left.mp hd hxA (Finset.mem_erase.mp hxR).2
    · rw [hu]
      exact hnew
  have hcard : R' \ B = (R \ B).erase e := by
    ext x
    simp only [R', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    aesop
  refine ⟨R', hr', ?_, ?_⟩
  · dsimp [R']
    rw [wt_insert _ _ _ (by simp [hfR]), wt_erase _ _ _ heR]
    linarith
  · rw [hcard]
    exact Finset.card_erase_lt_of_mem he

end MatroidProphetKW.Single.MPFresh
end
end
-- END MPProof.WeightedExchange

-- BEGIN MPProof.CompletionInside
section

noncomputable section
namespace MatroidProphetKW.Single.MPFresh

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem completion_inside_maxBase (M : Matroid α) (w : α → ℝ) (A R : Finset α)
    (hR : R ∈ completions M A) :
    ∃ S ∈ completions M A, S ⊆ maxBase M w ∧ wt w R ≤ wt w S := by
  classical
  suffices h : ∀ m : ℕ, ∀ R : Finset α, R ∈ completions M A →
      (R \ maxBase M w).card = m →
      ∃ S ∈ completions M A, S ⊆ maxBase M w ∧ wt w R ≤ wt w S by
    exact h _ R hR rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro R hR hm
    by_cases hs : R ⊆ maxBase M w
    · exact ⟨R, hR, hs, le_rfl⟩
    obtain ⟨e, heR, heB⟩ := Finset.not_subset.mp hs
    obtain ⟨R', hR', hw, hlt⟩ := completion_improve M w A (maxBase M w) R
      (maxBase_isBase M w) (maxBase_weight M w) hR e (Finset.mem_sdiff.mpr ⟨heR, heB⟩)
    rw [hm] at hlt
    obtain ⟨S, hS, hSB, hweight⟩ := ih _ hlt R' hR' rfl
    exact ⟨S, hS, hSB, hw.trans hweight⟩

theorem remCands_iff (M : Matroid α) (A R : Finset α) (w : α → ℝ) :
    R ∈ remCands M A w ↔ R ∈ completions M A ∧ R ⊆ maxBase M w := by
  classical
  simp only [remCands, Finset.mem_filter, Finset.mem_powerset, mem_completions]
  constructor
  · rintro ⟨hsub, hb⟩
    refine ⟨⟨?_, hb⟩, ?_⟩
    · rw [Finset.disjoint_left]
      intro x hxA hxR
      exact (Finset.mem_sdiff.mp (hsub hxR)).2 hxA
    · intro x hx
      exact (Finset.mem_sdiff.mp (hsub hx)).1
  · rintro ⟨⟨hd, hb⟩, hsub⟩
    refine ⟨?_, hb⟩
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hsub hx, fun hxA => Finset.disjoint_left.mp hd hxA hx⟩

theorem remCands_nonempty (M : Matroid α) (A : Finset α) (w : α → ℝ)
    (hA : M.Indep (A : Set α)) : (remCands M A w).Nonempty := by
  obtain ⟨R, hR⟩ := completions_nonempty M A hA
  obtain ⟨S, hS, hSB, _⟩ := completion_inside_maxBase M w A R hR
  exact ⟨S, (remCands_iff M A S w).2 ⟨hS, hSB⟩⟩

theorem Rset_mem (M : Matroid α) (A : Finset α) (w : α → ℝ)
    (hA : M.Indep (A : Set α)) : Rset M A w ∈ remCands M A w := by
  classical
  have hn := remCands_nonempty M A w hA
  simp only [Rset, dif_pos hn]
  exact (Finset.exists_max_image _ (wt w) hn).choose_spec.1

theorem Rset_maximal (M : Matroid α) (A : Finset α) (w : α → ℝ)
    (hA : M.Indep (A : Set α)) (R : Finset α) (hR : R ∈ completions M A) :
    wt w R ≤ wt w (Rset M A w) := by
  classical
  obtain ⟨S, hS, hSB, hw⟩ := completion_inside_maxBase M w A R hR
  have hn := remCands_nonempty M A w hA
  apply hw.trans
  simp only [Rset, dif_pos hn]
  exact (Finset.exists_max_image _ (wt w) hn).choose_spec.2 S
    ((remCands_iff M A S w).2 ⟨hS, hSB⟩)

end MatroidProphetKW.Single.MPFresh
end
end
-- END MPProof.CompletionInside

-- BEGIN MPProof.ResidualValue
section

noncomputable section
namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

def residual (M : Matroid α) (A : Finset α) (w : α → ℝ) : ℝ := wt w (Rset M A w)

theorem residual_eq_sup (M : Matroid α) (A : Finset α)
    (hA : M.Indep (A : Set α)) (w : α → ℝ) :
    residual M A w = (completions M A).sup' (completions_nonempty M A hA) (wt w) := by
  classical
  apply le_antisymm
  · exact Finset.le_sup' (wt w) ((remCands_iff M A _ w).mp (Rset_mem M A w hA)).1
  · exact Finset.sup'_le _ _ (fun R hR => Rset_maximal M A w hA R hR)

theorem residual_eq_zero_of_not_indep (M : Matroid α) (A : Finset α)
    (hA : ¬ M.Indep (A : Set α)) (w : α → ℝ) : residual M A w = 0 := by
  classical
  have hn : ¬ (remCands M A w).Nonempty := by
    rintro ⟨R, hR⟩
    have hb := ((mem_completions M A R).mp ((remCands_iff M A R w).mp hR).1).2
    exact hA (hb.indep.subset (by intro x hx; exact Finset.mem_union_left R hx))
  simp [residual, Rset, hn, wt]

omit [Fintype α] [DecidableEq α] in
theorem continuous_wt (A : Finset α) : Continuous (fun w : α → ℝ => wt w A) := by
  exact continuous_finsetSum _ (fun x _ => continuous_apply x)

theorem continuous_residual (M : Matroid α) (A : Finset α) : Continuous (residual M A) := by
  classical
  by_cases hA : M.Indep (A : Set α)
  · simp_rw [show residual M A = fun w => (completions M A).sup'
        (completions_nonempty M A hA) (wt w) by funext w; exact residual_eq_sup M A hA w]
    exact Continuous.finset_sup'_apply _ (fun R _ => continuous_wt R)
  · have he : residual M A = fun _ => 0 := funext (residual_eq_zero_of_not_indep M A hA)
    rw [he]
    exact continuous_const

omit [DecidableEq α] in
theorem wt_abs_le (w : α → ℝ) (A : Finset α) : |wt w A| ≤ ∑ x, |w x| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun x _ _ => abs_nonneg _)

theorem residual_abs_le (M : Matroid α) (A : Finset α) (w : α → ℝ) :
    |residual M A w| ≤ ∑ x, |w x| := wt_abs_le w _

theorem residual_nonneg (M : Matroid α) (A : Finset α) (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    0 ≤ residual M A w := Finset.sum_nonneg (fun x _ => hw x)

theorem integrable_residual (M : Matroid α) (A : Finset α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (hF : ∀ x, Integrable id (F x)) :
    Integrable (residual M A) (Measure.pi F) := by
  have hi : Integrable (fun w : α → ℝ => ∑ x, |w x|) (Measure.pi F) := by
    apply integrable_finsetSum
    intro x _
    exact (integrable_eval (hF x)).abs
  apply hi.mono' (continuous_residual M A).measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun w => by simpa only [Real.norm_eq_abs] using residual_abs_le M A w)

end MatroidProphetKW.Single.MPFresh
end
end
-- END MPProof.ResidualValue

-- BEGIN MPProof.ResidualExpectation
section

namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
lemma nonnegative_weights_ae (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF0 : ∀ x, F x (Set.Iio 0) = 0) :
    ∀ᵐ w ∂Measure.pi F, ∀ x, 0 ≤ w x := by
  rw [ae_all_iff]
  intro x
  have hs : ∀ᵐ t ∂F x, 0 ≤ t := by
    rw [ae_iff]
    simpa only [Set.Iio, not_le] using hF0 x
  exact Measure.tendsto_eval_ae_ae hs

lemma expected_residual_state_integrable (M : Matroid α)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (s : (α → ℝ) → Finset α) (hs : MeasurableFibers s) :
    Integrable (fun w => ∫ w', residual M (s w) w' ∂Measure.pi F) (Measure.pi F) := by
  exact hs.integrable_bind (Measure.pi F)
    (g := fun (A : Finset α) (_ : α → ℝ) => ∫ w', residual M A w' ∂Measure.pi F)
    (fun _ => measurable_const)
    (fun _ => integrable_const _)

lemma residual_state_product_integrable (M : Matroid α)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hFi : ∀ x, Integrable id (F x))
    (s : (α → ℝ) → Finset α) (hs : MeasurableFibers s) :
    Integrable (fun z : (α → ℝ) × (α → ℝ) => residual M (s z.1) z.2)
      ((Measure.pi F).prod (Measure.pi F)) := by
  exact (hs.precomp (g := fun z : (α → ℝ) × (α → ℝ) => z.1) measurable_fst).integrable_bind
    ((Measure.pi F).prod (Measure.pi F))
    (g := fun (A : Finset α) (z : (α → ℝ) × (α → ℝ)) => residual M A z.2)
    (fun A => (continuous_residual M A).measurable.comp measurable_snd)
    (fun A => (integrable_residual M A F hFi).comp_snd (Measure.pi F))

lemma residual_state_fubini (M : Matroid α)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hFi : ∀ x, Integrable id (F x))
    (s : (α → ℝ) → Finset α) (hs : MeasurableFibers s) :
    (∫ z, residual M (s z.1) z.2 ∂(Measure.pi F).prod (Measure.pi F)) =
      ∫ w, (∫ w', residual M (s w) w' ∂Measure.pi F) ∂Measure.pi F := by
  exact integral_prod _ (residual_state_product_integrable M F hFi s hs)

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.ResidualExpectation

-- BEGIN MPProof.ExpectedReward
section

namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Operational assembly. The two deterministic budget premises are discharged by the native
residual theory at the final theorem; they are not additional assumptions on the root. -/
theorem half_opt_of_actual_budgets (M : Matroid α) (T : Finset α → α → ℝ)
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hFi : ∀ x, Integrable id (F x)) (O : ℝ)
    (hrevenue : ∀ w, selectedRevenue M T adv w = O / 2 -
      (∫ w', residual M (run M (fun A _ _ x => T A x) (advOrder adv w) w) w'
        ∂Measure.pi F) / 2)
    (hbudget : ∀ w V,
      Disjoint (run M (fun A _ _ x => T A x) (advOrder adv w) w) V →
      M.Indep (↑(run M (fun A _ _ x => T A x) (advOrder adv w) w ∪ V) : Set α) →
      (∑ x ∈ V, T (beforeSet M T adv w x) x) ≤
        (∫ w', residual M (run M (fun A _ _ x => T A x) (advOrder adv w) w) w'
          ∂Measure.pi F) / 2) :
    O / 2 ≤ ∫ w, wt w (run M (fun A _ _ x => T A x) (advOrder adv w) w) ∂Measure.pi F := by
  classical
  let A := fun w => run M (fun A _ _ x => T A x) (advOrder adv w) w
  let R := fun w => ∫ w', residual M (A w) w' ∂Measure.pi F
  let G := fun z : (α → ℝ) × (α → ℝ) => ∑ x, guardedSurplus M T adv x z.1 (z.2 x)
  have hA : MeasurableFibers A := adaptive_run_measurableFibers M T adv hadv
  have hRi : Integrable R (Measure.pi F) := expected_residual_state_integrable M F A hA
  have hRip := hRi.comp_fst (Measure.pi F)
  have hres := residual_state_product_integrable M F hFi A hA
  have hGi : Integrable G ((Measure.pi F).prod (Measure.pi F)) :=
    integrable_finsetSum _ (fun x _ => ghost_surplus_integrable M T adv hadv F hFi x)
  have hpoint (z : (α → ℝ) × (α → ℝ)) : residual M (A z.1) z.2 - R z.1 / 2 ≤ G z := by
    let V := Rset M (A z.1) z.2
    have hmem := Rset_mem M (A z.1) z.2 (run_indep M _ _ _)
    have hc := (mem_completions M (A z.1) V).mp
      ((remCands_iff M (A z.1) V z.2).mp hmem).1
    exact ghost_surplus_lower M T adv z.1 z.2 V (R z.1 / 2) hc.2.indep
      (hbudget z.1 V hc.1 hc.2.indep)
  have hlow := integral_mono (hres.sub (hRip.div_const 2)) hGi hpoint
  have hRp : (∫ z : (α → ℝ) × (α → ℝ), R z.1 ∂(Measure.pi F).prod (Measure.pi F)) =
      ∫ w, R w ∂Measure.pi F := by
    rw [integral_prod _ hRip]
    simp
  change (∫ z, residual M (A z.1) z.2 - R z.1 / 2
    ∂(Measure.pi F).prod (Measure.pi F)) ≤
      ∫ z, G z ∂(Measure.pi F).prod (Measure.pi F) at hlow
  rw [integral_sub hres (hRip.div_const 2), integral_div,
    residual_state_fubini M F hFi A hA, hRp] at hlow
  have hrevI := selectedRevenue_integrable M T adv hadv F
  have hrev : (∫ w, selectedRevenue M T adv w ∂Measure.pi F) =
      O / 2 - (∫ w, R w ∂Measure.pi F) / 2 := by
    calc
      _ = ∫ w, O / 2 - R w / 2 ∂Measure.pi F := integral_congr_ae
        (Filter.Eventually.of_forall hrevenue)
      _ = _ := by rw [integral_sub (integrable_const _) (hRi.div_const 2), integral_div 2 R]; simp
  have hown : Integrable (fun w => ∑ x, guardedSurplus M T adv x w (w x)) (Measure.pi F) :=
    integrable_finsetSum _ (fun x _ => own_surplus_integrable M T adv hadv F hFi x)
  have hdecomp : (∫ w, wt w (A w) ∂Measure.pi F) =
      (∫ w, selectedRevenue M T adv w ∂Measure.pi F) +
        ∫ z, G z ∂(Measure.pi F).prod (Measure.pi F) := by
    calc
      _ = ∫ w, selectedRevenue M T adv w + ∑ x, guardedSurplus M T adv x w (w x)
          ∂Measure.pi F := integral_congr_ae
        (Filter.Eventually.of_forall (reward_accounting M T adv hadv))
      _ = _ := by rw [integral_add hrevI hown, total_surplus_resampling M T adv hadv F hFi]
  change O / 2 ≤ ∫ w, wt w (A w) ∂Measure.pi F
  rw [hdecomp, hrev]
  change (∫ w, R w ∂Measure.pi F) - (∫ w, R w ∂Measure.pi F) / 2 ≤ _ at hlow
  linarith

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.ExpectedReward

-- BEGIN MPProof.ForcedExchange
section

namespace MatroidProphetKW.Single.MPFresh

open Set

theorem basis_exchange_outside {α : Type*} (M : Matroid α) {D I : Set α} (hD : M.IsBase D)
    {e : α} (heE : e ∈ M.E) (heD : e ∉ D) (hecl : e ∉ M.closure I) :
    ∃ f ∈ D \ I, M.IsBase (insert e (D \ {f})) := by
  classical
  have hcD : e ∈ M.closure D := by rw [hD.closure_eq]; exact heE
  have hC := hD.indep.fundCircuit_isCircuit hcD heD
  have hex : ∃ f ∈ M.fundCircuit e D \ {e}, f ∉ M.closure I := by
    by_contra hh
    push Not at hh
    have hs : M.fundCircuit e D \ {e} ⊆ M.closure I := fun f hf => hh f hf
    have hc := M.closure_subset_closure hs
    rw [M.closure_closure] at hc
    exact hecl (hc (hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit e D)))
  obtain ⟨f, hfC, hfcl⟩ := hex
  have hfD : f ∈ D := (M.fundCircuit_subset_insert e D hfC.1).resolve_left (by simpa using hfC.2)
  have hfI : f ∉ I := fun hf => hfcl (M.mem_closure_of_mem' hf (hD.subset_ground hfD))
  have hef : e ≠ f := by simpa [ne_comm] using hfC.2
  have hind : M.Indep (insert e (D \ {f})) := by
    simpa only [Set.insert_sdiff_singleton_comm hef] using
      (hD.indep.mem_fundCircuit_iff hcD heD).mp hfC.1
  exact ⟨f, ⟨hfD, hfI⟩, hD.exchange_isBase_of_indep heD hind⟩

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.ForcedExchange

-- BEGIN MPProof.CompletionReplace
section

namespace MatroidProphetKW.Single.MPFresh

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem completion_replace (M : Matroid α) (A R : Finset α)
    (hR : R ∈ completions M A) (e f : α) (he : e ∉ A ∪ R) (hf : f ∈ R)
    (hb : M.IsBase (↑(insert e ((A ∪ R).erase f)) : Set α)) :
    insert e (R.erase f) ∈ completions M A := by
  classical
  have hd := ((mem_completions M A R).mp hR).1
  have hfA : f ∉ A := fun hx => Finset.disjoint_left.mp hd hx hf
  have heA : e ∉ A := fun hx => he (Finset.mem_union_left R hx)
  apply (mem_completions M A _).2
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hxR
    rcases Finset.mem_insert.mp hxR with hxe | hxR
    · exact heA (hxe ▸ hx)
    · exact Finset.disjoint_left.mp hd hx (Finset.mem_erase.mp hxR).2
  · have hu : A ∪ insert e (R.erase f) = insert e ((A ∪ R).erase f) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
      aesop
    rw [hu]
    exact hb

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.CompletionReplace

-- BEGIN MPProof.WeightLayers
section

noncomputable section
namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in
def levelSet (w : α → ℝ) (t : ℝ) : Finset α :=
  Finset.univ.filter (fun x => 0 < t ∧ t ≤ w x)

omit [DecidableEq α] in
theorem mem_levelSet (w : α → ℝ) (t : ℝ) (x : α) :
    x ∈ levelSet w t ↔ 0 < t ∧ t ≤ w x := by classical simp [levelSet]

theorem level_count_sum (w : α → ℝ) (R : Finset α) (t : ℝ) :
    ((R ∩ levelSet w t).card : ℝ) = ∑ x ∈ R, (Set.Ioc 0 (w x)).indicator (fun _ => (1 : ℝ)) t := by
  classical
  rw [show R ∩ levelSet w t = R.filter (fun x => 0 < t ∧ t ≤ w x) by ext x; simp [levelSet]]
  simp only [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : 0 < t ∧ t ≤ w x
  · simp [h, Set.indicator, Set.mem_Ioc]
  · simp [h, Set.indicator, Set.mem_Ioc]

theorem integrable_level_indicator (a : ℝ) :
    Integrable ((Set.Ioc 0 a).indicator (fun _ => (1 : ℝ))) volume := by
  apply (integrable_indicator_iff measurableSet_Ioc).2
  exact integrableOn_const (μ := volume) (s := Set.Ioc 0 a) (C := (1 : ℝ)) measure_Ioc_lt_top.ne

theorem integral_level_indicator (a : ℝ) (ha : 0 ≤ a) :
    (∫ t : ℝ, (Set.Ioc 0 a).indicator (fun _ => (1 : ℝ)) t) = a := by
  rw [integral_indicator measurableSet_Ioc, setIntegral_const]
  simp [ha]

theorem integrable_level_count (w : α → ℝ) (R : Finset α) :
    Integrable (fun t : ℝ => ((R ∩ levelSet w t).card : ℝ)) volume := by
  simp_rw [level_count_sum]
  exact integrable_finsetSum _ (fun x _ => integrable_level_indicator (w x))

theorem wt_eq_integral_level_count (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (R : Finset α) :
    wt w R = ∫ t : ℝ, ((R ∩ levelSet w t).card : ℝ) := by
  simp_rw [level_count_sum]
  rw [integral_finsetSum _ (fun x _ => integrable_level_indicator (w x))]
  simp_rw [integral_level_indicator _ (hw _)]
  rfl

end MatroidProphetKW.Single.MPFresh
end
end
-- END MPProof.WeightLayers

-- BEGIN MPProof.CompletionProfile
section

noncomputable section
namespace MatroidProphetKW.Single.MPFresh

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem optimal_completion_profile (M : Matroid α) (hE : M.E = Set.univ)
    (A R : Finset α) (w : α → ℝ) (hR : R ∈ completions M A)
    (hmax : ∀ Q ∈ completions M A, wt w Q ≤ wt w R) (t : ℝ) :
    M.IsBasis (↑(A ∪ (R ∩ levelSet w t)) : Set α) (↑(A ∪ levelSet w t) : Set α) := by
  classical
  have hD := ((mem_completions M A R).mp hR).2
  let I := A ∪ (R ∩ levelSet w t)
  have hID : I ⊆ A ∪ R := by intro x hx; simp only [I, Finset.mem_union, Finset.mem_inter] at hx ⊢; tauto
  have hi : M.Indep (I : Set α) := hD.indep.subset hID
  apply hi.isBasis_of_subset_of_subset_closure
  · intro x hx
    change x ∈ A ∪ (R ∩ levelSet w t) at hx
    change x ∈ A ∪ levelSet w t
    simp only [Finset.mem_union, Finset.mem_inter] at hx ⊢
    tauto
  intro e he
  by_contra hecl
  have heI : e ∉ I := fun hx => hecl (M.mem_closure_of_mem hx)
  have heA : e ∉ A := fun hx => heI (Finset.mem_union_left _ hx)
  have heS : e ∈ levelSet w t := (Finset.mem_union.mp he).resolve_left heA
  have heD : e ∉ A ∪ R := by
    intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact heA hx
    · exact heI (Finset.mem_union_right A (Finset.mem_inter.mpr ⟨hx, heS⟩))
  obtain ⟨f, hf, hb⟩ := basis_exchange_outside M hD (by rw [hE]; trivial) heD hecl
  have hfD : f ∈ A ∪ R := hf.1
  have hfI : f ∉ I := hf.2
  have hfA : f ∉ A := fun hx => hfI (Finset.mem_union_left _ hx)
  have hfR : f ∈ R := (Finset.mem_union.mp hfD).resolve_left hfA
  have hfS : f ∉ levelSet w t := fun hx => hfI (Finset.mem_union_right A (Finset.mem_inter.mpr ⟨hfR, hx⟩))
  have hnew : M.IsBase (↑(insert e ((A ∪ R).erase f)) : Set α) := by simpa using hb
  have hQ := completion_replace M A R hR e f heD hfR hnew
  have hw := hmax _ hQ
  have heR : e ∉ R := fun hx => heD (Finset.mem_union_right A hx)
  rw [wt_insert _ _ _ (by simp [heR]), wt_erase _ _ _ hfR] at hw
  have het := (mem_levelSet w t e).mp heS
  have hft : w f < t := by
    apply lt_of_not_ge
    intro hh
    exact hfS ((mem_levelSet w t f).mpr ⟨het.1, hh⟩)
  linarith

end MatroidProphetKW.Single.MPFresh
end
end
-- END MPProof.CompletionProfile

-- BEGIN MPProof.RankBasics
section

noncomputable section
namespace MatroidProphetKW.Single.MPFresh

variable {α : Type*} [Fintype α] [DecidableEq α]

def finRank (M : Matroid α) (S : Finset α) : ℕ := (M.eRk (S : Set α)).toNat

omit [Fintype α] [DecidableEq α] in
theorem basis_card_eq_rank (M : Matroid α) (I S : Finset α)
    (hI : M.IsBasis (I : Set α) (S : Set α)) : I.card = finRank M S := by
  have h := congrArg ENat.toNat hI.encard_eq_eRk
  simpa [finRank] using h

omit [Fintype α] [DecidableEq α] in
theorem indep_card_eq_rank (M : Matroid α) (I : Finset α)
    (hI : M.Indep (I : Set α)) : I.card = finRank M I :=
  basis_card_eq_rank M I I hI.isBasis_self

omit [Fintype α] in
theorem rank_insert_of_mem_closure (M : Matroid α) (S : Finset α) (e : α)
    (he : e ∈ M.closure (S : Set α)) : finRank M (insert e S) = finRank M S := by
  unfold finRank
  rw [Finset.coe_insert, ← M.eRk_closure_eq (insert e (S : Set α)),
    Matroid.closure_insert_eq_of_mem_closure he, M.eRk_closure_eq]

theorem rank_insert_of_notMem_closure (M : Matroid α) (S : Finset α) (e : α)
    (heE : e ∈ M.E) (he : e ∉ M.closure (S : Set α)) :
    finRank M (insert e S) = finRank M S + 1 := by
  unfold finRank
  rw [Finset.coe_insert, Matroid.eRk_insert_eq_add_one ⟨heE, he⟩]
  exact ENat.toNat_add (M.isRkFinite_set _).eRk_lt_top.ne (by simp)

end MatroidProphetKW.Single.MPFresh
end
end
-- END MPProof.RankBasics

-- BEGIN MPProof.ResidualProfile
section

noncomputable section
namespace MatroidProphetKW.Single.MPFresh
open MeasureTheory
variable {α : Type*} [Fintype α] [DecidableEq α]

def residualProfile (M : Matroid α) (A : Finset α) (w : α → ℝ) (t : ℝ) : ℝ :=
  ((Rset M A w ∩ levelSet w t).card : ℝ)

theorem residual_profile_rank (M : Matroid α) (hE : M.E = Set.univ)
    (A : Finset α) (hA : M.Indep (A : Set α)) (w : α → ℝ) (t : ℝ) :
    (A.card : ℝ) + residualProfile M A w t = (finRank M (A ∪ levelSet w t) : ℝ) := by
  have hr := ((remCands_iff M A _ w).mp (Rset_mem M A w hA)).1
  have hb := optimal_completion_profile M hE A (Rset M A w) w hr
    (Rset_maximal M A w hA) t
  have hc := basis_card_eq_rank M _ _ hb
  have hd : Disjoint A (Rset M A w ∩ levelSet w t) :=
    ((mem_completions M A _).mp hr).1.mono_right Finset.inter_subset_left
  rw [Finset.card_union_of_disjoint hd] at hc
  unfold residualProfile
  exact_mod_cast hc

theorem integrable_residualProfile (M : Matroid α) (A : Finset α) (w : α → ℝ) :
    Integrable (residualProfile M A w) volume := integrable_level_count w _

theorem residual_eq_integral_profile (M : Matroid α) (A : Finset α) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) : residual M A w = ∫ t, residualProfile M A w t :=
  wt_eq_integral_level_count w hw _

end MatroidProphetKW.Single.MPFresh
end
end
-- END MPProof.ResidualProfile

-- BEGIN MPProof.ResidualMarginal
section

noncomputable section
namespace MatroidProphetKW.Single.MPFresh
open MeasureTheory
variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in
theorem profile_loss_eq (M : Matroid α) (hE : M.E = Set.univ)
    (A : Finset α) (x : α) (hx : x ∉ A)
    (hi : M.Indep (↑(insert x A) : Set α)) (w : α → ℝ) (t : ℝ) :
    residualProfile M A w t - residualProfile M (insert x A) w t =
      if x ∈ M.closure (↑(A ∪ levelSet w t) : Set α) then 1 else 0 := by
  classical
  have hA : M.Indep (A : Set α) := hi.subset (by intro y hy; exact Finset.mem_insert_of_mem hy)
  have ha := residual_profile_rank M hE A hA w t
  have hb := residual_profile_rank M hE (insert x A) hi w t
  rw [Finset.card_insert_of_notMem hx, Nat.cast_add, Nat.cast_one,
    Finset.insert_union] at hb
  by_cases hc : x ∈ M.closure (↑(A ∪ levelSet w t) : Set α)
  · rw [if_pos hc]
    rw [rank_insert_of_mem_closure M _ x hc] at hb
    linarith
  · rw [if_neg hc]
    rw [rank_insert_of_notMem_closure M _ x (by rw [hE]; trivial) hc,
      Nat.cast_add, Nat.cast_one] at hb
    linarith

theorem profile_loss_mono (M : Matroid α) (hE : M.E = Set.univ)
    (A B : Finset α) (hAB : A ⊆ B) (x : α) (hx : x ∉ B)
    (hi : M.Indep (↑(insert x B) : Set α)) (w : α → ℝ) (t : ℝ) :
    residualProfile M A w t - residualProfile M (insert x A) w t ≤
      residualProfile M B w t - residualProfile M (insert x B) w t := by
  classical
  have hiA : M.Indep (↑(insert x A) : Set α) := hi.subset (Finset.insert_subset_insert x hAB)
  rw [profile_loss_eq M hE A x (fun h => hx (hAB h)) hiA,
    profile_loss_eq M hE B x hx hi]
  by_cases ha : x ∈ M.closure (↑(A ∪ levelSet w t) : Set α)
  · have hb : x ∈ M.closure (↑(B ∪ levelSet w t) : Set α) :=
      M.closure_mono (Finset.union_subset_union_left hAB) ha
    rw [if_pos ha, if_pos hb]
  · simp only [if_neg ha]
    split_ifs <;> norm_num

theorem residual_loss_mono (M : Matroid α) (hE : M.E = Set.univ)
    (A B : Finset α) (hAB : A ⊆ B) (x : α) (hx : x ∉ B)
    (hi : M.Indep (↑(insert x B) : Set α)) (w : α → ℝ) (hw : ∀ y, 0 ≤ w y) :
    residual M A w - residual M (insert x A) w ≤
      residual M B w - residual M (insert x B) w := by
  simp_rw [residual_eq_integral_profile M _ w hw]
  rw [← integral_sub (integrable_residualProfile M A w) (integrable_residualProfile M (insert x A) w),
    ← integral_sub (integrable_residualProfile M B w) (integrable_residualProfile M (insert x B) w)]
  exact integral_mono ((integrable_residualProfile M A w).sub (integrable_residualProfile M (insert x A) w))
    ((integrable_residualProfile M B w).sub (integrable_residualProfile M (insert x B) w))
    (profile_loss_mono M hE A B hAB x hx hi w)

theorem residual_loss_nonneg (M : Matroid α) (hE : M.E = Set.univ)
    (A : Finset α) (x : α) (w : α → ℝ) (hw : ∀ y, 0 ≤ w y) :
    0 ≤ residual M A w - residual M (insert x A) w := by
  classical
  by_cases hx : x ∈ A
  · simp [Finset.insert_eq_of_mem hx]
  by_cases hi : M.Indep (↑(insert x A) : Set α)
  · rw [residual_eq_integral_profile M A w hw, residual_eq_integral_profile M (insert x A) w hw,
      ← integral_sub (integrable_residualProfile M A w) (integrable_residualProfile M (insert x A) w)]
    apply integral_nonneg
    intro t
    change 0 ≤ residualProfile M A w t - residualProfile M (insert x A) w t
    rw [profile_loss_eq M hE A x hx hi w t]
    split_ifs <;> norm_num
  · rw [residual_eq_zero_of_not_indep M (insert x A) hi w, sub_zero]
    exact residual_nonneg M A w hw

end MatroidProphetKW.Single.MPFresh
end
end
-- END MPProof.ResidualMarginal

-- BEGIN MPProof.ResidualEmpty
section

noncomputable section
namespace MatroidProphetKW.Single.MPFresh
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem wt_mono_nonneg (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (A B : Finset α)
    (hAB : A ⊆ B) : wt w A ≤ wt w B :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x _ _ => hw x)

theorem residual_empty_eq_optW (M : Matroid α) (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    residual M ∅ w = optW M w := by
  classical
  have hi : M.Indep (↑(∅ : Finset α) : Set α) := by simp
  have hr := ((remCands_iff M ∅ _ w).mp (Rset_mem M ∅ w hi)).1
  have hb := ((mem_completions M ∅ _).mp hr).2
  apply le_antisymm
  · exact Finset.le_sup' (wt w) (by simpa [indepSets] using hb.indep)
  · apply Finset.sup'_le
    intro A hA
    have hAi : M.Indep (A : Set α) := by simpa [indepSets] using hA
    obtain ⟨B, hB, hAB⟩ := hAi.exists_isBase_superset
    let Q : Finset α := (Set.toFinite B).toFinset
    have hQ : Q ∈ completions M ∅ := by
      simp only [mem_completions, Finset.disjoint_empty_left, Finset.empty_union, true_and]
      simpa [Q] using hB
    apply (wt_mono_nonneg w hw A Q (by simpa [Q] using hAB)).trans
    exact Rset_maximal M ∅ w hi Q hQ

end MatroidProphetKW.Single.MPFresh
end
end
-- END MPProof.ResidualEmpty

-- BEGIN MPProof.ExpectedResidual
section

noncomputable section
namespace MatroidProphetKW.Single.MPFresh
open MeasureTheory
variable {α : Type*} [Fintype α] [DecidableEq α]

def expectedResidual (M : Matroid α) (F : α → Measure ℝ) (A : Finset α) : ℝ :=
  ∫ w, residual M A w ∂Measure.pi F

theorem kwT_eq_expectedResidual (M : Matroid α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)] (hFi : ∀ x, Integrable id (F x))
    (A : Finset α) (x : α) :
    kwT M F A x = (1/2) * (expectedResidual M F A - expectedResidual M F (insert x A)) := by
  change (1/2) * (∫ w, residual M A w - residual M (insert x A) w ∂Measure.pi F) = _
  unfold expectedResidual
  rw [integral_sub (integrable_residual M A F hFi) (integrable_residual M (insert x A) F hFi)]

theorem expectedResidual_nonneg (M : Matroid α) (F : α → Measure ℝ)
    (hw : ∀ᵐ w ∂Measure.pi F, ∀ x, 0 ≤ w x) (A : Finset α) :
    0 ≤ expectedResidual M F A :=
  integral_nonneg_of_ae (hw.mono (fun w h => residual_nonneg M A w h))

theorem expectedResidual_empty (M : Matroid α) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)]
    (hw : ∀ᵐ w ∂Measure.pi F, ∀ x, 0 ≤ w x) : expectedResidual M F ∅ = OPT M F := by
  apply integral_congr_ae
  exact hw.mono (fun w h => residual_empty_eq_optW M w h)

theorem kwT_nonneg (M : Matroid α) (hE : M.E = Set.univ) (F : α → Measure ℝ)
    [∀ x, IsProbabilityMeasure (F x)]
    (hw : ∀ᵐ w ∂Measure.pi F, ∀ x, 0 ≤ w x) (A : Finset α) (x : α) :
    0 ≤ kwT M F A x := by
  apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  exact integral_nonneg_of_ae (hw.mono (fun w h => residual_loss_nonneg M hE A x w h))

end MatroidProphetKW.Single.MPFresh
end
end
-- END MPProof.ExpectedResidual

-- BEGIN MPProof.ResidualBudget
section

noncomputable section
namespace MatroidProphetKW.Single.MPFresh
open MeasureTheory
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem residual_loss_sum_le (M : Matroid α) (hE : M.E = Set.univ)
    (A V : Finset α) (hd : Disjoint A V) (hi : M.Indep (↑(A ∪ V) : Set α))
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x ∈ V, (residual M A w - residual M (insert x A) w)) ≤
      residual M A w - residual M (A ∪ V) w := by
  classical
  induction V using Finset.induction_on generalizing A with
  | empty => simp
  | @insert x V hx ih =>
    have hxA : x ∉ A := fun h => Finset.disjoint_left.mp hd h (Finset.mem_insert_self _ _)
    have hd' : Disjoint (insert x A) V := by
      rw [Finset.disjoint_left]
      intro y hy hyV
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx hyV
      · exact Finset.disjoint_left.mp hd hy (Finset.mem_insert_of_mem hyV)
    have heq : insert x A ∪ V = A ∪ insert x V := by ext y; simp
    have hi' : M.Indep (↑(insert x A ∪ V) : Set α) := by rw [heq]; exact hi
    have hs := ih (insert x A) hd' hi'
    have hm : (∑ y ∈ V, (residual M A w - residual M (insert y A) w)) ≤
        ∑ y ∈ V, (residual M (insert x A) w - residual M (insert y (insert x A)) w) := by
      apply Finset.sum_le_sum
      intro y hy
      apply residual_loss_mono M hE A (insert x A) (Finset.subset_insert _ _) y
      · intro hh
        exact Finset.disjoint_left.mp hd' hh hy
      · apply hi'.subset
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact Finset.mem_union_right _ hy
        · exact Finset.mem_union_left _ hz
      · exact hw
    rw [heq] at hs
    rw [Finset.sum_insert hx]
    linarith

theorem residual_earlier_budget (M : Matroid α) (hE : M.E = Set.univ)
    (A V : Finset α) (hd : Disjoint A V) (hi : M.Indep (↑(A ∪ V) : Set α))
    (B : α → Finset α) (hB : ∀ x ∈ V, B x ⊆ A)
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x ∈ V, (residual M (B x) w - residual M (insert x (B x)) w)) ≤ residual M A w := by
  have hs : (∑ x ∈ V, (residual M (B x) w - residual M (insert x (B x)) w)) ≤
      ∑ x ∈ V, (residual M A w - residual M (insert x A) w) := by
    apply Finset.sum_le_sum
    intro x hx
    apply residual_loss_mono M hE (B x) A (hB x hx) x
    · exact fun h => Finset.disjoint_left.mp hd h hx
    · apply hi.subset
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_union_right _ hx
      · exact Finset.mem_union_left _ hy
    · exact hw
  have ht := residual_loss_sum_le M hE A V hd hi w hw
  have hn := residual_nonneg M (A ∪ V) w hw
  linarith

theorem kwT_earlier_budget (M : Matroid α) (hE : M.E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hFi : ∀ x, Integrable id (F x))
    (hw : ∀ᵐ w ∂Measure.pi F, ∀ x, 0 ≤ w x)
    (A V : Finset α) (hd : Disjoint A V) (hi : M.Indep (↑(A ∪ V) : Set α))
    (B : α → Finset α) (hB : ∀ x ∈ V, B x ⊆ A) :
    (∑ x ∈ V, kwT M F (B x) x) ≤ expectedResidual M F A / 2 := by
  have hiL : ∀ x ∈ V, Integrable (fun w => residual M (B x) w - residual M (insert x (B x)) w) (Measure.pi F) :=
    fun x _ => (integrable_residual M (B x) F hFi).sub (integrable_residual M (insert x (B x)) F hFi)
  have hh := integral_mono_ae (integrable_finsetSum V hiL) (integrable_residual M A F hFi)
    (hw.mono (fun w h => residual_earlier_budget M hE A V hd hi B hB w h))
  rw [integral_finsetSum V hiL] at hh
  have he : (∑ x ∈ V, kwT M F (B x) x) = (1/2) *
      ∑ x ∈ V, ∫ w, (residual M (B x) w - residual M (insert x (B x)) w) ∂Measure.pi F := by
    rw [Finset.mul_sum]
    rfl
  rw [he]
  change _ ≤ (∫ w, residual M A w ∂Measure.pi F) / 2
  linarith

end MatroidProphetKW.Single.MPFresh
end
end
-- END MPProof.ResidualBudget

-- BEGIN MPProof.NativeConclusion
section

namespace MatroidProphetKW.Single.MPFresh

open MeasureTheory

theorem native_main_theorem {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF0 : ∀ x, F x (Set.Iio 0) = 0) (hFi : ∀ x, Integrable id (F x))
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv) :
    (1 / 2) * OPT M F ≤ ∫ w, wt w (run M (kwThr M F) (advOrder adv w) w) ∂(Measure.pi F) := by
  have hw := nonnegative_weights_ae F hF0
  have hT : ∀ (A : Finset α) (x : α), M.Indep (A : Set α) → x ∉ A →
      M.Indep (↑(insert x A) : Set α) →
      kwT M F A x = expectedResidual M F A / 2 - expectedResidual M F (insert x A) / 2 := by
    intro A x _ _ _
    rw [kwT_eq_expectedResidual M F hFi]
    ring
  have hh := half_opt_of_actual_budgets M (kwT M F) adv hadv F hFi (OPT M F)
    (fun w => by
      have hr := selectedRevenue_potential M (kwT M F)
        (fun A => expectedResidual M F A / 2) hT adv hadv w
      rw [expectedResidual_empty M F hw] at hr
      exact hr)
    (fun w V hd hi => kwT_earlier_budget M hE F hFi hw _ V hd hi
      (fun x => beforeSet M (kwT M F) adv w x)
      (fun x _ => beforeSet_subset_final M (kwT M F) adv w x))
  calc
    (1 / 2) * OPT M F = OPT M F / 2 := by ring
    _ ≤ _ := hh

end MatroidProphetKW.Single.MPFresh
end
-- END MPProof.NativeConclusion

-- BEGIN MPProof.FinalRoot
section

namespace MatroidProphetKW.Single

open MeasureTheory

/-- Main theorem (Kleinberg–Weinberg, arXiv:1201.4764v1, §3, p. 4; Proposition 1, p. 6, with
`α = 2`; algorithm (9), p. 7): against every online weight-adaptive adversary, the algorithm of
§3.3 — select `x_i` iff `A_{i−1} ∪ {x_i} ∈ ℐ` and `w(x_i) ≥ ½ E[w′(R(A_{i−1})) − w′(R(A_{i−1} ∪ {x_i}))]`
— earns `E[w(A)] ≥ ½ · OPT`. -/
theorem main_theorem {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF0 : ∀ x, F x (Set.Iio 0) = 0) (hFi : ∀ x, Integrable id (F x))
    (adv : List α → (α → ℝ) → α) (hadv : IsAdversary adv) :
    (1 / 2) * OPT M F ≤ ∫ w, wt w (run M (kwThr M F) (advOrder adv w) w) ∂(Measure.pi F) := by
  exact MPFresh.native_main_theorem M hE F hF0 hFi adv hadv

end MatroidProphetKW.Single
end
-- END MPProof.FinalRoot

open MeasureTheory
theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ)
    (F : α → Measure ℝ) [∀ x, IsProbabilityMeasure (F x)]
    (hF0 : ∀ x, F x (Set.Iio 0) = 0) (hFi : ∀ x, Integrable id (F x))
    (adv : List α → (α → ℝ) → α) (hadv : MatroidProphetKW.Single.IsAdversary adv) :
    (1 / 2) * MatroidProphetKW.Single.OPT M F ≤ ∫ w, MatroidProphetKW.Single.wt w (MatroidProphetKW.Single.run M (MatroidProphetKW.Single.kwThr M F) (MatroidProphetKW.Single.advOrder adv w) w) ∂(Measure.pi F) := by
  exact MatroidProphetKW.Single.main_theorem M hE F hF0 hFi adv hadv
