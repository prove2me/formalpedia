-- Prove2me | solution 1 for MFOTLMon.Monitor.relations_built_correct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T21:47:55.061029+00:00
-- url     : https://prove2.me/submissions/8a88b2e4-6688-41a2-9567-c41c5000de0b

import Definitions.Def_MFOTLMon_Monitor_Automatic
import Definitions.Def_MFOTLMon_Monitor_Constructions
import Definitions.Def_MFOTLMon_Monitor_Algorithm

namespace MFOTLMon.Monitor

open Classical

variable {α β : Type}

theorem language_regular_empty : Language.IsRegular (0 : Language α) := by
  let M : DFA α Unit := ⟨fun s _ ↦ s, (), ∅⟩
  exact ⟨Unit, inferInstance, M, rfl⟩

theorem language_regular_univ : Language.IsRegular (⊤ : Language α) := by
  let M : DFA α Unit := ⟨fun s _ ↦ s, (), Set.univ⟩
  exact ⟨Unit, inferInstance, M, rfl⟩

theorem language_regular_preimage_filterMap (f : α → Option β) {L : Language β}
    (hL : L.IsRegular) : Language.IsRegular (List.filterMap f ⁻¹' L : Language α) := by
  obtain ⟨σ, hσ, M, hM⟩ := hL
  let N : DFA α σ :=
    { step := fun s a ↦ match f a with
        | none => s
        | some b => M.step s b
      start := M.start
      accept := M.accept }
  have heval (w : List α) (s : σ) : N.evalFrom s w = M.evalFrom s (w.filterMap f) := by
    induction w generalizing s with
    | nil => rfl
    | cons a w ih =>
      cases h : f a <;> simp [DFA.evalFrom_cons, N, h, ih]
  refine ⟨σ, hσ, N, ?_⟩
  ext w
  change N.evalFrom N.start w ∈ N.accept ↔ w.filterMap f ∈ L
  rw [heval]
  change M.evalFrom M.start (w.filterMap f) ∈ M.accept ↔ _
  rw [← hM]
  rfl

theorem language_regular_preimage_map (f : α → β) {L : Language β}
    (hL : L.IsRegular) : Language.IsRegular (List.map f ⁻¹' L : Language α) := by
  simpa only [List.filterMap_eq_map'] using
    language_regular_preimage_filterMap (fun a ↦ some (f a)) hL

theorem language_regular_image_filterMap (f : α → Option β) {L : Language α}
    (hL : L.IsRegular) : Language.IsRegular (List.filterMap f '' L : Language β) := by
  classical
  obtain ⟨σ, hσ, M, hM⟩ := hL
  let N : εNFA β σ :=
    { step := fun s b ↦ {t | ∃ a, f a = b ∧ M.step s a = t}
      start := {M.start}
      accept := M.accept }
  have hpath (v : List (Option β)) (s t : σ) :
      N.IsPath s t v ↔ ∃ u : List α, u.map f = v ∧ M.evalFrom s u = t := by
    induction v generalizing s t with
    | nil =>
      simp only [εNFA.isPath_nil]
      constructor
      · intro h
        exact ⟨[], rfl, h⟩
      · rintro ⟨u, hu, ht⟩
        have : u = [] := List.map_eq_nil_iff.mp hu
        simpa [this] using ht
    | cons b v ih =>
      constructor
      · intro hp
        cases hp with
        | cons q _ _ _ _ hq hp =>
          obtain ⟨a, ha, hstep⟩ := hq
          obtain ⟨u, hu, hrun⟩ := (ih q t).mp hp
          refine ⟨a :: u, by simp only [List.map_cons, ha, hu], ?_⟩
          simpa only [DFA.evalFrom_cons, hstep] using hrun
      · rintro ⟨u, hu, hrun⟩
        cases u with
        | nil => simp at hu
        | cons a u =>
          obtain ⟨ha, hu⟩ := List.cons.inj hu
          exact .cons (M.step s a) s t b v ⟨a, ha, rfl⟩
            ((ih (M.step s a) t).mpr ⟨u, hu, hrun⟩)
  have hreduce (u : List α) : (u.map f).reduceOption = u.filterMap f := by
    induction u with
    | nil => rfl
    | cons a u ih => cases h : f a <;> simp [h, ih]
  refine ⟨Set σ, inferInstance, N.toNFA.toDFA, ?_⟩
  rw [NFA.toDFA_correct, εNFA.toNFA_correct]
  ext v
  rw [N.mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨s, t, v', hs, ht, hv', hp⟩
    have hs' : s = M.start := hs
    obtain ⟨u, hu, hrun⟩ := (hpath v' s t).mp hp
    refine ⟨u, ?_, ?_⟩
    · rw [← hM]
      change M.evalFrom M.start u ∈ M.accept
      simpa only [← hs', hrun] using ht
    · rw [← hreduce, hu, hv']
  · rintro ⟨u, hu, rfl⟩
    refine ⟨M.start, M.evalFrom M.start u, u.map f, rfl, ?_, hreduce u, ?_⟩
    · rw [← hM] at hu
      exact hu
    · exact (hpath (u.map f) _ _).mpr ⟨u, rfl, rfl⟩

theorem regular_empty {Γ : Type} [Fintype Γ] (rep : DomainRep Γ) (n : ℕ) :
    RegularRel rep n ∅ := by
  have h : relLang rep.L rep.ν n ∅ = (0 : Language (Fin n → Option Γ)) := by
    ext w
    simp [relLang, Language.zero_def]
  rw [RegularRel, h]
  exact language_regular_empty

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor

open Classical

variable {Γ : Type}

/-- A track consists of a word followed by padding, with no letters after padding starts. -/
def PaddedWord : List (Option Γ) → Prop
  | [] => True
  | none :: w => ∀ a ∈ w, a = none
  | some _ :: w => PaddedWord w

theorem paddedWord_replicate (n : ℕ) : PaddedWord (List.replicate n (none : Option Γ)) := by
  cases n with
  | zero => trivial
  | succ n =>
      intro a ha
      exact (List.mem_replicate.mp ha).2

theorem paddedWord_map_append (u : List Γ) (n : ℕ) :
    PaddedWord (u.map some ++ List.replicate n none) := by
  induction u with
  | nil => exact paddedWord_replicate n
  | cons a u ih => exact ih

theorem paddedWord_iff (w : List (Option Γ)) :
    PaddedWord w ↔ ∃ (u : List Γ) (n : ℕ), w = u.map some ++ List.replicate n none := by
  constructor
  · intro hw
    induction w with
    | nil => exact ⟨[], 0, rfl⟩
    | cons a w ih =>
      cases a with
      | none =>
          have ht : w = List.replicate w.length none := List.eq_replicate_iff.mpr ⟨rfl, hw⟩
          refine ⟨[], w.length + 1, ?_⟩
          simpa only [List.map_nil, List.nil_append, List.replicate_succ] using
            congrArg (List.cons none) ht
      | some a =>
          obtain ⟨u, n, hu⟩ := ih hw
          exact ⟨a :: u, n, by simp [hu]⟩
  · rintro ⟨u, n, rfl⟩
    exact paddedWord_map_append u n

theorem language_regular_paddedWord :
    Language.IsRegular ({w | PaddedWord w} : Language (Option Γ)) := by
  let M : DFA (Option Γ) (Option Bool) :=
    { step := fun s a ↦ match s, a with
        | none, _ => none
        | some false, some _ => some false
        | some false, none => some true
        | some true, none => some true
        | some true, some _ => none
      start := some false
      accept := {s | s.isSome} }
  have hdead (w : List (Option Γ)) : M.evalFrom none w = none := by
    induction w with
    | nil => rfl
    | cons a w ih => exact ih
  have hlocked (w : List (Option Γ)) :
      M.evalFrom (some true) w ∈ M.accept ↔ ∀ a ∈ w, a = none := by
    induction w with
    | nil => simp [M, DFA.evalFrom_nil]
    | cons a w ih =>
        cases a <;> simp [DFA.evalFrom_cons, M, hdead, ih]
  have hstart (w : List (Option Γ)) : M.evalFrom (some false) w ∈ M.accept ↔ PaddedWord w := by
    induction w with
    | nil => simp [M, PaddedWord, DFA.evalFrom_nil]
    | cons a w ih =>
        cases a <;> simp [DFA.evalFrom_cons, M, hlocked, PaddedWord, ih]
  refine ⟨Option Bool, inferInstance, M, ?_⟩
  ext w
  exact hstart w

theorem language_regular_padded {L : Language Γ} (hL : L.IsRegular) :
    Language.IsRegular
      ({w : List (Option Γ) | PaddedWord w ∧ w.reduceOption ∈ L} : Language (Option Γ)) := by
  have he : ({w : List (Option Γ) | PaddedWord w ∧ w.reduceOption ∈ L} : Language (Option Γ)) =
      ({w | PaddedWord w} : Language (Option Γ)) ⊓
        (List.filterMap id ⁻¹' L : Language (Option Γ)) := by
    ext w
    rfl
  rw [he]
  exact language_regular_paddedWord.inf (language_regular_preimage_filterMap id hL)

theorem optionPad_eq (u : List Γ) (n : ℕ) (h : u.length ≤ n) :
    (List.ofFn (n := n) fun p ↦ u[(p : ℕ)]?) =
      u.map some ++ List.replicate (n - u.length) none := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_map, List.length_replicate]
    omega
  · intro j hj hj'
    by_cases hju : j < u.length
    · simp [hju]
    · have hge : u.length ≤ j := by omega
      simp [List.getElem_append, hju]

theorem conv_track {n : ℕ} (ws : Fin n → List Γ) (i : Fin n) :
    (conv ws).map (fun c ↦ c i) =
      (ws i).map some ++ List.replicate ((conv ws).length - (ws i).length) none := by
  have hlen : (ws i).length ≤ Finset.univ.sup (fun j ↦ (ws j).length) :=
    Finset.le_sup (f := fun j ↦ (ws j).length) (Finset.mem_univ i)
  simpa only [conv, List.map_ofFn, Function.comp_def, List.length_ofFn] using
    optionPad_eq (ws i) _ hlen

theorem conv_track_reduceOption {n : ℕ} (ws : Fin n → List Γ) (i : Fin n) :
    ((conv ws).map (fun c ↦ c i)).reduceOption = ws i := by
  rw [conv_track, List.reduceOption_append, List.reduceOption_replicate_none, List.append_nil]
  change ((ws i).map some).filterMap id = ws i
  simp only [List.filterMap_map, Function.comp_def, id_eq, List.filterMap_some]

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor

open Classical

variable {Γ : Type}

/-- The final column is active, with the empty word allowed. -/
def LastActive {n : ℕ} (w : List (Fin n → Option Γ)) : Prop :=
  match w.getLast? with
  | none => True
  | some c => ∃ i, c i ≠ none

theorem lastActive_iff {n : ℕ} (w : List (Fin n → Option Γ)) :
    LastActive w ↔ w = [] ∨
      ∃ (u : List (Fin n → Option Γ)) (c : Fin n → Option Γ),
        w = u ++ [c] ∧ ∃ i, c i ≠ none := by
  constructor
  · intro h
    cases hl : w.getLast? with
    | none => exact Or.inl (List.getLast?_eq_none_iff.mp hl)
    | some c =>
      obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.mp hl
      exact Or.inr ⟨u, c, hu, by simpa only [LastActive, hl] using h⟩
  · rintro (rfl | ⟨u, c, rfl, hc⟩)
    · trivial
    · simpa only [LastActive, List.getLast?_append, List.getLast?_singleton,
        Option.some_or] using hc

theorem language_regular_lastActive (n : ℕ) :
    Language.IsRegular ({w : List (Fin n → Option Γ) | LastActive w} :
      Language (Fin n → Option Γ)) := by
  let M : DFA (Fin n → Option Γ) Bool :=
    { step := fun _ c ↦ decide (∃ i, c i ≠ none)
      start := true
      accept := {b | b = true} }
  have heval (s : Bool) (w : List (Fin n → Option Γ)) :
      M.evalFrom s w = match w.getLast? with
        | none => s
        | some c => decide (∃ i, c i ≠ none) := by
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w c _ =>
      simp only [DFA.evalFrom_append_singleton, M, List.getLast?_append,
        List.getLast?_singleton, Option.some_or]
  refine ⟨Bool, inferInstance, M, ?_⟩
  ext w
  change M.evalFrom true w = true ↔ LastActive w
  rw [heval]
  cases hl : w.getLast? <;> simp only [LastActive, hl, decide_eq_true_eq]

theorem paddedWord_reconstruct (w : List (Option Γ)) (hw : PaddedWord w) :
    w = w.reduceOption.map some ++ List.replicate (w.length - w.reduceOption.length) none := by
  obtain ⟨u, k, rfl⟩ := (paddedWord_iff w).mp hw
  have hs : (u.map some).reduceOption = u := by
    change (u.map some).filterMap id = u
    simp only [List.filterMap_map, Function.comp_def, id_eq, List.filterMap_some]
  simp [List.reduceOption_append, hs]

theorem paddedWord_length_of_last (w : List (Option Γ)) (hw : PaddedWord w) (a : Γ)
    (hlast : w.getLast? = some (some a)) : w.reduceOption.length = w.length := by
  obtain ⟨u, k, rfl⟩ := (paddedWord_iff w).mp hw
  have hs : (u.map some).reduceOption = u := by
    change (u.map some).filterMap id = u
    simp only [List.filterMap_map, Function.comp_def, id_eq, List.filterMap_some]
  cases k with
  | zero => simp [hs]
  | succ k =>
    simp [List.getLast?_append, List.getLast?_replicate] at hlast

theorem conv_lastActive {n : ℕ} (ws : Fin n → List Γ) : LastActive (conv ws) := by
  cases hl : (conv ws).getLast? with
  | none => simp only [LastActive, hl]
  | some c =>
    rw [LastActive, hl]
    cases n with
    | zero => simp [conv] at hl
    | succ n =>
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
        (fun i : Fin (n + 1) ↦ (ws i).length)
      have hlen : (conv ws).length = (ws i).length := by
        simpa only [conv, List.length_ofFn] using hi
      have ht := congrArg List.getLast? (conv_track ws i)
      simp only [hlen, Nat.sub_self, List.replicate_zero, List.append_nil,
        List.getLast?_map, hl, Option.map_some] at ht
      cases hiLast : (ws i).getLast? with
      | none => simp [hiLast] at ht
      | some a =>
        have he : c i = some a := by
          simpa only [hiLast, Option.map_some, Option.some.injEq] using ht
        exact ⟨i, by rw [he]; exact Option.some_ne_none a⟩

theorem conv_decoded_eq {n : ℕ} (w : List (Fin n → Option Γ))
    (htracks : ∀ i, PaddedWord (w.map (fun c ↦ c i))) (hactive : LastActive w) :
    conv (fun i ↦ (w.map (fun c ↦ c i)).reduceOption) = w := by
  let ws : Fin n → List Γ := fun i ↦ (w.map (fun c ↦ c i)).reduceOption
  have hbound (i : Fin n) : (ws i).length ≤ w.length := by
    simpa only [ws, List.length_map] using
      List.reduceOption_length_le (w.map (fun c ↦ c i))
  have hle : Finset.univ.sup (fun i ↦ (ws i).length) ≤ w.length :=
    Finset.sup_le fun i _ ↦ hbound i
  have hge : w.length ≤ Finset.univ.sup (fun i ↦ (ws i).length) := by
    cases hl : w.getLast? with
    | none =>
      have hw : w = [] := List.getLast?_eq_none_iff.mp hl
      simp only [hw, List.length_nil, Nat.zero_le]
    | some c =>
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ none := by simpa only [LastActive, hl] using hactive
      cases hci : c i with
      | none => exact False.elim (hi hci)
      | some a =>
        have ht : (w.map (fun c ↦ c i)).getLast? = some (some a) := by
          simp only [List.getLast?_map, hl, Option.map_some, hci]
        have he : (ws i).length = w.length := by
          simpa only [ws, List.length_map] using
            paddedWord_length_of_last _ (htracks i) a ht
        have hb : (ws i).length ≤ Finset.univ.sup (fun i ↦ (ws i).length) :=
          Finset.le_sup (f := fun i ↦ (ws i).length) (Finset.mem_univ i)
        omega
  have hlen : (conv ws).length = w.length := by
    simpa only [conv, List.length_ofFn] using le_antisymm hle hge
  have hmap (i : Fin n) : (conv ws).map (fun c ↦ c i) = w.map (fun c ↦ c i) := by
    rw [conv_track, hlen]
    simpa only [ws, List.length_map] using (paddedWord_reconstruct _ (htracks i)).symm
  apply List.ext_getElem hlen
  intro j hj hk
  funext i
  have he := congrArg (fun u : List (Option Γ) ↦ u[j]?) (hmap i)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hk, Option.map_some, Option.some.injEq] at he
  exact he

theorem relLang_univ_iff (L : Language Γ) (ν : List Γ → ℕ) (n : ℕ)
    (w : List (Fin n → Option Γ)) :
    w ∈ relLang L ν n Set.univ ↔
      (∀ i, PaddedWord (w.map (fun c ↦ c i)) ∧
        (w.map (fun c ↦ c i)).reduceOption ∈ L) ∧ LastActive w := by
  constructor
  · rintro ⟨ws, hw, _, rfl⟩
    refine ⟨?_, conv_lastActive ws⟩
    intro i
    constructor
    · rw [conv_track]
      exact paddedWord_map_append _ _
    · rw [conv_track_reduceOption]
      exact hw i
  · rintro ⟨htracks, hactive⟩
    exact ⟨fun i ↦ (w.map (fun c ↦ c i)).reduceOption,
      fun i ↦ (htracks i).2, Set.mem_univ _,
      conv_decoded_eq w (fun i ↦ (htracks i).1) hactive⟩

private theorem valid_regular_forall {ι α : Type} [Fintype ι] (P : ι → Language α)
    (hP : ∀ i, (P i).IsRegular) : Language.IsRegular ({w | ∀ i, w ∈ P i} : Language α) := by
  have hf (s : Finset ι) : Language.IsRegular ({w | ∀ i ∈ s, w ∈ P i} : Language α) := by
    induction s using Finset.induction_on with
    | empty =>
      have he : ({w | ∀ i ∈ (∅ : Finset ι), w ∈ P i} : Language α) = (⊤ : Language α) := by
        ext w
        change (∀ i ∈ (∅ : Finset ι), w ∈ P i) ↔ True
        simp
      rw [he]
      exact language_regular_univ
    | @insert i s hi ih =>
      have he : ({w | ∀ j ∈ insert i s, w ∈ P j} : Language α) =
          P i ⊓ ({w | ∀ j ∈ s, w ∈ P j} : Language α) := by
        ext w
        change (∀ j ∈ insert i s, w ∈ P j) ↔ w ∈ P i ∧ ∀ j ∈ s, w ∈ P j
        simp only [Finset.mem_insert, forall_eq_or_imp]
      rw [he]
      exact (hP i).inf ih
  have huniv : ({w | ∀ i, w ∈ P i} : Language α) =
      ({w | ∀ i ∈ (Finset.univ : Finset ι), w ∈ P i} : Language α) := by
    ext w
    change (∀ i, w ∈ P i) ↔ ∀ i ∈ (Finset.univ : Finset ι), w ∈ P i
    simp
  rw [huniv]
  exact hf Finset.univ

theorem valid_convolution_regular {Γ : Type} [Fintype Γ] (rep : DomainRep Γ) (n : ℕ) :
    (relLang rep.L rep.ν n Set.univ).IsRegular := by
  have htracks :
      Language.IsRegular ({w : List (Fin n → Option Γ) | ∀ i : Fin n,
        PaddedWord (w.map (fun c ↦ c i)) ∧
        (w.map (fun c ↦ c i)).reduceOption ∈ rep.L} : Language (Fin n → Option Γ)) := by
    exact valid_regular_forall
      (fun i ↦ List.map (fun c : Fin n → Option Γ ↦ c i) ⁻¹'
        ({u | PaddedWord u ∧ u.reduceOption ∈ rep.L} : Language (Option Γ)))
      (fun i ↦ language_regular_preimage_map (fun c : Fin n → Option Γ ↦ c i)
        (language_regular_padded rep.L_regular))
  have h := htracks.inf (language_regular_lastActive (Γ := Γ) n)
  have he : relLang rep.L rep.ν n Set.univ =
      ({w : List (Fin n → Option Γ) | (∀ i : Fin n,
        PaddedWord (w.map (fun c ↦ c i)) ∧
        (w.map (fun c ↦ c i)).reduceOption ∈ rep.L) ∧ LastActive w} :
        Language (Fin n → Option Γ)) := by
    ext w
    exact relLang_univ_iff rep.L rep.ν n w
  rw [he]
  exact h

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor

variable {S : Signature}

@[simp] theorem mem_freeList (φ : Formula S) (x : ℕ) : x ∈ freeList φ ↔ x ∈ free φ := by
  exact Finset.mem_sort (· ≤ ·)

theorem freeList_nodup (φ : Formula S) : (freeList φ).Nodup :=
  Finset.sort_nodup _ _

@[simp] theorem freeList_prev (I : Interval) (φ : Formula S) :
    freeList (.prev I φ) = freeList φ := rfl

@[simp] theorem freeList_next (I : Interval) (φ : Formula S) :
    freeList (.next I φ) = freeList φ := rfl

theorem freeList_since_left (I : Interval) (φ ψ : Formula S) (h : free φ = free ψ) :
    freeList (.since I φ ψ) = freeList φ := by
  simp only [freeList, free, h, Finset.union_self]

theorem freeList_until_left (I : Interval) (φ ψ : Formula S) (h : free φ = free ψ) :
    freeList (.until I φ ψ) = freeList φ := by
  simp only [freeList, free, h, Finset.union_self]

theorem freeList_map_congr (φ : Formula S) (v w : ℕ → ℕ)
    (h : ∀ x ∈ free φ, v x = w x) : (freeList φ).map v = (freeList φ).map w :=
  List.map_congr_left fun x hx => h x ((mem_freeList φ x).mp hx)

theorem assign_on (v : ℕ → ℕ) (xs ds : List ℕ) (x : ℕ) (hx : x ∈ xs) :
    assign v xs ds x = ds.getD (xs.idxOf x) 0 := by
  simp only [assign, if_pos hx]

theorem assign_off (v : ℕ → ℕ) (xs ds : List ℕ) (x : ℕ) (hx : x ∉ xs) :
    assign v xs ds x = v x := by
  simp only [assign, if_neg hx]

theorem assign_map_on (v w : ℕ → ℕ) (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) :
    assign w xs (xs.map v) x = v x := by
  simp only [assign, if_pos hx, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf hx, Option.map_some, Option.getD_some]

theorem assign_agree (v w : ℕ → ℕ) (xs ds : List ℕ) (x : ℕ) (hx : x ∈ xs) :
    assign v xs ds x = assign w xs ds x := by
  simp only [assign, if_pos hx]

theorem map_assign (v : ℕ → ℕ) (xs ds : List ℕ) (hxs : xs.Nodup)
    (hlen : ds.length = xs.length) : xs.map (assign v xs ds) = ds := by
  apply List.ext_getElem (by simpa only [List.length_map] using hlen.symm)
  intro i hi hj
  have hix : i < xs.length := by simpa only [List.length_map] using hi
  rw [List.getElem_map, assign_on _ _ _ _ (List.getElem_mem hix), hxs.idxOf_getElem i hix]
  exact List.getD_eq_getElem _ _ hj

theorem evalTerm_congr_free (const : S.C → ℕ) (t : Term S) (v w : ℕ → ℕ)
    (h : ∀ x ∈ termVars t, v x = w x) : evalTerm const v t = evalTerm const w t := by
  cases t with
  | inl x => exact h x (by simp only [termVars, Finset.mem_singleton])
  | inr c => rfl

theorem sat_congr_free (D : TempStruct S) (φ : Formula S) (v w : ℕ → ℕ) (i : ℕ)
    (h : ∀ x ∈ free φ, v x = w x) : Sat D φ v i ↔ Sat D φ w i := by
  induction φ generalizing v w i with
  | eq t t' =>
      have ht := evalTerm_congr_free D.const t v w fun x hx => h x (Finset.mem_union_left _ hx)
      have ht' := evalTerm_congr_free D.const t' v w fun x hx => h x (Finset.mem_union_right _ hx)
      simp only [Sat, ht, ht']
  | pred r ts =>
      have he : (fun k => evalTerm D.const v (ts k)) = fun k => evalTerm D.const w (ts k) := by
        funext k
        exact evalTerm_congr_free D.const (ts k) v w fun x hx =>
          h x (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hx⟩)
      simp only [Sat, he]
  | neg φ ih => exact not_congr (ih v w i h)
  | or φ ψ ihφ ihψ =>
      exact or_congr (ihφ v w i fun x hx => h x (Finset.mem_union_left _ hx))
        (ihψ v w i fun x hx => h x (Finset.mem_union_right _ hx))
  | ex x φ ih =>
      apply exists_congr
      intro d
      apply ih
      intro y hy
      by_cases hyx : y = x
      · subst y; simp only [Function.update_self]
      · have hh := h y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
        simpa only [Function.update_of_ne hyx] using hh
  | prev I φ ih => exact and_congr_right fun _ => and_congr_right fun _ => ih v w (i - 1) h
  | next I φ ih => exact and_congr_right fun _ => ih v w (i + 1) h
  | since I φ ψ ihφ ihψ =>
      apply exists_congr
      intro j
      apply and_congr_right
      intro _
      apply and_congr_right
      intro _
      apply and_congr
      · exact ihψ v w j fun x hx => h x (Finset.mem_union_right _ hx)
      · apply forall_congr'
        intro k
        exact imp_congr_right fun _ => imp_congr_right fun _ =>
          ihφ v w k fun x hx => h x (Finset.mem_union_left _ hx)
  | «until» I φ ψ ihφ ihψ =>
      apply exists_congr
      intro j
      apply and_congr_right
      intro _
      apply and_congr_right
      intro _
      apply and_congr
      · exact ihψ v w j fun x hx => h x (Finset.mem_union_right _ hx)
      · apply forall_congr'
        intro k
        exact imp_congr_right fun _ => imp_congr_right fun _ =>
          ihφ v w k fun x hx => h x (Finset.mem_union_left _ hx)

theorem extSat_congr_free (rels : S.R → Set (List ℕ)) (const : S.C → ℕ)
    (P : Formula S → Set (List ℕ)) (φ : Formula S) (v w : ℕ → ℕ)
    (h : ∀ x ∈ free φ, v x = w x) : ExtSat rels const P φ v ↔ ExtSat rels const P φ w := by
  induction φ generalizing v w with
  | eq t t' =>
      have ht := evalTerm_congr_free const t v w fun x hx => h x (Finset.mem_union_left _ hx)
      have ht' := evalTerm_congr_free const t' v w fun x hx => h x (Finset.mem_union_right _ hx)
      simp only [ExtSat, ht, ht']
  | pred r ts =>
      have he : (fun k => evalTerm const v (ts k)) = fun k => evalTerm const w (ts k) := by
        funext k
        exact evalTerm_congr_free const (ts k) v w fun x hx =>
          h x (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hx⟩)
      simp only [ExtSat, he]
  | neg φ ih => exact not_congr (ih v w h)
  | or φ ψ ihφ ihψ =>
      exact or_congr (ihφ v w fun x hx => h x (Finset.mem_union_left _ hx))
        (ihψ v w fun x hx => h x (Finset.mem_union_right _ hx))
  | ex x φ ih =>
      apply exists_congr
      intro d
      apply ih
      intro y hy
      by_cases hyx : y = x
      · subst y; simp only [Function.update_self]
      · have hh := h y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
        simpa only [Function.update_of_ne hyx] using hh
  | prev I φ _ => simp only [ExtSat, freeList_map_congr (.prev I φ) v w h]
  | next I φ _ => simp only [ExtSat, freeList_map_congr (.next I φ) v w h]
  | since I φ ψ _ _ => simp only [ExtSat, freeList_map_congr (.since I φ ψ) v w h]
  | «until» I φ ψ _ _ => simp only [ExtSat, freeList_map_congr (.until I φ ψ) v w h]

theorem satSet_support (D : TempStruct S) (φ : Formula S) (i : ℕ) (ds : List ℕ)
    (h : ds ∈ satSet D φ i) : ds.length = (freeList φ).length := h.1

theorem hatSet_support (rels : S.R → Set (List ℕ)) (const : S.C → ℕ)
    (P : Formula S → Set (List ℕ)) (φ : Formula S) (ds : List ℕ)
    (h : ds ∈ hatSet rels const P φ) : ds.length = (freeList φ).length := h.1

theorem satSet_map_iff (D : TempStruct S) (φ : Formula S) (v : ℕ → ℕ) (i : ℕ) :
    (freeList φ).map v ∈ satSet D φ i ↔ Sat D φ v i := by
  constructor
  · rintro ⟨_, w, hw⟩
    exact (sat_congr_free D φ _ v i fun x hx =>
      assign_map_on v w (freeList φ) x ((mem_freeList φ x).mpr hx)).mp hw
  · intro hv
    refine ⟨List.length_map _, v, ?_⟩
    exact (sat_congr_free D φ _ v i fun x hx =>
      assign_map_on v v (freeList φ) x ((mem_freeList φ x).mpr hx)).mpr hv

theorem hatSet_map_iff (rels : S.R → Set (List ℕ)) (const : S.C → ℕ)
    (P : Formula S → Set (List ℕ)) (φ : Formula S) (v : ℕ → ℕ) :
    (freeList φ).map v ∈ hatSet rels const P φ ↔ ExtSat rels const P φ v := by
  constructor
  · rintro ⟨_, w, hw⟩
    exact (extSat_congr_free rels const P φ _ v fun x hx =>
      assign_map_on v w (freeList φ) x ((mem_freeList φ x).mpr hx)).mp hw
  · intro hv
    refine ⟨List.length_map _, v, ?_⟩
    exact (extSat_congr_free rels const P φ _ v fun x hx =>
      assign_map_on v v (freeList φ) x ((mem_freeList φ x).mpr hx)).mpr hv

theorem satSet_iff (D : TempStruct S) (φ : Formula S) (i : ℕ) (ds : List ℕ) :
    ds ∈ satSet D φ i ↔ ds.length = (freeList φ).length ∧
      Sat D φ (assign (fun _ => 0) (freeList φ) ds) i := by
  constructor
  · rintro ⟨hlen, v, hv⟩
    refine ⟨hlen, ?_⟩
    exact (sat_congr_free D φ _ _ i fun x hx =>
      assign_agree v (fun _ => 0) (freeList φ) ds x ((mem_freeList φ x).mpr hx)).mp hv
  · rintro ⟨hlen, hv⟩
    exact ⟨hlen, (fun _ => 0), hv⟩

theorem hatSet_iff (rels : S.R → Set (List ℕ)) (const : S.C → ℕ)
    (P : Formula S → Set (List ℕ)) (φ : Formula S) (ds : List ℕ) :
    ds ∈ hatSet rels const P φ ↔ ds.length = (freeList φ).length ∧
      ExtSat rels const P φ (assign (fun _ => 0) (freeList φ) ds) := by
  constructor
  · rintro ⟨hlen, v, hv⟩
    refine ⟨hlen, ?_⟩
    exact (extSat_congr_free rels const P φ _ _ fun x hx =>
      assign_agree v (fun _ => 0) (freeList φ) ds x ((mem_freeList φ x).mpr hx)).mp hv
  · rintro ⟨hlen, hv⟩
    exact ⟨hlen, (fun _ => 0), hv⟩

theorem extSat_iff_sat (D : TempStruct S) (i : ℕ) (P : Formula S → Set (List ℕ))
    (φ : Formula S) (hP : ∀ ψ ∈ tsub φ, P ψ = satSet D ψ i) (v : ℕ → ℕ) :
    ExtSat (D.rel i) D.const P φ v ↔ Sat D φ v i := by
  induction φ generalizing v with
  | eq t t' => rfl
  | pred r ts => rfl
  | neg φ ih => exact not_congr (ih hP v)
  | or φ ψ ihφ ihψ =>
      exact or_congr (ihφ (fun α hα => hP α (List.mem_append_left _ hα)) v)
        (ihψ (fun α hα => hP α (List.mem_append_right _ hα)) v)
  | ex x φ ih => exact exists_congr fun d => ih hP (Function.update v x d)
  | prev I φ _ =>
      change (freeList (Formula.prev I φ)).map v ∈ P (Formula.prev I φ) ↔ _
      rw [hP _ (by simp only [tsub, List.mem_singleton])]
      exact satSet_map_iff D _ v i
  | next I φ _ =>
      change (freeList (Formula.next I φ)).map v ∈ P (Formula.next I φ) ↔ _
      rw [hP _ (by simp only [tsub, List.mem_singleton])]
      exact satSet_map_iff D _ v i
  | since I φ ψ _ _ =>
      change (freeList (Formula.since I φ ψ)).map v ∈ P (Formula.since I φ ψ) ↔ _
      rw [hP _ (by simp only [tsub, List.mem_singleton])]
      exact satSet_map_iff D _ v i
  | «until» I φ ψ _ _ =>
      change (freeList (Formula.until I φ ψ)).map v ∈ P (Formula.until I φ ψ) ↔ _
      rw [hP _ (by simp only [tsub, List.mem_singleton])]
      exact satSet_map_iff D _ v i

theorem hatSet_eq_satSet (D : TempStruct S) (i : ℕ) (P : Formula S → Set (List ℕ))
    (φ : Formula S) (hP : ∀ ψ ∈ tsub φ, P ψ = satSet D ψ i) :
    hatSet (D.rel i) D.const P φ = satSet D φ i := by
  ext ds
  rw [hatSet_iff, satSet_iff, extSat_iff_sat D i P φ hP]

theorem prevP_satSet (D : TempStruct S) (I : Interval) (β : Formula S) (i : ℕ) :
    prevP D.τ I i (satSet D β (i - 1)) = satSet D (.prev I β) i := by
  ext ds
  by_cases h : 0 < i ∧ I.Mem (D.τ i - D.τ (i - 1))
  · rw [prevP, if_pos h, satSet_iff, satSet_iff]
    change (_ ∧ Sat D β _ (i - 1)) ↔ (_ ∧ 0 < i ∧ I.Mem _ ∧ Sat D β _ (i - 1))
    exact ⟨fun hd => ⟨hd.1, h.1, h.2, hd.2⟩, fun hd => ⟨hd.1, hd.2.2.2⟩⟩
  · rw [prevP, if_neg h]
    simp only [Set.mem_empty_iff_false, false_iff]
    rintro ⟨_, _, hpos, hmem, _⟩
    exact h ⟨hpos, hmem⟩

theorem nextP_satSet (D : TempStruct S) (I : Interval) (β : Formula S) (i : ℕ) :
    nextP D.τ I i (satSet D β (i + 1)) = satSet D (.next I β) i := by
  ext ds
  by_cases h : I.Mem (D.τ (i + 1) - D.τ i)
  · rw [nextP, if_pos h, satSet_iff, satSet_iff]
    change (_ ∧ Sat D β _ (i + 1)) ↔ (_ ∧ I.Mem _ ∧ Sat D β _ (i + 1))
    exact ⟨fun hd => ⟨hd.1, h, hd.2⟩, fun hd => ⟨hd.1, hd.2.2⟩⟩
  · rw [nextP, if_neg h]
    simp only [Set.mem_empty_iff_false, false_iff]
    rintro ⟨_, _, hmem, _⟩
    exact h hmem

theorem satSet_since_iff (D : TempStruct S) (I : Interval) (β γ : Formula S)
    (hfree : free β = free γ) (i : ℕ) (a : List ℕ) :
    a ∈ satSet D (.since I β γ) i ↔
      ∃ j, j ≤ i ∧ I.Mem (D.τ i - D.τ j) ∧ a ∈ satSet D γ j ∧
        ∀ k, j < k → k ≤ i → a ∈ satSet D β k := by
  have hfg : freeList β = freeList γ := by
    simp only [freeList, hfree]
  simp only [satSet_iff, freeList_since_left I β γ hfree, hfg, Sat]
  constructor
  · rintro ⟨hlen, j, hji, hI, hγ, hβ⟩
    exact ⟨j, hji, hI, ⟨hlen, hγ⟩, fun k hjk hki => ⟨hlen, hβ k hjk hki⟩⟩
  · rintro ⟨j, hji, hI, ⟨hlen, hγ⟩, hβ⟩
    exact ⟨hlen, j, hji, hI, hγ, fun k hjk hki => (hβ k hjk hki).2⟩

theorem satSet_until_iff (D : TempStruct S) (I : Interval) (β γ : Formula S)
    (hfree : free β = free γ) (i : ℕ) (a : List ℕ) :
    a ∈ satSet D (.until I β γ) i ↔
      ∃ j, i ≤ j ∧ I.Mem (D.τ j - D.τ i) ∧ a ∈ satSet D γ j ∧
        ∀ k, i ≤ k → k < j → a ∈ satSet D β k := by
  have hfg : freeList β = freeList γ := by
    simp only [freeList, hfree]
  simp only [satSet_iff, freeList_until_left I β γ hfree, hfg, Sat]
  constructor
  · rintro ⟨hlen, j, hij, hI, hγ, hβ⟩
    exact ⟨j, hij, hI, ⟨hlen, hγ⟩, fun k hik hkj => ⟨hlen, hβ k hik hkj⟩⟩
  · rintro ⟨j, hij, hI, ⟨hlen, hγ⟩, hβ⟩
    exact ⟨hlen, j, hij, hI, hγ, fun k hik hkj => (hβ k hik hkj).2⟩

theorem satSet_until_offset_iff (D : TempStruct S) (I : Interval) (β γ : Formula S)
    (hfree : free β = free γ) (i : ℕ) (a : List ℕ) :
    a ∈ satSet D (.until I β γ) i ↔
      ∃ j, I.Mem (D.τ (i + j) - D.τ i) ∧ a ∈ satSet D γ (i + j) ∧
        ∀ k, k < j → a ∈ satSet D β (i + k) := by
  rw [satSet_until_iff D I β γ hfree]
  constructor
  · rintro ⟨j, hij, hI, hγ, hβ⟩
    have he : i + (j - i) = j := by omega
    refine ⟨j - i, ?_, ?_, ?_⟩
    · simpa only [he] using hI
    · simpa only [he] using hγ
    · intro k hk
      exact hβ (i + k) (by omega) (by omega)
  · rintro ⟨j, hI, hγ, hβ⟩
    refine ⟨i + j, Nat.le_add_right i j, hI, hγ, ?_⟩
    intro k hik hkj
    have he : i + (k - i) = k := by omega
    simpa only [he] using hβ (k - i) (by omega)

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor

open Classical

variable {S : Signature} {Γ : Type}

theorem conv_injective {n : ℕ} : Function.Injective (conv (Γ := Γ) (k := n)) := by
  intro ws₁ ws₂ h
  funext i
  rw [← conv_track_reduceOption ws₁ i, ← conv_track_reduceOption ws₂ i, h]

theorem relLang_congr {L : Language Γ} {ν : List Γ → ℕ} {n : ℕ} {A B : Set (List ℕ)}
    (h : ∀ ds : List ℕ, ds.length = n → (ds ∈ A ↔ ds ∈ B)) :
    relLang L ν n A = relLang L ν n B := by
  ext w
  simp only [relLang]
  apply exists_congr
  intro ws
  exact and_congr_right fun _ ↦ and_congr_left fun _ ↦ h _ List.length_ofFn

theorem regular_congr [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A B : Set (List ℕ)}
    (h : ∀ ds : List ℕ, ds.length = n → (ds ∈ A ↔ ds ∈ B))
    (hA : RegularRel rep n A) : RegularRel rep n B := by
  rwa [RegularRel, ← relLang_congr h]

theorem regular_univ [Fintype Γ] (rep : DomainRep Γ) (n : ℕ) :
    RegularRel rep n Set.univ :=
  valid_convolution_regular rep n

theorem relLang_union (L : Language Γ) (ν : List Γ → ℕ) (n : ℕ) (A B : Set (List ℕ)) :
    relLang L ν n (A ∪ B) = relLang L ν n A + relLang L ν n B := by
  ext w
  change (∃ ws, (∀ i, ws i ∈ L) ∧ (List.ofFn (fun i ↦ ν (ws i)) ∈ A ∨
    List.ofFn (fun i ↦ ν (ws i)) ∈ B) ∧ conv ws = w) ↔
    (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∈ A ∧ conv ws = w) ∨
    (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∈ B ∧ conv ws = w)
  aesop

theorem regular_union [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A B : Set (List ℕ)}
    (hA : RegularRel rep n A) (hB : RegularRel rep n B) :
    RegularRel rep n (A ∪ B) := by
  rw [RegularRel, relLang_union]
  exact hA.add hB

theorem relLang_inter (L : Language Γ) (ν : List Γ → ℕ) (n : ℕ) (A B : Set (List ℕ)) :
    relLang L ν n (A ∩ B) = relLang L ν n A ⊓ relLang L ν n B := by
  ext w
  change (∃ ws, (∀ i, ws i ∈ L) ∧ (List.ofFn (fun i ↦ ν (ws i)) ∈ A ∧
    List.ofFn (fun i ↦ ν (ws i)) ∈ B) ∧ conv ws = w) ↔
    (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∈ A ∧ conv ws = w) ∧
    (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∈ B ∧ conv ws = w)
  constructor
  · rintro ⟨ws, hL, ⟨hA, hB⟩, rfl⟩
    exact ⟨⟨ws, hL, hA, rfl⟩, ⟨ws, hL, hB, rfl⟩⟩
  · rintro ⟨⟨ws₁, hL₁, hA, rfl⟩, ⟨ws₂, _, hB, hconv⟩⟩
    have heq := conv_injective hconv
    subst ws₂
    exact ⟨ws₁, hL₁, ⟨hA, hB⟩, rfl⟩

theorem regular_inter [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A B : Set (List ℕ)}
    (hA : RegularRel rep n A) (hB : RegularRel rep n B) :
    RegularRel rep n (A ∩ B) := by
  rw [RegularRel, relLang_inter]
  exact hA.inf hB

theorem relLang_compl (L : Language Γ) (ν : List Γ → ℕ) (n : ℕ) (A : Set (List ℕ)) :
    relLang L ν n Aᶜ = relLang L ν n Set.univ ⊓ (relLang L ν n A)ᶜ := by
  ext w
  change (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∉ A ∧ conv ws = w) ↔
    (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∈ Set.univ ∧ conv ws = w) ∧
    ¬ (∃ ws, (∀ i, ws i ∈ L) ∧ List.ofFn (fun i ↦ ν (ws i)) ∈ A ∧ conv ws = w)
  constructor
  · rintro ⟨ws, hL, hnotA, rfl⟩
    refine ⟨⟨ws, hL, trivial, rfl⟩, ?_⟩
    rintro ⟨ws', _, hA, hconv⟩
    have heq := conv_injective hconv
    subst ws'
    exact hnotA hA
  · rintro ⟨⟨ws, hL, _, rfl⟩, hnot⟩
    refine ⟨ws, hL, ?_, rfl⟩
    intro hA
    exact hnot ⟨ws, hL, hA, rfl⟩

theorem regular_compl [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A : Set (List ℕ)}
    (hA : RegularRel rep n A) : RegularRel rep n Aᶜ := by
  rw [RegularRel, relLang_compl]
  exact (regular_univ rep n).inf hA.compl

theorem regular_finset_union [Fintype Γ] {ι : Type} (rep : DomainRep Γ) (n : ℕ)
    (s : Finset ι) (P : ι → Set (List ℕ)) (hP : ∀ i ∈ s, RegularRel rep n (P i)) :
    RegularRel rep n {ds | ∃ i ∈ s, ds ∈ P i} := by
  induction s using Finset.induction_on with
  | empty =>
    refine regular_congr (A := ∅) (fun ds _ ↦ ?_) (regular_empty rep n)
    simp
  | @insert i s hi ih =>
    have h₁ := hP i (Finset.mem_insert_self i s)
    have h₂ := ih (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))
    refine regular_congr (fun ds _ ↦ ?_) (regular_union h₁ h₂)
    change (ds ∈ P i ∨ ∃ j ∈ s, ds ∈ P j) ↔ ∃ j ∈ insert i s, ds ∈ P j
    simp only [Finset.mem_insert, exists_eq_or_imp]

theorem regular_finset_inter [Fintype Γ] {ι : Type} (rep : DomainRep Γ) (n : ℕ)
    (s : Finset ι) (P : ι → Set (List ℕ)) (hP : ∀ i ∈ s, RegularRel rep n (P i)) :
    RegularRel rep n {ds | ∀ i ∈ s, ds ∈ P i} := by
  induction s using Finset.induction_on with
  | empty =>
    refine regular_congr (A := Set.univ) (fun ds _ ↦ ?_) (regular_univ rep n)
    simp
  | @insert i s hi ih =>
    have h₁ := hP i (Finset.mem_insert_self i s)
    have h₂ := ih (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))
    refine regular_congr (fun ds _ ↦ ?_) (regular_inter h₁ h₂)
    change (ds ∈ P i ∧ ∀ j ∈ s, ds ∈ P j) ↔ ∀ j ∈ insert i s, ds ∈ P j
    simp only [Finset.mem_insert, forall_eq_or_imp]

def projLetter {m n : ℕ} (f : Fin m → Fin n) (c : Fin n → Option Γ) :
    Option (Fin m → Option Γ) :=
  if ∀ i : Fin m, c (f i) = none then none else some (fun i ↦ c (f i))

private theorem ofFn_eq_map_range {α : Type} (N : ℕ) (h : ℕ → α) :
    List.ofFn (n := N) (fun p : Fin N ↦ h (p : ℕ)) = (List.range N).map h := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    simp

theorem filterMap_projLetter_conv {m n : ℕ} (f : Fin m → Fin n) (ws : Fin n → List Γ) :
    (conv ws).filterMap (projLetter f) = conv (ws ∘ f) := by
  let L₁ := Finset.univ.sup fun j : Fin n ↦ (ws j).length
  let L₂ := Finset.univ.sup fun i : Fin m ↦ (ws (f i)).length
  have hle : L₂ ≤ L₁ := by
    apply Finset.sup_le
    intro i _
    exact Finset.le_sup (f := fun j : Fin n ↦ (ws j).length) (Finset.mem_univ (f i))
  let h₁ : ℕ → (Fin n → Option Γ) := fun p j ↦ (ws j)[p]?
  let h₂ : ℕ → (Fin m → Option Γ) := fun p i ↦ (ws (f i))[p]?
  have hlt (p : ℕ) (hp : p < L₂) : projLetter f (h₁ p) = some (h₂ p) := by
    obtain ⟨i, _, hi⟩ := Finset.lt_sup_iff.mp hp
    have hne : ¬ (∀ i' : Fin m, h₁ p (f i') = none) := by
      intro hall
      have hnone := hall i
      change (ws (f i))[p]? = none at hnone
      rw [List.getElem?_eq_getElem hi] at hnone
      exact Option.some_ne_none _ hnone
    simp only [projLetter, if_neg hne]
    rfl
  have hge (p : ℕ) (hp : L₂ ≤ p) : projLetter f (h₁ p) = none := by
    have hall : ∀ i : Fin m, h₁ p (f i) = none := by
      intro i
      change (ws (f i))[p]? = none
      have hlen : (ws (f i)).length ≤ L₂ :=
        Finset.le_sup (f := fun i' : Fin m ↦ (ws (f i')).length) (Finset.mem_univ i)
      exact List.getElem?_eq_none (by omega)
    simp only [projLetter, if_pos hall]
  have hprefix (k : ℕ) (hk : k ≤ L₂) :
      ((List.range k).map h₁).filterMap (projLetter f) = (List.range k).map h₂ := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.filterMap_append, List.map_append,
        ih (by omega)]
      simp [hlt k (by omega)]
  have hsuffix (d : ℕ) :
      ((List.range (L₂ + d)).map h₁).filterMap (projLetter f) = (List.range L₂).map h₂ := by
    induction d with
    | zero => exact hprefix L₂ le_rfl
    | succ d ih =>
      rw [← Nat.add_assoc, List.range_succ, List.map_append, List.filterMap_append, ih]
      simp [hge (L₂ + d) (by omega)]
  change (List.ofFn (n := L₁) (fun p ↦ h₁ (p : ℕ))).filterMap (projLetter f) =
    List.ofFn (n := L₂) (fun p ↦ h₂ (p : ℕ))
  rw [ofFn_eq_map_range L₁ h₁, ofFn_eq_map_range L₂ h₂]
  have hL₁ : L₁ = L₂ + (L₁ - L₂) := by omega
  rw [hL₁]
  exact hsuffix (L₁ - L₂)

theorem regular_pullback [Fintype Γ] {rep : DomainRep Γ} {m n : ℕ} (f : Fin m → Fin n)
    {A : Set (List ℕ)} (hA : RegularRel rep m A) :
    RegularRel rep n {ds | ds.length = n ∧
      List.ofFn (fun i : Fin m ↦ ds.getD (f i) 0) ∈ A} := by
  have hget (ws : Fin n → List Γ) :
      List.ofFn (fun i : Fin m ↦ (List.ofFn (fun j : Fin n ↦ rep.ν (ws j))).getD (f i) 0) =
        List.ofFn (fun i : Fin m ↦ rep.ν ((ws ∘ f) i)) := by
    apply List.ext_getElem (by simp)
    intro i hi₁ hi₂
    simp
  have he : relLang rep.L rep.ν n {ds | ds.length = n ∧
      List.ofFn (fun i : Fin m ↦ ds.getD (f i) 0) ∈ A} =
      relLang rep.L rep.ν n Set.univ ⊓
        (List.filterMap (projLetter f) ⁻¹' relLang rep.L rep.ν m A) := by
    ext w
    change (∃ ws, (∀ j, ws j ∈ rep.L) ∧
      (List.ofFn (fun j ↦ rep.ν (ws j)) ∈ {ds | ds.length = n ∧
        List.ofFn (fun i : Fin m ↦ ds.getD (f i) 0) ∈ A}) ∧ conv ws = w) ↔
      (∃ ws, (∀ j, ws j ∈ rep.L) ∧ List.ofFn (fun j ↦ rep.ν (ws j)) ∈ Set.univ ∧ conv ws = w) ∧
      w.filterMap (projLetter f) ∈ relLang rep.L rep.ν m A
    constructor
    · rintro ⟨ws, hL, ⟨_, hmem⟩, rfl⟩
      rw [hget ws] at hmem
      refine ⟨⟨ws, hL, trivial, rfl⟩, ?_⟩
      rw [filterMap_projLetter_conv]
      exact ⟨ws ∘ f, fun i ↦ hL (f i), hmem, rfl⟩
    · rintro ⟨⟨ws, hL, _, rfl⟩, hmem⟩
      rw [filterMap_projLetter_conv] at hmem
      obtain ⟨us, _, hus, hconv⟩ := hmem
      have heq := conv_injective hconv
      subst us
      refine ⟨ws, hL, ⟨List.length_ofFn, ?_⟩, rfl⟩
      rw [hget ws]
      exact hus
  rw [RegularRel, he]
  exact (regular_univ rep n).inf (language_regular_preimage_filterMap (projLetter f) hA)

private def snocWord {α : Type} {n : ℕ} (ws : Fin n → α) (u : α) (j : Fin (n + 1)) : α :=
  if h : (j : ℕ) < n then ws ⟨j, h⟩ else u

private theorem snocWord_castSucc {α : Type} {n : ℕ} (ws : Fin n → α) (u : α) (i : Fin n) :
    snocWord ws u i.castSucc = ws i := by
  simp [snocWord, i.isLt]

private theorem snocWord_last {α : Type} {n : ℕ} (ws : Fin n → α) (u : α) :
    snocWord ws u (Fin.last n) = u := by
  simp [snocWord]

private theorem ofFn_succ_append {α : Type} {n : ℕ} (g : Fin (n + 1) → α) :
    List.ofFn g = List.ofFn (fun i : Fin n ↦ g i.castSucc) ++ [g (Fin.last n)] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ (f := g),
      List.ofFn_succ (f := fun i : Fin (n + 1) ↦ g i.castSucc), List.cons_append]
    exact congrArg (List.cons (g 0)) (ih (fun i ↦ g i.succ))

theorem regular_projLast [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A : Set (List ℕ)}
    (hA : RegularRel rep (n + 1) A) :
    RegularRel rep n {ds | ds.length = n ∧ ∃ d : ℕ, ds ++ [d] ∈ A} := by
  have he : relLang rep.L rep.ν n {ds | ds.length = n ∧ ∃ d : ℕ, ds ++ [d] ∈ A} =
      List.filterMap (projLetter (Fin.castSucc : Fin n → Fin (n + 1))) ''
        relLang rep.L rep.ν (n + 1) A := by
    ext w
    change (∃ ws, (∀ i, ws i ∈ rep.L) ∧
      (List.ofFn (fun i ↦ rep.ν (ws i)) ∈ {ds | ds.length = n ∧ ∃ d : ℕ, ds ++ [d] ∈ A}) ∧
      conv ws = w) ↔
      ∃ v ∈ relLang rep.L rep.ν (n + 1) A,
        v.filterMap (projLetter (Fin.castSucc : Fin n → Fin (n + 1))) = w
    constructor
    · rintro ⟨ws, hL, ⟨_, d, hd⟩, rfl⟩
      obtain ⟨u, huL, rfl⟩ := rep.ν_surj d
      let ws' : Fin (n + 1) → List Γ := snocWord ws u
      have hL' (j : Fin (n + 1)) : ws' j ∈ rep.L := by
        dsimp only [ws', snocWord]
        split_ifs with h
        · exact hL ⟨j, h⟩
        · exact huL
      have hcomp : ws' ∘ Fin.castSucc = ws := by
        funext i
        exact snocWord_castSucc ws u i
      have hofFn : List.ofFn (fun j : Fin (n + 1) ↦ rep.ν (ws' j)) =
          List.ofFn (fun i : Fin n ↦ rep.ν (ws i)) ++ [rep.ν u] := by
        rw [ofFn_succ_append]
        simp only [ws', snocWord_castSucc, snocWord_last]
      refine ⟨conv ws', ⟨ws', hL', ?_, rfl⟩, ?_⟩
      · rwa [hofFn]
      · rw [filterMap_projLetter_conv, hcomp]
    · rintro ⟨v, ⟨ws', hL', hmem, rfl⟩, rfl⟩
      rw [filterMap_projLetter_conv]
      refine ⟨ws' ∘ Fin.castSucc, fun i ↦ hL' i.castSucc,
        ⟨List.length_ofFn, rep.ν (ws' (Fin.last n)), ?_⟩, rfl⟩
      rw [ofFn_succ_append] at hmem
      exact hmem
  rw [RegularRel, he]
  exact language_regular_image_filterMap _ hA

theorem language_regular_singleton {α : Type} (u : List α) :
    Language.IsRegular ({u} : Language α) := by
  induction u with
  | nil =>
    let M : DFA α Bool :=
      { step := fun _ _ ↦ false
        start := true
        accept := {b | b = true} }
    have hfalse (w : List α) : M.evalFrom false w = false := by
      induction w with
      | nil => rfl
      | cons _ _ ih => exact ih
    refine ⟨Bool, inferInstance, M, ?_⟩
    ext w
    change M.evalFrom true w = true ↔ w = []
    cases w with
    | nil => simp [DFA.evalFrom_nil]
    | cons a w =>
      rw [DFA.evalFrom_cons]
      change M.evalFrom false w = true ↔ a :: w = []
      rw [hfalse]
      simp
  | cons a u ih =>
    obtain ⟨σ, hσ, M, hM⟩ := ih
    let N : DFA α (Option (Option σ)) :=
      { step := fun s b ↦ match s with
          | none => none
          | some none => if b = a then some (some M.start) else none
          | some (some q) => some (some (M.step q b))
        start := some none
        accept := {s | match s with | some (some q) => q ∈ M.accept | _ => False} }
    have hnone (w : List α) : N.evalFrom none w = none := by
      induction w with
      | nil => rfl
      | cons _ _ ihw => exact ihw
    have hsome (q : σ) (w : List α) :
        N.evalFrom (some (some q)) w = some (some (M.evalFrom q w)) := by
      induction w generalizing q with
      | nil => rfl
      | cons b w ihw => exact ihw (M.step q b)
    refine ⟨Option (Option σ), inferInstance, N, ?_⟩
    ext w
    cases w with
    | nil =>
      change N.evalFrom (some none) [] ∈ N.accept ↔ [] = a :: u
      simp [N, DFA.evalFrom_nil]
    | cons b w =>
      change N.evalFrom (some none) (b :: w) ∈ N.accept ↔ b :: w = a :: u
      rw [DFA.evalFrom_cons]
      dsimp only [N]
      by_cases hba : b = a
      · subst b
        rw [if_pos rfl, hsome]
        change w ∈ M.accepts ↔ a :: w = a :: u
        rw [hM]
        exact (List.cons_eq_cons.trans (and_iff_right rfl)).symm
      · rw [if_neg hba, hnone]
        simp [hba]

theorem regular_const [Fintype Γ] (rep : DomainRep Γ) (c : ℕ) :
    RegularRel rep 1 {[c]} := by
  obtain ⟨u, huL, rfl⟩ := rep.ν_surj c
  let L₂ : Language (Fin 2 → Option Γ) :=
    relLang rep.L rep.ν 2 {l | ∃ d : ℕ, l = [d, d]} ⊓
      (List.map (fun x : Fin 2 → Option Γ ↦ x 1) ⁻¹'
        (List.filterMap id ⁻¹' ({u} : Language Γ)))
  have hL₂ : L₂.IsRegular :=
    rep.eq_regular.inf
      (language_regular_preimage_map _
        (language_regular_preimage_filterMap id (language_regular_singleton u)))
  have he : relLang rep.L rep.ν 1 {[rep.ν u]} =
      List.filterMap (projLetter (Fin.castSucc : Fin 1 → Fin 2)) '' L₂ := by
    ext w
    change (∃ ws, (∀ i, ws i ∈ rep.L) ∧
      List.ofFn (fun i : Fin 1 ↦ rep.ν (ws i)) = [rep.ν u] ∧ conv ws = w) ↔
      ∃ v ∈ L₂, v.filterMap (projLetter (Fin.castSucc : Fin 1 → Fin 2)) = w
    constructor
    · rintro ⟨ws, hL, hν, rfl⟩
      have hν0 : rep.ν (ws 0) = rep.ν u := by
        simpa only [List.ofFn_succ, List.ofFn_zero, List.cons.injEq, and_true] using hν
      let ws' : Fin 2 → List Γ := snocWord ws u
      have hL' (j : Fin 2) : ws' j ∈ rep.L := by
        dsimp only [ws', snocWord]
        split_ifs with h
        · exact hL ⟨j, h⟩
        · exact huL
      have hcomp : ws' ∘ Fin.castSucc = ws := by
        funext i
        exact snocWord_castSucc ws u i
      have hws0 : ws' 0 = ws 0 := snocWord_castSucc ws u 0
      have hws1 : ws' 1 = u := snocWord_last ws u
      refine ⟨conv ws', ⟨⟨ws', hL', ⟨rep.ν u, ?_⟩, rfl⟩, ?_⟩, ?_⟩
      · simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, hws0, hws1, hν0]
      · change ((conv ws').map (fun x : Fin 2 → Option Γ ↦ x 1)).reduceOption ∈ ({u} : Language Γ)
        rw [conv_track_reduceOption, hws1]
        rfl
      · rw [filterMap_projLetter_conv, hcomp]
    · rintro ⟨v, ⟨⟨ws', hL', ⟨d, hd⟩, rfl⟩, htrack⟩, rfl⟩
      change ((conv ws').map (fun x : Fin 2 → Option Γ ↦ x 1)).reduceOption = u at htrack
      rw [conv_track_reduceOption] at htrack
      rw [filterMap_projLetter_conv]
      refine ⟨ws' ∘ Fin.castSucc, fun i ↦ hL' i.castSucc, ?_, rfl⟩
      simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, List.cons.injEq,
        and_true] at hd ⊢
      change rep.ν (ws' 0) = rep.ν u
      rw [hd.1, ← hd.2, htrack]
  rw [RegularRel, he]
  exact language_regular_image_filterMap _ hL₂

private theorem getD_eq_getElem_of_lt (ds : List ℕ) (j : ℕ) (hj : j < ds.length) :
    ds.getD j 0 = ds[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

private theorem getD_append_left (ds cs : List ℕ) (j : ℕ) (hj : j < ds.length) :
    (ds ++ cs).getD j 0 = ds.getD j 0 := by
  have hj' : j < (ds ++ cs).length := by simp; omega
  rw [getD_eq_getElem_of_lt _ _ hj', getD_eq_getElem_of_lt _ _ hj, List.getElem_append_left hj]

private theorem getD_append_right (ds cs : List ℕ) (k : ℕ) :
    (ds ++ cs).getD (ds.length + k) 0 = cs.getD k 0 := by
  by_cases hk : k < cs.length
  · have hk' : ds.length + k < (ds ++ cs).length := by simp; omega
    rw [getD_eq_getElem_of_lt _ _ hk', getD_eq_getElem_of_lt _ _ hk]
    simp [List.getElem_append_right]
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

private theorem getD_append_singleton_last (ds : List ℕ) (c : ℕ) :
    (ds ++ [c]).getD ds.length 0 = c := by
  have h := getD_append_right ds [c] 0
  simpa using h

theorem eq_ofFn_castSucc_append_last (ds : List ℕ) (n : ℕ) (h : ds.length = n + 1) :
    ds = List.ofFn (fun i : Fin n ↦ ds.getD (Fin.castSucc i) 0) ++ [ds.getD n 0] := by
  apply List.ext_getElem
  · simp [h]
  · intro j hj₁ hj₂
    by_cases hj : j < n
    · rw [List.getElem_append_left (by simpa using hj)]
      simp only [List.getElem_ofFn, Fin.val_castSucc]
      exact (getD_eq_getElem_of_lt ds j hj₁).symm
    · have hjeq : j = n := by omega
      subst j
      rw [List.getElem_append_right (by simp)]
      simp only [List.length_ofFn, Nat.sub_self, List.getElem_singleton]
      exact (getD_eq_getElem_of_lt ds n hj₁).symm

theorem regular_append_const [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A : Set (List ℕ)}
    (hA : RegularRel rep n A) (c : ℕ) :
    RegularRel rep (n + 1) {ds | ∃ a, a.length = n ∧ a ∈ A ∧ ds = a ++ [c]} := by
  have h₁ := regular_pullback (Fin.castSucc : Fin n → Fin (n + 1)) hA
  have h₂ := regular_pullback (fun _ : Fin 1 ↦ Fin.last n) (regular_const rep c)
  refine regular_congr (fun ds hlen ↦ ?_) (regular_inter h₁ h₂)
  change (ds.length = n + 1 ∧ List.ofFn (fun i : Fin n ↦ ds.getD (Fin.castSucc i) 0) ∈ A) ∧
    (ds.length = n + 1 ∧ List.ofFn (fun _ : Fin 1 ↦ ds.getD (Fin.last n) 0) ∈ ({[c]} : Set (List ℕ))) ↔
    ∃ a, a.length = n ∧ a ∈ A ∧ ds = a ++ [c]
  constructor
  · rintro ⟨⟨_, hA'⟩, ⟨_, hc'⟩⟩
    have hlast : ds.getD n 0 = c := by
      simpa only [List.ofFn_succ, List.ofFn_zero, Set.mem_singleton_iff,
        List.cons.injEq, and_true, Fin.val_last] using hc'
    refine ⟨List.ofFn (fun i : Fin n ↦ ds.getD (Fin.castSucc i) 0), List.length_ofFn, hA', ?_⟩
    rw [← hlast]
    exact eq_ofFn_castSucc_append_last ds n hlen
  · rintro ⟨a, ha_len, haA, rfl⟩
    have htake : List.ofFn (fun i : Fin n ↦ (a ++ [c]).getD (Fin.castSucc i) 0) = a := by
      apply List.ext_getElem (by simp [ha_len])
      intro i hi₁ hi₂
      simp only [List.getElem_ofFn, Fin.val_castSucc]
      rw [getD_append_left a [c] i hi₂, getD_eq_getElem_of_lt a i hi₂]
    have hlast : (a ++ [c]).getD n 0 = c := by
      rw [← ha_len]
      exact getD_append_singleton_last a c
    refine ⟨⟨hlen, ?_⟩, ⟨hlen, ?_⟩⟩
    · rwa [htake]
    · simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_last, hlast, Set.mem_singleton_iff]

theorem regular_spec_last [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A : Set (List ℕ)}
    (hA : RegularRel rep (n + 1) A) (c : ℕ) :
    RegularRel rep n {ds | ds.length = n ∧ ds ++ [c] ∈ A} := by
  have h₂ := regular_pullback (fun _ : Fin 1 ↦ Fin.last n) (regular_const rep c)
  have hproj := regular_projLast (regular_inter hA h₂)
  refine regular_congr (fun ds hlen ↦ ?_) hproj
  change (ds.length = n ∧ ∃ d : ℕ, ds ++ [d] ∈ A ∧
    ((ds ++ [d]).length = n + 1 ∧
      List.ofFn (fun _ : Fin 1 ↦ (ds ++ [d]).getD (Fin.last n) 0) ∈ ({[c]} : Set (List ℕ)))) ↔
    ds.length = n ∧ ds ++ [c] ∈ A
  constructor
  · rintro ⟨_, d, hdA, _, hdc⟩
    have hlast : (ds ++ [d]).getD n 0 = d := by
      rw [← hlen]
      exact getD_append_singleton_last ds d
    have hd : d = c := by
      simpa only [List.ofFn_succ, List.ofFn_zero, Set.mem_singleton_iff,
        List.cons.injEq, and_true, Fin.val_last, hlast] using hdc
    subst d
    exact ⟨hlen, hdA⟩
  · rintro ⟨_, hcA⟩
    have hlast : (ds ++ [c]).getD n 0 = c := by
      rw [← hlen]
      exact getD_append_singleton_last ds c
    refine ⟨hlen, c, hcA, by simp [hlen], ?_⟩
    simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_last, hlast, Set.mem_singleton_iff]

theorem regular_spec_append [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} (cs : List ℕ)
    {A : Set (List ℕ)} (hA : RegularRel rep (n + cs.length) A) :
    RegularRel rep n {ds | ds.length = n ∧ ds ++ cs ∈ A} := by
  induction cs generalizing n A with
  | nil =>
    refine regular_congr (fun ds hlen ↦ ?_) hA
    simp [hlen]
  | cons c cs ih =>
    have hA' : RegularRel rep (n + 1 + cs.length) A := by
      simpa only [List.length_cons, Nat.add_right_comm, Nat.add_assoc] using hA
    have h₁ := regular_spec_last (ih hA') c
    refine regular_congr (fun ds hlen ↦ ?_) h₁
    change (ds.length = n ∧ (ds ++ [c]).length = n + 1 ∧ (ds ++ [c]) ++ cs ∈ A) ↔
      ds.length = n ∧ ds ++ (c :: cs) ∈ A
    simp [hlen, List.append_assoc]

theorem regular_evalTerms [Fintype Γ] (rep : DomainRep Γ) (const : S.C → ℕ)
    (xs : List ℕ) {m : ℕ} (ts : Fin m → Term S)
    (hts : ∀ k (x : ℕ), ts k = .inl x → x ∈ xs)
    {A : Set (List ℕ)} (hA : RegularRel rep m A) :
    RegularRel rep xs.length {ds | ds.length = xs.length ∧
      List.ofFn (fun k : Fin m ↦ evalTerm const (assign (fun _ ↦ 0) xs ds) (ts k)) ∈ A} := by
  let n := xs.length
  let cs : List ℕ := List.ofFn (fun k : Fin m ↦ evalTerm const (fun _ ↦ 0) (ts k))
  have hcs : cs.length = m := List.length_ofFn
  let f : Fin m → Fin (n + cs.length) := fun k ↦
    match ts k with
    | .inl x =>
      ⟨xs.idxOf x, by
        have h₁ : xs.idxOf x ≤ n := List.idxOf_le_length
        have h₂ := k.2
        omega⟩
    | .inr _ => ⟨n + k.1, by have := k.2; omega⟩
  have hpull := regular_spec_append cs (regular_pullback f hA)
  refine regular_congr (fun ds hlen ↦ ?_) hpull
  change (ds.length = n ∧ (ds ++ cs).length = n + cs.length ∧
    List.ofFn (fun k : Fin m ↦ (ds ++ cs).getD (f k) 0) ∈ A) ↔
    ds.length = n ∧
      List.ofFn (fun k : Fin m ↦ evalTerm const (assign (fun _ ↦ 0) xs ds) (ts k)) ∈ A
  have heval : List.ofFn (fun k : Fin m ↦ (ds ++ cs).getD (f k) 0) =
      List.ofFn (fun k : Fin m ↦ evalTerm const (assign (fun _ ↦ 0) xs ds) (ts k)) := by
    apply List.ext_getElem (by simp)
    intro k hk₁ hk₂
    simp only [List.getElem_ofFn]
    let k' : Fin m := ⟨k, by simpa using hk₁⟩
    change (ds ++ cs).getD (f k') 0 = evalTerm const (assign (fun _ ↦ 0) xs ds) (ts k')
    cases htk : ts k' with
    | inl x =>
      have hx : x ∈ xs := hts k' x htk
      have hidx : xs.idxOf x < ds.length := by
        rw [hlen]
        exact List.idxOf_lt_length_of_mem hx
      have hf : (f k' : ℕ) = xs.idxOf x := by simp [f, htk]
      rw [hf, getD_append_left ds cs _ hidx, ← assign_on (fun _ ↦ 0) xs ds x hx]
      rfl
    | inr c =>
      have hf : (f k' : ℕ) = ds.length + k'.1 := by
        rw [hlen]
        simp [f, n, htk]
      have hkcs : k'.1 < cs.length := by simp [hcs, k'.2]
      rw [hf, getD_append_right ds cs k'.1, getD_eq_getElem_of_lt cs k'.1 hkcs]
      simp [cs, htk, evalTerm]
  dsimp only [n]
  rw [heval]
  simp [hlen]

theorem regular_extSat_of_subset [Fintype Γ] (rep : DomainRep Γ)
    (rels : S.R → Set (List ℕ)) (const : S.C → ℕ) (P : Formula S → Set (List ℕ))
    (ψ φ : Formula S) (hsub : free ψ ⊆ free φ)
    (hψ : RegularRel rep (freeList ψ).length (hatSet rels const P ψ)) :
    RegularRel rep (freeList φ).length {ds | ds.length = (freeList φ).length ∧
      ExtSat rels const P ψ (assign (fun _ ↦ 0) (freeList φ) ds)} := by
  let ys := freeList ψ
  let xs := freeList φ
  have hmem (k : Fin ys.length) : ys[k] ∈ xs := by
    rw [mem_freeList]
    exact hsub ((mem_freeList ψ _).mp (List.getElem_mem k.2))
  let f : Fin ys.length → Fin xs.length := fun k ↦
    ⟨xs.idxOf ys[k], List.idxOf_lt_length_of_mem (hmem k)⟩
  have hpull := regular_pullback f hψ
  refine regular_congr (fun ds hlen ↦ ?_) hpull
  change (ds.length = xs.length ∧ List.ofFn (fun k : Fin ys.length ↦ ds.getD (f k) 0) ∈ hatSet rels const P ψ) ↔
    ds.length = xs.length ∧ ExtSat rels const P ψ (assign (fun _ ↦ 0) xs ds)
  have hmap : List.ofFn (fun k : Fin ys.length ↦ ds.getD (f k) 0) =
      ys.map (assign (fun _ ↦ 0) xs ds) := by
    apply List.ext_getElem (by simp)
    intro k hk₁ hk₂
    simp only [List.getElem_ofFn, List.getElem_map]
    let k' : Fin ys.length := ⟨k, by simpa using hk₁⟩
    exact (assign_on (fun _ ↦ 0) xs ds ys[k'] (hmem k')).symm
  rw [hmap, hatSet_map_iff]

private theorem regular_hatSet_temporal [Fintype Γ] (rep : DomainRep Γ)
    (rels : S.R → Set (List ℕ)) (const : S.C → ℕ) (P : Formula S → Set (List ℕ))
    (α : Formula S)
    (hExt : ∀ v, ExtSat rels const P α v ↔ (freeList α).map v ∈ P α)
    (hP : RegularRel rep (freeList α).length (P α)) :
    RegularRel rep (freeList α).length (hatSet rels const P α) := by
  refine regular_congr (fun ds hlen ↦ ?_) hP
  rw [hatSet_iff, hExt, map_assign (fun _ ↦ 0) (freeList α) ds (freeList_nodup α) hlen]
  simp [hlen]

theorem regular_hatSet [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (i : ℕ) (P : Formula S → Set (List ℕ)) (φ : Formula S)
    (hP : ∀ ψ ∈ tsub φ, RegularRel rep (freeList ψ).length (P ψ)) :
    RegularRel rep (freeList φ).length (hatSet (D.rel i) D.const P φ) := by
  induction φ with
  | eq t₁ t₂ =>
    let xs := freeList (.eq t₁ t₂)
    let ts : Fin 2 → Term S := ![t₁, t₂]
    have hts : ∀ k (x : ℕ), ts k = .inl x → x ∈ xs := by
      intro k x hkx
      rw [mem_freeList]
      fin_cases k
      · apply Finset.mem_union_left
        change t₁ = .inl x at hkx
        simp [hkx, termVars]
      · apply Finset.mem_union_right
        change t₂ = .inl x at hkx
        simp [hkx, termVars]
    have hreg := regular_evalTerms rep D.const xs ts hts rep.eq_regular
    refine regular_congr (fun ds hlen ↦ ?_) hreg
    rw [hatSet_iff]
    change (ds.length = xs.length ∧
      ∃ d : ℕ, List.ofFn (fun k : Fin 2 ↦ evalTerm D.const (assign (fun _ ↦ 0) xs ds) (ts k)) = [d, d]) ↔
      ds.length = xs.length ∧
        evalTerm D.const (assign (fun _ ↦ 0) xs ds) t₁ = evalTerm D.const (assign (fun _ ↦ 0) xs ds) t₂
    simp only [List.ofFn_succ, List.ofFn_zero, List.cons.injEq, and_true, exists_eq_right']
    rfl
  | pred r ts =>
    let xs := freeList (.pred r ts)
    have hts : ∀ k (x : ℕ), ts k = .inl x → x ∈ xs := by
      intro k x hkx
      rw [mem_freeList]
      simp only [free, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨k, by simp [hkx, termVars]⟩
    have hreg := regular_evalTerms rep D.const xs ts hts (hD i r)
    refine regular_congr (fun ds hlen ↦ ?_) hreg
    rw [hatSet_iff]
    rfl
  | neg ψ ih =>
    have hreg := regular_compl (ih hP)
    refine regular_congr (fun ds hlen ↦ ?_) hreg
    change ds ∉ hatSet (D.rel i) D.const P ψ ↔ ds ∈ hatSet (D.rel i) D.const P (.neg ψ)
    rw [hatSet_iff, hatSet_iff]
    have hlen' : ds.length = (freeList ψ).length := hlen
    change ¬ (ds.length = (freeList ψ).length ∧
      ExtSat (D.rel i) D.const P ψ (assign (fun _ ↦ 0) (freeList ψ) ds)) ↔
      ds.length = (freeList ψ).length ∧
        ¬ ExtSat (D.rel i) D.const P ψ (assign (fun _ ↦ 0) (freeList ψ) ds)
    simp [hlen']
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ := regular_extSat_of_subset rep (D.rel i) D.const P ψ₁ (.or ψ₁ ψ₂)
      Finset.subset_union_left (ih₁ fun α hα ↦ hP α (List.mem_append_left _ hα))
    have h₂ := regular_extSat_of_subset rep (D.rel i) D.const P ψ₂ (.or ψ₁ ψ₂)
      Finset.subset_union_right (ih₂ fun α hα ↦ hP α (List.mem_append_right _ hα))
    refine regular_congr (fun ds hlen ↦ ?_) (regular_union h₁ h₂)
    rw [hatSet_iff]
    change ((ds.length = (freeList (.or ψ₁ ψ₂)).length ∧
      ExtSat (D.rel i) D.const P ψ₁ (assign (fun _ ↦ 0) (freeList (.or ψ₁ ψ₂)) ds)) ∨
      (ds.length = (freeList (.or ψ₁ ψ₂)).length ∧
      ExtSat (D.rel i) D.const P ψ₂ (assign (fun _ ↦ 0) (freeList (.or ψ₁ ψ₂)) ds))) ↔
      ds.length = (freeList (.or ψ₁ ψ₂)).length ∧
        (ExtSat (D.rel i) D.const P ψ₁ (assign (fun _ ↦ 0) (freeList (.or ψ₁ ψ₂)) ds) ∨
          ExtSat (D.rel i) D.const P ψ₂ (assign (fun _ ↦ 0) (freeList (.or ψ₁ ψ₂)) ds))
    simp [hlen]
  | ex x ψ ih =>
    let xs := freeList (.ex x ψ)
    let ys := freeList ψ
    have hmem (k : Fin ys.length) (hne : ys[(k : ℕ)] ≠ x) : ys[(k : ℕ)] ∈ xs := by
      rw [mem_freeList]
      exact Finset.mem_erase.mpr ⟨hne, (mem_freeList ψ _).mp (List.getElem_mem k.2)⟩
    let f : Fin ys.length → Fin (xs.length + 1) := fun k ↦
      if ys[(k : ℕ)] = x then Fin.last xs.length
      else ⟨xs.idxOf ys[(k : ℕ)], by
        have := List.idxOf_le_length (a := ys[(k : ℕ)]) (l := xs)
        omega⟩
    have hproj := regular_projLast (regular_pullback f (ih hP))
    refine regular_congr (fun ds hlen ↦ ?_) hproj
    rw [hatSet_iff]
    change (ds.length = xs.length ∧ ∃ d : ℕ, (ds ++ [d]).length = xs.length + 1 ∧
      List.ofFn (fun k : Fin ys.length ↦ (ds ++ [d]).getD (f k) 0) ∈ hatSet (D.rel i) D.const P ψ) ↔
      ds.length = xs.length ∧
        ∃ d : ℕ, ExtSat (D.rel i) D.const P ψ (Function.update (assign (fun _ ↦ 0) xs ds) x d)
    have hmap (d : ℕ) : List.ofFn (fun k : Fin ys.length ↦ (ds ++ [d]).getD (f k) 0) =
        ys.map (Function.update (assign (fun _ ↦ 0) xs ds) x d) := by
      apply List.ext_getElem (by simp)
      intro k hk₁ hk₂
      simp only [List.getElem_ofFn, List.getElem_map]
      let k' : Fin ys.length := ⟨k, by simpa using hk₁⟩
      change (ds ++ [d]).getD (f k') 0 =
        Function.update (assign (fun _ ↦ 0) xs ds) x d ys[(k' : ℕ)]
      by_cases hkx : ys[(k' : ℕ)] = x
      · have hf : (f k' : ℕ) = ds.length := by
          rw [hlen]
          simp [f, xs, hkx]
        rw [hf, getD_append_singleton_last ds d, hkx, Function.update_self]
      · have hf : (f k' : ℕ) = xs.idxOf ys[(k' : ℕ)] := by simp [f, hkx]
        have hidx : xs.idxOf ys[(k' : ℕ)] < ds.length := by
          rw [hlen]
          exact List.idxOf_lt_length_of_mem (hmem k' hkx)
        rw [hf, getD_append_left ds [d] _ hidx, Function.update_of_ne hkx,
          assign_on (fun _ ↦ 0) xs ds ys[(k' : ℕ)] (hmem k' hkx)]
    have hlen' : ds.length = xs.length := hlen
    simp only [hlen', List.length_append, List.length_singleton, true_and]
    apply exists_congr
    intro d
    rw [hmap d, hatSet_map_iff]
  | prev I ψ _ =>
    exact regular_hatSet_temporal rep (D.rel i) D.const P (.prev I ψ) (fun _ ↦ Iff.rfl)
      (hP _ (by simp [tsub]))
  | next I ψ _ =>
    exact regular_hatSet_temporal rep (D.rel i) D.const P (.next I ψ) (fun _ ↦ Iff.rfl)
      (hP _ (by simp [tsub]))
  | since I ψ₁ ψ₂ _ _ =>
    exact regular_hatSet_temporal rep (D.rel i) D.const P (.since I ψ₁ ψ₂) (fun _ ↦ Iff.rfl)
      (hP _ (by simp [tsub]))
  | «until» I ψ₁ ψ₂ _ _ =>
    exact regular_hatSet_temporal rep (D.rel i) D.const P (.until I ψ₁ ψ₂) (fun _ ↦ Iff.rfl)
      (hP _ (by simp [tsub]))

end MFOTLMon.Monitor

/-! Arithmetic and set invariants for the repaired bounded-until construction. -/

namespace MFOTLMon.Monitor

open Classical

variable {S : Signature}

/-- A positive lookahead bound cannot be crossed at offset zero. -/
theorem lookahead_find_pos (D : TempStruct S) (b' i : ℕ) (hb' : 0 < b') :
    0 < Nat.find (D.exists_lookahead b' i) := by
  have hm := Nat.find_spec (D.exists_lookahead b' i)
  by_contra h
  have heq : Nat.find (D.exists_lookahead b' i) = 0 := by omega
  rw [heq] at hm
  simp only [Nat.add_zero, Nat.sub_self] at hm
  omega

/-- Offsets in the finite lookahead window are exactly those below the metric bound. -/
theorem le_lookahead_iff (D : TempStruct S) (b' i : ℕ) (hb' : 0 < b') (j : ℕ) :
    j ≤ lookahead D b' i ↔ D.τ (i + j) - D.τ i < b' := by
  have hmpos := lookahead_find_pos D b' i hb'
  have hmspec := Nat.find_spec (D.exists_lookahead b' i)
  constructor
  · intro hj
    have hjm : j < Nat.find (D.exists_lookahead b' i) := by
      unfold lookahead at hj
      omega
    have hnot := Nat.find_min (D.exists_lookahead b' i) hjm
    omega
  · intro hj
    by_contra h
    have hmj : Nat.find (D.exists_lookahead b' i) ≤ j := by
      unfold lookahead at h
      omega
    have hmono := D.mono (show i + Nat.find (D.exists_lookahead b' i) ≤ i + j by omega)
    omega

/-- The final lookahead point is strictly before the upper metric endpoint. -/
theorem lookahead_spec (D : TempStruct S) (b' i : ℕ) (hb' : 0 < b') :
    D.τ (i + lookahead D b' i) - D.τ i < b' :=
  (le_lookahead_iff D b' i hb' _).mp le_rfl

/-- The point immediately after the lookahead window crosses its upper metric endpoint. -/
theorem lookahead_next_spec (D : TempStruct S) (b' i : ℕ) (hb' : 0 < b') :
    b' ≤ D.τ (i + (lookahead D b' i + 1)) - D.τ i := by
  have hmpos := lookahead_find_pos D b' i hb'
  have hm := Nat.find_spec (D.exists_lookahead b' i)
  have heq : lookahead D b' i + 1 = Nat.find (D.exists_lookahead b' i) := by
    unfold lookahead
    omega
  rwa [heq]

/-- Sliding the current point forward cannot move the absolute window endpoint backward. -/
theorem lookahead_endpoint_mono (D : TempStruct S) (b' : ℕ) (hb' : 0 < b')
    {i j : ℕ} (hij : i ≤ j) :
    i + lookahead D b' i ≤ j + lookahead D b' j := by
  by_cases hend : i + lookahead D b' i ≤ j
  · omega
  · have hjend : j ≤ i + lookahead D b' i := by omega
    have hidx : j + (i + lookahead D b' i - j) = i + lookahead D b' i := by omega
    have hspec := lookahead_spec D b' i hb'
    have hmono := D.mono hij
    have hsmall : D.τ (j + (i + lookahead D b' i - j)) - D.τ j < b' := by
      rw [hidx]
      omega
    have hk := (le_lookahead_iff D b' j hb' _).mpr hsmall
    omega

@[simp] theorem prevLookahead_zero (D : TempStruct S) (b' : ℕ) :
    prevLookahead D b' 0 = 0 := by
  simp only [prevLookahead, ↓reduceIte]

@[simp] theorem prevLookahead_succ (D : TempStruct S) (b' i : ℕ) :
    prevLookahead D b' (i + 1) = lookahead D b' i := by
  simp only [prevLookahead, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel]

/-- At most one old offset disappears when the current time point advances. -/
theorem lookahead_le_succ (D : TempStruct S) (b' i : ℕ) (hb' : 0 < b') :
    lookahead D b' i ≤ lookahead D b' (i + 1) + 1 := by
  have h : i + lookahead D b' i ≤ i + 1 + lookahead D b' (i + 1) := by
    simpa only [Nat.succ_eq_add_one] using
      lookahead_endpoint_mono D b' hb' (Nat.le_succ i)
  omega

/-- A finite metric interval has a positive upper endpoint. -/
theorem interval_hi_pos (I : Interval) (b' : ℕ) (hb' : I.hi = b') : 0 < b' := by
  have h := I.lo_lt_hi
  rw [hb'] at h
  have hlo : I.lo < b' := by exact_mod_cast h
  omega

/-- A timestamp age separates into its old age and the intervening elapsed time. -/
theorem until_timestamp_age (D : TempStruct S) {j i : ℕ} (hji : j ≤ i) :
    D.τ (i + 1) - D.τ j = (D.τ i - D.τ j) + (D.τ (i + 1) - D.τ i) := by
  have h₁ := D.mono hji
  have h₂ : D.τ i ≤ D.τ (i + 1) := D.mono (by omega)
  omega

/-- The one-coordinate tuple representation is injective. -/
theorem until_append_singleton_inj {a b : List ℕ} {j k : ℕ} :
    a ++ [j] = b ++ [k] ↔ a = b ∧ j = k := by
  constructor
  · intro h
    have hr := congrArg List.reverse h
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append] at hr
    obtain ⟨hjk, hab⟩ := List.cons.inj hr
    exact ⟨List.reverse_injective hab, hjk⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Three-coordinate tuple representation is injective, with no tuple-length premise. -/
theorem until_append_triple_inj {a b : List ℕ} {j j' t k k' u : ℕ} :
    a ++ [j, j', t] = b ++ [k, k', u] ↔ a = b ∧ j = k ∧ j' = k' ∧ t = u := by
  have hleft : a ++ [j, j', t] = ((a ++ [j]) ++ [j']) ++ [t] := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hright : b ++ [k, k', u] = ((b ++ [k]) ++ [k']) ++ [u] := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hleft, hright, until_append_singleton_inj, until_append_singleton_inj,
    until_append_singleton_inj]
  tauto

/-- Membership in one repaired R step, with the tuple coordinates exposed. -/
theorem untilStep_r_mem_iff (D : TempStruct S) (I : Interval) (i : ℕ)
    (B G : ℕ → Set (List ℕ)) (r s : Set (List ℕ)) (a : List ℕ) (j : ℕ) :
    a ++ [j] ∈ (untilStep D I i B G r s).1 ↔
      (prevLookahead D I.hi.toNat i ≤ j ∧ j ≤ lookahead D I.hi.toNat i ∧
        ∀ k, j ≤ k → k ≤ lookahead D I.hi.toNat i → a ∈ B (i + k)) ∨
      (i ≠ 0 ∧ ∃ q, j = q - 1 ∧ a ++ [q] ∈ r ∧
        ∀ k, prevLookahead D I.hi.toNat i ≤ k → k ≤ lookahead D I.hi.toNat i →
          a ∈ B (i + k)) := by
  by_cases hi : i = 0
  · simp [untilStep, hi, and_assoc]
  · simp [untilStep, hi, and_assoc]

/-- The repaired R construction represents exactly the bounded beta suffixes. -/
theorem untilR_mem_iff (D : TempStruct S) (I : Interval) (hb : 0 < I.hi.toNat)
    (B G : ℕ → Set (List ℕ)) (i : ℕ) (a : List ℕ) (j : ℕ) :
    a ++ [j] ∈ (untilRS D I B G i).1 ↔
      j ≤ lookahead D I.hi.toNat i ∧
        ∀ k, j ≤ k → k ≤ lookahead D I.hi.toNat i → a ∈ B (i + k) := by
  induction i generalizing j with
  | zero =>
      rw [untilRS, untilStep_r_mem_iff]
      simp only [prevLookahead_zero, Nat.zero_le, true_and, ne_eq, not_true_eq_false,
        false_and, or_false]
  | succ i ih =>
      rw [untilRS, untilStep_r_mem_iff]
      have hi : i + 1 ≠ 0 := by omega
      simp only [prevLookahead_succ]
      have hwindow := lookahead_le_succ D I.hi.toNat i hb
      constructor
      · rintro (⟨hnew, hj, hB⟩ | ⟨_, q, hjq, hprev, hnew⟩)
        · exact ⟨hj, hB⟩
        · obtain ⟨hq, hBprev⟩ := (ih q).mp hprev
          refine ⟨by omega, ?_⟩
          intro k hjk hk
          by_cases hkn : lookahead D I.hi.toNat i ≤ k
          · exact hnew k hkn hk
          · have hqk : q ≤ k + 1 := by omega
            have hkold : k + 1 ≤ lookahead D I.hi.toNat i := by omega
            have hmem := hBprev (k + 1) hqk hkold
            have hidx : i + (k + 1) = i + 1 + k := by omega
            rwa [hidx] at hmem
      · rintro ⟨hj, hB⟩
        by_cases hnew : lookahead D I.hi.toNat i ≤ j
        · exact Or.inl ⟨hnew, hj, hB⟩
        · right
          refine ⟨hi, j + 1, by omega, (ih (j + 1)).mpr ⟨by omega, ?_⟩, ?_⟩
          · intro k hjk hk
            have hkpos : 0 < k := by omega
            have hkcur : k - 1 ≤ lookahead D I.hi.toNat (i + 1) := by omega
            have hmem := hB (k - 1) (by omega) hkcur
            have hidx : i + 1 + (k - 1) = i + k := by omega
            rwa [hidx] at hmem
          · intro k hlow hhigh
            exact hB k (by omega) hhigh

end MFOTLMon.Monitor

/-! Pure witness invariants for the S component of repaired bounded until. -/

namespace MFOTLMon.Monitor

open Classical

variable {S : Signature}

/-- Expose the three alternatives in the repaired S update. -/
theorem untilStep_s_mem_iff (D : TempStruct S) (I : Interval) (i : ℕ)
    (B G : ℕ → Set (List ℕ)) (r s : Set (List ℕ)) (a : List ℕ) (j j' t : ℕ) :
    a ++ [j, j', t] ∈ (untilStep D I i B G r s).2 ↔
      (prevLookahead D I.hi.toNat i ≤ j ∧ j ≤ j' ∧ j' ≤ lookahead D I.hi.toNat i ∧
        a ∈ G (i + j') ∧ t = D.τ (i + j') - D.τ i ∧ I.lo ≤ t ∧
        ∀ k, j ≤ k → k < j' → a ∈ B (i + k)) ∨
      (i ≠ 0 ∧ ∃ q q' t', j = q - 1 ∧ j' = q' - 1 ∧
        a ++ [q, q', t'] ∈ s ∧ 1 ≤ q' ∧
        t + (D.τ i - D.τ (i - 1)) = t' ∧ I.lo ≤ t) ∨
      (i ≠ 0 ∧ ∃ q, j = q - 1 ∧ a ++ [q] ∈ r ∧
        prevLookahead D I.hi.toNat i ≤ j' ∧ j' ≤ lookahead D I.hi.toNat i ∧
        a ∈ G (i + j') ∧ t = D.τ (i + j') - D.τ i ∧ I.lo ≤ t ∧
        ∀ k, prevLookahead D I.hi.toNat i ≤ k → k < j' → a ∈ B (i + k)) := by
  dsimp only [untilStep]
  rw [Set.mem_union, Set.mem_union, or_assoc]
  refine or_congr ?_ (or_congr ?_ ?_)
  · simp only [Set.mem_setOf, until_append_triple_inj]
    constructor
    · rintro ⟨a₁, j₁, j'₁, t₁, ⟨rfl, rfl, rfl, rfl⟩, h⟩
      exact h
    · rintro h
      exact ⟨a, j, j', t, ⟨rfl, rfl, rfl, rfl⟩, h⟩
  · by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, ↓reduceIte, ne_eq, not_false_eq_true, true_and, Set.mem_setOf,
        until_append_triple_inj]
      constructor
      · rintro ⟨a₁, q, q', t₁, t', ⟨rfl, rfl, rfl, rfl⟩, hs, hq', ht', hlo⟩
        exact ⟨q, q', t', rfl, rfl, hs, hq', ht', hlo⟩
      · rintro ⟨q, q', t', rfl, rfl, hs, hq', ht', hlo⟩
        exact ⟨a, q, q', t, t', ⟨rfl, rfl, rfl, rfl⟩, hs, hq', ht', hlo⟩
  · by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, ↓reduceIte, ne_eq, not_false_eq_true, true_and, Set.mem_setOf,
        until_append_triple_inj]
      constructor
      · rintro ⟨a₁, q, j'₁, t₁, ⟨rfl, rfl, rfl, rfl⟩, hr, a₂, j₂, j'₂, t₂,
          ⟨rfl, rfl, rfl, rfl⟩, _, hj', hj'ℓ, hG, ht, hlo, hB⟩
        exact ⟨q, rfl, hr, hj', hj'ℓ, hG, ht, hlo, hB⟩
      · rintro ⟨q, rfl, hr, hj', hj'ℓ, hG, ht, hlo, hB⟩
        exact ⟨a, q, j', t, ⟨rfl, rfl, rfl, rfl⟩, hr, a, _, j', t,
          ⟨rfl, rfl, rfl, rfl⟩, le_rfl, hj', hj'ℓ, hG, ht, hlo, hB⟩

/-- The repaired S construction stores exactly the bounded until witnesses. -/
theorem untilS_mem_iff (D : TempStruct S) (I : Interval) (hb : 0 < I.hi.toNat)
    (B G : ℕ → Set (List ℕ)) (i : ℕ) (a : List ℕ) (j j' t : ℕ) :
    a ++ [j, j', t] ∈ (untilRS D I B G i).2 ↔
      j ≤ j' ∧ j' ≤ lookahead D I.hi.toNat i ∧
        t = D.τ (i + j') - D.τ i ∧ I.lo ≤ t ∧ a ∈ G (i + j') ∧
        ∀ k, j ≤ k → k < j' → a ∈ B (i + k) := by
  induction i generalizing j j' t with
  | zero =>
      rw [untilRS, untilStep_s_mem_iff]
      simp only [prevLookahead_zero, Nat.zero_le, true_and, ne_eq, not_true_eq_false,
        false_and, or_false]
      tauto
  | succ i ih =>
      rw [untilRS, untilStep_s_mem_iff]
      simp only [prevLookahead_succ, Nat.add_sub_cancel]
      have hi : i + 1 ≠ 0 := by omega
      have hwindow := lookahead_le_succ D I.hi.toNat i hb
      have htime : D.τ i ≤ D.τ (i + 1) := D.mono (by omega)
      constructor
      · rintro (⟨hnew, hj, hj', hG, ht, hlo, hB⟩ |
          ⟨_, q, q', t', hjq, hj'q', hprev, hq'pos, hage, hlo⟩ |
          ⟨_, q, hjq, hprev, hnew, hj', hG, ht, hlo, hBnew⟩)
        · exact ⟨hj, hj', ht, hlo, hG, hB⟩
        · obtain ⟨hqq', hq'ell, ht', hlo', hG, hBprev⟩ := (ih q q' t').mp hprev
          have hidx : i + q' = i + 1 + j' := by omega
          have hwitness := D.mono (show i + 1 ≤ i + q' by omega)
          have hcurage : t = D.τ (i + 1 + j') - D.τ (i + 1) := by
            rw [hidx] at ht' hwitness
            omega
          refine ⟨by omega, by omega, hcurage, hlo, ?_, ?_⟩
          · rwa [hidx] at hG
          · intro k hjk hkj'
            have hmem := hBprev (k + 1) (by omega) (by omega)
            have hkidx : i + (k + 1) = i + 1 + k := by omega
            rwa [hkidx] at hmem
        · obtain ⟨hq, hBprev⟩ :=
            (untilR_mem_iff D I hb B G i a q).mp hprev
          refine ⟨by omega, hj', ht, hlo, hG, ?_⟩
          intro k hjk hkj'
          by_cases hkn : lookahead D I.hi.toNat i ≤ k
          · exact hBnew k hkn hkj'
          · have hmem := hBprev (k + 1) (by omega) (by omega)
            have hkidx : i + (k + 1) = i + 1 + k := by omega
            rwa [hkidx] at hmem
      · rintro ⟨hjj', hj'ell, ht, hlo, hG, hB⟩
        by_cases hjnew : lookahead D I.hi.toNat i ≤ j
        · exact Or.inl ⟨hjnew, hjj', hj'ell, hG, ht, hlo, hB⟩
        · by_cases hj'old : j' < lookahead D I.hi.toNat i
          · apply Or.inr ∘ Or.inl
            let t' := t + (D.τ (i + 1) - D.τ i)
            refine ⟨hi, j + 1, j' + 1, t', by omega, by omega, ?_, by omega, rfl, hlo⟩
            apply (ih (j + 1) (j' + 1) t').mpr
            have hidx : i + (j' + 1) = i + 1 + j' := by omega
            have hwitness := D.mono (show i + 1 ≤ i + 1 + j' by omega)
            refine ⟨by omega, by omega, ?_, by dsimp [t']; omega, ?_, ?_⟩
            · dsimp [t']
              rw [hidx]
              omega
            · rwa [hidx]
            · intro k hjk hkj'
              have hkpos : 0 < k := by omega
              have hmem := hB (k - 1) (by omega) (by omega)
              have hkidx : i + 1 + (k - 1) = i + k := by omega
              rwa [hkidx] at hmem
          · apply Or.inr ∘ Or.inr
            refine ⟨hi, j + 1, by omega, ?_, by omega, hj'ell, hG, ht, hlo, ?_⟩
            · apply (untilR_mem_iff D I hb B G i a (j + 1)).mpr
              refine ⟨by omega, ?_⟩
              intro k hjk hk
              have hkpos : 0 < k := by omega
              have hmem := hB (k - 1) (by omega) (by omega)
              have hkidx : i + 1 + (k - 1) = i + k := by omega
              rwa [hkidx] at hmem
            · intro k hkl hkj'
              exact hB k (by omega) hkj'

/-- Projection of the S invariant gives the direct bounded-until witness condition. -/
theorem untilP_mem_iff (D : TempStruct S) (I : Interval) (b' : ℕ) (hb' : I.hi = b')
    (B G : ℕ → Set (List ℕ)) (i : ℕ) (a : List ℕ) :
    a ∈ untilP (untilRS D I B G i).2 ↔
      ∃ j', I.Mem (D.τ (i + j') - D.τ i) ∧ a ∈ G (i + j') ∧
        ∀ k, k < j' → a ∈ B (i + k) := by
  have hpos := interval_hi_pos I b' hb'
  have htoNat : I.hi.toNat = b' := by simp only [hb', ENat.toNat_natCast]
  have hb : 0 < I.hi.toNat := by omega
  change (∃ j' t, a ++ [0, j', t] ∈ (untilRS D I B G i).2) ↔ _
  constructor
  · rintro ⟨j', t, hs⟩
    obtain ⟨_, hj', ht, hlo, hG, hB⟩ := (untilS_mem_iff D I hb B G i a 0 j' t).mp hs
    have hupp := (le_lookahead_iff D I.hi.toNat i hb j').mp hj'
    refine ⟨j', ⟨?_, ?_⟩, hG, fun k hk ↦ hB k (Nat.zero_le k) hk⟩
    · rwa [← ht]
    · rw [hb']
      have hupp' : D.τ (i + j') - D.τ i < b' := by omega
      exact_mod_cast hupp'
  · rintro ⟨j', hI, hG, hB⟩
    have hupp : D.τ (i + j') - D.τ i < b' := by
      have h := hI.2
      rw [hb'] at h
      exact_mod_cast h
    have hj' := (le_lookahead_iff D I.hi.toNat i hb j').mpr (by omega)
    refine ⟨j', D.τ (i + j') - D.τ i, ?_⟩
    exact (untilS_mem_iff D I hb B G i a 0 j' _).mpr
      ⟨Nat.zero_le j', hj', rfl, hI.1, hG, fun k _ hk ↦ hB k hk⟩

end MFOTLMon.Monitor

/-! Pure witness invariants for the incremental since construction. -/

namespace MFOTLMon.Monitor

open Classical

variable {S : Signature}

/-- Expose new and retained witnesses in one since update. -/
theorem sinceStep_mem_iff (D : TempStruct S) (I : Interval) (i : ℕ)
    (B G r : Set (List ℕ)) (a : List ℕ) (t : ℕ) :
    a ++ [t] ∈ sinceStep D.τ I i B G r ↔
      (a ∈ G ∧ t = 0) ∨
      (i ≠ 0 ∧ a ∈ B ∧ (t : ℕ∞) < I.hi ∧
        ∃ t', a ++ [t'] ∈ r ∧ t = t' + (D.τ i - D.τ (i - 1))) := by
  by_cases hi : i = 0
  · simp [sinceStep, hi]
  · simp [sinceStep, hi, and_assoc]
    aesop

/-- The incremental since state stores exactly the witnesses whose ages
are below the upper bound. -/
theorem sinceR_mem_iff (D : TempStruct S) (I : Interval)
    (B G : ℕ → Set (List ℕ)) (i : ℕ) (a : List ℕ) (t : ℕ) :
    a ++ [t] ∈ sinceR D.τ I B G i ↔
      ∃ j, j ≤ i ∧ t = D.τ i - D.τ j ∧ (t : ℕ∞) < I.hi ∧ a ∈ G j ∧
        ∀ k, j < k → k ≤ i → a ∈ B k := by
  have hpos : (0 : ℕ∞) < I.hi := lt_of_le_of_lt (by simp only [zero_le]) I.lo_lt_hi
  induction i generalizing t with
  | zero =>
      rw [sinceR, sinceStep_mem_iff]
      simp only [ne_eq, not_true_eq_false, false_and, or_false]
      constructor
      · rintro ⟨hG, rfl⟩
        exact ⟨0, le_rfl, by omega, hpos, hG, fun k hk hk' ↦ by omega⟩
      · rintro ⟨j, hj, ht, _, hG, _⟩
        have hj0 : j = 0 := by omega
        subst j
        simpa only [Nat.sub_self] using And.intro hG ht
  | succ i ih =>
      rw [sinceR, sinceStep_mem_iff]
      simp only [Nat.add_sub_cancel]
      have hi : i + 1 ≠ 0 := by omega
      constructor
      · rintro (⟨hG, rfl⟩ | ⟨_, hB, hthi, t', hprev, htt'⟩)
        · exact ⟨i + 1, le_rfl, by omega, hpos, hG, fun k hk hk' ↦ by omega⟩
        · obtain ⟨j, hj, ht', _, hG, hBprev⟩ := (ih t').mp hprev
          have hage := until_timestamp_age D hj
          refine ⟨j, by omega, by omega, hthi, hG, ?_⟩
          intro k hjk hki
          by_cases hk : k = i + 1
          · simpa only [hk] using hB
          · exact hBprev k hjk (by omega)
      · rintro ⟨j, hj, ht, hthi, hG, hB⟩
        by_cases hlast : j = i + 1
        · left
          subst j
          exact ⟨hG, by simpa only [Nat.sub_self] using ht⟩
        · right
          have hji : j ≤ i := by omega
          have hage := until_timestamp_age D hji
          have hsmall : D.τ i - D.τ j ≤ t := by omega
          have hsmall' : ((D.τ i - D.τ j : ℕ) : ℕ∞) < I.hi :=
            lt_of_le_of_lt (by exact_mod_cast hsmall) hthi
          refine ⟨hi, hB (i + 1) (by omega) le_rfl, hthi, D.τ i - D.τ j, ?_, by omega⟩
          exact (ih _).mpr
            ⟨j, hji, rfl, hsmall', hG, fun k hjk hki ↦ hB k hjk (by omega)⟩

/-- The since projection enforces the lower metric bound on the stored witness. -/
theorem sinceP_mem_iff (D : TempStruct S) (I : Interval)
    (B G : ℕ → Set (List ℕ)) (i : ℕ) (a : List ℕ) :
    a ∈ sinceP I (sinceR D.τ I B G i) ↔
      ∃ j, j ≤ i ∧ I.Mem (D.τ i - D.τ j) ∧ a ∈ G j ∧
        ∀ k, j < k → k ≤ i → a ∈ B k := by
  change (∃ t, I.lo ≤ t ∧ a ++ [t] ∈ sinceR D.τ I B G i) ↔ _
  constructor
  · rintro ⟨t, hlo, hR⟩
    obtain ⟨j, hj, ht, hthi, hG, hB⟩ := (sinceR_mem_iff D I B G i a t).mp hR
    refine ⟨j, hj, ?_, hG, hB⟩
    rw [ht] at hlo hthi
    exact ⟨hlo, hthi⟩
  · rintro ⟨j, hj, hI, hG, hB⟩
    exact ⟨D.τ i - D.τ j, hI.1,
      (sinceR_mem_iff D I B G i a _).mpr ⟨j, hj, rfl, hI.2, hG, hB⟩⟩

end MFOTLMon.Monitor

/-! Semantic projection of the pure temporal witness invariants. -/

namespace MFOTLMon.Monitor

variable {S : Signature}

/-- Correct operand relations through the current time suffice for the since projection. -/
theorem sinceP_eq_satSet_of_correct (D : TempStruct S) (I : Interval)
    (β γ : Formula S) (hfree : free β = free γ)
    (B G : ℕ → Set (List ℕ)) (i : ℕ)
    (hB : ∀ k, k ≤ i → B k = satSet D β k)
    (hG : ∀ k, k ≤ i → G k = satSet D γ k) :
    sinceP I (sinceR D.τ I B G i) = satSet D (.since I β γ) i := by
  ext a
  rw [sinceP_mem_iff, satSet_since_iff D I β γ hfree]
  constructor
  · rintro ⟨j, hj, hI, hγ, hβ⟩
    refine ⟨j, hj, hI, ?_, ?_⟩
    · rwa [hG j hj] at hγ
    · intro k hjk hki
      have h := hβ k hjk hki
      rwa [hB k hki] at h
  · rintro ⟨j, hj, hI, hγ, hβ⟩
    refine ⟨j, hj, hI, ?_, ?_⟩
    · rwa [hG j hj]
    · intro k hjk hki
      rw [hB k hki]
      exact hβ k hjk hki

/-- Correct operand relations on the bounded future window suffice for the until projection. -/
theorem untilP_eq_satSet_of_correct (D : TempStruct S) (I : Interval)
    (b' : ℕ) (hb' : I.hi = b') (β γ : Formula S) (hfree : free β = free γ)
    (B G : ℕ → Set (List ℕ)) (i : ℕ)
    (hB : ∀ k, k ≤ i + lookahead D b' i → B k = satSet D β k)
    (hG : ∀ k, k ≤ i + lookahead D b' i → G k = satSet D γ k) :
    untilP (untilRS D I B G i).2 = satSet D (.until I β γ) i := by
  have hb := interval_hi_pos I b' hb'
  have hindex : ∀ j, I.Mem (D.τ (i + j) - D.τ i) → j ≤ lookahead D b' i := by
    intro j hI
    apply (le_lookahead_iff D b' i hb j).mpr
    have h := hI.2
    rw [hb'] at h
    exact_mod_cast h
  ext a
  rw [untilP_mem_iff D I b' hb', satSet_until_offset_iff D I β γ hfree]
  constructor
  · rintro ⟨j, hI, hγ, hβ⟩
    have hj := hindex j hI
    refine ⟨j, hI, ?_, ?_⟩
    · rwa [hG (i + j) (by omega)] at hγ
    · intro k hkj
      have h := hβ k hkj
      rwa [hB (i + k) (by omega)] at h
  · rintro ⟨j, hI, hγ, hβ⟩
    have hj := hindex j hI
    refine ⟨j, hI, ?_, ?_⟩
    · rwa [hG (i + j) (by omega)]
    · intro k hkj
      rw [hB (i + k) (by omega)]
      exact hβ k hkj

/-- Substitute correct operand relations in the complete since R invariant. -/
theorem sinceR_mem_satSet_iff (D : TempStruct S) (I : Interval) (β γ : Formula S)
    (B G : ℕ → Set (List ℕ)) (i : ℕ)
    (hB : ∀ k, k ≤ i → B k = satSet D β k)
    (hG : ∀ k, k ≤ i → G k = satSet D γ k) (a : List ℕ) (t : ℕ) :
    a ++ [t] ∈ sinceR D.τ I B G i ↔
      ∃ j, j ≤ i ∧ t = D.τ i - D.τ j ∧ (t : ℕ∞) < I.hi ∧ a ∈ satSet D γ j ∧
        ∀ k, j < k → k ≤ i → a ∈ satSet D β k := by
  rw [sinceR_mem_iff]
  constructor
  · rintro ⟨j, hj, ht, hthi, hγ, hβ⟩
    refine ⟨j, hj, ht, hthi, ?_, ?_⟩
    · rwa [hG j hj] at hγ
    · intro k hjk hki
      have h := hβ k hjk hki
      rwa [hB k hki] at h
  · rintro ⟨j, hj, ht, hthi, hγ, hβ⟩
    refine ⟨j, hj, ht, hthi, ?_, ?_⟩
    · rwa [hG j hj]
    · intro k hjk hki
      rw [hB k hki]
      exact hβ k hjk hki

/-- Substitute correct operand relations in the complete bounded-until R invariant. -/
theorem untilR_mem_satSet_iff (D : TempStruct S) (I : Interval) (b' : ℕ)
    (hb' : I.hi = b') (β : Formula S) (B G : ℕ → Set (List ℕ)) (i : ℕ)
    (hB : ∀ k, k ≤ i + lookahead D b' i → B k = satSet D β k)
    (a : List ℕ) (j : ℕ) :
    a ++ [j] ∈ (untilRS D I B G i).1 ↔
      j ≤ lookahead D b' i ∧
        ∀ k, j ≤ k → k ≤ lookahead D b' i → a ∈ satSet D β (i + k) := by
  have htoNat : I.hi.toNat = b' := by simp only [hb', ENat.toNat_natCast]
  have hpos := interval_hi_pos I b' hb'
  have hb : 0 < I.hi.toNat := by omega
  have hR := untilR_mem_iff D I hb B G i a j
  rw [htoNat] at hR
  rw [hR]
  constructor
  · rintro ⟨hj, hβ⟩
    refine ⟨hj, ?_⟩
    intro k hjk hk
    have h := hβ k hjk hk
    rwa [hB (i + k) (by omega)] at h
  · rintro ⟨hj, hβ⟩
    refine ⟨hj, ?_⟩
    intro k hjk hk
    rw [hB (i + k) (by omega)]
    exact hβ k hjk hk

/-- Substitute correct operand relations in the complete bounded-until S invariant. -/
theorem untilS_mem_satSet_iff (D : TempStruct S) (I : Interval) (b' : ℕ)
    (hb' : I.hi = b') (β γ : Formula S) (B G : ℕ → Set (List ℕ)) (i : ℕ)
    (hB : ∀ k, k ≤ i + lookahead D b' i → B k = satSet D β k)
    (hG : ∀ k, k ≤ i + lookahead D b' i → G k = satSet D γ k)
    (a : List ℕ) (j j' t : ℕ) :
    a ++ [j, j', t] ∈ (untilRS D I B G i).2 ↔
      j ≤ j' ∧ t = D.τ (i + j') - D.τ i ∧ I.Mem t ∧ a ∈ satSet D γ (i + j') ∧
        ∀ k, j ≤ k → k < j' → a ∈ satSet D β (i + k) := by
  have htoNat : I.hi.toNat = b' := by simp only [hb', ENat.toNat_natCast]
  have hpos := interval_hi_pos I b' hb'
  have hb : 0 < I.hi.toNat := by omega
  have hS := untilS_mem_iff D I hb B G i a j j' t
  rw [htoNat] at hS
  rw [hS]
  constructor
  · rintro ⟨hjj', hj', ht, hlo, hγ, hβ⟩
    have htime := (le_lookahead_iff D b' i hpos j').mp hj'
    have hI : I.Mem t := by
      refine ⟨hlo, ?_⟩
      rw [hb']
      have htlt : t < b' := by omega
      exact_mod_cast htlt
    refine ⟨hjj', ht, hI, ?_, ?_⟩
    · rwa [hG (i + j') (by omega)] at hγ
    · intro k hjk hkj'
      have h := hβ k hjk hkj'
      rwa [hB (i + k) (by omega)] at h
  · rintro ⟨hjj', ht, hI, hγ, hβ⟩
    have htlt : t < b' := by
      have h := hI.2
      rw [hb'] at h
      exact_mod_cast h
    have hj' := (le_lookahead_iff D b' i hpos j').mpr (by omega)
    refine ⟨hjj', hj', ht, hI.1, ?_, ?_⟩
    · rwa [hG (i + j') (by omega)]
    · intro k hjk hkj'
      rw [hB (i + k) (by omega)]
      exact hβ k hjk hkj'

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor

open Classical

variable {S : Signature} {Γ : Type}

theorem regular_guard [Fintype Γ] (rep : DomainRep Γ) (n : ℕ) (P : Prop)
    {A : Set (List ℕ)} (hA : P → RegularRel rep n A) :
    RegularRel rep n {ds | P ∧ ds ∈ A} := by
  by_cases hP : P
  · refine regular_congr (fun ds _ ↦ ?_) (hA hP)
    simp [hP]
  · refine regular_congr (A := ∅) (fun ds _ ↦ ?_) (regular_empty rep n)
    simp [hP]

theorem regular_append_list [Fintype Γ] {rep : DomainRep Γ} {n : ℕ} {A : Set (List ℕ)}
    (hA : RegularRel rep n A) (cs : List ℕ) :
    RegularRel rep (n + cs.length) {ds | ∃ a, a.length = n ∧ a ∈ A ∧ ds = a ++ cs} := by
  induction cs generalizing n A with
  | nil =>
    refine regular_congr (fun ds hlen ↦ ?_) hA
    change ds ∈ A ↔ ∃ a, a.length = n ∧ a ∈ A ∧ ds = a ++ []
    constructor
    · exact fun h ↦ ⟨ds, hlen, h, by simp⟩
    · rintro ⟨a, _, ha, heq⟩
      rw [List.append_nil] at heq
      exact heq ▸ ha
  | cons c cs ih =>
    have h₁ := regular_append_const hA c
    have h₂ := ih h₁
    have hlen_eq : n + 1 + cs.length = n + (c :: cs).length := by
      simp [Nat.add_right_comm, Nat.add_assoc]
    rw [hlen_eq] at h₂
    refine regular_congr (fun ds _ ↦ ?_) h₂
    change (∃ a₁, a₁.length = n + 1 ∧
      a₁ ∈ {ds | ∃ a, a.length = n ∧ a ∈ A ∧ ds = a ++ [c]} ∧ ds = a₁ ++ cs) ↔
      ∃ a, a.length = n ∧ a ∈ A ∧ ds = a ++ (c :: cs)
    constructor
    · rintro ⟨a₁, _, ⟨a, ha_len, haA, rfl⟩, rfl⟩
      exact ⟨a, ha_len, haA, by simp⟩
    · rintro ⟨a, ha_len, haA, rfl⟩
      exact ⟨a ++ [c], by simp [ha_len], ⟨a, ha_len, haA, rfl⟩, by simp⟩

theorem exists_append_singleton_of_length (ds : List ℕ) (n : ℕ) (h : ds.length = n + 1) :
    ∃ a t, a.length = n ∧ ds = a ++ [t] :=
  ⟨List.ofFn (fun i : Fin n ↦ ds.getD (Fin.castSucc i) 0), ds.getD n 0,
    List.length_ofFn, eq_ofFn_castSucc_append_last ds n h⟩

theorem exists_append_triple_of_length (ds : List ℕ) (n : ℕ) (h : ds.length = n + 3) :
    ∃ a j j' t, a.length = n ∧ ds = a ++ [j, j', t] := by
  obtain ⟨d₂, t, hd₂, rfl⟩ := exists_append_singleton_of_length ds (n + 2) h
  obtain ⟨d₁, j', hd₁, rfl⟩ := exists_append_singleton_of_length d₂ (n + 1) hd₂
  obtain ⟨a, j, ha, rfl⟩ := exists_append_singleton_of_length d₁ n hd₁
  exact ⟨a, j, j', t, ha, by simp⟩

theorem regular_sinceR [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S) (I : Interval)
    {n : ℕ} (B G : ℕ → Set (List ℕ)) (i : ℕ)
    (hB : ∀ k, k ≤ i → RegularRel rep n (B k))
    (hG : ∀ j, j ≤ i → RegularRel rep n (G j)) :
    RegularRel rep (n + 1) (sinceR D.τ I B G i) := by
  let A (j : ℕ) : Set (List ℕ) := G j ∩ {a | ∀ k ∈ Finset.Ioc j i, a ∈ B k}
  have hA (j : ℕ) (hj : j ∈ Finset.range (i + 1)) : RegularRel rep n (A j) := by
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact regular_inter (hG j hji)
      (regular_finset_inter rep n (Finset.Ioc j i) B fun k hk ↦
        hB k (Finset.mem_Ioc.mp hk).2)
  let R (j : ℕ) : Set (List ℕ) :=
    {ds | ((D.τ i - D.τ j : ℕ) : ℕ∞) < I.hi ∧
      ds ∈ {ds' | ∃ a, a.length = n ∧ a ∈ A j ∧ ds' = a ++ [D.τ i - D.τ j]}}
  have hR (j : ℕ) (hj : j ∈ Finset.range (i + 1)) : RegularRel rep (n + 1) (R j) :=
    regular_guard rep (n + 1) _ fun _ ↦ regular_append_const (hA j hj) _
  have hunion := regular_finset_union rep (n + 1) (Finset.range (i + 1)) R hR
  refine regular_congr (fun ds hlen ↦ ?_) hunion
  obtain ⟨a, t, ha_len, rfl⟩ := exists_append_singleton_of_length ds n hlen
  change (∃ j ∈ Finset.range (i + 1),
    ((D.τ i - D.τ j : ℕ) : ℕ∞) < I.hi ∧
      ∃ a', a'.length = n ∧ (a' ∈ G j ∧ ∀ k ∈ Finset.Ioc j i, a' ∈ B k) ∧
        a ++ [t] = a' ++ [D.τ i - D.τ j]) ↔
    a ++ [t] ∈ sinceR D.τ I B G i
  rw [sinceR_mem_iff]
  constructor
  · rintro ⟨j, hj, hhi, a', _, ⟨hGj, hBk⟩, heq⟩
    obtain ⟨rfl, rfl⟩ := until_append_singleton_inj.mp heq
    refine ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), rfl, hhi, hGj, ?_⟩
    intro k hjk hki
    exact hBk k (Finset.mem_Ioc.mpr ⟨hjk, hki⟩)
  · rintro ⟨j, hji, rfl, hhi, hGj, hBk⟩
    refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hji), hhi, a, ha_len,
      ⟨hGj, fun k hk ↦ hBk k (Finset.mem_Ioc.mp hk).1 (Finset.mem_Ioc.mp hk).2⟩, rfl⟩

theorem regular_sinceP [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S) (I : Interval)
    {n : ℕ} (B G : ℕ → Set (List ℕ)) (i : ℕ)
    (hB : ∀ k, k ≤ i → RegularRel rep n (B k))
    (hG : ∀ j, j ≤ i → RegularRel rep n (G j)) :
    RegularRel rep n (sinceP I (sinceR D.τ I B G i)) := by
  let R (j : ℕ) : Set (List ℕ) :=
    {a | I.Mem (D.τ i - D.τ j) ∧ a ∈ G j ∩ {a' | ∀ k ∈ Finset.Ioc j i, a' ∈ B k}}
  have hR (j : ℕ) (hj : j ∈ Finset.range (i + 1)) : RegularRel rep n (R j) := by
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact regular_guard rep n _ fun _ ↦
      regular_inter (hG j hji)
        (regular_finset_inter rep n (Finset.Ioc j i) B fun k hk ↦
          hB k (Finset.mem_Ioc.mp hk).2)
  have hunion := regular_finset_union rep n (Finset.range (i + 1)) R hR
  refine regular_congr (fun a _ ↦ ?_) hunion
  change (∃ j ∈ Finset.range (i + 1),
    I.Mem (D.τ i - D.τ j) ∧ a ∈ G j ∧ ∀ k ∈ Finset.Ioc j i, a ∈ B k) ↔
    a ∈ sinceP I (sinceR D.τ I B G i)
  rw [sinceP_mem_iff]
  constructor
  · rintro ⟨j, hj, hI, hGj, hBk⟩
    exact ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), hI, hGj,
      fun k hjk hki ↦ hBk k (Finset.mem_Ioc.mpr ⟨hjk, hki⟩)⟩
  · rintro ⟨j, hji, hI, hGj, hBk⟩
    exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hji), hI, hGj,
      fun k hk ↦ hBk k (Finset.mem_Ioc.mp hk).1 (Finset.mem_Ioc.mp hk).2⟩

theorem regular_untilR [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S) (I : Interval)
    (hb : 0 < I.hi.toNat) {n : ℕ} (B G : ℕ → Set (List ℕ)) (i : ℕ)
    (hB : ∀ k, k ≤ lookahead D I.hi.toNat i → RegularRel rep n (B (i + k))) :
    RegularRel rep (n + 1) (untilRS D I B G i).1 := by
  let ℓ := lookahead D I.hi.toNat i
  let R (j : ℕ) : Set (List ℕ) :=
    {ds | ∃ a, a.length = n ∧ a ∈ {a' | ∀ k ∈ Finset.Icc j ℓ, a' ∈ B (i + k)} ∧ ds = a ++ [j]}
  have hR (j : ℕ) (_ : j ∈ Finset.range (ℓ + 1)) : RegularRel rep (n + 1) (R j) :=
    regular_append_const
      (regular_finset_inter rep n (Finset.Icc j ℓ) (fun k ↦ B (i + k)) fun k hk ↦
        hB k (Finset.mem_Icc.mp hk).2) j
  have hunion := regular_finset_union rep (n + 1) (Finset.range (ℓ + 1)) R hR
  refine regular_congr (fun ds hlen ↦ ?_) hunion
  obtain ⟨a, j, ha_len, rfl⟩ := exists_append_singleton_of_length ds n hlen
  change (∃ j' ∈ Finset.range (ℓ + 1),
    ∃ a', a'.length = n ∧ (∀ k ∈ Finset.Icc j' ℓ, a' ∈ B (i + k)) ∧ a ++ [j] = a' ++ [j']) ↔
    a ++ [j] ∈ (untilRS D I B G i).1
  rw [untilR_mem_iff D I hb]
  constructor
  · rintro ⟨j', hj', a', _, hBk, heq⟩
    obtain ⟨rfl, rfl⟩ := until_append_singleton_inj.mp heq
    exact ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hj'),
      fun k hjk hkℓ ↦ hBk k (Finset.mem_Icc.mpr ⟨hjk, hkℓ⟩)⟩
  · rintro ⟨hjℓ, hBk⟩
    exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjℓ), a, ha_len,
      fun k hk ↦ hBk k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2, rfl⟩

theorem regular_untilS [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S) (I : Interval)
    (hb : 0 < I.hi.toNat) {n : ℕ} (B G : ℕ → Set (List ℕ)) (i : ℕ)
    (hB : ∀ k, k ≤ lookahead D I.hi.toNat i → RegularRel rep n (B (i + k)))
    (hG : ∀ k, k ≤ lookahead D I.hi.toNat i → RegularRel rep n (G (i + k))) :
    RegularRel rep (n + 3) (untilRS D I B G i).2 := by
  let ℓ := lookahead D I.hi.toNat i
  let A (j' j : ℕ) : Set (List ℕ) :=
    G (i + j') ∩ {a | ∀ k ∈ Finset.Ico j j', a ∈ B (i + k)}
  let S_pair (j' j : ℕ) : Set (List ℕ) :=
    {ds | I.lo ≤ D.τ (i + j') - D.τ i ∧
      ds ∈ {ds' | ∃ a, a.length = n ∧ a ∈ A j' j ∧
        ds' = a ++ [j, j', D.τ (i + j') - D.τ i]}}
  have hS_pair (j' : ℕ) (hj' : j' ∈ Finset.range (ℓ + 1)) (j : ℕ)
      (_ : j ∈ Finset.range (j' + 1)) : RegularRel rep (n + 3) (S_pair j' j) := by
    have hj'ℓ : j' ≤ ℓ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj')
    have hAj : RegularRel rep n (A j' j) :=
      regular_inter (hG j' hj'ℓ)
        (regular_finset_inter rep n (Finset.Ico j j') (fun k ↦ B (i + k)) fun k hk ↦
          hB k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hj'ℓ)))
    exact regular_guard rep (n + 3) _ fun _ ↦
      regular_append_list hAj [j, j', D.τ (i + j') - D.τ i]
  let S_outer (j' : ℕ) : Set (List ℕ) :=
    {ds | ∃ j ∈ Finset.range (j' + 1), ds ∈ S_pair j' j}
  have hS_outer (j' : ℕ) (hj' : j' ∈ Finset.range (ℓ + 1)) :
      RegularRel rep (n + 3) (S_outer j') :=
    regular_finset_union rep (n + 3) (Finset.range (j' + 1)) (S_pair j') (hS_pair j' hj')
  have hunion := regular_finset_union rep (n + 3) (Finset.range (ℓ + 1)) S_outer hS_outer
  refine regular_congr (fun ds hlen ↦ ?_) hunion
  obtain ⟨a, j, j', t, ha_len, rfl⟩ := exists_append_triple_of_length ds n hlen
  change (∃ q' ∈ Finset.range (ℓ + 1), ∃ q ∈ Finset.range (q' + 1),
    I.lo ≤ D.τ (i + q') - D.τ i ∧
      ∃ a', a'.length = n ∧ (a' ∈ G (i + q') ∧ ∀ k ∈ Finset.Ico q q', a' ∈ B (i + k)) ∧
        a ++ [j, j', t] = a' ++ [q, q', D.τ (i + q') - D.τ i]) ↔
    a ++ [j, j', t] ∈ (untilRS D I B G i).2
  rw [untilS_mem_iff D I hb]
  constructor
  · rintro ⟨q', hq'ℓ, q, hqq', hlo, a', _, ⟨hG', hB'⟩, heq⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := until_append_triple_inj.mp heq
    exact ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hqq'),
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hq'ℓ), rfl, hlo, hG',
      fun k hjk hkj' ↦ hB' k (Finset.mem_Ico.mpr ⟨hjk, hkj'⟩)⟩
  · rintro ⟨hjj', hj'ℓ, rfl, hlo, hG', hB'⟩
    exact ⟨j', Finset.mem_range.mpr (Nat.lt_succ_of_le hj'ℓ),
      j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjj'), hlo, a, ha_len,
      ⟨hG', fun k hk ↦ hB' k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2⟩, rfl⟩

theorem regular_untilP [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S) (I : Interval)
    (b' : ℕ) (hb' : I.hi = b') {n : ℕ} (B G : ℕ → Set (List ℕ)) (i : ℕ)
    (hB : ∀ k, k ≤ lookahead D b' i → RegularRel rep n (B (i + k)))
    (hG : ∀ k, k ≤ lookahead D b' i → RegularRel rep n (G (i + k))) :
    RegularRel rep n (untilP (untilRS D I B G i).2) := by
  have hpos := interval_hi_pos I b' hb'
  let ℓ := lookahead D b' i
  let R (j' : ℕ) : Set (List ℕ) :=
    {a | I.Mem (D.τ (i + j') - D.τ i) ∧
      a ∈ G (i + j') ∩ {a' | ∀ k ∈ Finset.range j', a' ∈ B (i + k)}}
  have hR (j' : ℕ) (hj' : j' ∈ Finset.range (ℓ + 1)) : RegularRel rep n (R j') := by
    have hj'ℓ : j' ≤ ℓ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj')
    exact regular_guard rep n _ fun _ ↦
      regular_inter (hG j' hj'ℓ)
        (regular_finset_inter rep n (Finset.range j') (fun k ↦ B (i + k)) fun k hk ↦
          hB k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Finset.mem_range.mp hk) hj'ℓ)))
  have hunion := regular_finset_union rep n (Finset.range (ℓ + 1)) R hR
  refine regular_congr (fun a _ ↦ ?_) hunion
  change (∃ j' ∈ Finset.range (ℓ + 1),
    I.Mem (D.τ (i + j') - D.τ i) ∧ a ∈ G (i + j') ∧ ∀ k ∈ Finset.range j', a ∈ B (i + k)) ↔
    a ∈ untilP (untilRS D I B G i).2
  rw [untilP_mem_iff D I b' hb']
  constructor
  · rintro ⟨j', _, hI, hG', hB'⟩
    exact ⟨j', hI, hG', fun k hk ↦ hB' k (Finset.mem_range.mpr hk)⟩
  · rintro ⟨j', hI, hG', hB'⟩
    have hupp : D.τ (i + j') - D.τ i < b' := by
      have h := hI.2
      rw [hb'] at h
      exact_mod_cast h
    have hj'ℓ : j' ≤ ℓ := (le_lookahead_iff D b' i hpos j').mpr hupp
    exact ⟨j', Finset.mem_range.mpr (Nat.lt_succ_of_le hj'ℓ), hI, hG',
      fun k hk ↦ hB' k (Finset.mem_range.mp hk)⟩

theorem lemma_3_7_proved [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (_hlt : HasOrderPred D) (I : Interval) (β γ : Formula S)
    (hfree : free β = free γ) (P : Formula S → ℕ → Set (List ℕ)) (i : ℕ) :
    let B : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) β
    let G : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) γ
    let n := (freeList (Formula.since I β γ)).length
    (∀ j, j ≤ i → ∀ φ ∈ tsub β ++ tsub γ, RegularRel rep (freeList φ).length (P φ j) ∧
      P φ j = satSet D φ j) →
    (RegularRel rep (n + 1) (sinceR D.τ I B G i) ∧
      ∀ a : List ℕ, a.length = n → ∀ t : ℕ,
        (a ++ [t] ∈ sinceR D.τ I B G i ↔
          ∃ j, j ≤ i ∧ t = D.τ i - D.τ j ∧ (t : ℕ∞) < I.hi ∧ a ∈ satSet D γ j ∧
            ∀ k, j < k → k ≤ i → a ∈ satSet D β k)) ∧
    (RegularRel rep n (sinceP I (sinceR D.τ I B G i)) ∧
      sinceP I (sinceR D.τ I B G i) = satSet D (Formula.since I β γ) i) := by
  dsimp only
  intro hP
  let B : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) β
  let G : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) γ
  let n := (freeList (Formula.since I β γ)).length
  have hnβ : n = (freeList β).length := by
    simp only [n, freeList_since_left I β γ hfree]
  have hnγ : n = (freeList γ).length := by
    rw [hnβ]
    simp only [freeList, hfree]
  have hBreg (j : ℕ) (hj : j ≤ i) : RegularRel rep n (B j) := by
    rw [hnβ]
    exact regular_hatSet rep D hD j (fun ψ ↦ P ψ j) β fun φ hφ ↦
      (hP j hj φ (List.mem_append_left _ hφ)).1
  have hGreg (j : ℕ) (hj : j ≤ i) : RegularRel rep n (G j) := by
    rw [hnγ]
    exact regular_hatSet rep D hD j (fun ψ ↦ P ψ j) γ fun φ hφ ↦
      (hP j hj φ (List.mem_append_right _ hφ)).1
  have hBeq (j : ℕ) (hj : j ≤ i) : B j = satSet D β j :=
    hatSet_eq_satSet D j (fun ψ ↦ P ψ j) β fun φ hφ ↦
      (hP j hj φ (List.mem_append_left _ hφ)).2
  have hGeq (j : ℕ) (hj : j ≤ i) : G j = satSet D γ j :=
    hatSet_eq_satSet D j (fun ψ ↦ P ψ j) γ fun φ hφ ↦
      (hP j hj φ (List.mem_append_right _ hφ)).2
  refine ⟨⟨regular_sinceR rep D I B G i hBreg hGreg, ?_⟩,
    ⟨regular_sinceP rep D I B G i hBreg hGreg,
      sinceP_eq_satSet_of_correct D I β γ hfree B G i hBeq hGeq⟩⟩
  intro a _ t
  exact sinceR_mem_satSet_iff D I β γ B G i hBeq hGeq a t

theorem lemma_3_8_proved [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (_hlt : HasOrderPred D) (I : Interval) (b' : ℕ) (hb' : I.hi = b')
    (β γ : Formula S) (hfree : free β = free γ) (P : Formula S → ℕ → Set (List ℕ)) (i : ℕ) :
    let B : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) β
    let G : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) γ
    let n := (freeList (Formula.until I β γ)).length
    let ℓ := lookahead D b' i
    let RS := untilRS D I B G i
    (∀ k, k ≤ i + ℓ → ∀ φ ∈ tsub β ++ tsub γ, RegularRel rep (freeList φ).length (P φ k) ∧
      P φ k = satSet D φ k) →
    (RegularRel rep (n + 1) RS.1 ∧
      ∀ a : List ℕ, a.length = n → ∀ j : ℕ,
        (a ++ [j] ∈ RS.1 ↔ j ≤ ℓ ∧ ∀ k, j ≤ k → k ≤ ℓ → a ∈ satSet D β (i + k))) ∧
    (RegularRel rep (n + 3) RS.2 ∧
      ∀ a : List ℕ, a.length = n → ∀ j j' t : ℕ,
        (a ++ [j, j', t] ∈ RS.2 ↔
          j ≤ j' ∧ t = D.τ (i + j') - D.τ i ∧ I.Mem t ∧ a ∈ satSet D γ (i + j') ∧
            ∀ k, j ≤ k → k < j' → a ∈ satSet D β (i + k))) ∧
    (RegularRel rep n (untilP RS.2) ∧ untilP RS.2 = satSet D (Formula.until I β γ) i) := by
  dsimp only
  intro hP
  let B : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) β
  let G : ℕ → Set (List ℕ) := fun j => hatSet (D.rel j) D.const (fun ψ => P ψ j) γ
  let n := (freeList (Formula.until I β γ)).length
  let ℓ := lookahead D b' i
  have htoNat : I.hi.toNat = b' := by simp only [hb', ENat.toNat_natCast]
  have hpos := interval_hi_pos I b' hb'
  have hb : 0 < I.hi.toNat := by omega
  have hnβ : n = (freeList β).length := by
    simp only [n, freeList_until_left I β γ hfree]
  have hnγ : n = (freeList γ).length := by
    rw [hnβ]
    simp only [freeList, hfree]
  have hBreg (k : ℕ) (hk : k ≤ i + ℓ) : RegularRel rep n (B k) := by
    rw [hnβ]
    exact regular_hatSet rep D hD k (fun ψ ↦ P ψ k) β fun φ hφ ↦
      (hP k hk φ (List.mem_append_left _ hφ)).1
  have hGreg (k : ℕ) (hk : k ≤ i + ℓ) : RegularRel rep n (G k) := by
    rw [hnγ]
    exact regular_hatSet rep D hD k (fun ψ ↦ P ψ k) γ fun φ hφ ↦
      (hP k hk φ (List.mem_append_right _ hφ)).1
  have hBeq (k : ℕ) (hk : k ≤ i + ℓ) : B k = satSet D β k :=
    hatSet_eq_satSet D k (fun ψ ↦ P ψ k) β fun φ hφ ↦
      (hP k hk φ (List.mem_append_left _ hφ)).2
  have hGeq (k : ℕ) (hk : k ≤ i + ℓ) : G k = satSet D γ k :=
    hatSet_eq_satSet D k (fun ψ ↦ P ψ k) γ fun φ hφ ↦
      (hP k hk φ (List.mem_append_right _ hφ)).2
  have hBreg' (k : ℕ) (hk : k ≤ lookahead D I.hi.toNat i) : RegularRel rep n (B (i + k)) := by
    rw [htoNat] at hk
    exact hBreg (i + k) (by omega)
  have hGreg' (k : ℕ) (hk : k ≤ lookahead D I.hi.toNat i) : RegularRel rep n (G (i + k)) := by
    rw [htoNat] at hk
    exact hGreg (i + k) (by omega)
  refine ⟨⟨regular_untilR rep D I hb B G i hBreg', ?_⟩,
    ⟨regular_untilS rep D I hb B G i hBreg' hGreg', ?_⟩,
    ⟨regular_untilP rep D I b' hb' B G i (fun k hk ↦ hBreg (i + k) (by omega))
      (fun k hk ↦ hGreg (i + k) (by omega)),
      untilP_eq_satSet_of_correct D I b' hb' β γ hfree B G i hBeq hGeq⟩⟩
  · intro a _ j
    exact untilR_mem_satSet_iff D I b' hb' β B G i hBeq a j
  · intro a _ j j' t
    exact untilS_mem_satSet_iff D I b' hb' β γ B G i hBeq hGeq a j j' t

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor

namespace QueueProof

variable {S : Signature}

theorem run_zero (D : TempStruct S) (Φ : Formula S) : run D Φ 0 = init Φ := rfl

theorem run_succ (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    run D Φ (k + 1) = iteration D Φ (run D Φ k) := by
  exact Function.iterate_succ_apply' (iteration D Φ) k (init Φ)

theorem evalLoop_ell (D : TempStruct S) (Φ : Formula S) (fuel : ℕ) (s : State S) :
    (evalLoop D Φ fuel s).ell = s.ell := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      rw [evalLoop]
      split
      · exact ih _
      · rfl

theorem evalLoop_Q (D : TempStruct S) (Φ : Formula S) (fuel : ℕ) (s : State S) :
    (evalLoop D Φ fuel s).Q = s.Q := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      rw [evalLoop]
      split
      · exact ih _
      · rfl

theorem iteration_ell (D : TempStruct S) (Φ : Formula S) (s : State S) :
    (iteration D Φ s).ell = s.ell + 1 := by
  exact congrArg (fun n : ℕ ↦ n + 1) (evalLoop_ell D Φ (s.ell + 2) (afterBuild D s))

theorem iteration_Q (D : TempStruct S) (Φ : Formula S) (s : State S) :
    (iteration D Φ s).Q = updateQ D Φ s := by
  change updateQ D Φ (evalLoop D Φ (s.ell + 2) (afterBuild D s)) = updateQ D Φ s
  simp only [updateQ, evalLoop_Q, evalLoop_ell]
  rfl

theorem run_ell (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    (run D Φ k).ell = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [run_succ, iteration_ell, ih]

theorem mem_updateQ_fresh (D : TempStruct S) (Φ : Formula S) (s : State S)
    (α : Formula S) (hα : α ∈ tempSubs Φ) :
    (α, s.ell + 1, waitfor α) ∈ updateQ D Φ s := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨α, hα, rfl⟩

theorem mem_iteration_fresh (D : TempStruct S) (Φ : Formula S) (s : State S)
    (α : Formula S) (hα : α ∈ tempSubs Φ) :
    (α, s.ell + 1, waitfor α) ∈ (iteration D Φ s).Q := by
  change (α, s.ell + 1, waitfor α) ∈
    updateQ D Φ (evalLoop D Φ (s.ell + 2) (afterBuild D s))
  have hell : (evalLoop D Φ (s.ell + 2) (afterBuild D s)).ell = s.ell :=
    evalLoop_ell D Φ (s.ell + 2) (afterBuild D s)
  simpa only [hell] using
    mem_updateQ_fresh D Φ (evalLoop D Φ (s.ell + 2) (afterBuild D s)) α hα

theorem observation_one (D : TempStruct S) (Φ : Formula S) :
    ∀ α ∈ tempSubs Φ, ∀ k : ℕ, (α, k, waitfor α) ∈ (run D Φ k).Q := by
  intro α hα k
  cases k with
  | zero =>
      change (α, 0, waitfor α) ∈ (tempSubs Φ).map (fun β ↦ (β, 0, waitfor β))
      exact List.mem_map.mpr ⟨α, hα, rfl⟩
  | succ k =>
      rw [run_succ]
      simpa only [run_ell] using mem_iteration_fresh D Φ (run D Φ k) α hα

end QueueProof

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor.QueueProof

variable {S : Signature}

/-- Equal job keys carry equal waiting lists. This permits repeated identical occurrences. -/
def Coherent (Q : List (Formula S × ℕ × List (Formula S))) : Prop :=
  ∀ (α : Formula S) (j : ℕ) (U V : List (Formula S)),
    (α, j, U) ∈ Q → (α, j, V) ∈ Q → U = V

theorem mem_updateQ_cases (D : TempStruct S) (Φ : Formula S) (s : State S)
    (α : Formula S) (j : ℕ) (W : List (Formula S))
    (h : (α, j, W) ∈ updateQ D Φ s) :
    (∃ U, (α, j, U) ∈ s.Q ∧ U ≠ [] ∧
      W = (update U (D.τ (s.ell + 1) - D.τ s.ell)).flatMap waitfor) ∨
      (α ∈ tempSubs Φ ∧ j = s.ell + 1 ∧ W = waitfor α) := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨⟨β, m, U⟩, hmem, heq⟩ := List.mem_filterMap.mp h
    dsimp only at heq
    split at heq
    · cases heq
    · rename_i hU
      have heq' := Option.some.inj heq
      cases heq'
      exact Or.inl ⟨U, hmem, by simpa only [List.isEmpty_iff] using hU, rfl⟩
  · obtain ⟨β, hβ, heq⟩ := List.mem_map.mp h
    cases heq
    exact Or.inr ⟨hβ, rfl, rfl⟩

theorem updateQ_bounds (D : TempStruct S) (Φ : Formula S) (s : State S)
    (hbound : ∀ α j W, (α, j, W) ∈ s.Q → j ≤ s.ell) :
    ∀ α j W, (α, j, W) ∈ updateQ D Φ s → j ≤ s.ell + 1 := by
  intro α j W h
  rcases mem_updateQ_cases D Φ s α j W h with ⟨U, hU, _, _⟩ | ⟨_, hj, _⟩
  · exact (hbound α j U hU).trans (Nat.le_succ _)
  · exact hj.le

theorem updateQ_temporal (D : TempStruct S) (Φ : Formula S) (s : State S)
    (htemp : ∀ α j W, (α, j, W) ∈ s.Q → α ∈ tempSubs Φ) :
    ∀ α j W, (α, j, W) ∈ updateQ D Φ s → α ∈ tempSubs Φ := by
  intro α j W h
  rcases mem_updateQ_cases D Φ s α j W h with ⟨U, hU, _, _⟩ | ⟨hα, _, _⟩
  · exact htemp α j U hU
  · exact hα

theorem updateQ_coherent (D : TempStruct S) (Φ : Formula S) (s : State S)
    (hbound : ∀ α j W, (α, j, W) ∈ s.Q → j ≤ s.ell) (hcoh : Coherent s.Q) :
    Coherent (updateQ D Φ s) := by
  intro α j U V hU hV
  rcases mem_updateQ_cases D Φ s α j U hU with ⟨U', hU', _, rfl⟩ | ⟨_, hj, rfl⟩
  · rcases mem_updateQ_cases D Φ s α j V hV with ⟨V', hV', _, rfl⟩ | ⟨_, hj, _⟩
    · rw [hcoh α j U' V' hU' hV']
    · have := hbound α j U' hU'
      omega
  · rcases mem_updateQ_cases D Φ s α j V hV with ⟨V', hV', _, _⟩ | ⟨_, _, rfl⟩
    · have := hbound α j V' hV'
      omega
    · rfl

theorem run_queue_properties (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    (∀ α j W, (α, j, W) ∈ (run D Φ k).Q → j ≤ k) ∧
      (∀ α j W, (α, j, W) ∈ (run D Φ k).Q → α ∈ tempSubs Φ) ∧
      Coherent (run D Φ k).Q := by
  induction k with
  | zero =>
      constructor
      · intro α j W h
        obtain ⟨β, _, heq⟩ := List.mem_map.mp h
        cases heq
        exact Nat.le_refl 0
      · constructor
        · intro α j W h
          obtain ⟨β, hβ, heq⟩ := List.mem_map.mp h
          cases heq
          exact hβ
        · intro α j U V hU hV
          obtain ⟨β, _, hβ⟩ := List.mem_map.mp hU
          obtain ⟨γ, _, hγ⟩ := List.mem_map.mp hV
          cases hβ
          cases hγ
          rfl
  | succ k ih =>
      rw [run_succ, iteration_Q]
      have hbound : ∀ α j W, (α, j, W) ∈ (run D Φ k).Q →
          j ≤ (run D Φ k).ell := by
        simpa only [run_ell] using ih.1
      exact ⟨by simpa only [run_ell] using updateQ_bounds D Φ _ hbound,
        updateQ_temporal D Φ _ ih.2.1, updateQ_coherent D Φ _ hbound ih.2.2⟩

theorem run_queue_bounds (D : TempStruct S) (Φ : Formula S) (k : ℕ)
    (α : Formula S) (j : ℕ) (W : List (Formula S))
    (h : (α, j, W) ∈ (run D Φ k).Q) : j ≤ k :=
  (run_queue_properties D Φ k).1 α j W h

theorem run_queue_temporal (D : TempStruct S) (Φ : Formula S) (k : ℕ)
    (α : Formula S) (j : ℕ) (W : List (Formula S))
    (h : (α, j, W) ∈ (run D Φ k).Q) : α ∈ tempSubs Φ :=
  (run_queue_properties D Φ k).2.1 α j W h

theorem run_queue_coherent (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    Coherent (run D Φ k).Q := (run_queue_properties D Φ k).2.2

end MFOTLMon.Monitor.QueueProof

namespace MFOTLMon.Monitor.QueueProof

variable {S : Signature}

def Future : Formula S → Prop
  | .next _ _ => True
  | .until _ _ _ => True
  | _ => False

def GoodWaiting (W : List (Formula S)) : Prop :=
  ∀ φ ∈ W, Bounded φ ∧ Future φ

def waitWeight : Formula S → ℕ
  | .eq _ _ => 0
  | .pred _ _ => 0
  | .neg β => waitWeight β
  | .ex _ β => waitWeight β
  | .prev _ β => waitWeight β
  | .or β γ => waitWeight β + waitWeight γ
  | .since _ β γ => waitWeight β + waitWeight γ
  | .next _ β => 1 + waitWeight β
  | .until I β γ => I.hi.toNat + waitWeight β + waitWeight γ

def waitingWeight (W : List (Formula S)) : ℕ := (W.map waitWeight).sum

noncomputable def advance (W : List (Formula S)) (t : ℕ) : List (Formula S) :=
  (update W t).flatMap waitfor

theorem waitingWeight_append (U V : List (Formula S)) :
    waitingWeight (U ++ V) = waitingWeight U + waitingWeight V := by
  simp only [waitingWeight, List.map_append, List.sum_append]

theorem waitingWeight_waitfor (φ : Formula S) : waitingWeight (waitfor φ) = waitWeight φ := by
  induction φ <;> simp_all only [waitfor, waitWeight, waitingWeight,
    List.map_append, List.sum_append, List.map_nil, List.sum_nil, List.map_cons,
    List.sum_cons, Nat.add_zero]

theorem goodWaiting_append (U V : List (Formula S)) :
    GoodWaiting (U ++ V) ↔ GoodWaiting U ∧ GoodWaiting V := by
  constructor
  · intro h
    exact ⟨fun φ hφ ↦ h φ (List.mem_append_left V hφ),
      fun φ hφ ↦ h φ (List.mem_append_right U hφ)⟩
  · rintro ⟨hU, hV⟩ φ hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact hU φ hφ
    · exact hV φ hφ

theorem goodWaiting_waitfor (φ : Formula S) (hφ : Bounded φ) : GoodWaiting (waitfor φ) := by
  revert hφ
  induction φ with
  | eq _ _ =>
      intro _ ψ hψ
      cases hψ
  | pred _ _ =>
      intro _ ψ hψ
      cases hψ
  | neg β ih => exact ih
  | ex x β ih => exact ih
  | prev I β ih => exact ih
  | or β γ ihβ ihγ =>
      intro hφ
      exact (goodWaiting_append _ _).mpr ⟨ihβ hφ.1, ihγ hφ.2⟩
  | since I β γ ihβ ihγ =>
      intro hφ
      exact (goodWaiting_append _ _).mpr ⟨ihβ hφ.1, ihγ hφ.2⟩
  | next I β _ =>
      intro hφ ψ hψ
      have hψ' : ψ = .next I β := List.mem_singleton.mp hψ
      subst ψ
      exact ⟨hφ, trivial⟩
  | «until» I β γ _ _ =>
      intro hφ ψ hψ
      have hψ' : ψ = .until I β γ := List.mem_singleton.mp hψ
      subst ψ
      exact ⟨hφ, trivial⟩

theorem interval_hi_toNat_pos (I : Interval) (hfinite : I.hi ≠ ⊤) : 0 < I.hi.toNat := by
  have hpositive : (0 : ℕ∞) < I.hi :=
    (show (0 : ℕ∞) ≤ (I.lo : ℕ∞) from bot_le).trans_lt I.lo_lt_hi
  exact ENat.toNat_pos (ne_of_gt hpositive) hfinite

theorem shift_bounded (I : Interval) (t : ℕ) (h : (t : ℕ∞) < I.hi)
    (hfinite : I.hi ≠ ⊤) : (I.shift t h).hi ≠ ⊤ := by
  change I.hi - (t : ℕ∞) ≠ ⊤
  rw [← ENat.natCast_toNat hfinite, ← ENat.natCast_sub]
  simp

theorem advance_append (U V : List (Formula S)) (t : ℕ) :
    advance (U ++ V) t = advance U t ++ advance V t := by
  simp only [advance, update, List.flatMap_append]

theorem advance_singleton_good (φ : Formula S) (hφ : Bounded φ) (hfuture : Future φ)
    (t : ℕ) : GoodWaiting (advance [φ] t) := by
  cases φ with
  | next I β =>
      simpa only [advance, update, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        using goodWaiting_waitfor β hφ
  | «until» I β γ =>
      by_cases ht : (t : ℕ∞) < I.hi
      · simp only [advance, update, List.flatMap_cons, List.flatMap_nil, ht, ↓reduceDIte,
          List.append_nil, waitfor]
        intro ψ hψ
        have hψ' := List.mem_singleton.mp hψ
        subst ψ
        exact ⟨⟨shift_bounded I t ht hφ.1, hφ.2⟩, trivial⟩
      · simpa only [advance, update, List.flatMap_cons, List.flatMap_nil, ht, ↓reduceDIte,
          List.append_nil] using
          (goodWaiting_append _ _).mpr
            ⟨goodWaiting_waitfor β hφ.2.1, goodWaiting_waitfor γ hφ.2.2⟩
  | _ => exact hfuture.elim

theorem advance_singleton_weight (φ : Formula S) (hφ : Bounded φ) (hfuture : Future φ)
    (t : ℕ) : waitingWeight (advance [φ] t) ≤ waitWeight φ ∧
      (0 < t → waitingWeight (advance [φ] t) < waitWeight φ) := by
  cases φ with
  | next I β =>
      simp only [advance, update, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        waitingWeight_waitfor, waitWeight]
      omega
  | «until» I β γ =>
      have hpositive := interval_hi_toNat_pos I hφ.1
      by_cases ht : (t : ℕ∞) < I.hi
      · have hshift : (I.shift t ht).hi.toNat = I.hi.toNat - t := by
          simp only [Interval.shift,
            ENat.toNat_sub (n := (t : ℕ∞)) (by simp), ENat.toNat_natCast]
        simp only [advance, update, List.flatMap_cons, List.flatMap_nil, ht, ↓reduceDIte,
          List.append_nil, waitfor, waitingWeight, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, Nat.add_zero, waitWeight, hshift]
        omega
      · simp only [advance, update, List.flatMap_cons, List.flatMap_nil, ht, ↓reduceDIte,
          List.append_nil, waitingWeight_append, waitingWeight_waitfor, waitWeight]
        omega
  | _ => exact hfuture.elim

theorem advance_good (W : List (Formula S)) (hW : GoodWaiting W) (t : ℕ) :
    GoodWaiting (advance W t) := by
  revert hW
  induction W with
  | nil =>
      intro _ ψ hψ
      cases hψ
  | cons φ W ih =>
      intro hW
      have hφ := hW φ List.mem_cons_self
      have htail : GoodWaiting W := fun ψ hψ ↦ hW ψ (List.mem_cons_of_mem φ hψ)
      change GoodWaiting (advance ([φ] ++ W) t)
      rw [advance_append, goodWaiting_append]
      exact ⟨advance_singleton_good φ hφ.1 hφ.2 t, ih htail⟩

theorem advance_weight (W : List (Formula S)) (hW : GoodWaiting W) (t : ℕ) :
    waitingWeight (advance W t) ≤ waitingWeight W ∧
      (0 < t → W ≠ [] → waitingWeight (advance W t) < waitingWeight W) := by
  revert hW
  induction W with
  | nil =>
      intro _
      simp only [advance, update, List.flatMap_nil, waitingWeight,
        List.map_nil, List.sum_nil, le_refl, ne_eq, not_true_eq_false, false_implies,
        implies_true, and_self]
  | cons φ W ih =>
      intro hW
      have hφ := hW φ List.mem_cons_self
      have htail : GoodWaiting W := fun ψ hψ ↦ hW ψ (List.mem_cons_of_mem φ hψ)
      have hh := advance_singleton_weight φ hφ.1 hφ.2 t
      have ht := ih htail
      have hadv : waitingWeight (advance (φ :: W) t) =
          waitingWeight (advance [φ] t) + waitingWeight (advance W t) := by
        change waitingWeight (advance ([φ] ++ W) t) = _
        rw [advance_append, waitingWeight_append]
      have hcons : waitingWeight (φ :: W) = waitWeight φ + waitingWeight W := rfl
      simp only [hadv, hcons]
      constructor
      · omega
      · intro hpositive _
        have := hh.2 hpositive
        omega

theorem bounded_of_mem_subformulas (Φ : Formula S) :
    Bounded Φ → ∀ α, α ∈ subformulas Φ → Bounded α := by
  induction Φ with
  | eq _ _ =>
      intro hΦ α hα
      have hα' := List.mem_singleton.mp hα
      subst α
      exact hΦ
  | pred _ _ =>
      intro hΦ α hα
      have hα' := List.mem_singleton.mp hα
      subst α
      exact hΦ
  | neg β ih =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · exact ih hΦ α hα
  | ex x β ih =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · exact ih hΦ α hα
  | prev I β ih =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · exact ih hΦ α hα
  | next I β ih =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · exact ih hΦ α hα
  | or β γ ihβ ihγ =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · rcases List.mem_append.mp hα with hα | hα
        · exact ihβ hΦ.1 α hα
        · exact ihγ hΦ.2 α hα
  | since I β γ ihβ ihγ =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · rcases List.mem_append.mp hα with hα | hα
        · exact ihβ hΦ.1 α hα
        · exact ihγ hΦ.2 α hα
  | «until» I β γ ihβ ihγ =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · rcases List.mem_append.mp hα with hα | hα
        · exact ihβ hΦ.2.1 α hα
        · exact ihγ hΦ.2.2 α hα

theorem bounded_of_mem_tempSubs (Φ : Formula S) (hΦ : Bounded Φ) (α : Formula S)
    (hα : α ∈ tempSubs Φ) : Bounded α :=
  bounded_of_mem_subformulas Φ hΦ α (List.mem_filter.mp hα).1

theorem run_goodWaiting (D : TempStruct S) (Φ : Formula S) (hΦ : Bounded Φ) (k : ℕ) :
    ∀ α j W, (α, j, W) ∈ (run D Φ k).Q → GoodWaiting W := by
  induction k with
  | zero =>
      intro α j W hmem
      obtain ⟨β, hβ, heq⟩ := List.mem_map.mp hmem
      cases heq
      exact goodWaiting_waitfor _ (bounded_of_mem_tempSubs Φ hΦ _ hβ)
  | succ k ih =>
      intro α j W hmem
      rw [run_succ, iteration_Q] at hmem
      rcases mem_updateQ_cases D Φ (run D Φ k) α j W hmem with
        ⟨U, hU, _, rfl⟩ | ⟨hα, _, rfl⟩
      · exact advance_good U (ih α j U hU) _
      · exact goodWaiting_waitfor α (bounded_of_mem_tempSubs Φ hΦ α hα)

theorem mem_next_of_nonempty (D : TempStruct S) (Φ : Formula S) (k : ℕ)
    (α : Formula S) (j : ℕ) (W : List (Formula S))
    (hmem : (α, j, W) ∈ (run D Φ k).Q) (hne : W ≠ []) :
    (α, j, advance W (D.τ (k + 1) - D.τ k)) ∈ (run D Φ (k + 1)).Q := by
  rw [run_succ, iteration_Q]
  apply List.mem_append_left
  apply List.mem_filterMap.mpr
  refine ⟨(α, j, W), hmem, ?_⟩
  have hempty : W.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [hempty, Bool.false_eq_true, ↓reduceIte, run_ell, advance]

theorem exists_progress_step (D : TempStruct S) (k : ℕ) :
    ∃ l, k ≤ l ∧ D.τ l < D.τ (l + 1) := by
  by_contra h
  have hconstant_step : ∀ l, k ≤ l → D.τ (l + 1) = D.τ l := by
    intro l hl
    have hmono := D.mono (Nat.le_succ l)
    change D.τ l ≤ D.τ (l + 1) at hmono
    have hnot : ¬ D.τ l < D.τ (l + 1) := fun hlt ↦ h ⟨l, hl, hlt⟩
    omega
  have hconstant : ∀ n, D.τ (k + n) = D.τ k := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Nat.add_succ, hconstant_step (k + n) (by omega), ih]
  obtain ⟨l, hl⟩ := D.progress (D.τ k)
  rcases le_or_gt l k with hlk | hkl
  · have := D.mono hlk
    omega
  · have heq : l = k + (l - k) := by omega
    rw [heq, hconstant] at hl
    omega

theorem pending_later_weight (D : TempStruct S) (Φ : Formula S) (hΦ : Bounded Φ)
    (k : ℕ) (α : Formula S) (j : ℕ) (W : List (Formula S))
    (hmem : (α, j, W) ∈ (run D Φ k).Q)
    (hno : ∀ l, k ≤ l → (α, j, ([] : List (Formula S))) ∉ (run D Φ l).Q) (n : ℕ) :
    ∃ V, (α, j, V) ∈ (run D Φ (k + n)).Q ∧ waitingWeight V ≤ waitingWeight W := by
  induction n with
  | zero => exact ⟨W, hmem, le_rfl⟩
  | succ n ih =>
      obtain ⟨V, hV, hweight⟩ := ih
      have hne : V ≠ [] := by
        intro heq
        subst V
        exact hno (k + n) (by omega) hV
      have hgood := run_goodWaiting D Φ hΦ (k + n) α j V hV
      refine ⟨advance V (D.τ (k + n + 1) - D.τ (k + n)), ?_, ?_⟩
      · simpa only [Nat.add_succ] using mem_next_of_nonempty D Φ (k + n) α j V hV hne
      · exact (advance_weight V hgood _).1.trans hweight

theorem observation_two (D : TempStruct S) (Φ : Formula S) (hΦ : Bounded Φ)
    (_huniq : TemporalSubformulasOnce Φ) :
    ∀ (k : ℕ) (α : Formula S) (j : ℕ) (W : List (Formula S)),
      (α, j, W) ∈ (run D Φ k).Q →
        ∃ k', k ≤ k' ∧ (α, j, ([] : List (Formula S))) ∈ (run D Φ k').Q := by
  classical
  intro k α j W hmem
  by_contra hnot
  have hno : ∀ l, k ≤ l → (α, j, ([] : List (Formula S))) ∉ (run D Φ l).Q := by
    intro l hl hmem'
    exact hnot ⟨l, hl, hmem'⟩
  let P : ℕ → Prop := fun n ↦ ∃ l V, k ≤ l ∧ (α, j, V) ∈ (run D Φ l).Q ∧
    waitingWeight V = n
  have hex : ∃ n, P n := ⟨waitingWeight W, k, W, le_rfl, hmem, rfl⟩
  obtain ⟨l, V, hkl, hV, hweight⟩ := Nat.find_spec hex
  obtain ⟨m, hlm, hprogress⟩ := exists_progress_step D l
  have hno_l : ∀ m, l ≤ m → (α, j, ([] : List (Formula S))) ∉ (run D Φ m).Q :=
    fun m hlm ↦ hno m (hkl.trans hlm)
  obtain ⟨U, hU, hUV⟩ := pending_later_weight D Φ hΦ l α j V hV hno_l (m - l)
  have hladd : l + (m - l) = m := Nat.add_sub_of_le hlm
  rw [hladd] at hU
  have hUne : U ≠ [] := by
    intro heq
    subst U
    exact hno m (hkl.trans hlm) hU
  let U' := advance U (D.τ (m + 1) - D.τ m)
  have hU' : (α, j, U') ∈ (run D Φ (m + 1)).Q :=
    mem_next_of_nonempty D Φ m α j U hU hUne
  have hless : waitingWeight U' < waitingWeight U :=
    (advance_weight U (run_goodWaiting D Φ hΦ m α j U hU) _).2 (by omega) hUne
  have hmin := Nat.find_min' hex
    (show P (waitingWeight U') from ⟨m + 1, U', by omega, hU', rfl⟩)
  omega

end MFOTLMon.Monitor.QueueProof

namespace MFOTLMon.Monitor

open Classical

variable {S : Signature} {Γ : Type}

theorem subformulas_refl (φ : Formula S) : φ ∈ subformulas φ := by
  cases φ <;> simp [subformulas]

theorem subformulas_trans {φ ψ χ : Formula S} (h₁ : φ ∈ subformulas ψ)
    (h₂ : ψ ∈ subformulas χ) : φ ∈ subformulas χ := by
  induction χ with
  | eq _ _ =>
      rw [ ← List.mem_singleton.mp h₂]
      exact h₁
  | pred _ _ =>
      rw [← List.mem_singleton.mp h₂]
      exact h₁
  | neg β ih =>
      rcases List.mem_cons.mp h₂ with rfl | h₂
      · exact h₁
      · exact List.mem_cons_of_mem _ (ih h₂)
  | ex _ β ih =>
      rcases List.mem_cons.mp h₂ with rfl | h₂
      · exact h₁
      · exact List.mem_cons_of_mem _ (ih h₂)
  | prev _ β ih =>
      rcases List.mem_cons.mp h₂ with rfl | h₂
      · exact h₁
      · exact List.mem_cons_of_mem _ (ih h₂)
  | next _ β ih =>
      rcases List.mem_cons.mp h₂ with rfl | h₂
      · exact h₁
      · exact List.mem_cons_of_mem _ (ih h₂)
  | or β γ ihβ ihγ =>
      rcases List.mem_cons.mp h₂ with rfl | h₂
      · exact h₁
      · apply List.mem_cons_of_mem
        rcases List.mem_append.mp h₂ with h₂ | h₂
        · exact List.mem_append_left _ (ihβ h₂)
        · exact List.mem_append_right _ (ihγ h₂)
  | since _ β γ ihβ ihγ =>
      rcases List.mem_cons.mp h₂ with rfl | h₂
      · exact h₁
      · apply List.mem_cons_of_mem
        rcases List.mem_append.mp h₂ with h₂ | h₂
        · exact List.mem_append_left _ (ihβ h₂)
        · exact List.mem_append_right _ (ihγ h₂)
  | «until» _ β γ ihβ ihγ =>
      rcases List.mem_cons.mp h₂ with rfl | h₂
      · exact h₁
      · apply List.mem_cons_of_mem
        rcases List.mem_append.mp h₂ with h₂ | h₂
        · exact List.mem_append_left _ (ihβ h₂)
        · exact List.mem_append_right _ (ihγ h₂)

theorem mem_subformulas_of_mem_tsub {φ ψ : Formula S} (h : ψ ∈ tsub φ) :
    ψ ∈ subformulas φ ∧ ψ.isTemporal = true := by
  induction φ with
  | eq _ _ => cases h
  | pred _ _ => cases h
  | neg β ih =>
      obtain ⟨hsub, htemp⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hsub, htemp⟩
  | ex _ β ih =>
      obtain ⟨hsub, htemp⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hsub, htemp⟩
  | or β γ ihβ ihγ =>
      rcases List.mem_append.mp h with h | h
      · obtain ⟨hsub, htemp⟩ := ihβ h
        exact ⟨List.mem_cons_of_mem _ (List.mem_append_left _ hsub), htemp⟩
      · obtain ⟨hsub, htemp⟩ := ihγ h
        exact ⟨List.mem_cons_of_mem _ (List.mem_append_right _ hsub), htemp⟩
  | prev I β _ =>
      rw [List.mem_singleton.mp h]
      exact ⟨subformulas_refl _, rfl⟩
  | next I β _ =>
      rw [List.mem_singleton.mp h]
      exact ⟨subformulas_refl _, rfl⟩
  | since I β γ _ _ =>
      rw [List.mem_singleton.mp h]
      exact ⟨subformulas_refl _, rfl⟩
  | «until» I β γ _ _ =>
      rw [List.mem_singleton.mp h]
      exact ⟨subformulas_refl _, rfl⟩

theorem mem_tempSubs_of_mem_tsub {Φ φ ψ : Formula S} (hφ : φ ∈ subformulas Φ)
    (hψ : ψ ∈ tsub φ) : ψ ∈ tempSubs Φ := by
  obtain ⟨hsub, htemp⟩ := mem_subformulas_of_mem_tsub hψ
  exact List.mem_filter.mpr ⟨subformulas_trans hsub hφ, htemp⟩

theorem size_le_of_mem_subformulas {φ ψ : Formula S} (h : ψ ∈ subformulas φ) :
    ψ.size ≤ φ.size := by
  induction φ with
  | eq _ _ =>
      rw [List.mem_singleton.mp h]
  | pred _ _ =>
      rw [List.mem_singleton.mp h]
  | neg β ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact le_rfl
      · have := ih h; dsimp [Formula.size]; omega
  | ex _ β ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact le_rfl
      · have := ih h; dsimp [Formula.size]; omega
  | prev _ β ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact le_rfl
      · have := ih h; dsimp [Formula.size]; omega
  | next _ β ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact le_rfl
      · have := ih h; dsimp [Formula.size]; omega
  | or β γ ihβ ihγ =>
      rcases List.mem_cons.mp h with rfl | h
      · exact le_rfl
      · rcases List.mem_append.mp h with h | h
        · have := ihβ h; dsimp [Formula.size]; omega
        · have := ihγ h; dsimp [Formula.size]; omega
  | since _ β γ ihβ ihγ =>
      rcases List.mem_cons.mp h with rfl | h
      · exact le_rfl
      · rcases List.mem_append.mp h with h | h
        · have := ihβ h; dsimp [Formula.size]; omega
        · have := ihγ h; dsimp [Formula.size]; omega
  | «until» _ β γ ihβ ihγ =>
      rcases List.mem_cons.mp h with rfl | h
      · exact le_rfl
      · rcases List.mem_append.mp h with h | h
        · have := ihβ h; dsimp [Formula.size]; omega
        · have := ihγ h; dsimp [Formula.size]; omega

theorem directFreeAligned_of_mem_subformulas (Φ : Formula S) :
    DirectFreeAligned Φ → ∀ α ∈ subformulas Φ, DirectFreeAligned α := by
  induction Φ with
  | eq _ _ =>
      intro hΦ α hα
      rw [List.mem_singleton.mp hα]
      exact hΦ
  | pred _ _ =>
      intro hΦ α hα
      rw [List.mem_singleton.mp hα]
      exact hΦ
  | neg β ih =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · exact ih hΦ α hα
  | ex _ β ih =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · exact ih hΦ α hα
  | prev _ β ih =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · exact ih hΦ α hα
  | next _ β ih =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · exact ih hΦ α hα
  | or β γ ihβ ihγ =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · rcases List.mem_append.mp hα with hα | hα
        · exact ihβ hΦ.1 α hα
        · exact ihγ hΦ.2 α hα
  | since _ β γ ihβ ihγ =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · rcases List.mem_append.mp hα with hα | hα
        · exact ihβ hΦ.2.1 α hα
        · exact ihγ hΦ.2.2 α hα
  | «until» _ β γ ihβ ihγ =>
      intro hΦ α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact hΦ
      · rcases List.mem_append.mp hα with hα | hα
        · exact ihβ hΦ.2.1 α hα
        · exact ihγ hΦ.2.2 α hα

theorem directFreeAligned_of_mem_tempSubs (Φ : Formula S) (hfree : DirectFreeAligned Φ)
    (α : Formula S) (hα : α ∈ tempSubs Φ) : DirectFreeAligned α :=
  directFreeAligned_of_mem_subformulas Φ hfree α (List.mem_filter.mp hα).1

theorem regular_satSet_of_size [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (hlt : HasOrderPred D) :
    ∀ (m : ℕ) (φ : Formula S), φ.size ≤ m → Bounded φ → DirectFreeAligned φ →
      ∀ j : ℕ, RegularRel rep (freeList φ).length (satSet D φ j) := by
  intro m
  induction m with
  | zero =>
      intro φ hsz
      cases φ <;> simp [Formula.size] at hsz
  | succ m ih =>
      intro φ hsz hbdd hfree j
      have htsub_child : ∀ {β : Formula S}, β.size ≤ m → Bounded β → DirectFreeAligned β →
          ∀ k, ∀ ψ ∈ tsub β, RegularRel rep (freeList ψ).length (satSet D ψ k) := by
        intro β hβsz hβbdd hβfree k ψ hψ
        have hsub := (mem_subformulas_of_mem_tsub hψ).1
        have hψsz : ψ.size ≤ m := (size_le_of_mem_subformulas hsub).trans hβsz
        have hψbdd := QueueProof.bounded_of_mem_subformulas β hβbdd ψ hsub
        have hψfree := directFreeAligned_of_mem_subformulas β hβfree ψ hsub
        exact ih ψ hψsz hψbdd hψfree k
      cases φ with
      | prev I β =>
          have hβsz : β.size ≤ m := by dsimp [Formula.size] at hsz; omega
          rw [← prevP_satSet D I β j]
          by_cases h : 0 < j ∧ I.Mem (D.τ j - D.τ (j - 1))
          · rw [prevP, if_pos h, freeList_prev]
            have h34 := regular_hatSet rep D hD (j - 1) (fun ψ ↦ satSet D ψ (j - 1)) β
              (fun ψ hψ ↦ htsub_child hβsz hbdd hfree (j - 1) ψ hψ)
            rwa [hatSet_eq_satSet D (j - 1) (fun ψ ↦ satSet D ψ (j - 1)) β (fun _ _ ↦ rfl)] at h34
          · rw [prevP, if_neg h]
            exact regular_empty rep _
      | next I β =>
          have hβsz : β.size ≤ m := by dsimp [Formula.size] at hsz; omega
          rw [← nextP_satSet D I β j]
          by_cases h : I.Mem (D.τ (j + 1) - D.τ j)
          · rw [nextP, if_pos h, freeList_next]
            have h34 := regular_hatSet rep D hD (j + 1) (fun ψ ↦ satSet D ψ (j + 1)) β
              (fun ψ hψ ↦ htsub_child hβsz hbdd hfree (j + 1) ψ hψ)
            rwa [hatSet_eq_satSet D (j + 1) (fun ψ ↦ satSet D ψ (j + 1)) β (fun _ _ ↦ rfl)] at h34
          · rw [nextP, if_neg h]
            exact regular_empty rep _
      | since I β γ =>
          have hβsz : β.size ≤ m := by dsimp [Formula.size] at hsz; omega
          have hγsz : γ.size ≤ m := by dsimp [Formula.size] at hsz; omega
          have h37 := (lemma_3_7_proved rep D hD hlt I β γ hfree.1 (fun ψ k ↦ satSet D ψ k) j
            (fun k _ ψ hψ ↦ by
              rcases List.mem_append.mp hψ with hψ | hψ
              · exact ⟨htsub_child hβsz hbdd.1 hfree.2.1 k ψ hψ, rfl⟩
              · exact ⟨htsub_child hγsz hbdd.2 hfree.2.2 k ψ hψ, rfl⟩)).2
          exact h37.2 ▸ h37.1
      | «until» I β γ =>
          have hβsz : β.size ≤ m := by dsimp [Formula.size] at hsz; omega
          have hγsz : γ.size ≤ m := by dsimp [Formula.size] at hsz; omega
          have hb' : I.hi = (I.hi.toNat : ℕ∞) := (ENat.natCast_toNat hbdd.1).symm
          have h38 := (lemma_3_8_proved rep D hD hlt I I.hi.toNat hb' β γ hfree.1
            (fun ψ k ↦ satSet D ψ k) j
            (fun k _ ψ hψ ↦ by
              rcases List.mem_append.mp hψ with hψ | hψ
              · exact ⟨htsub_child hβsz hbdd.2.1 hfree.2.1 k ψ hψ, rfl⟩
              · exact ⟨htsub_child hγsz hbdd.2.2 hfree.2.2 k ψ hψ, rfl⟩)).2.2
          exact h38.2 ▸ h38.1
      | eq t1 t2 =>
          have h34 := regular_hatSet rep D hD j (fun ψ ↦ satSet D ψ j) (.eq t1 t2)
            (fun ψ hψ ↦ by cases hψ)
          rwa [hatSet_eq_satSet D j (fun ψ ↦ satSet D ψ j) (.eq t1 t2) (fun _ _ ↦ rfl)] at h34
      | pred r ts =>
          have h34 := regular_hatSet rep D hD j (fun ψ ↦ satSet D ψ j) (.pred r ts)
            (fun ψ hψ ↦ by cases hψ)
          rwa [hatSet_eq_satSet D j (fun ψ ↦ satSet D ψ j) (.pred r ts) (fun _ _ ↦ rfl)] at h34
      | neg β =>
          have hβsz : β.size ≤ m := by dsimp [Formula.size] at hsz; omega
          have h34 := regular_hatSet rep D hD j (fun ψ ↦ satSet D ψ j) (.neg β)
            (fun ψ hψ ↦ htsub_child hβsz hbdd hfree j ψ hψ)
          rwa [hatSet_eq_satSet D j (fun ψ ↦ satSet D ψ j) (.neg β) (fun _ _ ↦ rfl)] at h34
      | ex x β =>
          have hβsz : β.size ≤ m := by dsimp [Formula.size] at hsz; omega
          have h34 := regular_hatSet rep D hD j (fun ψ ↦ satSet D ψ j) (.ex x β)
            (fun ψ hψ ↦ htsub_child hβsz hbdd hfree j ψ hψ)
          rwa [hatSet_eq_satSet D j (fun ψ ↦ satSet D ψ j) (.ex x β) (fun _ _ ↦ rfl)] at h34
      | or β γ =>
          have hβsz : β.size ≤ m := by dsimp [Formula.size] at hsz; omega
          have hγsz : γ.size ≤ m := by dsimp [Formula.size] at hsz; omega
          have h34 := regular_hatSet rep D hD j (fun ψ ↦ satSet D ψ j) (.or β γ)
            (fun ψ hψ ↦ by
              rcases List.mem_append.mp hψ with hψ | hψ
              · exact htsub_child hβsz hbdd.1 hfree.1 j ψ hψ
              · exact htsub_child hγsz hbdd.2 hfree.2 j ψ hψ)
          rwa [hatSet_eq_satSet D j (fun ψ ↦ satSet D ψ j) (.or β γ) (fun _ _ ↦ rfl)] at h34

theorem regular_satSet [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (hlt : HasOrderPred D) (φ : Formula S)
    (hbdd : Bounded φ) (hfree : DirectFreeAligned φ) (j : ℕ) :
    RegularRel rep (freeList φ).length (satSet D φ j) :=
  regular_satSet_of_size rep D hD hlt φ.size φ le_rfl hbdd hfree j

end MFOTLMon.Monitor

namespace MFOTLMon.Monitor.QueueProof

variable {S : Signature}

noncomputable def iterAdvance (D : TempStruct S) (j : ℕ) :
    ℕ → List (Formula S) → List (Formula S)
  | 0, W => W
  | n + 1, W => advance (iterAdvance D j n W) (D.τ (j + n + 1) - D.τ (j + n))

@[simp] theorem iterAdvance_zero (D : TempStruct S) (j : ℕ) (W : List (Formula S)) :
    iterAdvance D j 0 W = W := rfl

theorem iterAdvance_succ (D : TempStruct S) (j n : ℕ) (W : List (Formula S)) :
    iterAdvance D j (n + 1) W =
      advance (iterAdvance D j n W) (D.τ (j + n + 1) - D.τ (j + n)) := rfl

@[simp] theorem advance_nil (t : ℕ) : advance ([] : List (Formula S)) t = [] := rfl

@[simp] theorem iterAdvance_nil (D : TempStruct S) (j n : ℕ) :
    iterAdvance D j n ([] : List (Formula S)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterAdvance_succ, ih]

theorem iterAdvance_append (D : TempStruct S) (j n : ℕ) (U V : List (Formula S)) :
    iterAdvance D j n (U ++ V) = iterAdvance D j n U ++ iterAdvance D j n V := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterAdvance_succ, ih, advance_append, ← iterAdvance_succ, ← iterAdvance_succ]

theorem iterAdvance_add (D : TempStruct S) (j n m : ℕ) (W : List (Formula S)) :
    iterAdvance D j (n + m) W = iterAdvance D (j + n) m (iterAdvance D j n W) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hidx : j + (n + m) = j + n + m := by omega
    rw [Nat.add_succ, iterAdvance_succ, ih, iterAdvance_succ, hidx]

theorem iterAdvance_until_le_lookahead (D : TempStruct S) (j : ℕ) (I : Interval)
    (hfinite : I.hi ≠ ⊤) (β γ : Formula S) {n : ℕ}
    (hn : n ≤ lookahead D I.hi.toNat j) :
    ∃ I' : Interval, I'.hi = ((I.hi.toNat - (D.τ (j + n) - D.τ j) : ℕ) : ℕ∞) ∧
      iterAdvance D j n [.until I β γ] = [.until I' β γ] := by
  have hpos : 0 < I.hi.toNat := interval_hi_toNat_pos I hfinite
  induction n with
  | zero =>
    refine ⟨I, ?_, rfl⟩
    simp only [Nat.add_zero, Nat.sub_self]
    exact (ENat.natCast_toNat hfinite).symm
  | succ n ih =>
    obtain ⟨I', hI', heq⟩ := ih (by omega)
    let t := D.τ (j + n + 1) - D.τ (j + n)
    have hidx : j + (n + 1) = j + n + 1 := by omega
    have hlt_b : D.τ (j + n + 1) - D.τ j < I.hi.toNat := by
      have h := (le_lookahead_iff D I.hi.toNat j hpos (n + 1)).mp hn
      rwa [hidx] at h
    have hmono1 : D.τ j ≤ D.τ (j + n) := D.mono (by omega)
    have hmono2 : D.τ (j + n) ≤ D.τ (j + n + 1) := D.mono (by omega)
    have ht_lt_nat : t < I.hi.toNat - (D.τ (j + n) - D.τ j) := by
      dsimp only [t]
      omega
    have ht_lt : (t : ℕ∞) < I'.hi := by
      rw [hI']
      exact_mod_cast ht_lt_nat
    refine ⟨I'.shift t ht_lt, ?_, ?_⟩
    · change I'.hi - (t : ℕ∞) = _
      rw [hI', ← ENat.natCast_sub, hidx]
      congr 1
      dsimp only [t]
      omega
    · rw [iterAdvance_succ, heq]
      change advance [.until I' β γ] t = [.until (I'.shift t ht_lt) β γ]
      simp only [advance, update, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        ht_lt, ↓reduceDIte, waitfor]

theorem iterAdvance_until_lookahead_succ (D : TempStruct S) (j : ℕ) (I : Interval)
    (hfinite : I.hi ≠ ⊤) (β γ : Formula S) :
    iterAdvance D j (lookahead D I.hi.toNat j + 1) [.until I β γ] =
      waitfor β ++ waitfor γ := by
  let ℓ := lookahead D I.hi.toNat j
  have hpos : 0 < I.hi.toNat := interval_hi_toNat_pos I hfinite
  obtain ⟨I', hI', heq⟩ := iterAdvance_until_le_lookahead D j I hfinite β γ (le_refl ℓ)
  let t := D.τ (j + ℓ + 1) - D.τ (j + ℓ)
  have hidx : j + (ℓ + 1) = j + ℓ + 1 := by omega
  have hnext : I.hi.toNat ≤ D.τ (j + ℓ + 1) - D.τ j := by
    have h := lookahead_next_spec D I.hi.toNat j hpos
    change I.hi.toNat ≤ D.τ (j + (ℓ + 1)) - D.τ j at h
    rwa [hidx] at h
  have hmono1 : D.τ j ≤ D.τ (j + ℓ) := D.mono (by omega)
  have hmono2 : D.τ (j + ℓ) ≤ D.τ (j + ℓ + 1) := D.mono (by omega)
  have ht_ge_nat : I.hi.toNat - (D.τ (j + ℓ) - D.τ j) ≤ t := by
    dsimp only [t]
    omega
  have ht_not_lt : ¬ (t : ℕ∞) < I'.hi := by
    rw [hI']
    exact not_lt.mpr (by exact_mod_cast ht_ge_nat)
  rw [iterAdvance_succ, heq]
  change advance [.until I' β γ] t = waitfor β ++ waitfor γ
  simp only [advance, update, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    ht_not_lt, ↓reduceDIte]

noncomputable def horizon (D : TempStruct S) : Formula S → ℕ → ℕ
  | .eq _ _, j => j
  | .pred _ _, j => j
  | .neg β, j => horizon D β j
  | .ex _ β, j => horizon D β j
  | .prev _ β, j => horizon D β j
  | .or β γ, j => max (horizon D β j) (horizon D γ j)
  | .since _ β γ, j => max (horizon D β j) (horizon D γ j)
  | .next _ β, j => horizon D β (j + 1)
  | .until I β γ, j =>
      let ℓ := lookahead D I.hi.toNat j
      max (horizon D β (j + ℓ + 1)) (horizon D γ (j + ℓ + 1))

theorem le_horizon (D : TempStruct S) (φ : Formula S) (j : ℕ) :
    j ≤ horizon D φ j := by
  induction φ generalizing j with
  | eq _ _ => exact le_rfl
  | pred _ _ => exact le_rfl
  | neg β ih => exact ih j
  | ex _ β ih => exact ih j
  | prev _ β ih => exact ih j
  | or β γ ihβ _ => exact (ihβ j).trans (le_max_left _ _)
  | since _ β γ ihβ _ => exact (ihβ j).trans (le_max_left _ _)
  | next _ β ih => exact (Nat.le_succ j).trans (ih (j + 1))
  | «until» I β γ ihβ _ =>
      let m := j + lookahead D I.hi.toNat j + 1
      have hjm : j ≤ m := by dsimp only [m]; omega
      exact hjm.trans ((ihβ m).trans (le_max_left _ _))

theorem horizon_mono (D : TempStruct S) (φ : Formula S) (hφ : Bounded φ)
    {j₁ j₂ : ℕ} (hj : j₁ ≤ j₂) : horizon D φ j₁ ≤ horizon D φ j₂ := by
  induction φ generalizing j₁ j₂ with
  | eq _ _ => exact hj
  | pred _ _ => exact hj
  | neg β ih => exact ih hφ hj
  | ex _ β ih => exact ih hφ hj
  | prev _ β ih => exact ih hφ hj
  | or β γ ihβ ihγ => exact max_le_max (ihβ hφ.1 hj) (ihγ hφ.2 hj)
  | since _ β γ ihβ ihγ => exact max_le_max (ihβ hφ.1 hj) (ihγ hφ.2 hj)
  | next _ β ih => exact ih hφ (Nat.add_le_add_right hj 1)
  | «until» I β γ ihβ ihγ =>
      have hpos : 0 < I.hi.toNat := interval_hi_toNat_pos I hφ.1
      have hend := lookahead_endpoint_mono D I.hi.toNat hpos hj
      have hend' : j₁ + lookahead D I.hi.toNat j₁ + 1 ≤ j₂ + lookahead D I.hi.toNat j₂ + 1 :=
        Nat.add_le_add_right hend 1
      exact max_le_max (ihβ hφ.2.1 hend') (ihγ hφ.2.2 hend')

theorem horizon_tsub_le (D : TempStruct S) (φ : Formula S) (j : ℕ) :
    ∀ ψ ∈ tsub φ, horizon D ψ j ≤ horizon D φ j := by
  induction φ with
  | eq _ _ => intro _ h; cases h
  | pred _ _ => intro _ h; cases h
  | neg β ih => exact ih
  | ex _ β ih => exact ih
  | or β γ ihβ ihγ =>
      intro ψ hψ
      rcases List.mem_append.mp hψ with hψ | hψ
      · exact (ihβ ψ hψ).trans (le_max_left _ _)
      · exact (ihγ ψ hψ).trans (le_max_right _ _)
  | prev I β _ =>
      intro ψ hψ
      rw [List.mem_singleton.mp hψ]
  | next I β _ =>
      intro ψ hψ
      rw [List.mem_singleton.mp hψ]
  | since I β γ _ _ =>
      intro ψ hψ
      rw [List.mem_singleton.mp hψ]
  | «until» I β γ _ _ =>
      intro ψ hψ
      rw [List.mem_singleton.mp hψ]

theorem iterAdvance_waitfor_eq_nil_iff (D : TempStruct S) (φ : Formula S)
    (hφ : Bounded φ) (j n : ℕ) :
    iterAdvance D j n (waitfor φ) = [] ↔ horizon D φ j ≤ j + n := by
  induction φ generalizing j n with
  | eq _ _ =>
      simp only [waitfor, iterAdvance_nil, horizon, true_iff]
      omega
  | pred _ _ =>
      simp only [waitfor, iterAdvance_nil, horizon, true_iff]
      omega
  | neg β ih => exact ih hφ j n
  | ex _ β ih => exact ih hφ j n
  | prev _ β ih => exact ih hφ j n
  | or β γ ihβ ihγ =>
      simp only [waitfor, iterAdvance_append, List.append_eq_nil_iff,
        ihβ hφ.1 j n, ihγ hφ.2 j n, horizon, max_le_iff]
  | since _ β γ ihβ ihγ =>
      simp only [waitfor, iterAdvance_append, List.append_eq_nil_iff,
        ihβ hφ.1 j n, ihγ hφ.2 j n, horizon, max_le_iff]
  | next I β ih =>
      cases n with
      | zero =>
          simp only [waitfor, iterAdvance_zero, List.cons_ne_nil, horizon, Nat.add_zero, false_iff]
          have hle := le_horizon D β (j + 1)
          omega
      | succ m =>
          have h1 : iterAdvance D j 1 (waitfor (.next I β)) = waitfor β := by
            simp only [waitfor, iterAdvance_succ, iterAdvance_zero, Nat.add_zero,
              advance, update, List.flatMap_cons, List.flatMap_nil, List.append_nil]
          have hstep : iterAdvance D j (m + 1) (waitfor (.next I β)) =
              iterAdvance D (j + 1) m (waitfor β) := by
            rw [show m + 1 = 1 + m by omega, iterAdvance_add, h1]
          rw [hstep, ih hφ (j + 1) m, horizon]
          omega
  | «until» I β γ ihβ ihγ =>
      let ℓ := lookahead D I.hi.toNat j
      by_cases hn : n ≤ ℓ
      · obtain ⟨I', _, heq⟩ := iterAdvance_until_le_lookahead D j I hφ.1 β γ hn
        rw [waitfor, heq]
        simp only [List.cons_ne_nil, false_iff]
        change ¬ max (horizon D β (j + ℓ + 1)) (horizon D γ (j + ℓ + 1)) ≤ j + n
        have hle := (le_horizon D β (j + ℓ + 1)).trans (le_max_left _ (horizon D γ (j + ℓ + 1)))
        omega
      · have hge : ℓ + 1 ≤ n := by omega
        have hdecomp : n = (ℓ + 1) + (n - (ℓ + 1)) := by omega
        have hidx : j + (ℓ + 1) = j + ℓ + 1 := by omega
        rw [waitfor, hdecomp, iterAdvance_add, iterAdvance_until_lookahead_succ D j I hφ.1 β γ,
          hidx, iterAdvance_append, List.append_eq_nil_iff,
          ihβ hφ.2.1 (j + ℓ + 1) (n - (ℓ + 1)), ihγ hφ.2.2 (j + ℓ + 1) (n - (ℓ + 1))]
        change (horizon D β (j + ℓ + 1) ≤ j + ℓ + 1 + (n - (ℓ + 1)) ∧
          horizon D γ (j + ℓ + 1) ≤ j + ℓ + 1 + (n - (ℓ + 1))) ↔
          max (horizon D β (j + ℓ + 1)) (horizon D γ (j + ℓ + 1)) ≤ j + (ℓ + 1 + (n - (ℓ + 1)))
        rw [max_le_iff]
        omega

theorem mem_run_Q_iff (D : TempStruct S) (Φ : Formula S) (hΦ : Bounded Φ)
    (k : ℕ) (α : Formula S) (j : ℕ) (W : List (Formula S)) :
    (α, j, W) ∈ (run D Φ k).Q ↔
      α ∈ tempSubs Φ ∧ j ≤ k ∧ k ≤ horizon D α j ∧ W = iterAdvance D j (k - j) (waitfor α) := by
  induction k generalizing W with
  | zero =>
      simp only [run_zero, init, List.mem_map, Prod.mk.injEq]
      constructor
      · rintro ⟨β, hβ, rfl, rfl, rfl⟩
        exact ⟨hβ, le_rfl, le_horizon D β 0, rfl⟩
      · rintro ⟨hα, hj, _, rfl⟩
        have hj0 : j = 0 := by omega
        subst hj0
        exact ⟨α, hα, rfl, rfl, rfl⟩
  | succ k ih =>
      rw [run_succ, iteration_Q]
      constructor
      · intro h
        rcases mem_updateQ_cases D Φ (run D Φ k) α j W h with
          ⟨U, hU, hne, rfl⟩ | ⟨hα, hj, rfl⟩
        · obtain ⟨hα, hjk, hkh, rfl⟩ := (ih U).mp hU
          have hα_bdd := bounded_of_mem_tempSubs Φ hΦ α hα
          have hnot_le : ¬ horizon D α j ≤ j + (k - j) :=
            mt (iterAdvance_waitfor_eq_nil_iff D α hα_bdd j (k - j)).mpr hne
          have hlt : k < horizon D α j := by omega
          have hsub : k + 1 - j = (k - j) + 1 := by omega
          have hidx : j + (k - j) = k := by omega
          refine ⟨hα, by omega, by omega, ?_⟩
          rw [hsub, iterAdvance_succ, run_ell, hidx]
          rfl
        · rw [run_ell] at hj
          subst hj
          exact ⟨hα, le_rfl, le_horizon D α (k + 1), by simp⟩
      · rintro ⟨hα, hjk1, hk1h, rfl⟩
        rcases Nat.of_le_succ hjk1 with hjk | rfl
        · apply List.mem_append_left
          apply List.mem_filterMap.mpr
          let U := iterAdvance D j (k - j) (waitfor α)
          have hα_bdd := bounded_of_mem_tempSubs Φ hΦ α hα
          have hne : U ≠ [] := by
            intro hU
            have hle := (iterAdvance_waitfor_eq_nil_iff D α hα_bdd j (k - j)).mp hU
            omega
          have hU_mem : (α, j, U) ∈ (run D Φ k).Q :=
            (ih U).mpr ⟨hα, hjk, by omega, rfl⟩
          refine ⟨(α, j, U), hU_mem, ?_⟩
          have hempty : U.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
          have hsub : k + 1 - j = (k - j) + 1 := by omega
          have hidx : j + (k - j) = k := by omega
          simp only [hempty, Bool.false_eq_true, ↓reduceIte, run_ell, hsub,
            iterAdvance_succ, hidx, advance, U]
        · simp only [Nat.sub_self, iterAdvance_zero]
          simpa only [run_ell] using mem_updateQ_fresh D Φ (run D Φ k) α hα

theorem mem_run_Q_ready_iff (D : TempStruct S) (Φ : Formula S) (hΦ : Bounded Φ)
    (k : ℕ) (α : Formula S) (j : ℕ) :
    (α, j, ([] : List (Formula S))) ∈ (run D Φ k).Q ↔
      α ∈ tempSubs Φ ∧ horizon D α j = k := by
  rw [mem_run_Q_iff D Φ hΦ]
  constructor
  · rintro ⟨hα, hjk, hkh, hnil⟩
    have hα_bdd := bounded_of_mem_tempSubs Φ hΦ α hα
    have hle := (iterAdvance_waitfor_eq_nil_iff D α hα_bdd j (k - j)).mp hnil.symm
    exact ⟨hα, by omega⟩
  · rintro ⟨hα, rfl⟩
    have hα_bdd := bounded_of_mem_tempSubs Φ hΦ α hα
    have hjh := le_horizon D α j
    have hnil := (iterAdvance_waitfor_eq_nil_iff D α hα_bdd j (horizon D α j - j)).mpr (by omega)
    exact ⟨hα, hjh, le_rfl, hnil.symm⟩

end MFOTLMon.Monitor.QueueProof

namespace MFOTLMon.Monitor.QueueProof

variable {S : Signature}

theorem set_p_frame (st : Store S) {α β : Formula S} {j m : ℕ}
    (X : Set (List ℕ)) (hne : (α, j) ≠ (β, m)) :
    (st.set (.p β) m X) (.p α) j = st (.p α) j := by
  simp only [Store.set]
  split
  · rename_i h
    exact (hne (Prod.ext (Key.p.inj h.1) h.2)).elim
  · rfl

theorem set_r_p_frame (st : Store S) (α β : Formula S) (j m : ℕ)
    (X : Set (List ℕ)) : (st.set (.r β) m X) (.p α) j = st (.p α) j := by
  simp [Store.set]

theorem set_s_p_frame (st : Store S) (α β : Formula S) (j m : ℕ)
    (X : Set (List ℕ)) : (st.set (.s β) m X) (.p α) j = st (.p α) j := by
  simp [Store.set]

theorem build_p_frame (D : TempStruct S) (st : Store S) (e : Formula S × ℕ)
    (α : Formula S) (j : ℕ) (hne : (α, j) ≠ e) :
    build D st e (.p α) j = st (.p α) j := by
  rcases e with ⟨β, m⟩
  cases β with
  | eq _ _ => rfl
  | pred _ _ => rfl
  | neg _ => rfl
  | or _ _ => rfl
  | ex _ _ => rfl
  | prev I β =>
      dsimp only [build]
      split
      · exact set_p_frame st _ hne
      · cases hatAt D st (m - 1) β with
        | none => rfl
        | some B => exact set_p_frame st _ hne
  | next I β =>
      dsimp only [build]
      cases hatAt D st (m + 1) β with
      | none => rfl
      | some B => exact set_p_frame st _ hne
  | since I β γ =>
      dsimp only [build]
      cases hatAt D st m β <;> cases hatAt D st m γ <;>
        cases (if m = 0 then some ∅ else st (.r (.since I β γ)) (m - 1)) <;> try rfl
      dsimp only
      rw [set_p_frame _ _ hne, set_r_p_frame]
  | «until» I β γ =>
      dsimp only [build]
      split
      · rw [set_p_frame _ _ hne, set_s_p_frame, set_r_p_frame]
      · rfl

theorem foldl_build_p_frame (D : TempStruct S) (L : List (Formula S × ℕ))
    (st : Store S) (α : Formula S) (j : ℕ)
    (hne : ∀ e ∈ L, (α, j) ≠ e) :
    (L.foldl (build D) st) (.p α) j = st (.p α) j := by
  induction L generalizing st with
  | nil => rfl
  | cons e L ih =>
      change (L.foldl (build D) (build D st e)) (.p α) j = st (.p α) j
      calc
        _ = build D st e (.p α) j := ih _ (fun e' he' ↦ hne e' (List.mem_cons_of_mem e he'))
        _ = st (.p α) j := build_p_frame D st e α j (hne e (List.mem_cons_self))

theorem afterBuild_p_frame (D : TempStruct S) (s : State S) (α : Formula S) (j : ℕ)
    (hne : ∀ β m, (β, m, ([] : List (Formula S))) ∈ s.Q → (α, j) ≠ (β, m)) :
    (afterBuild D s).store (.p α) j = s.store (.p α) j := by
  apply foldl_build_p_frame
  intro e he
  have he' := List.mem_mergeSort.mp he
  obtain ⟨⟨β, m, U⟩, hmem, heq⟩ := List.mem_map.mp he'
  obtain ⟨hmem, hempty⟩ := List.mem_filter.mp hmem
  have hU : U = [] := List.isEmpty_iff.mp hempty
  subst U
  cases heq
  exact hne β m hmem

theorem afterBuild_pending_none (D : TempStruct S) (s : State S)
    (hcoh : Coherent s.Q) (α : Formula S) (j : ℕ) (W : List (Formula S))
    (hmem : (α, j, W) ∈ s.Q) (hne : W ≠ []) (habs : s.store (.p α) j = none) :
    (afterBuild D s).store (.p α) j = none := by
  rw [afterBuild_p_frame D s α j]
  · exact habs
  · intro β m hready heq
    cases heq
    exact hne (hcoh α j W [] hmem hready)

theorem afterBuild_future_none (D : TempStruct S) (s : State S)
    (hbound : ∀ β m U, (β, m, U) ∈ s.Q → m ≤ s.ell)
    (hfuture : ∀ β m, s.ell ≤ m → s.store (.p β) m = none)
    (α : Formula S) (j : ℕ) (hj : s.ell < j) :
    (afterBuild D s).store (.p α) j = none := by
  rw [afterBuild_p_frame D s α j]
  · exact hfuture α j hj.le
  · intro β m hready heq
    have := hbound β m [] hready
    cases heq
    omega

theorem evalLoop_preserves_none (D : TempStruct S) (Φ : Formula S) (fuel : ℕ)
    (s : State S) (key : Key S) (j : ℕ) (habs : s.store key j = none) :
    (evalLoop D Φ fuel s).store key j = none := by
  induction fuel generalizing s with
  | zero => exact habs
  | succ fuel ih =>
      rw [evalLoop]
      split
      · apply ih
        change (if 0 < s.i then s.store.discard (s.i - 1) else s.store) key j = none
        split <;> simp [Store.discard, habs]
      · exact habs

theorem evalLoop_blocked (D : TempStruct S) (Φ : Formula S) (fuel : ℕ)
    (α : Formula S) (j : ℕ) (hα : α ∈ tempSubs Φ) (s : State S)
    (hij : s.i ≤ j) (habs : s.store (.p α) j = none) :
    (evalLoop D Φ fuel s).i ≤ j ∧
      (evalLoop D Φ fuel s).store (.p α) j = none := by
  induction fuel generalizing s with
  | zero => exact ⟨hij, habs⟩
  | succ fuel ih =>
      rw [evalLoop]
      split
      · rename_i hcomplete
        have hlt : s.i < j := by
          have hne : s.i ≠ j := by
            intro heq
            have hp := hcomplete.2 α hα
            rw [heq, habs] at hp
            cases hp
          omega
        apply ih
        · exact hlt
        · change (if 0 < s.i then s.store.discard (s.i - 1) else s.store) (.p α) j = none
          split <;> simp [Store.discard, habs]
      · exact ⟨hij, habs⟩

theorem run_pending_invariant (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    (∀ α j W, (α, j, W) ∈ (run D Φ k).Q →
      (run D Φ k).i ≤ j ∧ (run D Φ k).store (.p α) j = none) ∧
      (∀ α j, k ≤ j → (run D Φ k).store (.p α) j = none) := by
  induction k with
  | zero =>
      constructor
      · intro α j W _
        exact ⟨Nat.zero_le j, rfl⟩
      · intro α j _
        rfl
  | succ k ih =>
      have hbound : ∀ α j W, (α, j, W) ∈ (run D Φ k).Q →
          j ≤ (run D Φ k).ell := by
        simpa only [run_ell] using (run_queue_properties D Φ k).1
      have hfuture : ∀ α j, (run D Φ k).ell ≤ j →
          (run D Φ k).store (.p α) j = none := by
        simpa only [run_ell] using ih.2
      constructor
      · intro α j W hmem
        rw [run_succ, iteration_Q] at hmem
        rcases mem_updateQ_cases D Φ (run D Φ k) α j W hmem with
          ⟨U, hU, hne, _⟩ | ⟨hα, hj, _⟩
        · have hbefore := ih.1 α j U hU
          have habs := afterBuild_pending_none D _ (run_queue_coherent D Φ k)
            α j U hU hne hbefore.2
          have hblock := evalLoop_blocked D Φ (k + 2) α j
            (run_queue_temporal D Φ k α j U hU) (afterBuild D (run D Φ k))
            hbefore.1 habs
          simpa only [run_succ, iteration, run_ell] using hblock
        · have hbefore := ih.1 α k (waitfor α) (observation_one D Φ α hα k)
          have hj' : j = k + 1 := by simpa only [run_ell] using hj
          have habs := afterBuild_future_none D _ hbound hfuture α j (by
            rw [run_ell, hj']
            exact Nat.lt_succ_self k)
          have hij : (afterBuild D (run D Φ k)).i ≤ j := by
            change (run D Φ k).i ≤ j
            omega
          have hblock := evalLoop_blocked D Φ (k + 2) α j hα
            (afterBuild D (run D Φ k)) hij habs
          simpa only [run_succ, iteration, run_ell] using hblock
      · intro α j hj
        have habs := afterBuild_future_none D _ hbound hfuture α j (by
          rw [run_ell]
          omega)
        have hpres := evalLoop_preserves_none D Φ (k + 2)
          (afterBuild D (run D Φ k)) (.p α) j habs
        simpa only [run_succ, iteration, run_ell] using hpres

theorem observation_three (D : TempStruct S) (Φ : Formula S)
    (_huniq : TemporalSubformulasOnce Φ) :
    ∀ (k : ℕ) (α : Formula S) (j : ℕ) (W : List (Formula S)),
      (α, j, W) ∈ (run D Φ k).Q → (run D Φ k).i ≤ j := by
  intro k α j W hmem
  exact ((run_pending_invariant D Φ k).1 α j W hmem).1

theorem run_i_le_of_temporal (D : TempStruct S) (Φ : Formula S) (k : ℕ)
    (α : Formula S) (hα : α ∈ tempSubs Φ) : (run D Φ k).i ≤ k :=
  ((run_pending_invariant D Φ k).1 α k (waitfor α) (observation_one D Φ α hα k)).1

theorem evalLoop_out_indices (D : TempStruct S) (Φ : Formula S) (fuel : ℕ) (s : State S)
    (hindices : s.out.map (fun e ↦ e.1) = List.range s.i) :
    (evalLoop D Φ fuel s).out.map (fun e ↦ e.1) = List.range (evalLoop D Φ fuel s).i := by
  induction fuel generalizing s with
  | zero => exact hindices
  | succ fuel ih =>
      rw [evalLoop]
      split
      · apply ih
        change (s.out ++ [_]).map (fun e : ℕ × Set (List ℕ) × ℕ ↦ e.1) =
          List.range (s.i + 1)
        simp only [List.map_append, hindices, List.map_cons, List.map_nil, List.range_succ]
      · exact hindices

theorem run_out_indices (D : TempStruct S) (Φ : Formula S) (k : ℕ) :
    (run D Φ k).out.map (fun e ↦ e.1) = List.range (run D Φ k).i := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [run_succ]
      exact evalLoop_out_indices D Φ _ (afterBuild D (run D Φ k)) ih

theorem run_output_exists_of_lt (D : TempStruct S) (Φ : Formula S) (k n : ℕ)
    (hn : n < (run D Φ k).i) :
    ∃ O t, (n, O, t) ∈ (run D Φ k).out := by
  have hmem : n ∈ (run D Φ k).out.map (fun e ↦ e.1) := by
    rw [run_out_indices]
    exact List.mem_range.mpr hn
  obtain ⟨⟨m, O, t⟩, hmem, heq⟩ := List.mem_map.mp hmem
  dsimp only at heq
  subst m
  exact ⟨O, t, hmem⟩

theorem run_output_lt (D : TempStruct S) (Φ : Formula S) (k n : ℕ)
    (O : Set (List ℕ)) (t : ℕ) (hmem : (n, O, t) ∈ (run D Φ k).out) :
    n < (run D Φ k).i := by
  have hmapped := List.mem_map_of_mem (f := fun e ↦ e.1) hmem
  rw [run_out_indices] at hmapped
  exact List.mem_range.mp hmapped

end MFOTLMon.Monitor.QueueProof

namespace MFOTLMon.Monitor

open Classical

variable {S : Signature} {Γ : Type}

def JobValid (D : TempStruct S) (st : Store S) (α : Formula S) (j : ℕ) : Prop :=
  st (.p α) j = some (satSet D α j) ∧
    (∀ I β γ, α = .since I β γ →
      st (.r α) j = some (sinceR D.τ I (fun m ↦ satSet D β m) (fun m ↦ satSet D γ m) j)) ∧
    (∀ I β γ, α = .until I β γ →
      st (.r α) j = some (untilRS D I (fun m ↦ satSet D β m) (fun m ↦ satSet D γ m) j).1 ∧
      st (.s α) j = some (untilRS D I (fun m ↦ satSet D β m) (fun m ↦ satSet D γ m) j).2)

@[simp] theorem afterBuild_i (D : TempStruct S) (s : State S) :
    (afterBuild D s).i = s.i := rfl

theorem set_r_frame (st : Store S) {α β : Formula S} {j m : ℕ}
    (X : Set (List ℕ)) (hne : (α, j) ≠ (β, m)) :
    (st.set (.r β) m X) (.r α) j = st (.r α) j := by
  simp only [Store.set]
  split
  · rename_i h
    exact (hne (Prod.ext (Key.r.inj h.1) h.2)).elim
  · rfl

theorem set_s_frame (st : Store S) {α β : Formula S} {j m : ℕ}
    (X : Set (List ℕ)) (hne : (α, j) ≠ (β, m)) :
    (st.set (.s β) m X) (.s α) j = st (.s α) j := by
  simp only [Store.set]
  split
  · rename_i h
    exact (hne (Prod.ext (Key.s.inj h.1) h.2)).elim
  · rfl

theorem build_base_frame (D : TempStruct S) (st : Store S) (e : Formula S × ℕ)
    (r : S.R) (m : ℕ) : build D st e (.base r) m = st (.base r) m := by
  rcases e with ⟨β, j⟩
  cases β with
  | eq _ _ => rfl
  | pred _ _ => rfl
  | neg _ => rfl
  | or _ _ => rfl
  | ex _ _ => rfl
  | prev I β =>
      dsimp only [build]
      split
      · simp [Store.set]
      · cases hatAt D st (j - 1) β <;> simp [Store.set]
  | next I β =>
      dsimp only [build]
      cases hatAt D st (j + 1) β <;> simp [Store.set]
  | since I β γ =>
      dsimp only [build]
      cases hatAt D st j β <;> cases hatAt D st j γ <;>
        cases (if j = 0 then some ∅ else st (.r (.since I β γ)) (j - 1)) <;>
        simp [Store.set]
  | «until» I β γ =>
      dsimp only [build]
      split <;> simp [Store.set]

theorem foldl_build_base_frame (D : TempStruct S) (L : List (Formula S × ℕ))
    (st : Store S) (r : S.R) (m : ℕ) :
    (L.foldl (build D) st) (.base r) m = st (.base r) m := by
  induction L generalizing st with
  | nil => rfl
  | cons e L ih =>
      change (L.foldl (build D) (build D st e)) (.base r) m = st (.base r) m
      rw [ih, build_base_frame]

theorem build_r_frame (D : TempStruct S) (st : Store S) (e : Formula S × ℕ)
    (α : Formula S) (j : ℕ) (hne : (α, j) ≠ e) :
    build D st e (.r α) j = st (.r α) j := by
  rcases e with ⟨β, m⟩
  cases β with
  | eq _ _ => rfl
  | pred _ _ => rfl
  | neg _ => rfl
  | or _ _ => rfl
  | ex _ _ => rfl
  | prev I β =>
      dsimp only [build]
      split
      · simp [Store.set]
      · cases hatAt D st (m - 1) β <;> simp [Store.set]
  | next I β =>
      dsimp only [build]
      cases hatAt D st (m + 1) β <;> simp [Store.set]
  | since I β γ =>
      dsimp only [build]
      cases hatAt D st m β <;> cases hatAt D st m γ <;>
        cases (if m = 0 then some ∅ else st (.r (.since I β γ)) (m - 1)) <;> try rfl
      dsimp only
      have h1 : ∀ (st' : Store S) X, (st'.set (.p (.since I β γ)) m X) (.r α) j = st' (.r α) j := by
        intro st' X; simp [Store.set]
      rw [h1, set_r_frame _ _ hne]
  | «until» I β γ =>
      dsimp only [build]
      split
      · have h1 : ∀ (st' : Store S) X, (st'.set (.p (.until I β γ)) m X) (.r α) j = st' (.r α) j := by
          intro st' X; simp [Store.set]
        have h2 : ∀ (st' : Store S) X, (st'.set (.s (.until I β γ)) m X) (.r α) j = st' (.r α) j := by
          intro st' X; simp [Store.set]
        rw [h1, h2, set_r_frame _ _ hne]
      · rfl

theorem build_s_frame (D : TempStruct S) (st : Store S) (e : Formula S × ℕ)
    (α : Formula S) (j : ℕ) (hne : (α, j) ≠ e) :
    build D st e (.s α) j = st (.s α) j := by
  rcases e with ⟨β, m⟩
  cases β with
  | eq _ _ => rfl
  | pred _ _ => rfl
  | neg _ => rfl
  | or _ _ => rfl
  | ex _ _ => rfl
  | prev I β =>
      dsimp only [build]
      split
      · simp [Store.set]
      · cases hatAt D st (m - 1) β <;> simp [Store.set]
  | next I β =>
      dsimp only [build]
      cases hatAt D st (m + 1) β <;> simp [Store.set]
  | since I β γ =>
      dsimp only [build]
      cases hatAt D st m β <;> cases hatAt D st m γ <;>
        cases (if m = 0 then some ∅ else st (.r (.since I β γ)) (m - 1)) <;>
        simp [Store.set]
  | «until» I β γ =>
      dsimp only [build]
      split
      · have h1 : ∀ (st' : Store S) X, (st'.set (.p (.until I β γ)) m X) (.s α) j = st' (.s α) j := by
          intro st' X; simp [Store.set]
        have h2 : ∀ (st' : Store S) X, (st'.set (.r (.until I β γ)) m X) (.s α) j = st' (.s α) j := by
          intro st' X; simp [Store.set]
        rw [h1, set_s_frame _ _ hne, h2]
      · rfl

theorem build_jobValid_frame (D : TempStruct S) (st : Store S) (e : Formula S × ℕ)
    (α : Formula S) (j : ℕ) (hne : (α, j) ≠ e) (h : JobValid D st α j) :
    JobValid D (build D st e) α j := by
  unfold JobValid
  refine ⟨?_, ?_, ?_⟩
  · rw [QueueProof.build_p_frame D st e α j hne]
    exact h.1
  · intro I β γ hα
    rw [build_r_frame D st e α j hne]
    exact h.2.1 I β γ hα
  · intro I β γ hα
    rw [build_r_frame D st e α j hne, build_s_frame D st e α j hne]
    exact h.2.2 I β γ hα

theorem hatAt_eq_some_satSet (D : TempStruct S) (st : Store S) (m : ℕ) (β : Formula S)
    (hbase : ∀ r, st (.base r) m = some (D.rel m r))
    (htsub : ∀ ψ ∈ tsub β, st (.p ψ) m = some (satSet D ψ m)) :
    hatAt D st m β = some (satSet D β m) := by
  have hcond : (∀ r, (st (.base r) m).isSome) ∧ (∀ ψ ∈ tsub β, (st (.p ψ) m).isSome) :=
    ⟨fun r ↦ by rw [hbase r]; rfl, fun ψ hψ ↦ by rw [htsub ψ hψ]; rfl⟩
  unfold hatAt
  rw [if_pos hcond]
  congr 1
  have hrel : (fun r ↦ (st (.base r) m).getD ∅) = D.rel m := by
    ext r ds
    rw [hbase r]
    rfl
  rw [hrel]
  exact hatSet_eq_satSet D m (fun ψ ↦ (st (.p ψ) m).getD ∅) β fun ψ hψ ↦ by
    rw [htsub ψ hψ]
    rfl

theorem untilStep_congr (D : TempStruct S) (I : Interval) (j : ℕ)
    (B₁ B₂ G₁ G₂ : ℕ → Set (List ℕ)) (r₁ r₂ s₁ s₂ : Set (List ℕ))
    (hBG : ∀ k, prevLookahead D I.hi.toNat j ≤ k → k ≤ lookahead D I.hi.toNat j →
      B₁ (j + k) = B₂ (j + k) ∧ G₁ (j + k) = G₂ (j + k))
    (hrs : j ≠ 0 → r₁ = r₂ ∧ s₁ = s₂) :
    untilStep D I j B₁ G₁ r₁ s₁ = untilStep D I j B₂ G₂ r₂ s₂ := by
  have hNr : {x | ∃ (a : List ℕ) (j₁ : ℕ), x = a ++ [j₁] ∧
        prevLookahead D I.hi.toNat j ≤ j₁ ∧ j₁ ≤ lookahead D I.hi.toNat j ∧
        ∀ k, j₁ ≤ k → k ≤ lookahead D I.hi.toNat j → a ∈ B₁ (j + k)} =
      {x | ∃ (a : List ℕ) (j₁ : ℕ), x = a ++ [j₁] ∧
        prevLookahead D I.hi.toNat j ≤ j₁ ∧ j₁ ≤ lookahead D I.hi.toNat j ∧
        ∀ k, j₁ ≤ k → k ≤ lookahead D I.hi.toNat j → a ∈ B₂ (j + k)} := by
    ext x
    refine exists_congr fun a ↦ exists_congr fun j₁ ↦ and_congr_right fun _ ↦
      and_congr_right fun hℓp ↦ and_congr_right fun _ ↦ forall_congr' fun k ↦
      imp_congr_right fun hj₁k ↦ imp_congr_right fun hkℓ ↦ ?_
    rw [(hBG k (hℓp.trans hj₁k) hkℓ).1]
  have hUr : (if j = 0 then ∅ else
        {x | ∃ (a : List ℕ) (j₁ : ℕ), x = a ++ [j₁ - 1] ∧ a ++ [j₁] ∈ r₁ ∧
          ∀ k, prevLookahead D I.hi.toNat j ≤ k → k ≤ lookahead D I.hi.toNat j →
            a ∈ B₁ (j + k)}) =
      (if j = 0 then ∅ else
        {x | ∃ (a : List ℕ) (j₁ : ℕ), x = a ++ [j₁ - 1] ∧ a ++ [j₁] ∈ r₂ ∧
          ∀ k, prevLookahead D I.hi.toNat j ≤ k → k ≤ lookahead D I.hi.toNat j →
            a ∈ B₂ (j + k)}) := by
    by_cases hj : j = 0
    · simp [hj]
    · simp only [hj, ↓reduceIte]
      ext x
      refine exists_congr fun a ↦ exists_congr fun j₁ ↦ and_congr_right fun _ ↦ ?_
      rw [(hrs hj).1]
      refine and_congr_right fun _ ↦ forall_congr' fun k ↦
        imp_congr_right fun hℓpk ↦ imp_congr_right fun hkℓ ↦ ?_
      rw [(hBG k hℓpk hkℓ).1]
  have hNs : {x | ∃ (a : List ℕ) (j₁ j' t : ℕ), x = a ++ [j₁, j', t] ∧
        prevLookahead D I.hi.toNat j ≤ j₁ ∧ j₁ ≤ j' ∧ j' ≤ lookahead D I.hi.toNat j ∧
        a ∈ G₁ (j + j') ∧ t = D.τ (j + j') - D.τ j ∧ I.lo ≤ t ∧
        ∀ k, j₁ ≤ k → k < j' → a ∈ B₁ (j + k)} =
      {x | ∃ (a : List ℕ) (j₁ j' t : ℕ), x = a ++ [j₁, j', t] ∧
        prevLookahead D I.hi.toNat j ≤ j₁ ∧ j₁ ≤ j' ∧ j' ≤ lookahead D I.hi.toNat j ∧
        a ∈ G₂ (j + j') ∧ t = D.τ (j + j') - D.τ j ∧ I.lo ≤ t ∧
        ∀ k, j₁ ≤ k → k < j' → a ∈ B₂ (j + k)} := by
    ext x
    refine exists_congr fun a ↦ exists_congr fun j₁ ↦ exists_congr fun j' ↦
      exists_congr fun t ↦ and_congr_right fun _ ↦ and_congr_right fun hℓp ↦
      and_congr_right fun hjj' ↦ and_congr_right fun hj'ℓ ↦ ?_
    rw [(hBG j' (hℓp.trans hjj') hj'ℓ).2]
    refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
      forall_congr' fun k ↦ imp_congr_right fun hjk ↦ imp_congr_right fun hkj' ↦ ?_
    rw [(hBG k (hℓp.trans hjk) (Nat.le_of_lt (lt_of_lt_of_le hkj' hj'ℓ))).1]
  have hUs : (if j = 0 then ∅ else
        {x | ∃ (a : List ℕ) (j₁ j' t t' : ℕ), x = a ++ [j₁ - 1, j' - 1, t] ∧
          a ++ [j₁, j', t'] ∈ s₁ ∧ 1 ≤ j' ∧ t + (D.τ j - D.τ (j - 1)) = t' ∧ I.lo ≤ t}) =
      (if j = 0 then ∅ else
        {x | ∃ (a : List ℕ) (j₁ j' t t' : ℕ), x = a ++ [j₁ - 1, j' - 1, t] ∧
          a ++ [j₁, j', t'] ∈ s₂ ∧ 1 ≤ j' ∧ t + (D.τ j - D.τ (j - 1)) = t' ∧ I.lo ≤ t}) := by
    by_cases hj : j = 0
    · simp [hj]
    · simp only [hj, ↓reduceIte, (hrs hj).2]
  unfold untilStep
  dsimp only
  rw [hNr, hUr, hNs, hUs]
  by_cases hj : j = 0
  · simp [hj]
  · simp only [hj, ↓reduceIte, (hrs hj).1]

theorem build_step_jobValid (D : TempStruct S) (st : Store S) (α : Formula S) (j : ℕ)
    (htemp : α.isTemporal = true) (hbdd : Bounded α) (hfree : DirectFreeAligned α)
    (hprev : ∀ I β, α = .prev I β → 0 < j → hatAt D st (j - 1) β = some (satSet D β (j - 1)))
    (hnext : ∀ I β, α = .next I β → hatAt D st (j + 1) β = some (satSet D β (j + 1)))
    (hsince : ∀ I β γ, α = .since I β γ →
      hatAt D st j β = some (satSet D β j) ∧ hatAt D st j γ = some (satSet D γ j) ∧
        (0 < j → JobValid D st (.since I β γ) (j - 1)))
    (huntil : ∀ I β γ, α = .until I β γ →
      (∀ k, prevLookahead D I.hi.toNat j ≤ k → k ≤ lookahead D I.hi.toNat j →
        hatAt D st (j + k) β = some (satSet D β (j + k)) ∧
        hatAt D st (j + k) γ = some (satSet D γ (j + k))) ∧
        (0 < j → JobValid D st (.until I β γ) (j - 1))) :
    JobValid D (build D st (α, j)) α j := by
  unfold JobValid
  cases α with
  | eq _ _ => cases htemp
  | pred _ _ => cases htemp
  | neg _ => cases htemp
  | or _ _ => cases htemp
  | ex _ _ => cases htemp
  | prev I β =>
      by_cases hj : j = 0
      · subst hj
        dsimp only [build, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Store.set, and_self, ↓reduceIte]
          have he (A : Set (List ℕ)) : prevP D.τ I 0 A = ∅ :=
            if_neg (fun h ↦ Nat.lt_irrefl 0 h.1)
          rw [← prevP_satSet D I β 0, he, he]
        · intro _ _ _ h; cases h
        · intro _ _ _ h; cases h
      · have hpos : 0 < j := Nat.pos_of_ne_zero hj
        have hhat := hprev I β rfl hpos
        dsimp only [build]
        rw [if_neg hj, hhat]
        refine ⟨?_, ?_, ?_⟩
        · simp only [Store.set, and_self, ↓reduceIte]
          rw [prevP_satSet D I β j]
        · intro _ _ _ h; cases h
        · intro _ _ _ h; cases h
  | next I β =>
      have hhat := hnext I β rfl
      dsimp only [build]
      rw [hhat]
      refine ⟨?_, ?_, ?_⟩
      · simp only [Store.set, and_self, ↓reduceIte]
        rw [nextP_satSet D I β j]
      · intro _ _ _ h; cases h
      · intro _ _ _ h; cases h
  | since I β γ =>
      obtain ⟨hB, hG, hprev_r⟩ := hsince I β γ rfl
      let B (m : ℕ) := satSet D β m
      let G (m : ℕ) := satSet D γ m
      have hR : (if j = 0 then some ∅ else st (.r (.since I β γ)) (j - 1)) =
          some (if j = 0 then ∅ else sinceR D.τ I B G (j - 1)) := by
        by_cases hj : j = 0
        · simp [hj]
        · have hpos : 0 < j := Nat.pos_of_ne_zero hj
          have hr := (hprev_r hpos).2.1 I β γ rfl
          simp [hj, hr, B, G]
      have hstep_eq : sinceStep D.τ I j (satSet D β j) (satSet D γ j)
          (if j = 0 then ∅ else sinceR D.τ I B G (j - 1)) = sinceR D.τ I B G j := by
        cases j with
        | zero => rfl
        | succ m => rfl
      dsimp only [build]
      rw [hB, hG, hR]
      dsimp only
      rw [hstep_eq]
      refine ⟨?_, ?_, ?_⟩
      · simp only [Store.set, and_self, ↓reduceIte]
        rw [sinceP_eq_satSet_of_correct D I β γ hfree.1 B G j (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)]
      · intro I' β' γ' h
        obtain ⟨rfl, rfl, rfl⟩ := Formula.since.inj h
        simp [Store.set, B, G]
      · intro _ _ _ h; cases h
  | «until» I β γ =>
      obtain ⟨hBG, hprev_rs⟩ := huntil I β γ rfl
      let B (m : ℕ) := satSet D β m
      let G (m : ℕ) := satSet D γ m
      have hcond1 : ∀ k, prevLookahead D I.hi.toNat j ≤ k → k ≤ lookahead D I.hi.toNat j →
          (hatAt D st (j + k) β).isSome ∧ (hatAt D st (j + k) γ).isSome := by
        intro k hk1 hk2
        obtain ⟨h1, h2⟩ := hBG k hk1 hk2
        rw [h1, h2]
        exact ⟨rfl, rfl⟩
      have hcond2 : j = 0 ∨ ((st (.r (.until I β γ)) (j - 1)).isSome ∧
          (st (.s (.until I β γ)) (j - 1)).isSome) := by
        by_cases hj : j = 0
        · exact Or.inl hj
        · right
          obtain ⟨hr, hs⟩ := (hprev_rs (Nat.pos_of_ne_zero hj)).2.2 I β γ rfl
          rw [hr, hs]
          exact ⟨rfl, rfl⟩
      have hrs_eq : untilStep D I j (fun m ↦ (hatAt D st m β).getD ∅)
          (fun m ↦ (hatAt D st m γ).getD ∅) ((st (.r (.until I β γ)) (j - 1)).getD ∅)
          ((st (.s (.until I β γ)) (j - 1)).getD ∅) = untilRS D I B G j := by
        have hcongr := untilStep_congr D I j (fun m ↦ (hatAt D st m β).getD ∅) B
          (fun m ↦ (hatAt D st m γ).getD ∅) G
          ((st (.r (.until I β γ)) (j - 1)).getD ∅)
          (if j = 0 then ∅ else (untilRS D I B G (j - 1)).1)
          ((st (.s (.until I β γ)) (j - 1)).getD ∅)
          (if j = 0 then ∅ else (untilRS D I B G (j - 1)).2)
          (fun k hk1 hk2 ↦ by
            obtain ⟨h1, h2⟩ := hBG k hk1 hk2
            rw [h1, h2]
            exact ⟨rfl, rfl⟩)
          (fun hj ↦ by
            obtain ⟨hr, hs⟩ := (hprev_rs (Nat.pos_of_ne_zero hj)).2.2 I β γ rfl
            simp [hj, hr, hs, B, G])
        rw [hcongr]
        cases j with
        | zero => rfl
        | succ m => rfl
      dsimp only [build]
      rw [if_pos ⟨hcond1, hcond2⟩, hrs_eq]
      have hb' : I.hi = (I.hi.toNat : ℕ∞) := (ENat.natCast_toNat hbdd.1).symm
      refine ⟨?_, ?_, ?_⟩
      · simp only [Store.set, and_self, ↓reduceIte]
        rw [untilP_eq_satSet_of_correct D I I.hi.toNat hb' β γ hfree.1 B G j
          (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)]
      · intro _ _ _ h; cases h
      · intro I' β' γ' h
        obtain ⟨rfl, rfl, rfl⟩ := Formula.until.inj h
        simp [Store.set, B, G]

def leJob (a b : Formula S × ℕ) : Bool :=
  decide (a.1.size < b.1.size ∨ (a.1.size = b.1.size ∧ a.2 ≤ b.2))

theorem leJob_total (a b : Formula S × ℕ) : (leJob a b || leJob b a) = true := by
  simp only [leJob, Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem leJob_trans (a b c : Formula S × ℕ) (hab : leJob a b = true)
    (hbc : leJob b c = true) : leJob a c = true := by
  simp only [leJob, decide_eq_true_eq] at hab hbc ⊢
  omega

theorem not_mem_cons_of_lt_job {e : Formula S × ℕ} {L : List (Formula S × ℕ)}
    (hpair : List.Pairwise (fun a b ↦ leJob a b = true) (e :: L))
    {x : Formula S × ℕ} (hlt : x.1.size < e.1.size ∨ (x.1.size = e.1.size ∧ x.2 < e.2)) :
    x ∉ e :: L := by
  intro hmem
  have hle : leJob e x = true := by
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · simp [leJob]
    · exact (List.pairwise_cons.mp hpair).1 x hmem'
  simp only [leJob, decide_eq_true_eq] at hle
  omega

theorem foldl_build_invariant (D : TempStruct S) (Φ : Formula S)
    (hΦ : Bounded Φ) (hfree : DirectFreeAligned Φ) (k : ℕ)
    (L : List (Formula S × ℕ))
    (hpair : List.Pairwise (fun a b ↦ leJob a b = true) L)
    (hL : ∀ e ∈ L, e.1 ∈ tempSubs Φ ∧ (run D Φ k).i ≤ e.2 ∧
      QueueProof.horizon D e.1 e.2 = k)
    (st : Store S)
    (hbase : ∀ r m, (run D Φ k).i ≤ m + 1 → m ≤ k → st (.base r) m = some (D.rel m r))
    (hbuilt : ∀ β ∈ tempSubs Φ, ∀ m, (run D Φ k).i ≤ m + 1 →
      QueueProof.horizon D β m ≤ k → (β, m) ∉ L → JobValid D st β m)
    (hp_some : ∀ β ∈ tempSubs Φ, ∀ m X, st (.p β) m = some X → X = satSet D β m) :
    (∀ β ∈ tempSubs Φ, ∀ m, (run D Φ k).i ≤ m + 1 →
      QueueProof.horizon D β m ≤ k → JobValid D (L.foldl (build D) st) β m) ∧
    (∀ β ∈ tempSubs Φ, ∀ m X, (L.foldl (build D) st) (.p β) m = some X → X = satSet D β m) := by
  induction L generalizing st with
  | nil =>
      exact ⟨fun β hβ m hm hhor ↦ hbuilt β hβ m hm hhor (by simp), hp_some⟩
  | cons e L' ih =>
      rcases e with ⟨α, j⟩
      obtain ⟨hα, hij, hhor⟩ := hL (α, j) List.mem_cons_self
      have hα_sub : α ∈ subformulas Φ := (List.mem_filter.mp hα).1
      have hα_temp : α.isTemporal = true := (List.mem_filter.mp hα).2
      have hα_bdd : Bounded α := QueueProof.bounded_of_mem_tempSubs Φ hΦ α hα
      have hα_free : DirectFreeAligned α := directFreeAligned_of_mem_tempSubs Φ hfree α hα
      have hjk : j ≤ k := hhor ▸ QueueProof.le_horizon D α j
      have hhat_child : ∀ {β : Formula S} {m : ℕ}, β ∈ subformulas α →
          β.size < α.size → (run D Φ k).i ≤ m + 1 → m ≤ k →
          QueueProof.horizon D β m ≤ k → hatAt D st m β = some (satSet D β m) := by
        intro β m hβsub hβsz hm_ge hm_le hβhor
        refine hatAt_eq_some_satSet D st m β (fun r ↦ hbase r m hm_ge hm_le) ?_
        intro ψ hψ
        have hψ_temp : ψ ∈ tempSubs Φ :=
          mem_tempSubs_of_mem_tsub (subformulas_trans hβsub hα_sub) hψ
        have hψ_sz : ψ.size < α.size :=
          Nat.lt_of_le_of_lt (size_le_of_mem_subformulas (mem_subformulas_of_mem_tsub hψ).1) hβsz
        have hψ_hor : QueueProof.horizon D ψ m ≤ k :=
          (QueueProof.horizon_tsub_le D β m ψ hψ).trans hβhor
        have hnot_mem : (ψ, m) ∉ (α, j) :: L' :=
          not_mem_cons_of_lt_job hpair (Or.inl hψ_sz)
        exact (hbuilt ψ hψ_temp m hm_ge hψ_hor hnot_mem).1
      have hstep : JobValid D (build D st (α, j)) α j := by
        refine build_step_jobValid D st α j hα_temp hα_bdd hα_free ?_ ?_ ?_ ?_
        · intro I β hα_eq hpos
          subst hα_eq
          have hβ_sub : β ∈ subformulas (.prev I β) := by simp [subformulas, subformulas_refl]
          have hβ_sz : β.size < (Formula.prev I β).size := by simp [Formula.size]
          have hβ_bdd : Bounded β := hα_bdd
          have hβ_hor : QueueProof.horizon D β (j - 1) ≤ k := by
            have h1 := QueueProof.horizon_mono D β hβ_bdd (show j - 1 ≤ j by omega)
            exact h1.trans hhor.le
          exact hhat_child hβ_sub hβ_sz (by omega) (by omega) hβ_hor
        · intro I β hα_eq
          subst hα_eq
          have hβ_sub : β ∈ subformulas (.next I β) := by simp [subformulas, subformulas_refl]
          have hβ_sz : β.size < (Formula.next I β).size := by simp [Formula.size]
          have hβ_hor : QueueProof.horizon D β (j + 1) ≤ k := hhor.le
          have hj1k : j + 1 ≤ k := (QueueProof.le_horizon D β (j + 1)).trans hβ_hor
          exact hhat_child hβ_sub hβ_sz (by omega) hj1k hβ_hor
        · intro I β γ hα_eq
          subst hα_eq
          have hβ_sub : β ∈ subformulas (.since I β γ) := by
            simp [subformulas, subformulas_refl]
          have hγ_sub : γ ∈ subformulas (.since I β γ) := by
            simp [subformulas, subformulas_refl]
          have hβ_sz : β.size < (Formula.since I β γ).size := by dsimp [Formula.size]; omega
          have hγ_sz : γ.size < (Formula.since I β γ).size := by dsimp [Formula.size]; omega
          have hβ_hor : QueueProof.horizon D β j ≤ k :=
            (le_max_left _ (QueueProof.horizon D γ j)).trans hhor.le
          have hγ_hor : QueueProof.horizon D γ j ≤ k :=
            (le_max_right (QueueProof.horizon D β j) _).trans hhor.le
          refine ⟨hhat_child hβ_sub hβ_sz (by omega) hjk hβ_hor,
            hhat_child hγ_sub hγ_sz (by omega) hjk hγ_hor, fun hpos ↦ ?_⟩
          have hprev_hor : QueueProof.horizon D (.since I β γ) (j - 1) ≤ k :=
            (QueueProof.horizon_mono D (.since I β γ) hα_bdd (by omega)).trans hhor.le
          have hnot_mem : (Formula.since I β γ, j - 1) ∉ (Formula.since I β γ, j) :: L' :=
            not_mem_cons_of_lt_job hpair (Or.inr ⟨rfl, by omega⟩)
          exact hbuilt (.since I β γ) hα (j - 1) (by omega) hprev_hor hnot_mem
        · intro I β γ hα_eq
          subst hα_eq
          let ℓ := lookahead D I.hi.toNat j
          have hβ_sub : β ∈ subformulas (.until I β γ) := by
            simp [subformulas, subformulas_refl]
          have hγ_sub : γ ∈ subformulas (.until I β γ) := by
            simp [subformulas, subformulas_refl]
          have hβ_sz : β.size < (Formula.until I β γ).size := by dsimp [Formula.size]; omega
          have hγ_sz : γ.size < (Formula.until I β γ).size := by dsimp [Formula.size]; omega
          have hβ_end : QueueProof.horizon D β (j + ℓ + 1) ≤ k :=
            (le_max_left _ (QueueProof.horizon D γ (j + ℓ + 1))).trans hhor.le
          have hγ_end : QueueProof.horizon D γ (j + ℓ + 1) ≤ k :=
            (le_max_right (QueueProof.horizon D β (j + ℓ + 1)) _).trans hhor.le
          refine ⟨fun m _ hmℓ ↦ ?_, fun hpos ↦ ?_⟩
          · have hjm : j + m ≤ j + ℓ + 1 := by omega
            have hjm_k : j + m ≤ k :=
              hjm.trans ((QueueProof.le_horizon D β (j + ℓ + 1)).trans hβ_end)
            have hβ_hor : QueueProof.horizon D β (j + m) ≤ k :=
              (QueueProof.horizon_mono D β hα_bdd.2.1 hjm).trans hβ_end
            have hγ_hor : QueueProof.horizon D γ (j + m) ≤ k :=
              (QueueProof.horizon_mono D γ hα_bdd.2.2 hjm).trans hγ_end
            exact ⟨hhat_child hβ_sub hβ_sz (by omega) hjm_k hβ_hor,
              hhat_child hγ_sub hγ_sz (by omega) hjm_k hγ_hor⟩
          · have hprev_hor : QueueProof.horizon D (.until I β γ) (j - 1) ≤ k :=
              (QueueProof.horizon_mono D (.until I β γ) hα_bdd (by omega)).trans hhor.le
            have hnot_mem : (Formula.until I β γ, j - 1) ∉ (Formula.until I β γ, j) :: L' :=
              not_mem_cons_of_lt_job hpair (Or.inr ⟨rfl, by omega⟩)
            exact hbuilt (.until I β γ) hα (j - 1) (by omega) hprev_hor hnot_mem
      apply ih (List.pairwise_cons.mp hpair).2
        (fun e he ↦ hL e (List.mem_cons_of_mem _ he)) (build D st (α, j))
      · intro r m hm_ge hm_le
        rw [build_base_frame]
        exact hbase r m hm_ge hm_le
      · intro β hβ m hm_ge hβ_hor hnot_mem'
        by_cases heq : (β, m) = (α, j)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          exact hstep
        · have hnot_mem : (β, m) ∉ (α, j) :: L' := by
            intro h
            rcases List.mem_cons.mp h with h | h
            · exact heq h
            · exact hnot_mem' h
          exact build_jobValid_frame D st (α, j) β m heq
            (hbuilt β hβ m hm_ge hβ_hor hnot_mem)
      · intro β hβ m X hX
        by_cases heq : (β, m) = (α, j)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [hstep.1] at hX
          exact (Option.some.inj hX).symm
        · rw [QueueProof.build_p_frame D st (α, j) β m heq] at hX
          exact hp_some β hβ m X hX

theorem afterBuild_invariant (D : TempStruct S) (Φ : Formula S)
    (hΦ : Bounded Φ) (hfree : DirectFreeAligned Φ) (k : ℕ)
    (hbase : ∀ r m, (run D Φ k).i ≤ m + 1 → m < k →
      (run D Φ k).store (.base r) m = some (D.rel m r))
    (hbase_some : ∀ r m X, (run D Φ k).store (.base r) m = some X → X = D.rel m r)
    (hbuilt : ∀ β ∈ tempSubs Φ, ∀ m, (run D Φ k).i ≤ m + 1 →
      QueueProof.horizon D β m < k → JobValid D (run D Φ k).store β m)
    (hp_some : ∀ β ∈ tempSubs Φ, ∀ m X,
      (run D Φ k).store (.p β) m = some X → X = satSet D β m) :
    let s0 := afterBuild D (run D Φ k)
    (∀ r m, s0.i ≤ m + 1 → m ≤ k → s0.store (.base r) m = some (D.rel m r)) ∧
    (∀ r m X, s0.store (.base r) m = some X → X = D.rel m r) ∧
    (∀ β ∈ tempSubs Φ, ∀ m, s0.i ≤ m + 1 →
      QueueProof.horizon D β m ≤ k → JobValid D s0.store β m) ∧
    (∀ β ∈ tempSubs Φ, ∀ m X, s0.store (.p β) m = some X → X = satSet D β m) := by
  dsimp only
  let s := run D Φ k
  let st1 : Store S := fun key j ↦ match key with
    | .base r => if j = s.ell then some (D.rel s.ell r) else s.store (.base r) j
    | key => s.store key j
  let ready : List (Formula S × ℕ) :=
    ((s.Q.filter fun e ↦ e.2.2.isEmpty).map fun e ↦ (e.1, e.2.1)).mergeSort
      fun a b ↦ leJob a b
  have hmem_ready : ∀ α j, (α, j) ∈ ready ↔ (α, j, ([] : List (Formula S))) ∈ s.Q := by
    intro α j
    rw [List.mem_mergeSort, List.mem_map]
    constructor
    · rintro ⟨⟨β, m, W⟩, hfilt, heq⟩
      obtain ⟨hQ, hempty⟩ := List.mem_filter.mp hfilt
      have hW : W = [] := List.isEmpty_iff.mp hempty
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rwa [hW] at hQ
    · intro hQ
      refine ⟨(α, j, []), List.mem_filter.mpr ⟨hQ, rfl⟩, rfl⟩
  have hpair : List.Pairwise (fun a b ↦ leJob a b = true) ready :=
    List.pairwise_mergeSort leJob_trans leJob_total _
  have hL : ∀ e ∈ ready, e.1 ∈ tempSubs Φ ∧ s.i ≤ e.2 ∧
      QueueProof.horizon D e.1 e.2 = k := by
    intro ⟨α, j⟩ hmem
    have hQ := (hmem_ready α j).mp hmem
    obtain ⟨hα, hhor⟩ := (QueueProof.mem_run_Q_ready_iff D Φ hΦ k α j).mp hQ
    have hij := ((QueueProof.run_pending_invariant D Φ k).1 α j [] hQ).1
    exact ⟨hα, hij, hhor⟩
  have hst1_base : ∀ r m, s.i ≤ m + 1 → m ≤ k → st1 (.base r) m = some (D.rel m r) := by
    intro r m hm_ge hm_le
    dsimp only [st1]
    rw [QueueProof.run_ell]
    by_cases hmk : m = k
    · subst hmk; simp
    · simp only [hmk, ↓reduceIte]
      exact hbase r m hm_ge (by omega)
  have hst1_base_some : ∀ r m X, st1 (.base r) m = some X → X = D.rel m r := by
    intro r m X hX
    dsimp only [st1] at hX
    split at hX
    · rename_i h
      subst h
      exact (Option.some.inj hX).symm
    · exact hbase_some r m X hX
  have hst1_built : ∀ β ∈ tempSubs Φ, ∀ m, s.i ≤ m + 1 →
      QueueProof.horizon D β m ≤ k → (β, m) ∉ ready → JobValid D st1 β m := by
    intro β hβ m hm_ge hhor hnot_mem
    have hnot_Q : (β, m, ([] : List (Formula S))) ∉ s.Q :=
      mt (hmem_ready β m).mpr hnot_mem
    have hne_k : QueueProof.horizon D β m ≠ k :=
      fun heq ↦ hnot_Q ((QueueProof.mem_run_Q_ready_iff D Φ hΦ k β m).mpr ⟨hβ, heq⟩)
    exact hbuilt β hβ m hm_ge (by omega)
  have hfold := foldl_build_invariant D Φ hΦ hfree k ready hpair hL st1
    hst1_base hst1_built hp_some
  refine ⟨?_, ?_, hfold.1, hfold.2⟩
  · intro r m hm_ge hm_le
    change (ready.foldl (build D) st1) (.base r) m = some (D.rel m r)
    rw [foldl_build_base_frame]
    exact hst1_base r m hm_ge hm_le
  · intro r m X hX
    change (ready.foldl (build D) st1) (.base r) m = some X at hX
    rw [foldl_build_base_frame] at hX
    exact hst1_base_some r m X hX

theorem evalLoop_invariant [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (hlt : HasOrderPred D) (Φ : Formula S)
    (hΦ : Bounded Φ) (hfree : DirectFreeAligned Φ) (k fuel : ℕ) (s : State S)
    (hbase : ∀ r m, s.i ≤ m + 1 → m ≤ k → s.store (.base r) m = some (D.rel m r))
    (hbase_some : ∀ r m X, s.store (.base r) m = some X → X = D.rel m r)
    (hbuilt : ∀ β ∈ tempSubs Φ, ∀ m, s.i ≤ m + 1 →
      QueueProof.horizon D β m ≤ k → JobValid D s.store β m)
    (hp_some : ∀ β ∈ tempSubs Φ, ∀ m X, s.store (.p β) m = some X → X = satSet D β m)
    (hout : ∀ n O t, (n, O, t) ∈ s.out →
      O = satSet D (.neg Φ) n ∧ RegularRel rep (freeList Φ).length O ∧ t = D.τ n) :
    let s1 := evalLoop D Φ fuel s
    (∀ r m, s1.i ≤ m + 1 → m ≤ k → s1.store (.base r) m = some (D.rel m r)) ∧
    (∀ r m X, s1.store (.base r) m = some X → X = D.rel m r) ∧
    (∀ β ∈ tempSubs Φ, ∀ m, s1.i ≤ m + 1 →
      QueueProof.horizon D β m ≤ k → JobValid D s1.store β m) ∧
    (∀ β ∈ tempSubs Φ, ∀ m X, s1.store (.p β) m = some X → X = satSet D β m) ∧
    (∀ n O t, (n, O, t) ∈ s1.out →
      O = satSet D (.neg Φ) n ∧ RegularRel rep (freeList Φ).length O ∧ t = D.τ n) := by
  induction fuel generalizing s with
  | zero => exact ⟨hbase, hbase_some, hbuilt, hp_some, hout⟩
  | succ fuel ih =>
      rw [evalLoop]
      split
      · rename_i hcomp
        dsimp only
        let O := hatSet (fun r ↦ (s.store (.base r) s.i).getD ∅) D.const
          (fun α ↦ (s.store (.p α) s.i).getD ∅) (.neg Φ)
        let st' := if 0 < s.i then s.store.discard (s.i - 1) else s.store
        have hO_eq : O = satSet D (.neg Φ) s.i := by
          have hrel : (fun r ↦ (s.store (.base r) s.i).getD ∅) = D.rel s.i := by
            ext r ds
            obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp (hcomp.1 r)
            rw [hX, hbase_some r s.i X hX]
            rfl
          dsimp only [O]
          rw [hrel]
          exact hatSet_eq_satSet D s.i (fun α ↦ (s.store (.p α) s.i).getD ∅) (.neg Φ)
            fun ψ hψ ↦ by
              have hψ_temp : ψ ∈ tempSubs Φ :=
                mem_tempSubs_of_mem_tsub (subformulas_refl Φ) hψ
              obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp (hcomp.2 ψ hψ_temp)
              rw [hX, hp_some ψ hψ_temp s.i X hX]
              rfl
        have hO_reg : RegularRel rep (freeList Φ).length O := by
          rw [hO_eq]
          exact regular_satSet rep D hD hlt (.neg Φ) hΦ hfree s.i
        have hst'_eq : ∀ key m, s.i ≤ m → st' key m = s.store key m := by
          intro key m hm
          dsimp only [st']
          split
          · rename_i hpos
            have hne : m ≠ s.i - 1 := by omega
            simp [Store.discard, hne]
          · rfl
        have hst'_some : ∀ key m X, st' key m = some X → s.store key m = some X := by
          intro key m X hX
          dsimp only [st'] at hX
          split at hX
          · dsimp only [Store.discard] at hX
            split at hX
            · cases hX
            · exact hX
          · exact hX
        apply ih { s with out := s.out ++ [(s.i, O, D.τ s.i)], store := st', i := s.i + 1 }
        · intro r m hm_ge hm_le
          dsimp only at hm_ge ⊢
          rw [hst'_eq _ m (by omega)]
          exact hbase r m (by omega) hm_le
        · intro r m X hX
          dsimp only at hX
          exact hbase_some r m X (hst'_some _ m X hX)
        · intro β hβ m hm_ge hhor
          dsimp only at hm_ge ⊢
          have hvalid := hbuilt β hβ m (by omega) hhor
          unfold JobValid
          refine ⟨?_, ?_, ?_⟩
          · rw [hst'_eq _ m (by omega)]; exact hvalid.1
          · intro I β' γ' hα; rw [hst'_eq _ m (by omega)]; exact hvalid.2.1 I β' γ' hα
          · intro I β' γ' hα; rw [hst'_eq _ m (by omega), hst'_eq _ m (by omega)]
            exact hvalid.2.2 I β' γ' hα
        · intro β hβ m X hX
          dsimp only at hX
          exact hp_some β hβ m X (hst'_some _ m X hX)
        · intro n O' t hmem
          dsimp only at hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hout n O' t hmem
          · obtain ⟨rfl, h2⟩ := Prod.mk.inj (List.mem_singleton.mp hmem)
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
            exact ⟨hO_eq, hO_reg, rfl⟩
      · exact ⟨hbase, hbase_some, hbuilt, hp_some, hout⟩

theorem run_store_invariant [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (hlt : HasOrderPred D) (Φ : Formula S)
    (hΦ : Bounded Φ) (hfree : DirectFreeAligned Φ) (k : ℕ) :
    (∀ r m, (run D Φ k).i ≤ m + 1 → m < k →
      (run D Φ k).store (.base r) m = some (D.rel m r)) ∧
    (∀ r m X, (run D Φ k).store (.base r) m = some X → X = D.rel m r) ∧
    (∀ β ∈ tempSubs Φ, ∀ m, (run D Φ k).i ≤ m + 1 →
      QueueProof.horizon D β m < k → JobValid D (run D Φ k).store β m) ∧
    (∀ β ∈ tempSubs Φ, ∀ m X, (run D Φ k).store (.p β) m = some X → X = satSet D β m) ∧
    (∀ n O t, (n, O, t) ∈ (run D Φ k).out →
      O = satSet D (.neg Φ) n ∧ RegularRel rep (freeList Φ).length O ∧ t = D.τ n) := by
  induction k with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro _ _ _ h; omega
      · intro _ _ _ h; cases h
      · intro _ _ _ _ h; omega
      · intro _ _ _ _ h; cases h
      · intro _ _ _ h; cases h
  | succ k ih =>
      obtain ⟨hbase, hbase_some, hbuilt, hp_some, hout⟩ := ih
      have hafter := afterBuild_invariant D Φ hΦ hfree k hbase hbase_some hbuilt hp_some
      have heval := evalLoop_invariant rep D hD hlt Φ hΦ hfree k
        ((run D Φ k).ell + 2) (afterBuild D (run D Φ k))
        hafter.1 hafter.2.1 hafter.2.2.1 hafter.2.2.2 hout
      rw [QueueProof.run_succ]
      refine ⟨fun r m hm_ge hm_lt ↦ heval.1 r m hm_ge (by omega),
        heval.2.1,
        fun β hβ m hm_ge hhor_lt ↦ heval.2.2.1 β hβ m hm_ge (by omega),
        heval.2.2.2.1,
        heval.2.2.2.2⟩

theorem relations_built_correct_proved [Fintype Γ] (rep : DomainRep Γ)
    (D : TempStruct S) (hD : IsAutomatic rep D) (hlt : HasOrderPred D) (Φ : Formula S)
    (hΦ : Bounded Φ) (_huniq : TemporalSubformulasOnce Φ) (hfree : DirectFreeAligned Φ) :
    ∀ (k : ℕ) (α : Formula S) (j : ℕ), (α, j, ([] : List (Formula S))) ∈ (run D Φ k).Q →
      (afterBuild D (run D Φ k)).store (Key.p α) j = some (satSet D α j) ∧
        RegularRel rep (freeList α).length (satSet D α j) := by
  intro k α j hQ
  obtain ⟨hα, hhor⟩ := (QueueProof.mem_run_Q_ready_iff D Φ hΦ k α j).mp hQ
  have hij : (afterBuild D (run D Φ k)).i ≤ j + 1 := by
    rw [afterBuild_i]
    have h := ((QueueProof.run_pending_invariant D Φ k).1 α j [] hQ).1
    omega
  obtain ⟨hbase, hbase_some, hbuilt, hp_some, _⟩ :=
    run_store_invariant rep D hD hlt Φ hΦ hfree k
  have hafter := afterBuild_invariant D Φ hΦ hfree k hbase hbase_some hbuilt hp_some
  have hvalid := hafter.2.2.1 α hα j hij hhor.le
  have hα_bdd := QueueProof.bounded_of_mem_tempSubs Φ hΦ α hα
  have hα_free := directFreeAligned_of_mem_tempSubs Φ hfree α hα
  exact ⟨hvalid.1, regular_satSet rep D hD hlt α hα_bdd hα_free j⟩

theorem evalLoop_i_le (D : TempStruct S) (Φ : Formula S) (fuel : ℕ) (s : State S) :
    s.i ≤ (evalLoop D Φ fuel s).i := by
  induction fuel generalizing s with
  | zero => exact le_rfl
  | succ fuel ih =>
      rw [evalLoop]
      split
      · dsimp only
        let s' : State S :=
          { s with
            out := s.out ++ [(s.i, hatSet (fun r => (s.store (Key.base r) s.i).getD ∅) D.const
              (fun α => (s.store (Key.p α) s.i).getD ∅) Φ.neg, D.τ s.i)]
            store := if 0 < s.i then s.store.discard (s.i - 1) else s.store
            i := s.i + 1 }
        exact (Nat.le_succ s.i).trans (ih s')
      · exact le_rfl

theorem evalLoop_step_of_complete (D : TempStruct S) (Φ : Formula S) (fuel : ℕ)
    (s : State S) (hcomp : Complete Φ s.store s.i) :
    s.i + 1 ≤ (evalLoop D Φ (fuel + 1) s).i := by
  rw [evalLoop, if_pos hcomp]
  dsimp only
  let s' : State S :=
    { s with
      out := s.out ++ [(s.i, hatSet (fun r => (s.store (Key.base r) s.i).getD ∅) D.const
        (fun α => (s.store (Key.p α) s.i).getD ∅) Φ.neg, D.τ s.i)]
      store := if 0 < s.i then s.store.discard (s.i - 1) else s.store
      i := s.i + 1 }
  exact evalLoop_i_le D Φ fuel s'

theorem run_i_mono (D : TempStruct S) (Φ : Formula S) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    (run D Φ k₁).i ≤ (run D Φ k₂).i := by
  induction hk with
  | refl => exact le_rfl
  | step _ ih =>
      rw [QueueProof.run_succ]
      exact ih.trans (evalLoop_i_le D Φ _ (afterBuild D _))

theorem foldr_max_horizon_ge (D : TempStruct S) (L : List (Formula S)) (m : ℕ) :
    ∀ α ∈ L, QueueProof.horizon D α m ≤
      L.foldr (fun α acc ↦ max (QueueProof.horizon D α m) acc) 0 := by
  induction L with
  | nil => intro _ h; cases h
  | cons β L ih =>
      intro α hα
      rcases List.mem_cons.mp hα with rfl | hα
      · exact le_max_left _ _
      · exact (ih α hα).trans (le_max_right _ _)

theorem run_i_eventually [Fintype Γ] (rep : DomainRep Γ) (D : TempStruct S)
    (hD : IsAutomatic rep D) (hlt : HasOrderPred D) (Φ : Formula S)
    (hΦ : Bounded Φ) (hfree : DirectFreeAligned Φ) (m : ℕ) :
    ∃ k : ℕ, m ≤ (run D Φ k).i := by
  induction m with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ m ih =>
      obtain ⟨k₀, hk₀⟩ := ih
      let H := (tempSubs Φ).foldr (fun α acc ↦ max (QueueProof.horizon D α m) acc) 0
      let k := max k₀ (max m H)
      have hk₀_le : k₀ ≤ k := le_max_left _ _
      have hm_le_k : m ≤ k := (le_max_left m H).trans (le_max_right k₀ _)
      have hH_le_k : H ≤ k := (le_max_right m H).trans (le_max_right k₀ _)
      have hm_le_i : m ≤ (run D Φ k).i := hk₀.trans (run_i_mono D Φ hk₀_le)
      by_cases hgt : m + 1 ≤ (run D Φ k).i
      · exact ⟨k, hgt⟩
      · have heq : (run D Φ k).i = m := by omega
        obtain ⟨hbase, hbase_some, hbuilt, hp_some, _⟩ :=
          run_store_invariant rep D hD hlt Φ hΦ hfree k
        have hafter := afterBuild_invariant D Φ hΦ hfree k hbase hbase_some hbuilt hp_some
        let s0 := afterBuild D (run D Φ k)
        have hs0_i : s0.i = m := heq
        have hs0_le : s0.i ≤ m + 1 := by omega
        have hcomp : Complete Φ s0.store s0.i := by
          rw [hs0_i]
          refine ⟨fun r ↦ ?_, fun α hα ↦ ?_⟩
          · rw [hafter.1 r m hs0_le hm_le_k]; rfl
          · have hhor : QueueProof.horizon D α m ≤ k :=
              (foldr_max_horizon_ge D (tempSubs Φ) m α hα).trans hH_le_k
            rw [(hafter.2.2.1 α hα m hs0_le hhor).1]; rfl
        refine ⟨k + 1, ?_⟩
        rw [QueueProof.run_succ]
        have hstep := evalLoop_step_of_complete D Φ ((run D Φ k).ell + 1) s0 hcomp
        rw [hs0_i] at hstep
        exact hstep

theorem theorem_3_9_proved [Fintype Γ] (rep : DomainRep Γ)
    (D : TempStruct S) (hD : IsAutomatic rep D) (hlt : HasOrderPred D) (Φ : Formula S)
    (hΦ : Bounded Φ) (_huniq : TemporalSubformulasOnce Φ) (hfree : DirectFreeAligned Φ) :
    (∀ (k n : ℕ) (O : Set (List ℕ)) (t : ℕ), (n, O, t) ∈ (run D Φ k).out →
        O = satSet D (Formula.neg Φ) n ∧ RegularRel rep (freeList Φ).length O ∧ t = D.τ n) ∧
    (∀ n : ℕ, n = 0 ∨ ∃ (k : ℕ) (O : Set (List ℕ)) (t : ℕ),
      (n - 1, O, t) ∈ (run D Φ k).out) := by
  refine ⟨fun k n O t hmem ↦ (run_store_invariant rep D hD hlt Φ hΦ hfree k).2.2.2.2 n O t hmem,
    fun n ↦ ?_⟩
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    obtain ⟨k, hk⟩ := run_i_eventually rep D hD hlt Φ hΦ hfree n
    obtain ⟨O, t, hout⟩ := QueueProof.run_output_exists_of_lt D Φ k (n - 1) (by omega)
    exact ⟨k, O, t, hout⟩

end MFOTLMon.Monitor

open MFOTLMon.Monitor

theorem solution {S : Signature} {Γ : Type} [Fintype Γ] (rep : DomainRep Γ)
    (D : TempStruct S) (hD : IsAutomatic rep D) (hlt : HasOrderPred D) (Φ : Formula S)
    (hΦ : Bounded Φ) (huniq : TemporalSubformulasOnce Φ) (hfree : DirectFreeAligned Φ) :
    ∀ (k : ℕ) (α : Formula S) (j : ℕ), (α, j, ([] : List (Formula S))) ∈ (run D Φ k).Q →
      (afterBuild D (run D Φ k)).store (Key.p α) j = some (satSet D α j) ∧
        RegularRel rep (freeList α).length (satSet D α j) := by
  exact relations_built_correct_proved rep D hD hlt Φ hΦ huniq hfree
