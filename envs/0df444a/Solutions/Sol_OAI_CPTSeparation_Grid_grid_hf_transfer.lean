-- Prove2me | solution 1 for OAI.CPTSeparation.Grid.grid_hf_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T21:18:54.224996+00:00
-- url     : https://prove2.me/submissions/7d1f10c6-319c-4489-8bad-4bbc4157f5af

import Mathlib
import Definitions.Def_ChoicelessPolynomialTime
import Definitions.Def_OAIQWCPT000
import Theorems.Thm_OAI_CPTSeparation_Projection_card_sq_le_projections

section
-- module Solutions.OAIQW_CPTSeparation.Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Grid

section

variable {n : ℕ}

theorem head_injective_on_axis {e e' : Edge n}
    (ha : edgeAxis e = edgeAxis e') (hh : head e = head e') : e = e' := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals rcases e' with ⟨i',j',k'⟩ | (⟨i',j',k'⟩ | ⟨i',j',k'⟩)
  all_goals simp_all [edgeAxis,head]

theorem tail_injective_on_axis {e e' : Edge n}
    (ha : edgeAxis e = edgeAxis e') (hh : tail e = tail e') : e = e' := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals rcases e' with ⟨i',j',k'⟩ | (⟨i',j',k'⟩ | ⟨i',j',k'⟩)
  all_goals simp_all [edgeAxis,tail]

theorem degree_le_six (v : Vertex n) :
    Fintype.card {e : Edge n // head e = v ∨ tail e = v} ≤ 6 := by
  classical
  let f : {e : Edge n // head e = v ∨ tail e = v} → Fin 3 × Bool :=
    fun e => (edgeAxis e.val, decide (head e.val = v))
  have hf : Function.Injective f := by
    intro e e' heq
    have ha : edgeAxis e.val = edgeAxis e'.val := congrArg Prod.fst heq
    have hb : decide (head e.val = v) = decide (head e'.val = v) := congrArg Prod.snd heq
    apply Subtype.ext
    by_cases he : head e.val = v
    · have he' : head e'.val = v := by simpa only [he,decide_true,true_eq_decide_iff] using hb
      exact head_injective_on_axis ha (he.trans he'.symm)
    · have he' : head e'.val ≠ v := by simpa only [he,decide_false,false_eq_decide_iff] using hb
      exact tail_injective_on_axis ha
        ((e.property.resolve_left he).trans (e'.property.resolve_left he').symm)
  have h := Fintype.card_le_of_injective f hf
  simpa using h

end

open Classical Support

variable {n : ℕ} {b b' b'' : Vertex n → Scalar}

theorem AtomShift.functional {t : Edge n → Scalar} {x : Atom b} {y z : Atom b'}
    (hy : AtomShift t x y) (hz : AtomShift t x z) : y = z := by
  cases hy <;> cases hz <;> rfl

theorem AtomShift.equal_iff {t : Edge n → Scalar} {x x' : Atom b} {y y' : Atom b'}
    (h : AtomShift t x y) (h' : AtomShift t x' y') : x = x' ↔ y = y' := by
  constructor
  · intro he; subst x'; exact h.functional h'
  · intro he; subst y'; exact h.symm.functional h'.symm

theorem AtomShift.relation {t : Edge n → Scalar} {r : Symbol}
    {x x' : Atom b} {y y' : Atom b'} (h : AtomShift t x y) (h' : AtomShift t x' y')
    (hr : AtomRelation b r x x') : AtomRelation b' r y y' := by
  cases hr with
  | ed e s => cases h; cases h'; exact .ed _ _
  | cf v s => cases h; cases h'; exact .cf _ _
  | eb e s a => cases h; cases h'; exact .eb _ _ _
  | vb v s a => cases h; cases h'; exact .vb _ _ _
  | inc v s e => cases h; cases h'; exact .inc _ _ e
  | z e s a δ hz =>
    cases h; cases h'
    apply AtomRelation.z
    simpa only [shiftLocal,mul_inv_rev,mul_assoc,inv_mul_cancel_left] using hz

theorem AtomShift.relation_iff {t : Edge n → Scalar} {r : Symbol}
    {x x' : Atom b} {y y' : Atom b'} (h : AtomShift t x y) (h' : AtomShift t x' y') :
    AtomRelation b r x x' ↔ AtomRelation b' r y y' :=
  ⟨fun hr => h.relation h' hr,fun hr => h.symm.relation h'.symm hr⟩

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Counting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Counting

section

variable {R I A B : Type*}

namespace Formula

variable [DecidableEq I]

theorem free_conjoin_subset (l : List (Formula R I)) (S : Finset I)
    (h : ∀ φ ∈ l, φ.free ⊆ S) : (conjoin l).free ⊆ S := by
  induction l with
  | nil => simp [conjoin,free]
  | cons φ l ih =>
    exact Finset.union_subset (h φ (by simp)) (ih (fun ψ hψ => h ψ (by simp [hψ])))

end Formula

variable [DecidableEq I]

theorem type_separator (S : Structure R A) (T : Structure R B) (names : Finset I)
    (v : I → A) (w : I → B) (hne : typeOf S names v ≠ typeOf T names w) :
    ∃ φ : Formula R I, φ.free ⊆ names ∧ φ.eval S v ∧ ¬ φ.eval T w := by
  classical
  have h : ¬ ∀ φ : Formula R I, φ.free ⊆ names → (φ.eval S v ↔ φ.eval T w) :=
    fun heq => hne ((typeOf_eq_iff S T names v w).mpr heq)
  push Not at h
  obtain ⟨φ,hφ,hdiff⟩ := h
  by_cases hv : φ.eval S v
  · exact ⟨φ,hφ,hv,by tauto⟩
  · have hw : φ.eval T w := by tauto
    exact ⟨.neg φ,hφ,hv,fun hn => hn hw⟩

theorem isolate_type [Fintype I] [Fintype A] [Fintype B]
    (S : Structure R A) (T : Structure R B) (names : Finset I) (v₀ : I → A) :
    ∃ θ : Formula R I, θ.free ⊆ names ∧
      (∀ v, θ.eval S v ↔ typeOf S names v = typeOf S names v₀) ∧
      (∀ w, θ.eval T w ↔ typeOf T names w = typeOf S names v₀) := by
  classical
  let Z := (I → A) ⊕ (I → B)
  let ev : Z → Formula R I → Prop := fun z φ => z.elim (φ.eval S) (φ.eval T)
  let tp : Z → Set (Formula R I) := fun z =>
    z.elim (typeOf S names) (typeOf T names)
  have heq (z : Z) (φ : Formula R I) (hφ : φ.free ⊆ names)
      (h : tp z = typeOf S names v₀) : ev z φ ↔ φ.eval S v₀ := by
    cases z with
    | inl v => exact (typeOf_eq_iff S S names v v₀).mp h φ hφ
    | inr w => exact (typeOf_eq_iff T S names w v₀).mp h φ hφ
  have hcut : ∀ z : Z, ∃ φ : Formula R I,
      φ.free ⊆ names ∧ φ.eval S v₀ ∧ (ev z φ → tp z = typeOf S names v₀) := by
    intro z
    by_cases h : tp z = typeOf S names v₀
    · exact ⟨.neg .falsum,Finset.empty_subset _,not_false,fun _ => h⟩
    · have hs : ∃ φ : Formula R I, φ.free ⊆ names ∧ φ.eval S v₀ ∧ ¬ ev z φ := by
        cases z with
        | inl v => exact type_separator S S names v₀ v (Ne.symm h)
        | inr w => exact type_separator S T names v₀ w (Ne.symm h)
      obtain ⟨φ,hφ,hv,hw⟩ := hs
      exact ⟨φ,hφ,hv,fun h' => (hw h').elim⟩
  choose cut hfree htrue hcut using hcut
  let l := (Finset.univ : Finset Z).toList.map cut
  let θ := Formula.conjoin l
  have hf : θ.free ⊆ names := by
    apply Formula.free_conjoin_subset
    intro φ hφ
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hφ
    exact hfree z
  have hall (z : Z) : ev z θ ↔ tp z = typeOf S names v₀ := by
    have hc : ev z θ ↔ ∀ φ ∈ l, ev z φ := by
      cases z with
      | inl v => exact Formula.eval_conjoin S l v
      | inr w => exact Formula.eval_conjoin T l w
    rw [hc]
    constructor
    · intro h
      exact hcut z (h (cut z) (List.mem_map.mpr ⟨z,Finset.mem_toList.mpr (Finset.mem_univ z),rfl⟩))
    · intro h φ hφ
      obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hφ
      exact (heq z (cut z') (hfree z') h).mpr (htrue z')
  exact ⟨θ,hf,fun v => hall (.inl v),fun w => hall (.inr w)⟩

theorem extension_equiv [Fintype I] [Fintype A] [Fintype B]
    (S : Structure R A) (T : Structure R B) (names : Finset I) (i : I)
    (_ : i ∉ names) (v v₀ : I → A) (w : I → B)
    (htype : typeOf S names v = typeOf T names w) :
    Nonempty ({a : A // typeOf S (insert i names) (Function.update v i a) =
          typeOf S (insert i names) v₀} ≃
        {b : B // typeOf T (insert i names) (Function.update w i b) =
          typeOf S (insert i names) v₀}) := by
  classical
  obtain ⟨θ,hfree,hS,hT⟩ := isolate_type S T (insert i names) v₀
  let X := {a : A // θ.eval S (Function.update v i a)}
  let Y := {b : B // θ.eval T (Function.update w i b)}
  let : Fintype X := Fintype.ofFinite X
  let n := Fintype.card X
  have hf : (Formula.exact i n θ).free ⊆ names := by
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    have hmem := hfree (Finset.mem_erase.mp hj).2
    exact (Finset.mem_insert.mp hmem).resolve_left hji
  have hn : (Formula.exact i n θ).eval S v := ⟨Fintype.equivFin X⟩
  have hn' := (typeOf_eq_iff S T names v w).mp htype (.exact i n θ) hf |>.mp hn
  obtain ⟨e⟩ := hn'
  let eS := Equiv.subtypeEquivRight (fun a => hS (Function.update v i a))
  let eT := Equiv.subtypeEquivRight (fun b => hT (Function.update w i b))
  exact ⟨eS.symm.trans ((Fintype.equivFin X).trans (e.symm.trans eT))⟩

end

variable {R I A B : Type*} [decidableI : DecidableEq I]

theorem typeOf_project (S : Structure R A) (T : Structure R B)
    {names small : Finset I} (hsub : small ⊆ names) {v : I → A} {w : I → B}
    (h : typeOf S names v = typeOf T names w) :
    typeOf S small v = typeOf T small w := by
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hf
  exact (typeOf_eq_iff _ _ _ _ _).mp h φ (hf.trans hsub)

theorem typeOf_permute (S : Structure R A) (T : Structure R B)
    (names : Finset I) (e : I ≃ I) {v : I → A} {w : I → B}
    (h : typeOf S names v = typeOf T names w) :
    typeOf S (names.map e.symm.toEmbedding) (v ∘ e) =
      typeOf T (names.map e.symm.toEmbedding) (w ∘ e) := by
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hf
  have hf' : (φ.rename e).free ⊆ names := by
    rw [Formula.free_rename]
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨k,hk,hkj⟩ := Finset.mem_map.mp (hf hj)
    simpa only [Equiv.toEmbedding_apply,← hkj,Equiv.apply_symm_apply] using hk
  simpa using (typeOf_eq_iff _ _ _ _ _).mp h (φ.rename e) hf'

theorem extension_bijection [Fintype I] [Fintype A] [Fintype B]
    (S : Structure R A) (T : Structure R B) (names : Finset I) (i : I)
    (hi : i ∉ names) (v : I → A) (w : I → B)
    (h : typeOf S names v = typeOf T names w) :
    ∃ e : A ≃ B, ∀ a, typeOf S (insert i names) (Function.update v i a) =
      typeOf T (insert i names) (Function.update w i (e a)) := by
  classical
  let f : A → Set (Formula R I) := fun a =>
    typeOf S (insert i names) (Function.update v i a)
  let g : B → Set (Formula R I) := fun b =>
    typeOf T (insert i names) (Function.update w i b)
  have he : ∀ ρ, Nonempty ({a // f a = ρ} ≃ {b // g b = ρ}) := by
    intro ρ
    by_cases ha : ∃ a, f a = ρ
    · obtain ⟨a,rfl⟩ := ha
      exact extension_equiv S T names i hi v (Function.update v i a) w h
    · by_cases hb : ∃ b, g b = ρ
      · obtain ⟨b,rfl⟩ := hb
        obtain ⟨e⟩ := extension_equiv T S names i hi w (Function.update w i b) v h.symm
        exact False.elim (ha ⟨(e ⟨b,rfl⟩).1,(e ⟨b,rfl⟩).2⟩)
      · let : IsEmpty {a // f a = ρ} := ⟨fun a => ha ⟨a.1,a.2⟩⟩
        let : IsEmpty {b // g b = ρ} := ⟨fun b => hb ⟨b.1,b.2⟩⟩
        exact ⟨Equiv.equivOfIsEmpty _ _⟩
  let e := Equiv.ofFiberEquiv (fun ρ => Classical.choice (he ρ))
  refine ⟨e,fun a => ?_⟩
  change f a = g (e a)
  exact (Equiv.ofFiberEquiv_map (fun ρ => Classical.choice (he ρ)) a).symm

theorem extend_type [Fintype I] [Fintype A] [Fintype B]
    (S : Structure R A) (T : Structure R B) (names extra : Finset I)
    (v : I → A) (w : I → B) (h : typeOf S names v = typeOf T names w) :
    ∃ w' : I → B, typeOf S (names ∪ extra) v = typeOf T (names ∪ extra) w' ∧
      ∀ i ∈ names, w' i = w i := by
  classical
  induction extra using Finset.induction_on with
  | empty => exact ⟨w,by simpa using h,fun _ _ => rfl⟩
  | @insert i extra hi ih =>
    obtain ⟨w',ht,hw⟩ := ih
    by_cases hin : i ∈ names ∪ extra
    · have heq : names ∪ insert i extra = names ∪ extra := by
        rw [Finset.union_insert,Finset.insert_eq_of_mem hin]
      exact ⟨w',heq ▸ ht,hw⟩
    · obtain ⟨e,he⟩ := extension_bijection S T (names ∪ extra) i hin v w' ht
      refine ⟨Function.update w' i (e (v i)),?_,?_⟩
      · have ht' := he (v i)
        have heq : names ∪ insert i extra = insert i (names ∪ extra) := by
          ext j; simp only [Finset.mem_union,Finset.mem_insert]; tauto
        simpa only [heq,Function.update_eq_self] using ht'
      · intro j hj
        have hji : j ≠ i := by
          intro heq
          apply hin
          rw [←heq]
          exact Finset.mem_union_left extra hj
        rw [Function.update_of_ne hji]
        exact hw j hj

section Tuple

variable {J J' : Type*} [Fintype J] [Fintype J']

theorem tupleType_project [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ↪ I) (e' : J' ↪ I)
    (u : J' ↪ J) (a : J → A) (b : J → B)
    (h : tupleType S e a = tupleType T e b) :
    tupleType S e' (a ∘ u) = tupleType T e' (b ∘ u) := by
  classical
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair e' (fun j => e (u j))
    e'.injective (e.injective.comp u.injective)
  have hm : (tupleNames (u.trans e)).map σ.symm.toEmbedding = tupleNames e' := by
    ext i
    simp only [Finset.mem_map,Equiv.toEmbedding_apply,mem_tupleNames]
    constructor
    · rintro ⟨k,⟨j,rfl⟩,rfl⟩
      exact ⟨j,by simp only [Function.Embedding.trans_apply,← hσ j,σ.symm_apply_apply]⟩
    · rintro ⟨j,rfl⟩
      refine ⟨e (u j),⟨j,rfl⟩,?_⟩
      rw [← hσ j,σ.symm_apply_apply]
  have hs : tupleNames (u.trans e) ⊆ tupleNames e := by
    intro i hi
    obtain ⟨j,rfl⟩ := (mem_tupleNames _ _).mp hi
    exact (mem_tupleNames _ _).mpr ⟨u j,rfl⟩
  have hp := typeOf_project S T hs h
  have ht := typeOf_permute S T (tupleNames (u.trans e)) σ hp
  rw [hm] at ht
  rw [tupleType_assignment S e' (a ∘ u) (tupleAssignment e a ∘ σ)
    (fun j => by simp [hσ]),
    tupleType_assignment T e' (b ∘ u) (tupleAssignment e b ∘ σ)
    (fun j => by simp [hσ])]
  exact ht

theorem tupleType_extend [Fintype I] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ↪ I) (e' : J' ↪ I)
    (u : J ↪ J') (a : J' → A) (b : J → B)
    (h : tupleType S e (a ∘ u) = tupleType T e b) :
    ∃ b' : J' → B, b' ∘ u = b ∧ tupleType S e' a = tupleType T e' b' := by
  classical
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair e (fun j => e' (u j))
    e.injective (e'.injective.comp u.injective)
  let v := tupleAssignment e' a
  let w := tupleAssignment e b ∘ σ.symm
  have hw (j : J) : w (e' (u j)) = b j := by
    simp [w,Function.comp_def,←hσ j]
  have hn : (tupleNames e).map σ.toEmbedding = tupleNames (u.trans e') := by
    ext i
    simp only [Finset.mem_map,Equiv.toEmbedding_apply,mem_tupleNames]
    constructor
    · rintro ⟨k,⟨j,rfl⟩,rfl⟩
      exact ⟨j,(hσ j).symm⟩
    · rintro ⟨j,rfl⟩
      exact ⟨e j,⟨j,rfl⟩,hσ j⟩
  have ht := typeOf_permute S T (tupleNames e) σ.symm h
  simp only [Equiv.symm_symm,hn] at ht
  have hv : typeOf S (tupleNames (u.trans e')) v =
      typeOf S (tupleNames (u.trans e')) (tupleAssignment e (a ∘ u) ∘ σ.symm) := by
    apply typeOf_congr
    intro i hi
    obtain ⟨j,rfl⟩ := (mem_tupleNames _ _).mp hi
    change tupleAssignment e' a (e' (u j)) =
      tupleAssignment e (a ∘ u) (σ.symm (e' (u j)))
    rw [tupleAssignment_apply,← hσ j,σ.symm_apply_apply,tupleAssignment_apply]
    rfl
  obtain ⟨w',ht',hp⟩ := extend_type S T (tupleNames (u.trans e')) (tupleNames e')
    v w (hv.trans ht)
  have hs : tupleNames (u.trans e') ⊆ tupleNames e' := by
    intro i hi
    obtain ⟨j,rfl⟩ := (mem_tupleNames _ _).mp hi
    exact (mem_tupleNames _ _).mpr ⟨u j,rfl⟩
  rw [Finset.union_eq_right.mpr hs] at ht'
  refine ⟨fun j => w' (e' j),?_,?_⟩
  · funext j
    rw [Function.comp_apply,hp (e' (u j)) ((mem_tupleNames _ _).mpr ⟨j,rfl⟩),hw]
  · rw [tupleType_assignment T e' _ w' (fun _ => rfl)]
    exact ht'

end Tuple

section Append

variable {J D : Type*} [Fintype J] [Fintype D] [Fintype I]

variable [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

theorem tupleType_append (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (e' : J ⊕ D ↪ I) (a : J → A) (b : J → B) (c : D → A)
    (h : tupleType S e a = tupleType T e b) :
    ∃ d : D → B, tupleType S e' (Sum.elim a c) = tupleType T e' (Sum.elim b d) := by
  obtain ⟨b',hb',ht⟩ := tupleType_extend S T e e' (Function.Embedding.inl)
    (Sum.elim a c) b h
  refine ⟨b' ∘ Sum.inr,?_⟩
  have heq : b' = Sum.elim b (b' ∘ Sum.inr) := by
    funext j
    cases j with
    | inl j => exact congrFun hb' j
    | inr j => rfl
  rw [heq] at ht
  exact ht

end Append

end CPTSeparation.Counting

namespace CPTSeparation.Grid

section

open Classical Finset

variable {n : ℕ} {b b' : Vertex n → Scalar}

theorem AtomShift.classLabel {t : Edge n → Scalar} {x : Atom b} {y : Atom b'}
    (h : AtomShift t x y) : Grid.classLabel x = Grid.classLabel y := by
  cases h <;> simp [Grid.classLabel]

theorem AtomShift.analysisRelation {t : Edge n → Scalar} {x x' : Atom b} {y y' : Atom b'}
    (h : AtomShift t x y) (h' : AtomShift t x' y') (r : AnalysisSymbol) :
    (analysisStructure b).rel r x x' ↔ (analysisStructure b').rel r y y' := by
  cases r with
  | input r => exact h.relation_iff h'
  | preorder => change classIndex x ≤ classIndex x' ↔ classIndex y ≤ classIndex y'
                simp only [classIndex,h.classLabel,h'.classLabel]
  | raw d =>
    change rawDifference b d x x' ↔ rawDifference b' d y y'
    cases h <;> cases h' <;> simp only [rawDifference,shiftLocal_flow]
    rename_i e s f a
    constructor
    · rintro ⟨rfl,he⟩; exact ⟨rfl,by linear_combination he⟩
    · rintro ⟨rfl,he⟩; exact ⟨rfl,by linear_combination he⟩

theorem predecessors_recovers_class {x y : Atom b}
    (h : (predecessors x).card = (predecessors y).card) : classLabel x = classLabel y := by
  have hlt {x y : Atom b} (hxy : classIndex x < classIndex y) :
      (predecessors x).card < (predecessors y).card := by
    apply card_lt_card
    apply ssubset_iff_subset_ne.mpr
    refine ⟨?_,?_⟩
    · intro z hz; exact mem_filter.mpr ⟨mem_univ _,lt_trans (mem_filter.mp hz).2 hxy⟩
    · intro he
      have hx : x ∈ predecessors y := mem_filter.mpr ⟨mem_univ _,hxy⟩
      rw [←he] at hx
      exact (lt_irrefl _) (mem_filter.mp hx).2
  have hi : classIndex x = classIndex y := by
    rcases lt_trichotomy (classIndex x) (classIndex y) with hh | hh | hh
    · exact False.elim ((ne_of_lt (hlt hh)) h)
    · exact hh
    · exact False.elim ((ne_of_lt (hlt hh)) h.symm)
  exact (Fintype.equivFin (ClassLabel n)).injective hi

theorem free_classFormula {I : Type*} [DecidableEq I] (i j : I) (h : ℕ) :
    (classFormula i j h).free ⊆ {i} := by
  simp only [classFormula,Counting.Formula.free]
  intro k hk
  simp only [mem_erase,mem_union,mem_insert,mem_singleton] at hk ⊢
  tauto

theorem eval_classFormula {I : Type*} [DecidableEq I] (v : I → Atom b) {i j : I}
    (hne : i ≠ j) (h : ℕ) :
    (classFormula i j h).eval (analysisStructure b) v ↔ (predecessors (v i)).card = h := by
  have hh (x : Atom b) :
      ((analysisStructure b).rel .preorder (Function.update v j x j) (Function.update v j x i) ∧
      ¬(analysisStructure b).rel .preorder (Function.update v j x i) (Function.update v j x j)) ↔
      x ∈ predecessors (v i) := by
    simp only [analysisStructure,Function.update_self,Function.update_of_ne hne,
      predecessors,mem_filter,mem_univ,true_and,lt_iff_le_not_ge]
  change Nonempty (_ ≃ Fin h) ↔ _
  let e := Equiv.subtypeEquivRight hh
  constructor
  · rintro ⟨f⟩
    simpa using Fintype.card_congr (e.symm.trans f)
  · intro he
    exact ⟨e.trans ((Fintype.equivFin _).trans (finCongr (by simpa using he)))⟩

theorem type_recovers_classes {I : Type*} [DecidableEq I] (names : Finset I)
    {v w : I → Atom b} (ht : Counting.typeOf (analysisStructure b) names v =
      Counting.typeOf (analysisStructure b) names w) {i j : I} (hi : i ∈ names) (hne : i ≠ j) :
    classLabel (v i) = classLabel (w i) := by
  apply predecessors_recovers_class
  let h := (predecessors (v i)).card
  have hf : (classFormula i j h).free ⊆ names :=
    (free_classFormula i j h).trans (singleton_subset_iff.mpr hi)
  have he := (Counting.typeOf_eq_iff _ _ _ _ _).mp ht (classFormula i j h) hf
  exact ((eval_classFormula w hne h).mp (he.mp ((eval_classFormula v hne h).mpr rfl))).symm

theorem blockEdges_card (J : Block n) : (blockEdges J).card ≤ 6 := by
  cases J with
  | inl e => simp [blockEdges]
  | inr v =>
    have hh : (blockEdges (.inr v)).card = Fintype.card {e : Edge n // head e = v ∨ tail e = v} := by
      rw [←Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun e => by simp [blockEdges,incident]))
    rw [hh]
    exact degree_le_six v

theorem touch_card (x : Atom b) : (touch x).card ≤ 6 := blockEdges_card (atomBlock x)

theorem AtomShift.congr {t t' : Edge n → Scalar} {x : Atom b} {y : Atom b'}
    (h : AtomShift t x y) (he : ∀ e ∈ touch x, t e = t' e) : AtomShift t' x y := by
  cases h with
  | edge e s =>
    have hh := he e (by simp [touch,atomBlock,blockEdges])
    simpa only [hh] using (AtomShift.edge (b := b) (b' := b') (t := t') e s)
  | config v s h =>
    have hv : boundary t' v = b' v-b v := by
      rw [←sum_incident,←h,←sum_incident]
      apply sum_congr rfl
      intro e _
      rw [he e.val (by simpa [touch,atomBlock,blockEdges] using e.property)]
    have hs : s.shift t h = s.shift t' hv := by
      apply Configuration.ext
      intro e
      simp only [Configuration.shift_state,he e.val (by simpa [touch,atomBlock,blockEdges] using e.property)]
    rw [hs]
    exact .config v s hv

theorem touches_card {I : Type*} [DecidableEq I] (names : Finset I) (v : I → Atom b) :
    (touches names v).card ≤ 6*names.card := by
  calc
    _ ≤ ∑ i ∈ names, (touch (v i)).card := card_biUnion_le
    _ ≤ ∑ _ ∈ names, 6 := sum_le_sum (fun i _ => touch_card (v i))
    _ = 6*names.card := by simp [Nat.mul_comm]

theorem touch_subset_touches {I : Type*} [DecidableEq I] (names : Finset I)
    (v : I → Atom b) {i : I} (hi : i ∈ names) : touch (v i) ⊆ touches names v := by
  intro e he; exact mem_biUnion.mpr ⟨i,hi,he⟩

theorem touches_mono {I : Type*} [DecidableEq I] {s t : Finset I} (hst : s ⊆ t)
    (v : I → Atom b) : touches s v ⊆ touches t v := by
  intro e he
  obtain ⟨i,hi,he⟩ := mem_biUnion.mp he
  exact mem_biUnion.mpr ⟨i,hst hi,he⟩

theorem touches_insert_update {I : Type*} [DecidableEq I] (names : Finset I)
    (v : I → Atom b) (i : I) (a : Atom b) :
    touches (insert i (names.erase i)) (Function.update v i a) =
      touches (names.erase i) v ∪ touch a := by
  ext e
  simp only [touches,mem_biUnion,mem_insert,mem_erase,mem_union]
  constructor
  · rintro ⟨j,(rfl | hj),he⟩
    · exact Or.inr (by simpa using he)
    · exact Or.inl ⟨j,hj,by simpa [Function.update_of_ne hj.1] using he⟩
  · rintro (⟨j,hj,he⟩ | he)
    · exact ⟨j,Or.inr hj,by simpa [Function.update_of_ne hj.1] using he⟩
    · exact ⟨i,Or.inl rfl,by simpa using he⟩

end

section

open Classical Finset

variable {n : ℕ} {b : Vertex n → Scalar}

theorem hasState_stateAt (x : Atom b) (e : Edge n) (he : e ∈ touch x) :
    HasState x e (stateAt x e he) := by
  cases x with
  | inl x =>
    rcases x with ⟨f,s⟩
    have hh : e = f := by simpa [touch,atomBlock,blockEdges] using he
    subst e
    simp
  | inr x =>
    rcases x with ⟨v,s⟩
    exact (hasState_config _ _ _ _).mpr ⟨by simpa [touch,atomBlock,blockEdges] using he,rfl⟩

theorem classLabel_edge_iff (y : Atom b) (e : Edge n) (u : EdgeFaces e → Support.Plane) :
    classLabel y = .inl ⟨e,u⟩ ↔ ∃ t : LocalGroup e, y = .inl ⟨e,t⟩ ∧ t.face = u := by
  cases y with
  | inl y =>
    rcases y with ⟨f,s⟩
    constructor
    · intro h
      have hh := Sum.inl.inj h
      have hf := congrArg Sigma.fst hh
      dsimp at hf
      subst f
      have hu := (Sigma.mk.inj_iff.mp hh).2
      exact ⟨s,rfl,eq_of_heq hu⟩
    · rintro ⟨t,h,rfl⟩; cases h; rfl
  | inr y => simp [classLabel]

theorem atomShift_of_states (x y : Atom b) (t : Edge n → Scalar)
    (hc : classLabel x = classLabel y)
    (hs : ∀ e (he : e ∈ touch x), HasState y e (shiftLocal e (t e) (stateAt x e he))) :
    AtomShift t x y := by
  cases x with
  | inl x =>
    rcases x with ⟨e,s⟩
    obtain ⟨s',rfl,hface⟩ := (classLabel_edge_iff y e s.face).mp hc.symm
    have h := hs e (by simp [touch,atomBlock,blockEdges])
    simp only [hasState_edge] at h
    have hh : s' = shiftLocal e (t e) s := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    subst s'
    exact .edge e s
  | inr x =>
    rcases x with ⟨v,s⟩
    cases y with
    | inl y => cases hc
    | inr y =>
      rcases y with ⟨w,s'⟩
      have hw := congrArg Sigma.fst (Sum.inr.inj hc)
      dsimp at hw
      subst w
      have hstates : s'.state = shiftStates t s.state := by
        funext e
        have he : e.val ∈ touch (.inr ⟨v,s⟩) := by simpa [touch,atomBlock,blockEdges] using e.property
        obtain ⟨h,hval⟩ := (hasState_config _ _ _ _).mp (hs e.val he)
        exact hval
      have hb : boundary t v = b v-b v := by
        have h := s'.charge
        rw [hstates,shiftStates_divergence,s.charge] at h
        linear_combination h
      have hy : s' = s.shift t hb := by
        apply Configuration.ext
        intro e
        exact congrFun hstates e
      rw [hy]
      exact .config v s hb

theorem augmented_diagram_shift {J : Type*} (a a' : J → Atom b)
    (y : Occurrences a → Atom b) (h : SameDiagram (Augment a) (Sum.elim a' y)) :
    ∃ t : Edge n → Scalar, ∀ j, AtomShift t (a j) (a' j) := by
  have hy (o : Occurrences a) : ∃ s : LocalGroup o.2.val,
      y o = .inl ⟨o.2.val,s⟩ ∧ s.face = (stateAt (a o.1) o.2.val o.2.property).face :=
    (classLabel_edge_iff _ _ _).mp (h.classes (.inr o)).symm
  choose target htarget hface using hy
  let delta (o : Occurrences a) : Scalar :=
    (target o).flow-(stateAt (a o.1) o.2.val o.2.property).flow
  have hd (o p : Occurrences a) (he : o.2.val = p.2.val) : delta o = delta p := by
    have hh := (h.relation (.raw
      ((stateAt (a p.1) p.2.val p.2.property).flow -
        (stateAt (a o.1) o.2.val o.2.property).flow)) (.inr o) (.inr p)).mp
      (show (analysisStructure b).rel _ (Augment a (.inr o)) (Augment a (.inr p)) from ⟨he,rfl⟩)
    change rawDifference b _ (y o) (y p) at hh
    rw [htarget o,htarget p] at hh
    have hh' := hh.2
    dsimp [delta]
    linear_combination -hh'
  let t (e : Edge n) : Scalar := if he : ∃ o : Occurrences a, o.2.val = e
    then delta he.choose else 0
  have ht (o : Occurrences a) : t o.2.val = delta o := by
    have he : ∃ p : Occurrences a, p.2.val = o.2.val := ⟨o,rfl⟩
    simp only [t,dite_eq_left he]
    exact hd he.choose o he.choose_spec
  have heq (o : Occurrences a) :
      target o = shiftLocal o.2.val (t o.2.val) (stateAt (a o.1) o.2.val o.2.property) := by
    apply Support.H.ext
    · simpa only [shiftLocal_face] using hface o
    · simp only [shiftLocal_flow,ht,delta]; abel
  refine ⟨t,fun j => atomShift_of_states _ _ _ (h.classes (.inl j)) ?_⟩
  intro e he
  let o : Occurrences a := ⟨j,e,he⟩
  have hs := hasState_stateAt (a j) e he
  have hh : a' j = y o ∨ AtomRelation b .I (a' j) (y o) :=
    hs.elim (fun hh => Or.inl ((h.equal (.inl j) (.inr o)).mp hh))
      (fun hh => Or.inr ((h.relation (.input .I) (.inl j) (.inr o)).mp hh))
  rw [htarget o,heq o] at hh
  exact hh

end

section

open Classical Finset

variable {n : ℕ} {b : Vertex n → Scalar}

variable {J I : Type*} [Fintype J] [finiteI : Fintype I] [DecidableEq I] [Nonempty (Atom b)]

omit n b J I in
theorem sameDiagram_of_type.{uDecl1, uDecl2}
    {n : ℕ}
    {b : Grid.Vertex n → Grid.Scalar}
    {J : Type uDecl1}
    {I : Type uDecl2}
    [Fintype J]
    [Fintype I]
    [DecidableEq I]
    [Nonempty (Grid.Atom b)] (names : J ↪ I) (a a' : J → Atom b)
    (ht : Counting.tupleType (analysisStructure b) names a =
      Counting.tupleType (analysisStructure b) names a')
    (spare : I) (hsp : spare ∉ Counting.tupleNames names) : SameDiagram a a' := by
  have hmem (j : J) : names j ∈ Counting.tupleNames names := by simp
  refine ⟨?_,?_,?_⟩
  · intro j
    have hn : names j ≠ spare := by intro h; exact hsp (h ▸ hmem j)
    have hh := type_recovers_classes (Counting.tupleNames names) ht (hmem j) hn
    simpa only [Counting.tupleAssignment_apply] using hh
  · intro i j
    have hh := (Counting.typeOf_eq_iff _ _ _ _ _).mp ht
      (.equal (names i) (names j)) (by change ({names i,names j} : Finset I) ⊆ Counting.tupleNames names; exact insert_subset_iff.mpr ⟨hmem i,singleton_subset_iff.mpr (hmem j)⟩)
    simpa only [Counting.Formula.eval,Counting.tupleAssignment_apply] using hh
  · intro r i j
    have hh := (Counting.typeOf_eq_iff _ _ _ _ _).mp ht
      (.relation r (names i) (names j)) (by change ({names i,names j} : Finset I) ⊆ Counting.tupleNames names; exact insert_subset_iff.mpr ⟨hmem i,singleton_subset_iff.mpr (hmem j)⟩)
    simpa only [Counting.Formula.eval,Counting.tupleAssignment_apply] using hh

end

open Classical Finset

variable {n : ℕ} {b : Vertex n → Scalar}

variable {J : Type*} [Fintype J]

theorem occurrences_card (a : J → Atom b) : Fintype.card (Occurrences a) ≤ 6*Fintype.card J := by
  rw [Fintype.card_sigma]
  calc
    _ = ∑ j : J, (touch (a j)).card := by congr 1; ext j; exact Fintype.card_coe _
    _ ≤ ∑ _ : J, 6 := sum_le_sum (fun j _ => touch_card (a j))
    _ = _ := by simp [Nat.mul_comm]

theorem augment_card (a : J → Atom b) : Fintype.card (J ⊕ Occurrences a) ≤ 7*Fintype.card J := by
  rw [Fintype.card_sum]
  have := occurrences_card a
  omega

theorem namesBelow_spare {P : Type*} [Fintype P] {M : ℕ} (h : Fintype.card P < M) :
    (⟨Fintype.card P,h⟩ : Fin M) ∉ Counting.tupleNames (namesBelow h) := by
  intro hh
  obtain ⟨j,hj⟩ := (Counting.mem_tupleNames _ _).mp hh
  have hv := congrArg Fin.val hj
  change (Fintype.equivFin P j).val = Fintype.card P at hv
  exact (Fintype.equivFin P j).isLt.ne hv

theorem tuple_partial_shift {M : ℕ} [Nonempty (Atom b)] (names : J ↪ Fin M)
    (a a' : J → Atom b) (hw : 7*Fintype.card J < M)
    (ht : Counting.tupleType (analysisStructure b) names a =
      Counting.tupleType (analysisStructure b) names a') :
    ∃ t : Edge n → Scalar, ∀ j, AtomShift t (a j) (a' j) := by
  have hcard : Fintype.card (J ⊕ Occurrences a) < M := lt_of_le_of_lt (augment_card a) hw
  obtain ⟨y,hy⟩ := Counting.tupleType_append (analysisStructure b) (analysisStructure b)
    names (namesBelow hcard) a a' (occurrenceAtom a) ht
  exact augmented_diagram_shift a a' y
    (sameDiagram_of_type _ _ _ hy ⟨_,hcard⟩ (namesBelow_spare hcard))

theorem AtomShift.stateAt_flow {t : Edge n → Scalar} {x y : Atom b}
    (h : AtomShift t x y) (e : Edge n) (he : e ∈ touch x) :
    (stateAt y e (by rw [←touch_shift h]; exact he)).flow =
      t e + (stateAt x e he).flow := by
  cases h with
  | edge f s =>
    have hef : e = f := by simpa [touch,atomBlock,blockEdges] using he
    subst e
    simp only [stateAt_edge (b := b),shiftLocal_flow]
  | config v s h =>
    have hi : incident v e := by simpa [touch,atomBlock,blockEdges] using he
    change ((s.shift t h).state ⟨e,hi⟩).flow = t e + (s.state ⟨e,hi⟩).flow
    simp

theorem AtomShift.unique_on_touch {t u : Edge n → Scalar} {x y : Atom b}
    (ht : AtomShift t x y) (hu : AtomShift u x y) (e : Edge n) (he : e ∈ touch x) :
    t e = u e := by
  have hh := (ht.stateAt_flow e he).symm.trans (hu.stateAt_flow e he)
  exact add_right_cancel hh

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Flows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.BoxLines

open Finset

variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

private theorem fin_constant {P : Fin (n+1) → Prop}
    (h : ∀ i : Fin n, P i.castSucc ↔ P i.succ) (i : Fin (n+1)) : P i ↔ P 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact (h i).symm.trans ih

theorem partial_line_boundary (R : Finset (Fin (n+1) × J)) {j : J}
    (hj : j ∈ projection R \ fullLines R) :
    ∃ i : Fin n, (i,j) ∈ edgeBoundary R := by
  classical
  by_contra hn
  have h : ∀ i : Fin n, (i.castSucc,j) ∈ R ↔ (i.succ,j) ∈ R := by
    intro i
    by_contra hh
    exact hn ⟨i,by simp [edgeBoundary,hh]⟩
  obtain ⟨hj,hf⟩ := mem_sdiff.mp hj
  obtain ⟨⟨i,j'⟩,hi,he⟩ := mem_image.mp hj
  dsimp at he
  subst j'
  have hzero := (fin_constant (P := fun i => (i,j) ∈ R) h i).mp hi
  apply hf
  simp only [fullLines,mem_filter,mem_univ,true_and]
  intro i
  exact (fin_constant (P := fun i => (i,j) ∈ R) h i).mpr hzero

theorem line_count (R : Finset (Fin (n+1) × J)) :
    (n+1) * (projection R).card ≤ (n+1) * (edgeBoundary R).card + R.card := by
  classical
  have hF : fullLines R ⊆ projection R := by
    intro j hj
    have h := (mem_filter.mp hj).2
    exact mem_image.mpr ⟨(0,j),h 0,rfl⟩
  have hfull : (n+1) * (fullLines R).card ≤ R.card := by
    have hh : (univ : Finset (Fin (n+1))) ×ˢ fullLines R ⊆ R := by
      rintro ⟨i,j⟩ hp
      exact (mem_filter.mp (mem_product.mp hp).2).2 i
    simpa only [card_product,card_univ,Fintype.card_fin] using card_le_card hh
  have hpartial : (projection R \ fullLines R).card ≤ (edgeBoundary R).card := by
    have hh : projection R \ fullLines R ⊆ (edgeBoundary R).image Prod.snd := by
      intro j hj
      obtain ⟨i,hi⟩ := partial_line_boundary R hj
      exact mem_image.mpr ⟨(i,j),hi,rfl⟩
    exact (card_le_card hh).trans card_image_le
  have hc := card_sdiff_add_card_eq_card hF
  calc
    (n+1) * (projection R).card =
        (n+1) * (projection R \ fullLines R).card + (n+1) * (fullLines R).card := by
      rw [←hc,Nat.mul_add]
    _ ≤ (n+1) * (edgeBoundary R).card + R.card :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hpartial) hfull

end CPTSeparation.BoxLines

namespace CPTSeparation.Grid

section

open Finset

variable {n : ℕ}

theorem swapXY_injective : Function.Injective (@swapXY n) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
  simp only [swapXY,Prod.mk.injEq] at h ⊢
  tauto

theorem moveZ_injective : Function.Injective (@moveZ n) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
  simp only [moveZ,Prod.mk.injEq] at h ⊢
  tauto

private theorem boundary_x_le (R : Finset (Vertex n)) :
    (BoxLines.edgeBoundary R).card ≤ (edgeBoundary R).card := by
  apply card_le_card_of_injOn (fun p => ex p.1 p.2.1 p.2.2)
  · rintro ⟨i,j,k⟩ hp
    have hp' := (Finset.mem_filter.mp (show (i,j,k) ∈ BoxLines.edgeBoundary R from hp)).2
    apply Finset.mem_filter.mpr
    exact ⟨mem_univ _,hp'⟩
  · intro p _ q _ h
    exact Sum.inl.inj h

private theorem boundary_y_le (R : Finset (Vertex n)) :
    (BoxLines.edgeBoundary (R.image swapXY)).card ≤ (edgeBoundary R).card := by
  apply card_le_card_of_injOn (fun p => ey p.2.1 p.1 p.2.2)
  · rintro ⟨j,i,k⟩ hp
    have he (v : Vertex n) : swapXY v ∈ R.image swapXY ↔ v ∈ R :=
      by
        constructor
        · intro h
          obtain ⟨w,hw,he⟩ := mem_image.mp h
          simpa only [swapXY_injective he] using hw
        · intro h; exact mem_image.mpr ⟨v,h,rfl⟩
    have h1 := he (i,j.castSucc,k)
    have h2 := he (i,j.succ,k)
    have hp' := (Finset.mem_filter.mp (show (j,i,k) ∈ BoxLines.edgeBoundary (R.image swapXY) from hp)).2
    apply Finset.mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change ¬ ((i,j.castSucc,k) ∈ R ↔ (i,j.succ,k) ∈ R)
    change ¬(swapXY (i,j.castSucc,k) ∈ R.image swapXY ↔ swapXY (i,j.succ,k) ∈ R.image swapXY) at hp'
    simpa only [he] using hp'
  · rintro ⟨j,i,k⟩ _ ⟨j',i',k'⟩ _ h
    simp only [ey,Sum.inr.injEq,Sum.inl.injEq,Prod.mk.injEq] at h ⊢
    tauto

private theorem boundary_z_le (R : Finset (Vertex n)) :
    (BoxLines.edgeBoundary (R.image moveZ)).card ≤ (edgeBoundary R).card := by
  apply card_le_card_of_injOn (fun p => ez p.2.1 p.2.2 p.1)
  · rintro ⟨k,i,j⟩ hp
    have he (v : Vertex n) : moveZ v ∈ R.image moveZ ↔ v ∈ R :=
      by
        constructor
        · intro h
          obtain ⟨w,hw,he⟩ := mem_image.mp h
          simpa only [moveZ_injective he] using hw
        · intro h; exact mem_image.mpr ⟨v,h,rfl⟩
    have h1 := he (i,j,k.castSucc)
    have h2 := he (i,j,k.succ)
    have hp' := (Finset.mem_filter.mp (show (k,i,j) ∈ BoxLines.edgeBoundary (R.image moveZ) from hp)).2
    apply Finset.mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change ¬ ((i,j,k.castSucc) ∈ R ↔ (i,j,k.succ) ∈ R)
    change ¬(moveZ (i,j,k.castSucc) ∈ R.image moveZ ↔ moveZ (i,j,k.succ) ∈ R.image moveZ) at hp'
    simpa only [he] using hp'
  · rintro ⟨k,i,j⟩ _ ⟨k',i',j'⟩ _ h
    simp only [ez,Sum.inr.injEq,Prod.mk.injEq] at h ⊢
    tauto

theorem projection_line_bounds (R : Finset (Vertex n)) :
    let A := (R.image fun v => (v.1,v.2.1)).card
    let B := (R.image fun v => (v.1,v.2.2)).card
    let D := (R.image fun v => (v.2.1,v.2.2)).card
    (n+1)*A ≤ (n+1)*(edgeBoundary R).card + R.card ∧
    (n+1)*B ≤ (n+1)*(edgeBoundary R).card + R.card ∧
    (n+1)*D ≤ (n+1)*(edgeBoundary R).card + R.card := by
  have hx := (BoxLines.line_count R).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (n+1) (boundary_x_le R)) _)
  have hy := (BoxLines.line_count (R.image swapXY)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (n+1) (boundary_y_le R)) _)
  have hz := (BoxLines.line_count (R.image moveZ)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (n+1) (boundary_z_le R)) _)
  simp only [card_image_of_injective _ swapXY_injective,BoxLines.projection,
    image_image,Function.comp_def,swapXY] at hy
  simp only [card_image_of_injective _ moveZ_injective,BoxLines.projection,
    image_image,Function.comp_def,moveZ] at hz
  exact ⟨hz,hy,hx⟩

end

theorem boxConstant_pos : 0 < boxConstant := by
  unfold boxConstant
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
    (by norm_num : -(1:ℝ)/3 < 0)
  simpa using h

private theorem boundary_algebra {L r d p : ℝ} (hL : 0 < L) (hr : 0 < r)
    (_ : 0 ≤ d) (hp : 0 ≤ p) (hhalf : 2*r ≤ L^3)
    (hproj : r^2 ≤ p^3) (hline : L*p ≤ L*d+r) :
    boxConstant * r^((2:ℝ)/3) ≤ d := by
  have hr0 := le_of_lt hr
  have h23 : (r^((2:ℝ)/3))^3 = r^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr0]
    norm_num
  have h13 : (r^((1:ℝ)/3))^3 = r := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr0]
    norm_num
  have hc3 : ((2:ℝ)^(-(1:ℝ)/3))^3 = (1:ℝ)/2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hc : 0 ≤ (2:ℝ)^(-(1:ℝ)/3) := Real.rpow_nonneg (by norm_num) _
  have hp' : r^((2:ℝ)/3) ≤ p := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hr0 _) hp (by norm_num : (3:ℕ) ≠ 0)).mp
    simpa only [h23] using hproj
  have hl' : r^((1:ℝ)/3) ≤ (2:ℝ)^(-(1:ℝ)/3)*L := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hr0 _)
      (mul_nonneg hc hL.le) (by norm_num : (3:ℕ) ≠ 0)).mp
    rw [h13,mul_pow,hc3]
    linarith
  have hprod : r^((1:ℝ)/3)*r^((2:ℝ)/3) = r := by
    rw [←Real.rpow_add hr]
    norm_num
  have hsmall := mul_le_mul_of_nonneg_right hl' (Real.rpow_nonneg hr0 ((2:ℝ)/3))
  rw [hprod] at hsmall
  have hproj' := mul_le_mul_of_nonneg_left hp' hL.le
  unfold boxConstant
  nlinarith

theorem box_boundary {n : ℕ} (R : Finset (Vertex n)) (hne : R.Nonempty)
    (hhalf : 2*R.card ≤ (n+1)^3) :
    boxConstant * (R.card:ℝ)^((2:ℝ)/3) ≤ (edgeBoundary R).card := by
  let A := (R.image fun v => (v.1,v.2.1)).card
  let B := (R.image fun v => (v.1,v.2.2)).card
  let D := (R.image fun v => (v.2.1,v.2.2)).card
  let p := max A (max B D)
  have ha : A ≤ p := le_max_left _ _
  have hb : B ≤ p := (le_max_left B D).trans (le_max_right _ _)
  have hd : D ≤ p := (le_max_right B D).trans (le_max_right _ _)
  have hp : R.card^2 ≤ p^3 := by
    calc
      _ ≤ A*B*D := Projection.card_sq_le_projections R
      _ ≤ p*p*p := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hd
      _ = p^3 := by ring
  obtain ⟨hA,hB,hD⟩ := projection_line_bounds R
  have hline : (n+1)*p ≤ (n+1)*(edgeBoundary R).card + R.card := by
    dsimp [p]
    rw [mul_max_of_nonneg _ _ (Nat.zero_le _),mul_max_of_nonneg _ _ (Nat.zero_le _)]
    exact max_le hA (max_le hB hD)
  apply boundary_algebra (L := (n+1:ℕ)) (p := p)
  · positivity
  · exact_mod_cast Finset.card_pos.mpr hne
  · positivity
  · positivity
  · exact_mod_cast hhalf
  · exact_mod_cast hp
  · exact_mod_cast hline

end CPTSeparation.Grid

namespace CPTSeparation.Flows

section

open Classical

variable {V E : Type*} [finiteV : Fintype V] [finiteE : Fintype E] [decidableV : DecidableEq V] [decidableE : DecidableEq E]

variable (tail head : E → V) (T : Finset E)

omit V E tail head T in
theorem edge_connected.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) (e : E) (he : e ∉ T) :
    (connected tail head T).r (tail e) (head e) :=
  Relation.EqvGen.rel _ _ ⟨e,he,rfl,rfl⟩

omit V E tail head T in
theorem path_flow.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) {v w : V} (h : (connected tail head T).r v w) :
    ∃ t : E → Scalar, (∀ e ∈ T, t e = 0) ∧
      incidence tail head t = Pi.single w 1 - Pi.single v 1 := by
  induction h with
  | rel v w h =>
    obtain ⟨e,he,rfl,rfl⟩ := h
    refine ⟨Pi.single e 1,?_,incidence_single tail head e 1⟩
    intro f hf
    exact Pi.single_eq_of_ne (by intro h; subst f; exact he hf) _
  | refl v => exact ⟨0,by simp,by simp⟩
  | symm v w h ih =>
    obtain ⟨t,ht,hd⟩ := ih
    refine ⟨-t,by simpa using ht,?_⟩
    rw [map_neg,hd]; abel
  | trans u v w _ _ ih ih' =>
    obtain ⟨t,ht,hd⟩ := ih
    obtain ⟨t',ht',hd'⟩ := ih'
    refine ⟨t+t',fun e he => by simp [ht e he,ht' e he],?_⟩
    rw [map_add,hd,hd']; abel

omit V in
private theorem sum_single.{uDecl1}
    {V : Type uDecl1}
    [Fintype V]
    [DecidableEq V] (U : Finset V) (v : V) (z : Scalar) :
    ∑ x ∈ U, (Pi.single v z : V → Scalar) x = if v ∈ U then z else 0 := by
  simp [Pi.single_apply]

omit V E tail head in
theorem sum_incidence.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) (t : E → Scalar) : ∑ v, incidence tail head t v = 0 := by
  change (∑ v, (∑ e, t e • (Pi.single (head e) 1 - Pi.single (tail e) 1) : V → Scalar) v) = _
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,mul_sub]
  rw [Finset.sum_comm]
  have h (e : E) : ∑ v, (t e * (Pi.single (head e) (1:Scalar) : V → Scalar) v -
      t e * (Pi.single (tail e) (1:Scalar) : V → Scalar) v) = 0 := by
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum]
    simp [Pi.single_apply]
  simp only [h,Finset.sum_const_zero]

theorem sum_incidence_component (t : E → Scalar) (ht : ∀ e ∈ T, t e = 0) (v : V) :
    ∑ w ∈ component tail head T v, incidence tail head t w = 0 := by
  change (∑ w ∈ component tail head T v,
    (∑ e, t e • (Pi.single (head e) 1 - Pi.single (tail e) 1) : V → Scalar) w) = _
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,mul_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,sum_single,sum_single]
  by_cases he : e ∈ T
  · simp [ht e he]
  have hc : head e ∈ component tail head T v ↔ tail e ∈ component tail head T v := by
    simp only [mem_component]
    exact ⟨fun h => (connected tail head T).trans h ((connected tail head T).symm (edge_connected tail head T e he)),
      fun h => (connected tail head T).trans h (edge_connected tail head T e he)⟩
  simp only [hc,sub_self]

theorem solvable_iff (b : V → Scalar) :
    (∃ t : E → Scalar, (∀ e ∈ T, t e = 0) ∧ incidence tail head t = b) ↔
      ∀ v, ∑ w ∈ component tail head T v, b w = 0 := by
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact sum_incidence_component tail head T t ht
  · intro hb
    let q : V → Component tail head T := Quotient.mk (connected tail head T)
    let : Fintype (Component tail head T) := Fintype.ofFinite _
    have hp (v : V) : ∃ t : E → Scalar, (∀ e ∈ T, t e = 0) ∧
        incidence tail head t = Pi.single v 1 - Pi.single ((q v).out) 1 := by
      apply path_flow tail head T
      exact Quotient.exact (Quotient.out_eq (q v))
    choose t ht hd using hp
    refine ⟨∑ v, b v • t v,?_,?_⟩
    · intro e he
      simp [Finset.sum_apply,ht _ e he]
    · rw [map_sum]
      simp only [map_smul,hd,smul_sub,Finset.sum_sub_distrib]
      have hfirst : (∑ v, b v • (Pi.single v (1:Scalar) : V → Scalar)) = b := by
        funext j; simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
      have hsecond : (∑ v, b v • (Pi.single (q v).out (1:Scalar) : V → Scalar)) = 0 := by
        rw [←Fintype.sum_fiberwise q]
        apply Finset.sum_eq_zero
        intro c _
        have hf : (∑ v : {v : V // q v = c}, b v) = 0 := by
          have he (v : V) : q v = c ↔ v ∈ component tail head T c.out := by
            rw [mem_component]
            constructor
            · intro h
              exact Quotient.exact ((Quotient.out_eq c).trans h.symm)
            · intro h
              exact (Quotient.sound h).symm.trans (Quotient.out_eq c)
          let ee := Equiv.subtypeEquivRight he
          have hs := Fintype.sum_equiv ee (fun v : {v : V // q v = c} => b v)
            (fun v : component tail head T c.out => b v) (fun _ => rfl)
          rw [hs]
          exact (Finset.sum_coe_sort (component tail head T c.out) b).trans (hb c.out)
        have hx : (∑ v : {v : V // q v = c}, b v •
            (Pi.single (q v).out (1:Scalar) : V → Scalar)) =
            (∑ v : {v : V // q v = c}, b v) • Pi.single c.out 1 := by
          rw [Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro v _; rw [v.2]
        rw [hx,hf,zero_smul]
      rw [hfirst,hsecond,sub_zero]

theorem partial_flow_iff (σ : E → Scalar) :
    (∃ k : E → Scalar, incidence tail head k = 0 ∧ ∀ e ∈ T, k e = σ e) ↔
      ∀ v, ∑ w ∈ component tail head T v,
        incidence tail head (fun e => if e ∈ T then σ e else 0) w = 0 := by
  let z : E → Scalar := fun e => if e ∈ T then σ e else 0
  constructor
  · rintro ⟨k,hk,he⟩ v
    have ht : ∀ e ∈ T, (k-z) e = 0 := by intro e h; simp [z,h,he e h]
    have h := sum_incidence_component tail head T (k-z) ht v
    simpa [map_sub,hk,Finset.sum_neg_distrib] using h
  · intro h
    have hb : ∀ v, ∑ w ∈ component tail head T v, (-incidence tail head z) w = 0 := by
      intro v; simpa [Finset.sum_neg_distrib] using congrArg Neg.neg (h v)
    obtain ⟨t,ht,hd⟩ := (solvable_iff tail head T (-incidence tail head z)).mpr hb
    refine ⟨z+t,by simp [hd],?_⟩
    intro e he; simp [z,he,ht e he]

end

open Classical Finset

variable {V E : Type*} [Fintype V] [finiteE : Fintype E] [decidableV : DecidableEq V] [decidableE : DecidableEq E]

variable (tail head : E → V) (T : Finset E)

omit V E tail head T in
theorem cell_nonempty.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) (c : Component tail head T) : (cell tail head T c).Nonempty :=
  ⟨c.out,(mem_cell tail head T c c.out).mpr (Quotient.out_eq c)⟩

omit V E tail head T in
theorem cells_disjoint.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) {c d : Component tail head T} (h : c ≠ d) :
    Disjoint (cell tail head T c) (cell tail head T d) := by
  apply disjoint_left.mpr
  intro v hc hd
  exact h ((mem_cell tail head T c v).mp hc |>.symm.trans ((mem_cell tail head T d v).mp hd))

omit V E tail head T in
theorem sum_cells.{uDecl1, uDecl2, uDecl3}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) {M : Type uDecl3} [AddCommMonoid M] (f : V → M) :
    ∑ c : Component tail head T, ∑ v ∈ cell tail head T c, f v = ∑ v, f v := by
  have he (c : Component tail head T) :
      (∑ v ∈ cell tail head T c, f v) = ∑ v, if quotientMap tail head T v = c then f v else 0 := by
    rw [←sum_filter]
    congr 1
    ext v; simp
  simp only [he]
  rw [sum_comm]
  simp

omit V E tail head T in
theorem sum_card_cells.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) : ∑ c : Component tail head T, (cell tail head T c).card = Fintype.card V := by
  simpa using sum_cells tail head T (fun _ => (1:ℕ))

theorem boundary_cell_subset (c : Component tail head T) :
    edgeBoundary tail head (cell tail head T c) ⊆ T := by
  intro e he
  by_contra hn
  have hc := edge_connected tail head T e hn
  have hq : quotientMap tail head T (tail e) = quotientMap tail head T (head e) := Quotient.sound hc
  have hh := (mem_filter.mp he).2
  exact hh (by simp only [mem_cell,hq])

theorem sum_boundary_cells :
    ∑ c : Component tail head T, (edgeBoundary tail head (cell tail head T c)).card ≤ 2*T.card := by
  have he (c : Component tail head T) :
      (edgeBoundary tail head (cell tail head T c)).card =
      ∑ e ∈ T, if e ∈ edgeBoundary tail head (cell tail head T c) then 1 else 0 := by
    rw [←card_filter]
    congr 1
    ext e
    simp only [mem_filter]
    exact ⟨fun h => ⟨boundary_cell_subset tail head T c h,h⟩,fun h => h.2⟩
  simp only [he]
  rw [sum_comm]
  calc
    _ ≤ ∑ _ ∈ T, 2 := by
      apply sum_le_sum
      intro e _
      calc
        _ ≤ ∑ c : Component tail head T,
            ((if quotientMap tail head T (tail e) = c then 1 else 0) +
             (if quotientMap tail head T (head e) = c then 1 else 0)) := by
          apply sum_le_sum
          intro c _
          simp only [edgeBoundary,mem_filter,mem_univ,true_and,mem_cell]
          by_cases h1 : quotientMap tail head T (tail e) = c <;>
            by_cases h2 : quotientMap tail head T (head e) = c <;> simp [h1,h2]
        _ = 2 := by rw [sum_add_distrib]; simp
    _ = 2*T.card := by simp [mul_comm]

omit V E tail head T in
theorem small_failing_component.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V)
    (T : Finset E) (b : V → Scalar) (hb : ∑ v, b v = 0)
    (hfail : ∃ c : Component tail head T, (∑ v ∈ cell tail head T c, b v) ≠ 0) :
    ∃ c : Component tail head T, (∑ v ∈ cell tail head T c, b v) ≠ 0 ∧
      2*(cell tail head T c).card ≤ Fintype.card V := by
  obtain ⟨c,hc⟩ := hfail
  by_cases hsmall : 2*(cell tail head T c).card ≤ Fintype.card V
  · exact ⟨c,hc,hsmall⟩
  have he : ∃ d : Component tail head T, d ≠ c ∧ (∑ v ∈ cell tail head T d, b v) ≠ 0 := by
    by_contra hh
    push Not at hh
    have hsum : (∑ d : Component tail head T, ∑ v ∈ cell tail head T d, b v) =
        ∑ v ∈ cell tail head T c, b v := by
      apply sum_eq_single c
      · intro d _ hd; exact hh d hd
      · simp
    rw [sum_cells,hb] at hsum
    exact hc hsum.symm
  obtain ⟨d,hd,hfd⟩ := he
  refine ⟨d,hfd,?_⟩
  have hdis := cells_disjoint tail head T hd.symm
  have hcard := card_le_card (subset_univ (cell tail head T c ∪ cell tail head T d))
  rw [card_union_of_disjoint hdis,card_univ] at hcard
  omega

end CPTSeparation.Flows

namespace CPTSeparation.Grid

open Classical Finset

variable {n : ℕ}

private theorem bound_of_boundary {r b : ℝ} (hr : 0 ≤ r) (_ : 0 ≤ b)
    (h : boxConstant * r^((2:ℝ)/3) ≤ b) : r ≤ (b/boxConstant)^((3:ℝ)/2) := by
  have hu : r^((2:ℝ)/3) ≤ b/boxConstant := by
    apply (le_div_iff₀ boxConstant_pos).mpr
    simpa only [mul_comm] using h
  have hv := Real.rpow_le_rpow (Real.rpow_nonneg hr _) hu (by norm_num : (0:ℝ) ≤ 3/2)
  rw [←Real.rpow_mul hr] at hv
  norm_num at hv
  exact hv

theorem small_cell_bound (T : Finset (Edge n)) (c : Flows.Component tail head T)
    (hsmall : 2*(Flows.cell tail head T c).card ≤ (n+1)^3) :
    ((Flows.cell tail head T c).card:ℝ) ≤
      ((Flows.edgeBoundary tail head (Flows.cell tail head T c)).card / boxConstant)^((3:ℝ)/2) :=
  bound_of_boundary (by positivity) (by positivity)
    (box_boundary _ (Flows.cell_nonempty tail head T c) hsmall)

theorem partial_flow_small_obstruction (T : Finset (Edge n)) (σ : Edge n → Scalar)
    (hfail : ¬ ∃ k : Edge n → Scalar, Flows.incidence tail head k = 0 ∧
      ∀ e ∈ T, k e = σ e) :
    ∃ c : Flows.Component tail head T,
      (∑ v ∈ Flows.cell tail head T c,
        Flows.incidence tail head (fun e => if e ∈ T then σ e else 0) v) ≠ 0 ∧
      2*(Flows.cell tail head T c).card ≤ (n+1)^3 ∧
      ((Flows.cell tail head T c).card:ℝ) ≤
        (T.card/boxConstant)^((3:ℝ)/2) := by
  let z : Edge n → Scalar := fun e => if e ∈ T then σ e else 0
  have hf : ∃ v, (∑ w ∈ Flows.component tail head T v, Flows.incidence tail head z w) ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hfail ((Flows.partial_flow_iff tail head T σ).mpr hh)
  obtain ⟨v,hv⟩ := hf
  have hcell : Flows.cell tail head T (Flows.quotientMap tail head T v) =
      Flows.component tail head T v := by
    ext w
    rw [Flows.mem_cell,Flows.mem_component]
    exact ⟨fun h => Quotient.exact h.symm,fun h => (Quotient.sound h).symm⟩
  obtain ⟨c,hc,hs⟩ := Flows.small_failing_component tail head T (Flows.incidence tail head z)
    (Flows.sum_incidence tail head z) ⟨Flows.quotientMap tail head T v,by simpa only [hcell] using hv⟩
  have hcard : Fintype.card (Vertex n) = (n+1)^3 := by simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
  rw [hcard] at hs
  refine ⟨c,hc,hs,(small_cell_bound T c hs).trans ?_⟩
  apply Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) boxConstant_pos.le) _ (by norm_num)
  apply div_le_div_of_nonneg_right _ boxConstant_pos.le
  exact_mod_cast card_le_card (Flows.boundary_cell_subset tail head T c)

private theorem sum_rpow_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, (f i)^((3:ℝ)/2) ≤ (∑ i ∈ s, f i)^((3:ℝ)/2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha,sum_insert ha]
    have hs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    calc
      f a ^ ((3:ℝ)/2) + ∑ i ∈ s, f i ^ ((3:ℝ)/2) ≤
          f a ^ ((3:ℝ)/2) + (∑ i ∈ s, f i) ^ ((3:ℝ)/2) := add_le_add (le_refl _) (ih hs)
      _ ≤ (f a + ∑ i ∈ s, f i) ^ ((3:ℝ)/2) :=
        Real.add_rpow_le_rpow_add (hf a (mem_insert_self _ _)) (sum_nonneg hs) (by norm_num)

theorem small_components_bound (T : Finset (Edge n)) (S : Finset (Flows.Component tail head T))
    (hs : ∀ c ∈ S, 2*(Flows.cell tail head T c).card ≤ (n+1)^3) :
    (∑ c ∈ S, ((Flows.cell tail head T c).card:ℝ)) ≤
      ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) := by
  let b (c : Flows.Component tail head T) : ℝ :=
    (Flows.edgeBoundary tail head (Flows.cell tail head T c)).card / boxConstant
  have hn (c) : 0 ≤ b c := div_nonneg (Nat.cast_nonneg _) boxConstant_pos.le
  calc
    _ ≤ ∑ c ∈ S, (b c)^((3:ℝ)/2) := sum_le_sum (fun c hc => small_cell_bound T c (hs c hc))
    _ ≤ (∑ c ∈ S, b c)^((3:ℝ)/2) := sum_rpow_le S b (fun c _ => hn c)
    _ ≤ ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) := by
      apply Real.rpow_le_rpow (sum_nonneg (fun c _ => hn c)) _ (by norm_num)
      dsimp [b]
      rw [←sum_div]
      apply div_le_div_of_nonneg_right _ boxConstant_pos.le
      calc
        _ ≤ ∑ c : Flows.Component tail head T,
            ((Flows.edgeBoundary tail head (Flows.cell tail head T c)).card:ℝ) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
        _ ≤ 2*T.card := by exact_mod_cast Flows.sum_boundary_cells tail head T

theorem exists_giant (T : Finset (Edge n))
    (hnum : ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) < ((n+1)^3:ℕ)) :
    ∃ c : Flows.Component tail head T, (n+1)^3 < 2*(Flows.cell tail head T c).card := by
  by_contra hh
  push Not at hh
  have h := small_components_bound T univ (fun c _ => hh c)
  rw [←Nat.cast_sum,Flows.sum_card_cells] at h
  have hc : Fintype.card (Vertex n) = (n+1)^3 := by simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
  rw [hc] at h
  exact (not_lt_of_ge h) hnum

end CPTSeparation.Grid

namespace CPTSeparation.Flows

open Classical Finset

variable {V E : Type*} [finiteV : Fintype V] [finiteE : Fintype E] [decidableV : DecidableEq V] [decidableE : DecidableEq E]

variable (tail head : E → V)

omit V E tail head in
theorem connected_mono.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T U : Finset E} (hT : T ⊆ U) {v w : V}
    (h : (connected tail head U).r v w) : (connected tail head T).r v w := by
  induction h with
  | rel v w h =>
    obtain ⟨e,he,rfl,rfl⟩ := h
    exact edge_connected tail head T e (fun hh => he (hT hh))
  | refl v => exact .refl v
  | symm v w h ih => exact .symm _ _ ih
  | trans v w z h h' ih ih' => exact .trans _ _ _ ih ih'

omit V E tail head in
theorem component_mono.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T U : Finset E} (hT : T ⊆ U) (v : V) :
    component tail head U v ⊆ component tail head T v := by
  intro w hw
  exact (mem_component _ _ _ _ _).mpr (connected_mono tail head hT ((mem_component _ _ _ _ _).mp hw))

omit V E tail head in
theorem giant_mono.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T U : Finset E} (hT : T ⊆ U) {v : V} (h : IsGiant tail head U v) :
    IsGiant tail head T v := lt_of_lt_of_le h (Nat.mul_le_mul_left 2 (card_le_card (component_mono tail head hT v)))

omit V E tail head in
theorem giants_connected.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T : Finset E} {v w : V}
    (hv : IsGiant tail head T v) (hw : IsGiant tail head T w) : (connected tail head T).r v w := by
  by_contra hh
  have hd : Disjoint (component tail head T v) (component tail head T w) := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact hh ((connected tail head T).trans ((mem_component _ _ _ _ _).mp hx)
      ((connected tail head T).symm ((mem_component _ _ _ _ _).mp hx')))
  have hk : (component tail head T v).card + (component tail head T w).card ≤ Fintype.card V := by
    rw [←card_union_of_disjoint hd]
    exact card_le_univ _
  dsimp [IsGiant] at hv hw
  omega

omit V E tail head in
theorem component_isolated.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T : Finset E} (v : V)
    (h : ∀ e, tail e = v ∨ head e = v → e ∈ T) : component tail head T v = {v} := by
  have hh {x y : V} (hc : (connected tail head T).r x y) : x = v ↔ y = v := by
    induction hc with
    | rel x y hr =>
      obtain ⟨e,he,rfl,rfl⟩ := hr
      exact ⟨fun hv => False.elim (he (h e (Or.inl hv))),fun hv => False.elim (he (h e (Or.inr hv)))⟩
    | refl x => rfl
    | symm x y hc ih => exact ih.symm
    | trans x y z hc hc' ih ih' => exact ih.trans ih'
  ext w
  simp only [mem_component,mem_singleton]
  exact ⟨fun hw => (hh hw).mp rfl,fun hw => by subst w; exact (connected tail head T).refl _⟩

omit V E tail head in
theorem giant_ne_isolated.{uDecl1, uDecl2}
    {V : Type uDecl1}
    {E : Type uDecl2}
    [Fintype V]
    [Fintype E]
    [DecidableEq V]
    [DecidableEq E]
    (tail : E → V)
    (head : E → V) {T : Finset E} {w v : V} (hV : 2 ≤ Fintype.card V)
    (hw : IsGiant tail head T w) (h : ∀ e, tail e = v ∨ head e = v → e ∈ T) : w ≠ v := by
  intro he; subst w
  have hh := component_isolated tail head v h
  dsimp [IsGiant] at hw
  rw [hh,card_singleton] at hw
  omega

end CPTSeparation.Flows

namespace CPTSeparation.Grid

section

open Classical Finset

variable {n : ℕ}

theorem grid_connected (v w : Vertex n) : (Flows.connected tail head ∅).r v w := by
  have hx (i j k : Fin (n+1)) : (Flows.connected tail head ∅).r (0,j,k) (i,j,k) := by
    induction i using Fin.induction with
    | zero => exact (Flows.connected tail head ∅).refl _
    | succ i ih =>
      exact (Flows.connected tail head ∅).trans ih (Flows.edge_connected tail head ∅ (ex i j k) (by simp))
  have hy (i j k : Fin (n+1)) : (Flows.connected tail head ∅).r (i,0,k) (i,j,k) := by
    induction j using Fin.induction with
    | zero => exact (Flows.connected tail head ∅).refl _
    | succ j ih =>
      exact (Flows.connected tail head ∅).trans ih (Flows.edge_connected tail head ∅ (ey i j k) (by simp))
  have hz (i j k : Fin (n+1)) : (Flows.connected tail head ∅).r (i,j,0) (i,j,k) := by
    induction k using Fin.induction with
    | zero => exact (Flows.connected tail head ∅).refl _
    | succ k ih =>
      exact (Flows.connected tail head ∅).trans ih (Flows.edge_connected tail head ∅ (ez i j k) (by simp))
  have h (v : Vertex n) : (Flows.connected tail head ∅).r (0,0,0) v :=
    (Flows.connected tail head ∅).trans (hx v.1 0 0)
      ((Flows.connected tail head ∅).trans (hy v.1 v.2.1 0) (hz v.1 v.2.1 v.2.2))
  exact (Flows.connected tail head ∅).trans ((Flows.connected tail head ∅).symm (h v)) (h w)

theorem grid_empty_component (v : Vertex n) : Flows.component tail head ∅ v = univ := by
  ext w; simp only [Flows.mem_component,mem_univ,iff_true]; exact grid_connected v w

theorem grid_empty_giant (v : Vertex n) : Flows.IsGiant tail head ∅ v := by
  dsimp [Flows.IsGiant]
  rw [grid_empty_component,card_univ]
  have hpos : 0 < Fintype.card (Vertex n) := Fintype.card_pos_iff.mpr ⟨(0,0,0)⟩
  omega

end

section

open Classical Finset

variable {n M : ℕ} {b : Vertex n → Scalar}

theorem AtomShift.config_boundary {t : Edge n → Scalar} {v : Vertex n}
    {s : Configuration b v} {y : Atom b} (h : AtomShift t (.inr ⟨v,s⟩) y) :
    boundary t v = 0 := by
  cases h with
  | config v s h => simpa only [sub_self] using h

theorem quantitative_homogeneity_shift (hn : 1 ≤ n) {J : Type*} [Fintype J] [Nonempty (Atom b)]
    (names : J ↪ Fin M) (a a' : J → Atom b)
    (hw : (7*Fintype.card J:ℝ) + 7*((6*Fintype.card J:ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (ht : Counting.tupleType (analysisStructure b) names a =
      Counting.tupleType (analysisStructure b) names a') :
    ∃ k : Edge n → Scalar, boundary k = 0 ∧ ∀ j, AtomShift k (a j) (a' j) := by
  let : Nonempty (Atom b) := ⟨.inr ⟨(0,0,0),someConfiguration hn b (0,0,0)⟩⟩
  have hp : 0 ≤ ((6*Fintype.card J:ℝ)/boxConstant)^((3:ℝ)/2) := Real.rpow_nonneg (div_nonneg (by positivity) boxConstant_pos.le) _
  have hw' : 7*Fintype.card J < M := by
    have hh : (7*Fintype.card J:ℝ)+1 ≤ M := by linarith
    have hh' : 7*Fintype.card J+1 ≤ M := by exact_mod_cast hh
    omega
  obtain ⟨σ,hσ⟩ := tuple_partial_shift names a a' hw' ht
  let T : Finset (Edge n) := touches univ a
  have hT : T.card ≤ 6*Fintype.card J := by simpa [T] using touches_card univ a
  suffices hs : ∃ k : Edge n → Scalar, Flows.incidence tail head k = 0 ∧ ∀ e ∈ T, k e = σ e by
    obtain ⟨k,hk,he⟩ := hs
    refine ⟨k,hk,fun j => (hσ j).congr ?_⟩
    intro e hej
    exact (he e (touch_subset_touches univ a (mem_univ j) hej)).symm
  by_contra hs
  obtain ⟨C,hbad,hsmall,hcard⟩ := partial_flow_small_obstruction T σ hs
  let U := Flows.cell tail head T C
  have hU : (U.card:ℝ) ≤ ((6*Fintype.card J:ℝ)/boxConstant)^((3:ℝ)/2) := by
    apply hcard.trans
    apply Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) boxConstant_pos.le) _ (by norm_num)
    apply div_le_div_of_nonneg_right _ boxConstant_pos.le
    exact_mod_cast hT
  let conf (v : U) : Atom b := .inr ⟨v.val,someConfiguration hn b v.val⟩
  have hwU : 7*Fintype.card (J ⊕ U) < M := by
    have hh : (7*(Fintype.card J+U.card):ℝ)+1 ≤ M := by linarith
    have hh' : 7*(Fintype.card J+U.card)+1 ≤ M := by exact_mod_cast hh
    simpa only [Fintype.card_sum,Fintype.card_coe] using (show 7*(Fintype.card J+U.card)<M by omega)
  have hcardU : Fintype.card (J ⊕ U) < M := by omega
  obtain ⟨conf',htU⟩ := Counting.tupleType_append (analysisStructure b) (analysisStructure b)
    names (namesBelow hcardU) a a' conf ht
  obtain ⟨d,hd⟩ := tuple_partial_shift (namesBelow hcardU) (Sum.elim a conf) (Sum.elim a' conf') hwU htU
  have hdT : ∀ e ∈ T, d e = σ e := by
    intro e he
    obtain ⟨j,hj,he⟩ := mem_biUnion.mp he
    exact (hd (.inl j)).unique_on_touch (hσ j) e he
  have hdU : ∀ v ∈ U, Flows.incidence tail head d v = 0 := by
    intro v hv
    exact (hd (.inr ⟨v,hv⟩)).config_boundary
  let z : Edge n → Scalar := fun e => if e ∈ T then σ e else 0
  have hd0 : ∀ e ∈ T, (d-z) e = 0 := by intro e he; simp [z,he,hdT e he]
  have hbal := Flows.sum_incidence_component tail head T (d-z) hd0 C.out
  have hsum : (∑ v ∈ U, Flows.incidence tail head d v) = 0 := sum_eq_zero hdU
  change (∑ v ∈ U, Flows.incidence tail head (d-z) v) = 0 at hbal
  simp only [map_sub,Pi.sub_apply,sum_sub_distrib,hsum,zero_sub,neg_eq_zero] at hbal
  exact hbad hbal

end

open Classical

variable {n M : ℕ} {b : Vertex n → Scalar}

theorem central_atomShift (k : CentralGroup n) (x : Atom b) :
    AtomShift k.toAdd.val x (k • x) := by
  have hk (e : Edge n) : restrictGroup e (Support.H.central flowCycle k.toAdd) =
      Support.H.central (localCycle e) (k.toAdd.val e) := by
    apply Support.H.ext <;> rfl
  cases x with
  | inl x =>
    rcases x with ⟨e,s⟩
    change AtomShift k.toAdd.val (.inl ⟨e,s⟩)
      (.inl ⟨e,restrictGroup e (Support.H.central flowCycle k.toAdd)*s⟩)
    rw [hk]
    exact .edge e s
  | inr x =>
    rcases x with ⟨v,s⟩
    have hb : boundary k.toAdd.val v = b v-b v := by
      have hh := congrFun k.toAdd.property v
      simp
    have hs : Support.H.central flowCycle k.toAdd • s = s.shift k.toAdd.val hb := by
      apply Configuration.ext
      intro e
      change restrictGroup e.val (Support.H.central flowCycle k.toAdd)*s.state e = _
      rw [hk]
      rfl
    change AtomShift k.toAdd.val (.inr ⟨v,s⟩) (.inr ⟨v,Support.H.central flowCycle k.toAdd • s⟩)
    rw [hs]
    exact .config v s hb

theorem quantitative_homogeneity (hn : 1 ≤ n) {J : Type*} [Fintype J] [Nonempty (Atom b)]
    (names : J ↪ Fin M) (a a' : J → Atom b)
    (hw : (7*Fintype.card J:ℝ) + 7*((6*Fintype.card J:ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (ht : Counting.tupleType (analysisStructure b) names a =
      Counting.tupleType (analysisStructure b) names a') :
    ∃ k : CentralGroup n, ∀ j, k • a j = a' j := by
  obtain ⟨k,hk,ha⟩ := quantitative_homogeneity_shift hn names a a' hw ht
  let g : CentralGroup n := Multiplicative.ofAdd ⟨k,hk⟩
  exact ⟨g,fun j => (central_atomShift g (a j)).functional (ha j)⟩

end CPTSeparation.Grid

namespace CPTSeparation.Counting.Formula

open Classical Finset

variable {R I A B : Type*} [DecidableEq I]

theorem eval_of_partialBijectionSystem (S : Structure R A) (T : Structure R B)
    (E : Finset I → (I → A) → (I → B) → Prop)
    (heq : ∀ names v w, E names v w → ∀ i ∈ names, ∀ j ∈ names, (v i = v j ↔ w i = w j))
    (hrel : ∀ names v w, E names v w → ∀ r i, i ∈ names → ∀ j, j ∈ names →
      (S.rel r (v i) (v j) ↔ T.rel r (w i) (w j)))
    (hext : ∀ names v w, E names v w → ∀ i, ∃ e : A ≃ B,
      ∀ a, E (insert i (names.erase i)) (Function.update v i a) (Function.update w i (e a)))
    (φ : Formula R I) : ∀ names v w, E names v w → φ.free ⊆ names →
      (φ.eval S v ↔ φ.eval T w) := by
  induction φ with
  | falsum => intros; rfl
  | equal i j =>
    intro names v w h hf
    exact heq names v w h i (hf (by simp [free])) j (hf (by simp [free]))
  | relation r i j =>
    intro names v w h hf
    exact hrel names v w h r i (hf (by simp [free])) j (hf (by simp [free]))
  | neg φ ih => intro names v w h hf; exact not_congr (ih names v w h hf)
  | and φ ψ ih ih' =>
    intro names v w h hf
    exact and_congr (ih names v w h (subset_union_left.trans hf))
      (ih' names v w h (subset_union_right.trans hf))
  | ex i φ ih =>
    intro names v w h hf
    obtain ⟨e,he⟩ := hext names v w h i
    have hfree : φ.free ⊆ insert i (names.erase i) := by
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · exact mem_insert_of_mem (mem_erase.mpr ⟨hji,hf (mem_erase.mpr ⟨hji,hj⟩)⟩)
    change (∃ a, φ.eval S (Function.update v i a)) ↔ _
    constructor
    · rintro ⟨a,ha⟩; exact ⟨e a,(ih _ _ _ (he a) hfree).mp ha⟩
    · rintro ⟨b,hb⟩; obtain ⟨a,rfl⟩ := e.surjective b
      exact ⟨a,(ih _ _ _ (he a) hfree).mpr hb⟩
  | exact i n φ ih =>
    intro names v w h hf
    obtain ⟨e,he⟩ := hext names v w h i
    have hfree : φ.free ⊆ insert i (names.erase i) := by
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · exact mem_insert_of_mem (mem_erase.mpr ⟨hji,hf (mem_erase.mpr ⟨hji,hj⟩)⟩)
    let f : {a : A // φ.eval S (Function.update v i a)} ≃
        {b : B // φ.eval T (Function.update w i b)} :=
      e.subtypeEquiv (fun a => ih _ _ _ (he a) hfree)
    exact ⟨fun ⟨g⟩ => ⟨f.symm.trans g⟩,fun ⟨g⟩ => ⟨f.trans g⟩⟩

end CPTSeparation.Counting.Formula

namespace CPTSeparation.Grid

open Classical Finset

variable {n M : ℕ} {b b' : Vertex n → Scalar}

theorem boundary_eq_incidence : (boundary : (Edge n → Scalar) →ₗ[Scalar] (Vertex n → Scalar)) =
    Flows.incidence tail head := rfl

theorem giant_exists_of_bound (hbound : GiantBound n M) (T : Finset (Edge n)) (hT : T.card ≤ 6*M) :
    ∃ v, Flows.IsGiant tail head T v := by
  have hnum : ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) < ((n+1)^3:ℕ) := by
    apply lt_of_le_of_lt _ hbound
    apply Real.rpow_le_rpow (div_nonneg (by positivity) boxConstant_pos.le) _ (by norm_num)
    apply div_le_div_of_nonneg_right _ boxConstant_pos.le
    have hh : (T.card:ℝ) ≤ 6*M := by exact_mod_cast hT
    linarith
  obtain ⟨c,hc⟩ := exists_giant T hnum
  refine ⟨c.out,?_⟩
  change Fintype.card (Vertex n) < 2*(Flows.cell tail head T c).card
  have hcard : Fintype.card (Vertex n) = (n+1)^3 := by
    simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
  simpa only [hcard] using hc

theorem defect_transport (hbound : GiantBound n M) (T U : Finset (Edge n)) (hTU : T ⊆ U)
    (hU : U.card ≤ 6*M) (t : Edge n → Scalar) (w : Vertex n)
    (hw : Flows.IsGiant tail head T w) (ht : boundary t = b'-b-Pi.single w 1) :
    ∃ t' : Edge n → Scalar, ∃ w' : Vertex n,
      Flows.IsGiant tail head U w' ∧ boundary t' = b'-b-Pi.single w' 1 ∧ ∀ e ∈ T, t' e = t e := by
  obtain ⟨w',hw'⟩ := giant_exists_of_bound hbound U hU
  have hc := Flows.giants_connected tail head (Flows.giant_mono tail head hTU hw') hw
  obtain ⟨p,hp,hd⟩ := Flows.path_flow tail head T hc
  refine ⟨t+p,w',hw',?_,?_⟩
  · rw [map_add,ht,boundary_eq_incidence,hd]
    abel
  · intro e he; simp [hp e he]

theorem CompatibleAssignment.mono {I : Type*} [DecidableEq I] {names small : Finset I}
    (hs : small ⊆ names) {a : I → Atom b} {a' : I → Atom b'}
    (h : CompatibleAssignment names a a') : CompatibleAssignment small a a' := by
  obtain ⟨t,w,hw,ht,ha⟩ := h
  exact ⟨t,w,Flows.giant_mono tail head (touches_mono hs a) hw,ht,fun i hi => ha i (hs hi)⟩

theorem CompatibleAssignment.extend (hn : 1 ≤ n) (hbound : GiantBound n M)
    (names : Finset (Fin M)) (a : Fin M → Atom b) (a' : Fin M → Atom b')
    (h : CompatibleAssignment names a a') (i : Fin M) :
    ∃ e : Atom b ≃ Atom b', ∀ x,
      CompatibleAssignment (insert i (names.erase i)) (Function.update a i x) (Function.update a' i (e x)) := by
  obtain ⟨t,w,hw,ht,ha⟩ := h.mono (erase_subset i names)
  let T := touches (names.erase i) a
  have hcard : (names.erase i).card + 1 ≤ M := by
    have hsub : names.erase i ⊆ (univ : Finset (Fin M)).erase i := erase_subset_erase i (subset_univ _)
    have hh := card_le_card hsub
    have hpos := i.isLt
    rw [card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin] at hh
    omega
  have hj (J : Block n) : (T ∪ blockEdges J).card ≤ 6*M := by
    calc
      _ ≤ T.card + (blockEdges J).card := card_union_le _ _
      _ ≤ 6*(names.erase i).card + 6 := Nat.add_le_add (touches_card _ _) (blockEdges_card _)
      _ ≤ 6*M := by omega
  have hmove (J : Block n) := defect_transport hbound T (T ∪ blockEdges J)
    subset_union_left (hj J) t w hw ht
  choose tj wj hjg hjd hjs using hmove
  have hV : 2 ≤ Fintype.card (Vertex n) := by
    have hc : Fintype.card (Vertex n) = (n+1)^3 := by
      simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
    rw [hc]
    have hh : 2^3 ≤ (n+1)^3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have hv (v : Vertex n) : boundary (tj (.inr v)) v = b' v-b v := by
    have hwv : wj (.inr v) ≠ v := Flows.giant_ne_isolated tail head hV (hjg (.inr v)) (by
      intro e he
      exact mem_union_right _ (by simpa [blockEdges,incident,or_comm] using he))
    have hh := congrFun (hjd (.inr v)) v
    simpa [Pi.single_apply,Ne.symm hwv] using hh
  let e := blockShiftEquiv (fun e => tj (.inl e)) (fun v => tj (.inr v)) hv
  refine ⟨e,fun x => ?_⟩
  let J := atomBlock x
  refine ⟨tj J,wj J,?_,hjd J,?_⟩
  · rw [touches_insert_update]
    exact hjg J
  · intro j hj'
    rcases mem_insert.mp hj' with rfl | hj'
    · simp only [Function.update_self]
      cases x with
      | inl x => rcases x with ⟨f,s⟩; exact AtomShift.edge f s
      | inr x => rcases x with ⟨v,s⟩; exact AtomShift.config v s (hv v)
    · have hji := (mem_erase.mp hj').1
      simp only [Function.update_of_ne hji]
      exact (ha j hj').congr (fun f hf => (hjs J f (touch_subset_touches _ _ hj' hf)).symm)

theorem base_equivalence_numeric (hn : 1 ≤ n) (hbound : GiantBound n M) (vstar : Vertex n)
    (φ : Counting.Formula AnalysisSymbol (Fin M)) (hφ : φ.free = ∅)
    (a : Fin M → Atom (0 : Vertex n → Scalar))
    (a' : Fin M → Atom (Pi.single vstar 1)) :
    φ.eval (analysisStructure (0 : Vertex n → Scalar)) a ↔
      φ.eval (analysisStructure (Pi.single vstar 1)) a' := by
  have heq : ∀ (names : Finset (Fin M)) (v : Fin M → Atom (0 : Vertex n → Scalar))
      (w : Fin M → Atom (Pi.single vstar 1)), CompatibleAssignment names v w → ∀ i ∈ names, ∀ j ∈ names,
      (v i = v j ↔ w i = w j) := by
    intro names v w ⟨t,x,hg,hb,ha⟩ i hi j hj
    exact (ha i hi).equal_iff (ha j hj)
  have hrel : ∀ (names : Finset (Fin M)) (v : Fin M → Atom (0 : Vertex n → Scalar))
      (w : Fin M → Atom (Pi.single vstar 1)), CompatibleAssignment names v w → ∀ r i, i ∈ names → ∀ j, j ∈ names →
      ((analysisStructure (0 : Vertex n → Scalar)).rel r (v i) (v j) ↔
      (analysisStructure (Pi.single vstar 1)).rel r (w i) (w j)) := by
    intro names v w ⟨t,x,hg,hb,ha⟩ r i hi j hj
    exact (ha i hi).analysisRelation (ha j hj) r
  apply Counting.Formula.eval_of_partialBijectionSystem _ _ CompatibleAssignment heq hrel
    (fun names v w hh i => CompatibleAssignment.extend hn hbound names v w hh i) φ ∅ a a' _ (by simp [hφ])
  refine ⟨0,vstar,?_,by simp,by simp⟩
  simpa [touches] using grid_empty_giant vstar

end CPTSeparation.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Hereditary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Hereditary

variable {A B : Type*}

attribute [local instance] CPTSeparation.Hereditary.instDecidableEqHF

theorem atom_injective : Function.Injective (atom : A → HF A) := by
  intro a b h
  have h' := Lists.equiv_atom.mp (mk_eq_mk.mp h)
  cases h'
  rfl

theorem ofFinset_elements {x : HF A} (hx : isSet x = true) : ofFinset (elements x) = x := by
  apply ext_sets (isSet_ofFinset _) hx
  intro z
  rw [mem_ofFinset]
  rfl

theorem atom_or_set (x : HF A) : (∃ a, x = atom a) ∨ x = ofFinset (elements x) := by
  induction x using Quotient.inductionOn with
  | _ l =>
    rcases l with ⟨(_ | _), l⟩
    · cases l with
      | atom a => exact Or.inl ⟨a,rfl⟩
    · exact Or.inr (ofFinset_elements rfl).symm

theorem mem_wellFounded : WellFounded (fun x y : HF A => x ∈ y) :=
  (measure rank).wf.mono (fun _ _ h => rank_lt_of_mem h)

end CPTSeparation.Hereditary

namespace CPTSeparation.Forms

open Classical

open Counting Hereditary

variable {R I J A B : Type*}

theorem swap_type [Fintype J] [DecidableEq I] [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ⊕ J ↪ I)
    (a b : J → A) (a' b' : J → B)
    (h : tupleType S e (Sum.elim a b) = tupleType T e (Sum.elim a' b')) :
    tupleType S e (Sum.elim b a) = tupleType T e (Sum.elim b' a') := by
  have ht := tupleType_project S T e e (Equiv.sumComm J J).toEmbedding _ _ h
  have h1 : Sum.elim a b ∘ (Equiv.sumComm J J).toEmbedding = Sum.elim b a := by
    funext j; cases j <;> rfl
  have h2 : Sum.elim a' b' ∘ (Equiv.sumComm J J).toEmbedding = Sum.elim b' a' := by
    funext j; cases j <;> rfl
  simpa only [h1,h2] using ht

section AtomicTransfer

variable [Fintype I] [Fintype J] [DecidableEq I]

variable [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

variable (S : Structure R A) (T : Structure R B)

variable (e2 : J ⊕ J ↪ I) (e3 : (J ⊕ J) ⊕ J ↪ I)

variable (e4 : ((J ⊕ J) ⊕ J) ⊕ J ↪ I)

open Form

include e3 e4

private theorem set_subset_transfer
    (n k : ℕ) (child : Fin n → Form J (Set (Formula R I)))
    (other : Fin k → Form J (Set (Formula R I)))
    (label : Fin n → Set (Formula R I)) (lab : Fin k → Set (Formula R I))
    (hc : ∀ i j (c d : J → A) (c' d' : J → B),
      tupleType S e2 (Sum.elim c d) = tupleType T e2 (Sum.elim c' d') →
      (value S e2 (child i) c = value S e2 (other j) d ↔
        value T e2 (child i) c' = value T e2 (other j) d'))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b'))
    (hsub : ∀ x, x ∈ value S e2 (.set n child label) a →
      x ∈ value S e2 (.set k other lab) b) :
    ∀ x, x ∈ value T e2 (.set n child label) a' →
      x ∈ value T e2 (.set k other lab) b' := by
  intro x hx
  obtain ⟨i,c',hl,rfl⟩ := (mem_value_set T e2 n child label a' x).mp hx
  obtain ⟨c,h3⟩ := tupleType_append T S e2 e3 (Sum.elim a' b') (Sum.elim a b) c' ht.symm
  have hca := tupleType_project T S e3 e2 cross31 _ _ h3
  simp only [elim_comp_cross31] at hca
  have hmem : value S e2 (child i) c ∈ value S e2 (.set n child label) a :=
    (mem_value_set S e2 n child label a _).mpr ⟨i,c,hca.symm.trans hl,rfl⟩
  obtain ⟨j,d,hlab,heq⟩ := (mem_value_set S e2 k other lab b _).mp (hsub _ hmem)
  obtain ⟨d',h4⟩ := tupleType_append S T e3 e4 (Sum.elim (Sum.elim a b) c)
    (Sum.elim (Sum.elim a' b') c') d h3.symm
  have hdb := tupleType_project S T e4 e2 cross42 _ _ h4
  have hcd := tupleType_project S T e4 e2 cross34 _ _ h4
  simp only [elim_comp_cross42] at hdb
  simp only [elim_comp_cross34] at hcd
  exact (mem_value_set T e2 k other lab b' _).mpr
    ⟨j,d',hdb.symm.trans hlab,((hc i j c d c' d' hcd).mp heq.symm).symm⟩

private theorem set_eq_forward
    (n k : ℕ) (child : Fin n → Form J (Set (Formula R I)))
    (other : Fin k → Form J (Set (Formula R I)))
    (label : Fin n → Set (Formula R I)) (lab : Fin k → Set (Formula R I))
    (hc : ∀ i j (c d : J → A) (c' d' : J → B),
      tupleType S e2 (Sum.elim c d) = tupleType T e2 (Sum.elim c' d') →
      (value S e2 (child i) c = value S e2 (other j) d ↔
        value T e2 (child i) c' = value T e2 (other j) d'))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b'))
    (h : value S e2 (.set n child label) a = value S e2 (.set k other lab) b) :
    value T e2 (.set n child label) a' = value T e2 (.set k other lab) b' := by
  apply Hereditary.ext_sets (by simp) (by simp)
  intro x
  constructor
  · exact set_subset_transfer S T e2 e3 e4 n k child other label lab hc a b a' b' ht
      (fun z hz => by rw [←h]; exact hz) x
  · apply set_subset_transfer S T e2 e3 e4 k n other child lab label
      (fun j i c d c' d' ht' => ?_) b a b' a' (swap_type S T e2 a b a' b' ht)
      (fun z hz => by rw [h]; exact hz) x
    have hh := hc i j d c d' c' (swap_type S T e2 c d c' d' ht')
    exact ⟨fun he => (hh.mp he.symm).symm,fun he => (hh.mpr he.symm).symm⟩

theorem equality_transfer (φ ψ : Form J (Set (Formula R I)))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b')) :
    value S e2 φ a = value S e2 ψ b ↔ value T e2 φ a' = value T e2 ψ b' := by
  induction φ generalizing ψ a b a' b' with
  | atom i =>
    cases ψ with
    | atom j =>
      have he := (typeOf_eq_iff S T (tupleNames e2) _ _).mp ht
        (.equal (e2 (.inl i)) (e2 (.inr j))) (by
          intro p hp
          simp only [Formula.free,Finset.mem_insert,Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> exact (mem_tupleNames _ _).mpr ⟨_,rfl⟩)
      simpa only [Formula.eval,tupleAssignment_apply,Sum.elim_inl,Sum.elim_inr,
        value_atom,Hereditary.atom_injective.eq_iff] using he
    | set k other lab =>
      have hfalseA : value S e2 (.atom i) a ≠ value S e2 (.set k other lab) b := by
        intro h; have hh := congrArg isSet h; simp at hh
      have hfalseB : value T e2 (.atom i) a' ≠ value T e2 (.set k other lab) b' := by
        intro h; have hh := congrArg isSet h; simp at hh
      exact iff_of_false hfalseA hfalseB
  | set n child label ih =>
    cases ψ with
    | atom j =>
      have hfalseA : value S e2 (.set n child label) a ≠ value S e2 (.atom j) b := by
        intro h; have hh := congrArg isSet h; simp at hh
      have hfalseB : value T e2 (.set n child label) a' ≠ value T e2 (.atom j) b' := by
        intro h; have hh := congrArg isSet h; simp at hh
      exact iff_of_false hfalseA hfalseB
    | set k other lab =>
      constructor
      · exact set_eq_forward S T e2 e3 e4 n k child other label lab
          (fun i j c d c' d' ht' => ih i (other j) c d c' d' ht') a b a' b' ht
      · exact set_eq_forward T S e2 e3 e4 n k child other label lab
          (fun i j c' d' c d ht' => (ih i (other j) c d c' d' ht'.symm).symm)
          a' b' a b ht.symm

private theorem membership_forward (φ : Form J (Set (Formula R I)))
    (k : ℕ) (other : Fin k → Form J (Set (Formula R I)))
    (lab : Fin k → Set (Formula R I))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b'))
    (hm : value S e2 φ a ∈ value S e2 (.set k other lab) b) :
    value T e2 φ a' ∈ value T e2 (.set k other lab) b' := by
  obtain ⟨i,c,hl,heq⟩ := (mem_value_set S e2 k other lab b _).mp hm
  obtain ⟨c',h3⟩ := tupleType_append S T e2 e3 (Sum.elim b a) (Sum.elim b' a') c
    (swap_type S T e2 a b a' b' ht)
  have hcb := tupleType_project S T e3 e2 cross31 _ _ h3
  simp only [elim_comp_cross31] at hcb
  let u : J ⊕ J ↪ (J ⊕ J) ⊕ J :=
    cross31.trans (Function.Embedding.sumMap (Equiv.sumComm J J).toEmbedding
      (Function.Embedding.refl J))
  have hca := tupleType_project S T e3 e2 u _ _ h3
  have hueq (a b c : J → A) : Sum.elim (Sum.elim b a) c ∘ u = Sum.elim c a := by
    funext j; cases j <;> rfl
  have hueq' (a b c : J → B) : Sum.elim (Sum.elim b a) c ∘ u = Sum.elim c a := by
    funext j; cases j <;> rfl
  rw [hueq,hueq'] at hca
  exact (mem_value_set T e2 k other lab b' _).mpr ⟨i,c',hcb.symm.trans hl,
    (equality_transfer S T e2 e3 e4 (other i) φ c a c' a' hca).mp heq⟩

theorem membership_transfer (φ ψ : Form J (Set (Formula R I)))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b')) :
    value S e2 φ a ∈ value S e2 ψ b ↔ value T e2 φ a' ∈ value T e2 ψ b' := by
  cases ψ with
  | atom j => simp
  | set k other lab =>
    exact ⟨membership_forward S T e2 e3 e4 φ k other lab a b a' b' ht,
      membership_forward T S e2 e3 e4 φ k other lab a' b' a b ht.symm⟩

end AtomicTransfer

variable {G : Type*} [Group G] [MulAction G A]

variable [finiteI : Fintype I] [DecidableEq I] [finiteA : Fintype A] [nonemptyA : Nonempty A] {s : ℕ}

variable (S : Structure R A) (e2 : Fin s ⊕ Fin s ↪ I)

variable (hAut : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

open Form

omit A G s in
private theorem hereditary_mem.{uDecl4, uDecl6}
    {A : Type uDecl4}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    [Fintype A]
    [Nonempty A]
    {s : ℕ} {x y : HF A}
    (hx : HereditarilySupported (G := G) s x) (hy : y ∈ x) :
    HereditarilySupported (G := G) s y := by
  intro z hz
  exact hx z (hz.trans (Relation.ReflTransGen.single hy))

omit A G in
private theorem smul_mem.{uDecl4, uDecl6}
    {A : Type uDecl4}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    [Fintype A]
    [Nonempty A] (g : G) {x y : HF A} (h : y ∈ x) : g • y ∈ g • x := by
  change Hereditary.map (fun a => g • a) y ∈
    elements (Hereditary.map (fun a => g • a) x)
  let := Hereditary.instDecidableEqHF (A := A)
  rw [elements_map]
  exact Finset.mem_image.mpr ⟨y,h,rfl⟩

include hAut in

omit R I A G s S e2 hAut in
theorem representation.{uDecl1, uDecl2, uDecl4, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl4}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    {s : ℕ}
    (S : Counting.Structure R A)
    (e2 : Fin s ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b) (hs : 0 < s)
    (hHom : ∀ p q : Fin s ⊕ Fin s → A,
      tupleType S e2 p = tupleType S e2 q → ∃ g : G, ∀ i, g • p i = q i)
    (x : HF A) (hx : HereditarilySupported (G := G) s x) :
    ∃ φ : Form (Fin s) (Set (Formula R I)), ∃ a : Fin s → A, value S e2 φ a = x := by
  induction x using mem_wellFounded.induction with
  | h x ih =>
    rcases atom_or_set x with ⟨b,rfl⟩ | hxset
    · exact ⟨.atom ⟨0,hs⟩,fun _ => b,rfl⟩
    · obtain ⟨a,ha⟩ := hx x Relation.ReflTransGen.refl
      have hr : ∀ y : {y // y ∈ elements x},
          ∃ φ : Form (Fin s) (Set (Formula R I)), ∃ b : Fin s → A,
            value S e2 φ b = y.1 := by
        intro y
        exact ih y.1 y.2 (hereditary_mem hx y.2)
      choose form mol hvalue using hr
      let n := Fintype.card {y // y ∈ elements x}
      let en : Fin n ≃ {y // y ∈ elements x} := (Fintype.equivFin _).symm
      let child : Fin n → Form (Fin s) (Set (Formula R I)) := fun i => form (en i)
      let β : Fin n → Fin s → A := fun i => mol (en i)
      let label : Fin n → Set (Formula R I) := fun i => tupleType S e2 (Sum.elim (β i) a)
      refine ⟨.set n child label,a,?_⟩
      apply Hereditary.ext_sets (by simp) (by rw [hxset]; rfl)
      intro y
      constructor
      · intro hy
        obtain ⟨i,b,ht,rfl⟩ := (mem_value_set S e2 n child label a y).mp hy
        obtain ⟨g,hg⟩ := hHom (Sum.elim (β i) a) (Sum.elim b a) ht.symm
        have hga : ∀ j, g • a j = a j := fun j => hg (.inr j)
        have hgb : (fun j => g • β i j) = b := funext (fun j => hg (.inl j))
        have hyx : (en i).1 ∈ x := (en i).2
        have hmap := smul_mem g hyx
        rw [ha g hga] at hmap
        have hv : value S e2 (child i) b = g • (en i).1 := by
          rw [←hgb,←value_smul S e2 hAut]
          exact congrArg (fun z : HF A => g • z) (hvalue (en i))
        rw [hv]
        exact hmap
      · intro hy
        let y' : {y // y ∈ elements x} := ⟨y,hy⟩
        let i := en.symm y'
        apply (mem_value_set S e2 n child label a y).mpr
        refine ⟨i,β i,rfl,?_⟩
        have hv := hvalue (en i)
        simpa only [child,β,i,Equiv.apply_symm_apply] using hv

end CPTSeparation.Forms

namespace CPTSeparation.Counting

open Classical

variable {R I J A B : Type*} [DecidableEq I]

variable [Fintype I] [Fintype J] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

theorem tupleType_append_one_bijection (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (E : J ⊕ Unit ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) :
    ∃ f : A ≃ B, ∀ x, tupleType S E (Sum.elim a (fun _ => x)) =
      tupleType T E (Sum.elim b (fun _ => f x)) := by
  let ep := Function.Embedding.inl.trans E
  let i := E (Sum.inr ())
  have hp := tupleType_project S T e ep (Function.Embedding.refl J) a b ht
  change tupleType S ep a = tupleType T ep b at hp
  have hi : i ∉ tupleNames ep := by
    rintro hh
    obtain ⟨j,hj⟩ := (mem_tupleNames ep i).mp hh
    have hh := E.injective hj
    cases hh
  have hn : insert i (tupleNames ep) = tupleNames E := by
    ext p
    simp only [Finset.mem_insert,mem_tupleNames]
    constructor
    · rintro (rfl|⟨j,rfl⟩)
      · exact ⟨Sum.inr (),rfl⟩
      · exact ⟨Sum.inl j,rfl⟩
    · rintro ⟨j,rfl⟩
      rcases j with j|u
      · exact Or.inr ⟨j,rfl⟩
      · cases u; exact Or.inl rfl
  have ha (x : A) : tupleType S E (Sum.elim a (fun _ => x)) =
      typeOf S (tupleNames E) (Function.update (tupleAssignment ep a) i x) := by
    apply tupleType_assignment
    intro j
    rcases j with j|u
    · have hne : E (Sum.inl j) ≠ i := by
        intro h; have hh := E.injective h; cases hh
      rw [Function.update_of_ne hne]
      exact tupleAssignment_apply ep a j
    · cases u; simp [i]
  have hb (x : B) : tupleType T E (Sum.elim b (fun _ => x)) =
      typeOf T (tupleNames E) (Function.update (tupleAssignment ep b) i x) := by
    apply tupleType_assignment
    intro j
    rcases j with j|u
    · have hne : E (Sum.inl j) ≠ i := by
        intro h; have hh := E.injective h; cases hh
      rw [Function.update_of_ne hne]
      exact tupleAssignment_apply ep b j
    · cases u; simp [i]
  obtain ⟨f,hf⟩ := extension_bijection S T (tupleNames ep) i hi
    (tupleAssignment ep a) (tupleAssignment ep b) hp
  refine ⟨f,fun x => ?_⟩
  rw [ha,hb]
  simpa only [hn] using hf x

theorem tupleType_append_fin_bijection (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (n : ℕ) (E : J ⊕ Fin n ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) :
    ∃ f : (Fin n → A) ≃ (Fin n → B), ∀ c,
      tupleType S E (Sum.elim a c) = tupleType T E (Sum.elim b (f c)) := by
  induction n with
  | zero =>
    let f : (Fin 0 → A) ≃ (Fin 0 → B) :=
      ⟨fun _ => Fin.elim0,fun _ => Fin.elim0,
        fun _ => Subsingleton.elim _ _,fun _ => Subsingleton.elim _ _⟩
    refine ⟨f,fun c => ?_⟩
    let u : J ⊕ Fin 0 ↪ J :=
      ⟨Sum.elim id Fin.elim0,by
        intro x y h
        rcases x with x|x
        · rcases y with y|y
          · exact congrArg Sum.inl h
          · exact Fin.elim0 y
        · exact Fin.elim0 x⟩
    have h := tupleType_project S T e E u a b ht
    have ha : a ∘ u = Sum.elim a c := by
      funext j; rcases j with j|i
      · rfl
      · exact Fin.elim0 i
    have hb : b ∘ u = Sum.elim b (f c) := by
      funext j; rcases j with j|i
      · rfl
      · exact Fin.elim0 i
    simpa only [ha,hb] using h
  | succ n ih =>
    let pre : J ⊕ Fin n ↪ J ⊕ Fin (n+1) :=
      Function.Embedding.sumMap (Function.Embedding.refl J) Fin.castSuccEmb
    let ep := pre.trans E
    obtain ⟨f,hf⟩ := ih ep
    let E1 := (appendPosition J n).toEmbedding.trans E
    have h1 (c : Fin n → A) : ∃ g : A ≃ B, ∀ x,
        tupleType S E1 (Sum.elim (Sum.elim a c) (fun _ => x)) =
        tupleType T E1 (Sum.elim (Sum.elim b (f c)) (fun _ => g x)) :=
      tupleType_append_one_bijection S T ep E1 _ _ (hf c)
    choose g hg using h1
    let F := (snocEquiv (A:=A) n).trans
      ((triangular f g).trans (snocEquiv (A:=B) n).symm)
    refine ⟨F,fun c => ?_⟩
    have hh := tupleType_project S T E1 E (appendPosition J n).symm.toEmbedding
      _ _ (hg (fun i => c i.castSucc) (c (Fin.last n)))
    have ha : (Sum.elim (Sum.elim a (fun i => c i.castSucc))
        (fun _ => c (Fin.last n))) ∘ (appendPosition J n).symm = Sum.elim a c := by
      funext j
      rcases j with j|i
      · rfl
      · induction i using Fin.lastCases <;> simp [appendPosition]
    have hb : (Sum.elim (Sum.elim b (f (fun i => c i.castSucc)))
        (fun _ => g (fun i => c i.castSucc) (c (Fin.last n)))) ∘
        (appendPosition J n).symm = Sum.elim b (F c) := by
      funext j
      rcases j with j|i
      · rfl
      · induction i using Fin.lastCases <;>
          simp [appendPosition,F,snocEquiv,triangular,snocTuple]
    simpa only [Equiv.coe_toEmbedding,ha,hb] using hh

theorem tupleType_append_bijection {D : Type*} [Fintype D]
    (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (E : J ⊕ D ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) :
    ∃ f : (D → A) ≃ (D → B), ∀ c,
      tupleType S E (Sum.elim a c) = tupleType T E (Sum.elim b (f c)) := by
  let en := Fintype.equivFin D
  let E' := (Equiv.sumCongr (Equiv.refl J) en.symm).toEmbedding.trans E
  obtain ⟨f,hf⟩ := tupleType_append_fin_bijection S T e (Fintype.card D) E' a b ht
  let F := (Equiv.arrowCongr en (Equiv.refl A)).trans
    (f.trans (Equiv.arrowCongr en.symm (Equiv.refl B)))
  refine ⟨F,fun c => ?_⟩
  have hh := tupleType_project S T E' E
    (Equiv.sumCongr (Equiv.refl J) en).toEmbedding _ _ (hf (c ∘ en.symm))
  have ha : (Sum.elim a (c ∘ en.symm)) ∘ (Equiv.sumCongr (Equiv.refl J) en) =
      Sum.elim a c := by
    funext j; rcases j with j|j <;> simp
  have hb : (Sum.elim b (f (c ∘ en.symm))) ∘ (Equiv.sumCongr (Equiv.refl J) en) =
      Sum.elim b (F c) := by
    funext j; rcases j with j|j <;> rfl
  simpa only [Equiv.coe_toEmbedding,ha,hb] using hh

theorem tupleType_extension_equiv {D : Type*} [Fintype D]
    (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (E : J ⊕ D ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) (τ : Set (Formula R I)) :
    Nonempty ({c : D → A // tupleType S E (Sum.elim a c) = τ} ≃
      {d : D → B // tupleType T E (Sum.elim b d) = τ}) := by
  obtain ⟨f,hf⟩ := tupleType_append_bijection S T e E a b ht
  exact ⟨f.subtypeEquiv (fun c => by rw [hf c])⟩

end CPTSeparation.Counting

end

end OAI
end

section
-- module Solutions.OAIQW_CPTSeparation.Forms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CPTSeparation.Forms

open Classical Counting Hereditary

open scoped BigOperators

private theorem card_eq_mul_fiber {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (y₀ : Y)
    (h : ∀ y, Fintype.card {x // f x = y} = Fintype.card {x // f x = y₀}) :
    Fintype.card X = Fintype.card Y * Fintype.card {x // f x = y₀} := by
  calc
    Fintype.card X = Fintype.card (Σ y, {x // f x = y}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ y, Fintype.card {x // f x = y} := Fintype.card_sigma
    _ = _ := by simp only [h,Finset.sum_const,Finset.card_univ,smul_eq_mul]

private theorem range_card_mul_fiber {X Y : Type*} [Fintype X]
    (f : X → Y) (x₀ : X)
    (h : ∀ x, Nat.card {z // f z = f x} = Nat.card {z // f z = f x₀}) :
    Fintype.card X = Nat.card (Set.range f) * Nat.card {z // f z = f x₀} := by
  let := (Set.finite_range f).fintype
  let fR : X → Set.range f := fun x => ⟨f x,⟨x,rfl⟩⟩
  have k (y : Set.range f) : Nat.card {x // fR x = y} =
      Nat.card {z // f z = f x₀} := by
    have hp (x : X) : fR x = y ↔ f x = y.1 := Subtype.ext_iff
    rw [Nat.card_congr (Equiv.subtypeEquivRight hp)]
    obtain ⟨x,hx⟩ := y.2
    rw [←hx]
    exact h x
  have hh := card_eq_mul_fiber fR (fR x₀) (fun y => by
    simpa only [←Nat.card_eq_fintype_card] using (k y).trans (k (fR x₀)).symm)
  have hh' : Nat.card X = Nat.card (Set.range f) * Nat.card {x // fR x = fR x₀} := by
    simpa only [←Nat.card_eq_fintype_card] using hh
  rw [k] at hh'
  simpa only [←Nat.card_eq_fintype_card] using hh'

variable {R I A B P : Type*} [finiteI : Fintype I] [DecidableEq I]

variable [finiteA : Fintype A] [Fintype B] [nonemptyA : Nonempty A] [Nonempty B] [finiteP : Fintype P]

variable {s : ℕ}

section Group

variable {G : Type*} [Group G] [MulAction G A]

variable (S : Structure R A) (ep : P ⊕ Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)

variable (hAut : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (p : P → A) (τ : Set (Formula R I))

include hAut in

omit R I A P s G S ep e2 hAut p τ in
theorem uniform_value_fibers.{uDecl1, uDecl2, uDecl3, uDecl5, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {P : Type uDecl5}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    [Fintype P]
    {s : ℕ}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    (S : Counting.Structure R A)
    (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (p : P → A)
    (τ : Set (Counting.Formula R I))
    (hHom : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (φ : Form (Fin s) (Set (Formula R I))) (a a' : Molecules S ep p τ) :
    Fintype.card {b : Molecules S ep p τ // Form.value S e2 φ b.1 = Form.value S e2 φ a.1} =
    Fintype.card {b : Molecules S ep p τ // Form.value S e2 φ b.1 = Form.value S e2 φ a'.1} := by
  obtain ⟨g,hg⟩ := hHom (Sum.elim p a.1) (Sum.elim p a'.1) (a.2.trans a'.2.symm)
  have hp : ∀ i, g • p i = p i := fun i => hg (.inl i)
  have ha : (fun i => g • a.1 i) = a'.1 := funext (fun i => hg (.inr i))
  let f := moleculesPerm S ep hAut p τ g hp
  have hv (b : Molecules S ep p τ) :
      Form.value S e2 φ (f b).1 = g • Form.value S e2 φ b.1 := by
    exact (value_smul S e2 hAut g φ b.1).symm
  have hv' : Form.value S e2 φ a'.1 = g • Form.value S e2 φ a.1 := by
    rw [←ha]
    exact (value_smul S e2 hAut g φ a.1).symm
  apply Fintype.card_congr
  apply f.subtypeEquiv
  intro b
  rw [hv,hv']
  exact (MulAction.injective g).eq_iff.symm

omit R I A P s G S ep e2 hAut p τ in
private theorem label_orbit.{uDecl1, uDecl2, uDecl3, uDecl5, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {P : Type uDecl5}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    [Fintype P]
    {s : ℕ}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    (S : Counting.Structure R A)
    (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (p : P → A)
    (τ : Set (Counting.Formula R I))
    (hHom : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (φ : Form (Fin s) (Set (Formula R I))) (x y : HF A)
    (hx : x ∈ labelValues S ep e2 p τ φ) (hy : y ∈ labelValues S ep e2 p τ φ) :
    ∃ g : G, (∀ i, g • p i = p i) ∧ g • x = y := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  obtain ⟨g,hg⟩ := hHom (Sum.elim p a.1) (Sum.elim p b.1) (a.2.trans b.2.symm)
  refine ⟨g,fun i => hg (.inl i),?_⟩
  rw [value_smul S e2 hAut]
  exact congrArg (Form.value S e2 φ) (funext (fun i => hg (.inr i)))

omit R I A P s G S ep e2 hAut p τ in
private theorem label_smul_mem.{uDecl1, uDecl2, uDecl3, uDecl5, uDecl6}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {P : Type uDecl5}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    [Fintype P]
    {s : ℕ}
    {G : Type uDecl6}
    [Group G]
    [MulAction G A]
    (S : Counting.Structure R A)
    (ep : P ⊕ Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I)
    (hAut : ∀ (g : G) (r : R) (a b : A), S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (p : P → A)
    (τ : Set (Counting.Formula R I)) (g : G) (hp : ∀ i, g • p i = p i)
    (φ : Form (Fin s) (Set (Formula R I))) (x : HF A)
    (hx : x ∈ labelValues S ep e2 p τ φ) : g • x ∈ labelValues S ep e2 p τ φ := by
  obtain ⟨a,rfl⟩ := hx
  refine ⟨moleculesPerm S ep hAut p τ g hp a,?_⟩
  exact (value_smul S e2 hAut g φ a.1).symm

include hAut in

theorem label_partition
    (hHom : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (φ ψ : Form (Fin s) (Set (Formula R I))) (σ : Set (Formula R I)) (x : HF A)
    (hx : x ∈ labelValues S ep e2 p τ φ) (hx' : x ∈ labelValues S ep e2 p σ ψ) :
    labelValues S ep e2 p τ φ = labelValues S ep e2 p σ ψ := by
  ext y
  constructor
  · intro hy
    obtain ⟨g,hp,hg⟩ := label_orbit S ep e2 hAut p τ hHom φ x y hx hy
    rw [←hg]
    exact label_smul_mem S ep e2 hAut p σ g hp ψ x hx'
  · intro hy
    obtain ⟨g,hp,hg⟩ := label_orbit S ep e2 hAut p σ hHom ψ x y hx' hy
    rw [←hg]
    exact label_smul_mem S ep e2 hAut p τ g hp φ x hx

end Group

variable (S : Structure R A) (T : Structure R B)

variable (ep : P ⊕ Fin s ↪ I) (epp : (P ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e2 : Fin s ⊕ Fin s ↪ I)

variable (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

include epp e3 e4 in

theorem value_fiber_equiv (p : P → A) (q : P → B) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I)))
    (a : Molecules S ep p τ) (a' : Molecules T ep q τ) :
    Nonempty ({b : Molecules S ep p τ // Form.value S e2 φ b.1 = Form.value S e2 φ a.1} ≃
    {b : Molecules T ep q τ // Form.value T e2 φ b.1 = Form.value T e2 φ a'.1}) := by
  obtain ⟨f,hf⟩ := tupleType_append_bijection S T ep epp
    (Sum.elim p a.1) (Sum.elim q a'.1) (a.2.trans a'.2.symm)
  have htype (b : Fin s → A) : tupleType S ep (Sum.elim p b) =
      tupleType T ep (Sum.elim q (f b)) := by
    have hh := tupleType_project S T epp ep skipMiddle _ _ (hf b)
    simpa only [elim_skipMiddle] using hh
  have hval (b : Fin s → A) : Form.value S e2 φ b = Form.value S e2 φ a.1 ↔
      Form.value T e2 φ (f b) = Form.value T e2 φ a'.1 := by
    have hh := tupleType_project S T epp e2 lastTwo _ _ (hf b)
    simp only [elim_lastTwo] at hh
    simpa only [eq_comm] using equality_transfer S T e2 e3 e4 φ φ a.1 b a'.1 (f b) hh
  let F : {b : Fin s → A // tupleType S ep (Sum.elim p b) = τ ∧
      Form.value S e2 φ b = Form.value S e2 φ a.1} ≃
      {b : Fin s → B // tupleType T ep (Sum.elim q b) = τ ∧
      Form.value T e2 φ b = Form.value T e2 φ a'.1} := f.subtypeEquiv (fun b => show
      (tupleType S ep (Sum.elim p b) = τ ∧ Form.value S e2 φ b = Form.value S e2 φ a.1) ↔
      (tupleType T ep (Sum.elim q (f b)) = τ ∧ Form.value T e2 φ (f b) = Form.value T e2 φ a'.1)
    from and_congr (by rw [htype b]) (hval b))
  exact ⟨(Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    (F.trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)⟩

include epp e3 e4 in

theorem label_overlap_transfer (e0 : P ↪ I) (p : P → A) (q : P → B)
    (hp : tupleType S e0 p = tupleType T e0 q)
    (φ ψ : Form (Fin s) (Set (Formula R I))) (τ σ : Set (Formula R I))
    (hx : ∃ x, x ∈ labelValues S ep e2 p τ φ ∧ x ∈ labelValues S ep e2 p σ ψ) :
    ∃ y, y ∈ labelValues T ep e2 q τ φ ∧ y ∈ labelValues T ep e2 q σ ψ := by
  obtain ⟨x,⟨a,ha⟩,⟨b,hb⟩⟩ := hx
  obtain ⟨a',ha'⟩ := tupleType_append S T e0 ep p q a.1 hp
  obtain ⟨b',hb'⟩ := tupleType_append S T ep epp
    (Sum.elim p a.1) (Sum.elim q a') b.1 ha'
  have ht := tupleType_project S T epp ep skipMiddle _ _ hb'
  simp only [elim_skipMiddle] at ht
  have he := tupleType_project S T epp e2 lastTwo _ _ hb'
  simp only [elim_lastTwo] at he
  have hv := (equality_transfer S T e2 e3 e4 φ ψ a.1 b.1 a' b' he).mp (ha.trans hb.symm)
  refine ⟨Form.value T e2 φ a',?_,?_⟩
  · exact ⟨⟨a',ha'.symm.trans a.2⟩,rfl⟩
  · exact ⟨⟨b',ht.symm.trans b.2⟩,hv.symm⟩

include epp e3 e4 in

theorem label_values_card
    {G H : Type*} [Group G] [MulAction G A] [Group H] [MulAction H B]
    (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)
    (hHomA : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : P ⊕ Fin s → B,
      tupleType T ep a = tupleType T ep b → ∃ g : H, ∀ i, g • a i = b i)
    (p : P → A) (q : P → B) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I)))
    (a : Molecules S ep p τ) (a' : Molecules T ep q τ) :
    Nat.card (labelValues S ep e2 p τ φ) = Nat.card (labelValues T ep e2 q τ φ) := by
  let va : Molecules S ep p τ → HF A := fun b => Form.value S e2 φ b.1
  let vb : Molecules T ep q τ → HF B := fun b => Form.value T e2 φ b.1
  have ha := range_card_mul_fiber va a (fun b => by simpa only [←Nat.card_eq_fintype_card] using uniform_value_fibers S ep e2 hAutA p τ hHomA φ b a)
  have hb := range_card_mul_fiber vb a' (fun b => by simpa only [←Nat.card_eq_fintype_card] using uniform_value_fibers T ep e2 hAutB q τ hHomB φ b a')
  let e0 := Function.Embedding.inl.trans ep
  have hp := tupleType_project S T ep e0 Function.Embedding.inl
    (Sum.elim p a.1) (Sum.elim q a'.1) (a.2.trans a'.2.symm)
  change tupleType S e0 p = tupleType T e0 q at hp
  obtain ⟨f⟩ := tupleType_extension_equiv S T e0 ep p q hp τ
  have hn : Fintype.card (Molecules S ep p τ) = Fintype.card (Molecules T ep q τ) :=
    Fintype.card_congr f
  obtain ⟨fv⟩ := value_fiber_equiv S T ep epp e2 e3 e4 p q τ φ a a'
  have he : Nat.card {b // va b = va a} = Nat.card {b // vb b = vb a'} :=
    Nat.card_congr fv
  have hpos : 0 < Nat.card {b // va b = va a} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨⟨a,rfl⟩⟩
  have hc := ha.symm.trans (hn.trans hb)
  rw [←he] at hc
  have hh := Nat.eq_of_mul_eq_mul_right hpos hc
  simpa only [←Nat.card_eq_fintype_card,labelValues,va,vb] using hh

end CPTSeparation.Forms

namespace CPTSeparation

open Classical

theorem glue_finite_cells {L X Y : Type*} (C : L → Set X) (D : L → Set Y)
    (coverC : ∀ x, ∃ l, x ∈ C l) (coverD : ∀ y, ∃ l, y ∈ D l)
    (partC : ∀ l k x, x ∈ C l → x ∈ C k → C l = C k)
    (partD : ∀ l k y, y ∈ D l → y ∈ D k → D l = D k)
    (same : ∀ l k, C l = C k ↔ D l = D k)
    (finC : ∀ l, (C l).Finite) (finD : ∀ l, (D l).Finite)
    (card : ∀ l, Nat.card (C l) = Nat.card (D l)) :
    ∃ f : X ≃ Y, ∀ x, ∃ l, x ∈ C l ∧ f x ∈ D l := by
  let Q := Quotient (cellSetoid C)
  let lc : X → L := fun x => (coverC x).choose
  let ld : Y → L := fun y => (coverD y).choose
  have hc (x : X) : x ∈ C (lc x) := (coverC x).choose_spec
  have hd (y : Y) : y ∈ D (ld y) := (coverD y).choose_spec
  let c : X → Q := fun x => Quotient.mk _ (lc x)
  let d : Y → Q := fun y => Quotient.mk _ (ld y)
  have ce (x : X) (q : Q) : c x = q ↔ x ∈ C q.out := by
    constructor
    · intro h
      have he : C (lc x) = C q.out := Quotient.exact (h.trans (Quotient.out_eq q).symm)
      rw [←he]; exact hc x
    · intro h
      have he := partC (lc x) q.out x (hc x) h
      exact (Quotient.sound he).trans (Quotient.out_eq q)
  have de (y : Y) (q : Q) : d y = q ↔ y ∈ D q.out := by
    constructor
    · intro h
      have he : C (ld y) = C q.out := Quotient.exact (h.trans (Quotient.out_eq q).symm)
      rw [←(same _ _).mp he]; exact hd y
    · intro h
      have he := (same _ _).mpr (partD (ld y) q.out y (hd y) h)
      exact (Quotient.sound he).trans (Quotient.out_eq q)
  have ef (q : Q) : Nonempty ({x // c x = q} ≃ {y // d y = q}) := by
    let := (finC q.out).fintype
    let := (finD q.out).fintype
    have hcard : Fintype.card (C q.out) = Fintype.card (D q.out) := by
      simpa only [Nat.card_eq_fintype_card] using card q.out
    let e := Fintype.equivOfCardEq hcard
    exact ⟨(Equiv.subtypeEquivRight (fun x => ce x q)).trans
      (e.trans (Equiv.subtypeEquivRight (fun y => de y q)).symm)⟩
  let F := Equiv.ofFiberEquiv (fun q => Classical.choice (ef q))
  refine ⟨F,fun x => ⟨(c x).out,(ce x (c x)).mp rfl,?_⟩⟩
  apply (de (F x) (c x)).mp
  exact Equiv.ofFiberEquiv_map _ x

end CPTSeparation

namespace CPTSeparation.Forms

section

open Classical Counting Hereditary

variable {R I A B P G H : Type*}

variable [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

variable [Nonempty A] [Nonempty B] [Fintype P]

variable [Group G] [MulAction G A] [Group H] [MulAction H B]

variable {s : ℕ}

variable (S : Structure R A) (T : Structure R B)

variable (ep : P ⊕ Fin s ↪ I) (epp : (P ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e2 : Fin s ⊕ Fin s ↪ I) (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

variable (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)

include hAutA in
private theorem cell_finite (p : P → A) (φ : Form (Fin s) (Set (Formula R I))) (τ : Set (Formula R I)) :
    (Cell (G := G) S ep e2 p φ τ).Finite := by
  let := Fintype.ofEquiv (labelValues S ep e2 p τ φ) (cellEquiv S ep e2 hAutA p φ τ).symm
  exact Set.toFinite _

include hAutA hAutB epp e3 e4 in

theorem supported_domain_bijection (hs : 0 < s) (e0 : P ↪ I)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : P ⊕ Fin s → B,
      tupleType T ep a = tupleType T ep b → ∃ g : H, ∀ i, g • a i = b i)
    (p : P → A) (q : P → B) (hp : tupleType S e0 p = tupleType T e0 q) :
    ∃ f : Domain (A := A) G s ≃ Domain (A := B) H s,
      ∀ x, ∃ φ : Form (Fin s) (Set (Formula R I)), ∃ a : Fin s → A, ∃ b : Fin s → B,
        Form.value S e2 φ a = x.1 ∧ Form.value T e2 φ b = (f x).1 ∧
        tupleType S ep (Sum.elim p a) = tupleType T ep (Sum.elim q b) := by
  let L := {l : Form (Fin s) (Set (Formula R I)) × Set (Formula R I) //
    Nonempty (Molecules S ep p l.2)}
  let C : L → Set (Domain (A := A) G s) := fun l => Cell S ep e2 p l.1.1 l.1.2
  let D : L → Set (Domain (A := B) H s) := fun l => Cell T ep e2 q l.1.1 l.1.2
  have nonemptyB (l : L) : Nonempty (Molecules T ep q l.1.2) := by
    obtain ⟨f⟩ := tupleType_extension_equiv S T e0 ep p q hp l.1.2
    exact Nonempty.map f l.2
  have coverC : ∀ x, ∃ l, x ∈ C l := by
    intro x
    obtain ⟨φ,a,ha⟩ := representation S e2 hAutA hs hHomA2 x.1 x.2
    let τ := tupleType S ep (Sum.elim p a)
    let l : L := ⟨(φ,τ),⟨⟨a,rfl⟩⟩⟩
    exact ⟨l,⟨⟨a,rfl⟩,ha⟩⟩
  have coverD : ∀ y, ∃ l, y ∈ D l := by
    intro y
    obtain ⟨φ,b,hb⟩ := representation T e2 hAutB hs hHomB2 y.1 y.2
    obtain ⟨a,ha⟩ := tupleType_append T S e0 ep q p b hp.symm
    let τ := tupleType T ep (Sum.elim q b)
    let l : L := ⟨(φ,τ),⟨⟨a,ha.symm⟩⟩⟩
    exact ⟨l,⟨⟨b,rfl⟩,hb⟩⟩
  have partC : ∀ l k x, x ∈ C l → x ∈ C k → C l = C k := by
    intro l k x hx hk
    have hh := label_partition S ep e2 hAutA p l.1.2 hHomA l.1.1 k.1.1 k.1.2 x.1 hx hk
    exact congrArg (fun Z : Set (HF A) => {x : Domain G s | x.1 ∈ Z}) hh
  have partD : ∀ l k x, x ∈ D l → x ∈ D k → D l = D k := by
    intro l k x hx hk
    have hh := label_partition T ep e2 hAutB q l.1.2 hHomB l.1.1 k.1.1 k.1.2 x.1 hx hk
    exact congrArg (fun Z : Set (HF B) => {x : Domain H s | x.1 ∈ Z}) hh
  have same : ∀ l k, C l = C k ↔ D l = D k := by
    intro l k
    constructor
    · intro he
      obtain ⟨a⟩ := l.2
      let x : Domain G s := ⟨Form.value S e2 l.1.1 a.1,
        value_hereditarily_supported S e2 hAutA _ _⟩
      have hx : x ∈ C l := ⟨a,rfl⟩
      have hk : x ∈ C k := he ▸ hx
      obtain ⟨y,hy,hy'⟩ := label_overlap_transfer S T ep epp e2 e3 e4 e0 p q hp
        l.1.1 k.1.1 l.1.2 k.1.2 ⟨x.1,hx,hk⟩
      have hsupp : HereditarilySupported (G := H) s y := by
        obtain ⟨b,rfl⟩ := hy
        exact value_hereditarily_supported T e2 hAutB _ _
      exact partD l k ⟨y,hsupp⟩ hy hy'
    · intro he
      obtain ⟨b⟩ := nonemptyB l
      let y : Domain H s := ⟨Form.value T e2 l.1.1 b.1,
        value_hereditarily_supported T e2 hAutB _ _⟩
      have hy : y ∈ D l := ⟨b,rfl⟩
      have hk : y ∈ D k := he ▸ hy
      obtain ⟨x,hx,hx'⟩ := label_overlap_transfer T S ep epp e2 e3 e4 e0 q p hp.symm
        l.1.1 k.1.1 l.1.2 k.1.2 ⟨y.1,hy,hk⟩
      have hsupp : HereditarilySupported (G := G) s x := by
        obtain ⟨a,rfl⟩ := hx
        exact value_hereditarily_supported S e2 hAutA _ _
      exact partC l k ⟨x,hsupp⟩ hx hx'
  have card : ∀ l, Nat.card (C l) = Nat.card (D l) := by
    intro l
    obtain ⟨a⟩ := l.2
    obtain ⟨b⟩ := nonemptyB l
    have hh := label_values_card S T ep epp e2 e3 e4 hAutA hAutB hHomA hHomB
      p q l.1.2 l.1.1 a b
    have he := Nat.card_congr (cellEquiv S ep e2 hAutA p l.1.1 l.1.2)
    have hf := Nat.card_congr (cellEquiv T ep e2 hAutB q l.1.1 l.1.2)
    exact he.trans (hh.trans hf.symm)
  obtain ⟨f,hf⟩ := CPTSeparation.glue_finite_cells C D coverC coverD partC partD same
    (fun l => cell_finite S ep e2 hAutA p l.1.1 l.1.2)
    (fun l => cell_finite T ep e2 hAutB q l.1.1 l.1.2) card
  refine ⟨f,fun x => ?_⟩
  obtain ⟨l,⟨a,ha⟩,⟨b,hb⟩⟩ := hf x
  exact ⟨l.1.1,a.1,b.1,ha,hb,a.2.trans b.2.symm⟩

end

open Classical Counting Hereditary

variable {R I A B V G H : Type*}

variable [finiteI : Fintype I] [DecidableEq I] [finiteA : Fintype A] [Fintype B]

variable [nonemptyA : Nonempty A] [Nonempty B] [finiteV : Fintype V] [decidableV : DecidableEq V]

variable [Group G] [MulAction G A] [Group H] [MulAction H B]

variable {s : ℕ}

variable (S : Structure R A) (T : Structure R B)

variable (ef : V × Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)

variable (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

include e3 e4 in
theorem represented_equal (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i j : V) : v i = v j ↔ w i = w j := by
  by_cases hij : i = j
  · subst j; simp
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  have hh := tupleType_project S T ef e2 (twoBlocks i j hij) a b ht
  simp only [comp_twoBlocks] at hh
  have he := equality_transfer S T e2 e3 e4 (φ i) (φ j) _ _ _ _ hh
  simpa only [ha,hb,Subtype.ext_iff] using he

include e3 e4 in
theorem represented_mem (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i j : V) : (v i).1 ∈ (v j).1 ↔ (w i).1 ∈ (w j).1 := by
  by_cases hij : i = j
  · subst j
    exact iff_of_false (fun h => (Nat.lt_irrefl _ (rank_lt_of_mem h)))
      (fun h => (Nat.lt_irrefl _ (rank_lt_of_mem h)))
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  have hh := tupleType_project S T ef e2 (twoBlocks i j hij) a b ht
  simp only [comp_twoBlocks] at hh
  have he := membership_transfer S T e2 e3 e4 (φ i) (φ j) _ _ _ _ hh
  simpa only [ha,hb] using he

omit R I A B V G H s S T ef e2 in
theorem represented_atom.{uDecl1, uDecl2, uDecl3, uDecl4, uDecl5, uDecl6, uDecl7}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {B : Type uDecl4}
    {V : Type uDecl5}
    {G : Type uDecl6}
    {H : Type uDecl7}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Fintype B]
    [Nonempty A]
    [Nonempty B]
    [Fintype V]
    [DecidableEq V]
    [Group G]
    [MulAction G A]
    [Group H]
    [MulAction H B]
    {s : ℕ}
    (S : Counting.Structure R A)
    (T : Counting.Structure R B)
    (ef : V × Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I) (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i : V) : isSet (v i).1 = false ↔ isSet (w i).1 = false := by
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  rw [←ha i,←hb i]
  cases φ i <;> simp

omit R I A s S e2 in
private theorem base_value.{uDecl1, uDecl2, uDecl3}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    {s : ℕ}
    (S : Counting.Structure R A)
    (e2 : Fin s ⊕ Fin s ↪ I) (φ ψ : Form (Fin s) (Set (Formula R I)))
    (a b : Fin s → A) (r : R) :
    (∃ x y, Form.value S e2 φ a = Hereditary.atom x ∧
      Form.value S e2 ψ b = Hereditary.atom y ∧ S.rel r x y) ↔
    match φ,ψ with
    | .atom i, .atom j => S.rel r (a i) (b j)
    | _, _ => False := by
  have hn (n : ℕ) (child : Fin n → Form (Fin s) (Set (Formula R I)))
      (label : Fin n → Set (Formula R I)) (c : Fin s → A) (x : A) :
      Form.value S e2 (.set n child label) c ≠ Hereditary.atom x := by
    intro h; have hh := congrArg isSet h; simp at hh
  cases φ <;> cases ψ <;> simp [Form.value_atom,atom_injective.eq_iff,hn]

omit R I A B V G H s S T ef e2 in
theorem represented_base.{uDecl1, uDecl2, uDecl3, uDecl4, uDecl5, uDecl6, uDecl7}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {B : Type uDecl4}
    {V : Type uDecl5}
    {G : Type uDecl6}
    {H : Type uDecl7}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Fintype B]
    [Nonempty A]
    [Nonempty B]
    [Fintype V]
    [DecidableEq V]
    [Group G]
    [MulAction G A]
    [Group H]
    [MulAction H B]
    {s : ℕ}
    (S : Counting.Structure R A)
    (T : Counting.Structure R B)
    (ef : V × Fin s ↪ I)
    (e2 : Fin s ⊕ Fin s ↪ I) (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (r : R) (i j : V) :
    (hfStructure S).rel (.base r) (v i) (v j) ↔ (hfStructure T).rel (.base r) (w i) (w j) := by
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  change (∃ x y, (v i).1 = Hereditary.atom x ∧ (v j).1 = Hereditary.atom y ∧ S.rel r x y) ↔
    (∃ x y, (w i).1 = Hereditary.atom x ∧ (w j).1 = Hereditary.atom y ∧ T.rel r x y)
  rw [←ha i,←ha j,←hb i,←hb j,base_value S e2,base_value T e2]
  cases hi : φ i with
  | set n child label => simp
  | atom k =>
    cases hj : φ j with
    | set n child label => simp
    | atom l =>
      have he := (typeOf_eq_iff S T (tupleNames ef) _ _).mp ht
        (.relation r (ef (i,k)) (ef (j,l))) (by
          intro p hp
          simp only [Formula.free,Finset.mem_insert,Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> exact (mem_tupleNames _ _).mpr ⟨_,rfl⟩)
      simpa only [Formula.eval,tupleAssignment_apply] using he

omit R I A G in
private theorem homogeneity_reindex.{uDecl1, uDecl2, uDecl3, uDecl6, uDecl8, uDecl9}
    {R : Type uDecl1}
    {I : Type uDecl2}
    {A : Type uDecl3}
    {G : Type uDecl6}
    [Fintype I]
    [DecidableEq I]
    [Fintype A]
    [Nonempty A]
    [Group G]
    [MulAction G A] {J : Type uDecl8} {K : Type uDecl9} [Fintype J] [Fintype K]
    (S : Structure R A) (e : J ↪ I) (f : K ↪ I) (u : K ≃ J)
    (hh : ∀ a b : J → A, tupleType S e a = tupleType S e b →
      ∃ g : G, ∀ j, g • a j = b j) :
    ∀ a b : K → A, tupleType S f a = tupleType S f b → ∃ g : G, ∀ j, g • a j = b j := by
  intro a b hab
  have h := tupleType_project S S f e u.symm.toEmbedding a b hab
  obtain ⟨g,hg⟩ := hh _ _ h
  exact ⟨g,fun j => by simpa using hg (u j)⟩

variable (eplus : (V × Fin s) ⊕ Fin s ↪ I)

variable (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)

include eplus e3 e4 hAutA hAutB in

theorem represented_extension (hs : 0 < s)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : V × Fin s → A,
      tupleType S ef a = tupleType S ef b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : V × Fin s → B,
      tupleType T ef a = tupleType T ef b → ∃ g : H, ∀ i, g • a i = b i)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i : V) :
    ∃ f : Domain (A := A) G s ≃ Domain (A := B) H s,
      ∀ x, Represented S T ef e2 (Function.update v i x) (Function.update w i (f x)) := by
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  let P := {j : V // j ≠ i} × Fin s
  let u : P ⊕ Fin s ≃ V × Fin s := splitBlock i
  let ep := u.toEmbedding.trans ef
  let epp := (Equiv.sumCongr u (Equiv.refl (Fin s))).toEmbedding.trans eplus
  let e0 := Function.Embedding.inl.trans ep
  let keep : P ↪ V × Fin s := Function.Embedding.inl.trans u.toEmbedding
  let p : P → A := a ∘ keep
  let q : P → B := b ∘ keep
  have hp : tupleType S e0 p = tupleType T e0 q :=
    tupleType_project S T ef e0 keep a b ht
  have homA := homogeneity_reindex S ef ep u hHomA
  have homB := homogeneity_reindex T ef ep u hHomB
  obtain ⟨f,hf⟩ := supported_domain_bijection S T ep epp e2 e3 e4
    hAutA hAutB hs e0 hHomA2 hHomB2 homA homB p q hp
  refine ⟨f,fun x => ?_⟩
  obtain ⟨ψ,c,d,hc,hd,hcd⟩ := hf x
  let a' := Sum.elim p c ∘ u.symm
  let b' := Sum.elim q d ∘ u.symm
  refine ⟨Function.update φ i ψ,a',b',?_,?_,?_⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [a',u,Function.comp_def,splitBlock] using hc
    · simpa [a',u,p,keep,Function.comp_def,splitBlock_symm_old i j hj,
        Function.update_of_ne hj,splitBlock,hj] using ha j
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [b',u,Function.comp_def,splitBlock] using hd
    · simpa [b',u,q,keep,Function.comp_def,splitBlock_symm_old i j hj,
        Function.update_of_ne hj,splitBlock,hj] using hb j
  · exact tupleType_project S T ep ef u.symm.toEmbedding _ _ hcd

include eplus e3 e4 hAutA hAutB in

theorem supported_eval_transfer (hs : 0 < s)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : V × Fin s → A,
      tupleType S ef a = tupleType S ef b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : V × Fin s → B,
      tupleType T ef a = tupleType T ef b → ∃ g : H, ∀ i, g • a i = b i)
    (φ : Formula (HFRelation R) V)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) :
    φ.eval (hfStructure S) v ↔ φ.eval (hfStructure T) w := by
  apply Formula.eval_of_bijectionSystem (hfStructure S) (hfStructure T)
    (Represented S T ef e2) _ _ _ φ v w h
  · exact represented_equal S T ef e2 e3 e4
  · intro v w h r i j
    cases r with
    | mem => exact represented_mem S T ef e2 e3 e4 v w h i j
    | atom => exact represented_atom S T ef e2 v w h i
    | base r => exact represented_base S T ef e2 v w h r i j
  · exact represented_extension S T ef e2 e3 e4 eplus hAutA hAutB hs
      hHomA2 hHomB2 hHomA hHomB

include eplus e3 e4 hAutA hAutB in

theorem supported_sentences_transfer (hs : 0 < s)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : V × Fin s → A,
      tupleType S ef a = tupleType S ef b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : V × Fin s → B,
      tupleType T ef a = tupleType T ef b → ∃ g : H, ∀ i, g • a i = b i)
    (hbase : tupleType S (Function.Embedding.ofIsEmpty : Empty ↪ I) Empty.elim =
      tupleType T (Function.Embedding.ofIsEmpty : Empty ↪ I) Empty.elim)
    (φ : Formula (HFRelation R) V) (hφ : φ.free = ∅)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s) :
    φ.eval (hfStructure S) v ↔ φ.eval (hfStructure T) w := by
  let a : V × Fin s → A := fun _ => Classical.choice inferInstance
  have he : tupleType S (Function.Embedding.ofIsEmpty : Empty ↪ I)
      (a ∘ (Function.Embedding.ofIsEmpty : Empty ↪ V × Fin s)) =
        tupleType T (Function.Embedding.ofIsEmpty : Empty ↪ I) Empty.elim := by
    convert hbase using 1
    congr 1; funext x; exact x.elim
  obtain ⟨b,_,hab⟩ := tupleType_extend S T
    (Function.Embedding.ofIsEmpty : Empty ↪ I) ef
    (Function.Embedding.ofIsEmpty : Empty ↪ V × Fin s) a Empty.elim he
  let emptyForm : Form (Fin s) (Set (Formula R I)) := .set 0 Fin.elim0 Fin.elim0
  let v' : V → Domain (A := A) G s := fun i =>
    ⟨Form.value S e2 emptyForm (fun j => a (i,j)),
      value_hereditarily_supported S e2 hAutA emptyForm _⟩
  let w' : V → Domain (A := B) H s := fun i =>
    ⟨Form.value T e2 emptyForm (fun j => b (i,j)),
      value_hereditarily_supported T e2 hAutB emptyForm _⟩
  have hr : Represented S T ef e2 v' w' :=
    ⟨(fun _ => emptyForm),a,b,(fun _ => rfl),(fun _ => rfl),hab⟩
  have hh := supported_eval_transfer S T ef e2 e3 e4 eplus hAutA hAutB hs
    hHomA2 hHomB2 hHomA hHomB φ v' w' hr
  exact (Formula.eval_congr _ φ (fun i hi => by simp [hφ] at hi)).trans
    (hh.trans (Formula.eval_congr _ φ (fun i hi => by simp [hφ] at hi)))

omit R A in
private theorem homogeneous_tuple.{uDecl1, uDecl3, uDecl8, uDecl9}
    {R : Type uDecl1}
    {A : Type uDecl3}
    [Fintype A]
    [Nonempty A] {J : Type uDecl8} [Fintype J] {M r : ℕ}
    (S : Structure R A) (G : Type uDecl9) [Group G] [MulAction G A]
    (h : HomogeneousThrough S G M r) (e : J ↪ Fin M)
    (hc : Fintype.card J ≤ r) :
    ∀ a b : J → A, tupleType S e a = tupleType S e b → ∃ g : G, ∀ j, g • a j = b j := by
  exact homogeneity_reindex S ((Fintype.equivFin J).symm.toEmbedding.trans e) e
    (Fintype.equivFin J) (h _ hc _)

theorem hf_transfer {m M : ℕ} (hs : 0 < s) (_ : 0 < m) (hM : 0 < M)
    (hwidth : max 4 (m+1) * s ≤ M)
    (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)
    (hHomA : HomogeneousThrough S G M (max 2 m * s))
    (hHomB : HomogeneousThrough T H M (max 2 m * s))
    (hbase : tupleType S (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim =
      tupleType T (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim)
    (φ : Formula (HFRelation R) (Fin m)) (hφ : φ.free = ∅)
    (v : Fin m → Domain (A := A) G s) (w : Fin m → Domain (A := B) H s) :
    φ.eval (hfStructure S) v ↔ φ.eval (hfStructure T) w := by
  have h4 : 4*s ≤ M := (Nat.mul_le_mul_right s (le_max_left _ _)).trans hwidth
  have hp : (m+1)*s ≤ M := (Nat.mul_le_mul_right s (le_max_right _ _)).trans hwidth
  have h2 : Fintype.card (Fin s ⊕ Fin s) ≤ M := by simp only [Fintype.card_sum,Fintype.card_fin]; omega
  have h3 : Fintype.card ((Fin s ⊕ Fin s) ⊕ Fin s) ≤ M := by simp only [Fintype.card_sum,Fintype.card_fin]; omega
  have h4' : Fintype.card (((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s) ≤ M := by simp only [Fintype.card_sum,Fintype.card_fin]; omega
  have hpf : Fintype.card ((Fin m × Fin s) ⊕ Fin s) ≤ M := by simpa [Nat.add_mul] using hp
  have hfull : Fintype.card (Fin m × Fin s) ≤ M := by simp only [Fintype.card_prod,Fintype.card_fin]; nlinarith
  have hom2 : Fintype.card (Fin s ⊕ Fin s) ≤ max 2 m*s := by
    simpa [two_mul] using Nat.mul_le_mul_right s (le_max_left 2 m)
  have homf : Fintype.card (Fin m × Fin s) ≤ max 2 m*s := by
    simpa using Nat.mul_le_mul_right s (le_max_right 2 m)
  exact supported_sentences_transfer S T (namesOfCard hfull) (namesOfCard h2)
    (namesOfCard h3) (namesOfCard h4') (namesOfCard hpf) hAutA hAutB hs
    (homogeneous_tuple S G hHomA _ hom2) (homogeneous_tuple T H hHomB _ hom2)
    (homogeneous_tuple S G hHomA _ homf) (homogeneous_tuple T H hHomB _ homf)
    hbase φ hφ v w

end CPTSeparation.Forms

namespace CPTSeparation.Grid

open Classical Finset

variable {n M m s : ℕ} {b : Vertex n → Scalar}

theorem central_analysis_isomorphism (k : CentralGroup n) (r : AnalysisSymbol) (x y : Atom b) :
    (analysisStructure b).rel r (k • x) (k • y) ↔ (analysisStructure b).rel r x y :=
  ((central_atomShift k x).analysisRelation (central_atomShift k y) r).symm

theorem homogeneous_through_numeric (hn : 1 ≤ n) [Nonempty (Atom b)] (R : ℕ)
    (hw : (7*R:ℝ)+7*((6*R:ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M) :
    Forms.HomogeneousThrough (analysisStructure b) (CentralGroup n) M R := by
  intro k hk names a a' ht
  apply quantitative_homogeneity hn names a a' _ ht
  simp only [Fintype.card_fin]
  have hkr : (k:ℝ) ≤ R := by exact_mod_cast hk
  have hp : ((6*k:ℝ)/boxConstant)^((3:ℝ)/2) ≤ ((6*R:ℝ)/boxConstant)^((3:ℝ)/2) := by
    apply Real.rpow_le_rpow (div_nonneg (by positivity) boxConstant_pos.le) _ (by norm_num)
    exact div_le_div_of_nonneg_right (by linarith) boxConstant_pos.le
  linarith

theorem base_empty_type (hn : 1 ≤ n) (hbound : GiantBound n M) (vstar : Vertex n)
    [Nonempty (Atom (0 : Vertex n → Scalar))] [Nonempty (Atom (Pi.single vstar 1))] :
    Counting.tupleType (analysisStructure (0 : Vertex n → Scalar))
      (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim =
    Counting.tupleType (analysisStructure (Pi.single vstar 1))
      (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim := by
  apply (Counting.typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hφ
  have he : φ.free = ∅ := by
    apply subset_empty.mp
    simpa only [Counting.tupleNames,Finset.univ_eq_empty,Finset.map_empty] using hφ
  exact base_equivalence_numeric hn hbound vstar φ he _ _

theorem grid_hf_transfer_oai (hn : 1 ≤ n) (hs : 0 < s) (hm : 0 < m)
    (vstar : Vertex n) [Nonempty (Atom (0 : Vertex n → Scalar))]
    [Nonempty (Atom (Pi.single vstar 1))]
    (hwidth : max 4 (m+1)*s ≤ M)
    (hhom : (7*(max 2 m*s):ℝ)+7*((6*(max 2 m*s):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M)
    (φ : Counting.Formula (Forms.HFRelation AnalysisSymbol) (Fin m)) (hφ : φ.free = ∅)
    (v : Fin m → Forms.Domain (A := Atom (0 : Vertex n → Scalar)) (CentralGroup n) s)
    (w : Fin m → Forms.Domain (A := Atom (Pi.single vstar 1)) (CentralGroup n) s) :
    φ.eval (Forms.hfStructure (analysisStructure (0 : Vertex n → Scalar))) v ↔
      φ.eval (Forms.hfStructure (analysisStructure (Pi.single vstar 1))) w := by
  have hM : 0 < M := lt_of_lt_of_le (Nat.mul_pos (by omega) hs) hwidth
  exact Forms.hf_transfer _ _ hs hm hM hwidth
    (fun g r a b => central_analysis_isomorphism g r a b)
    (fun g r a b => central_analysis_isomorphism g r a b)
    (homogeneous_through_numeric hn _ (by simpa only [Nat.cast_mul] using hhom))
    (homogeneous_through_numeric hn _ (by simpa only [Nat.cast_mul] using hhom))
    (base_empty_type hn hgiant vstar) φ hφ v w

end CPTSeparation.Grid

end

end OAI
end

theorem solution : type_of% @OAI.CPTSeparation.Grid.grid_hf_transfer_oai := @OAI.CPTSeparation.Grid.grid_hf_transfer_oai
