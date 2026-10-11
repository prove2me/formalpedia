-- Prove2me | solution 1 for OAI.CHObstruction.main
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T15:27:02.248326+00:00
-- url     : https://prove2.me/submissions/ccb45b16-6443-4593-96c7-020828836a44

import Mathlib
import Definitions.Def_CHObstruction

/-! Proof of `OAI.CHObstruction.main`, ported from the Apache-2.0 licensed Lean development in
openai/math (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, `lean/OAI/ModelTheory/Categoricity/*.lean`),
concatenated into a single file against the platform definitions `Definitions.Def_CHObstruction`. -/

/-- Compatibility lemma (present in newer Lean cores): a `dite` whose condition holds. -/
theorem dite_eq_left {c : Prop} {_ : Decidable c} {α : Sort _} {t : c → α} {e : ¬c → α}
    (h : c) : dite c t e = t h := dif_pos h

/-- Compatibility lemma (present in newer Lean cores): a `dite` whose condition fails. -/
theorem dite_eq_right {c : Prop} {_ : Decidable c} {α : Sort _} {t : c → α} {e : ¬c → α}
    (h : ¬c) : dite c t e = e h := dif_neg h

-- ===== Collapse.lean =====

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace TaggedCollapse

variable {Q : Type u} (R : Q → Q → Prop) (wf : WellFounded R)

def collapse (x : Q) : ZFSet.{u} :=
  wf.fix (fun x rec => ZFSet.range (fun y : {y // R y x} => rec y.val y.property)) x

theorem collapse_eq (x : Q) :
    collapse R wf x = ZFSet.range (fun y : {y // R y x} => collapse R wf y.val) := by
  exact wf.fix_eq _ x

theorem mem_collapse {x : Q} {z : ZFSet.{u}} :
    z ∈ collapse R wf x ↔ ∃ y, R y x ∧ collapse R wf y = z := by
  rw [collapse_eq]
  simp only [ZFSet.mem_range, Subtype.exists, exists_prop]

theorem injective
    (extensional : ∀ x y, (∀ z, R z x ↔ R z y) → x = y) :
    Function.Injective (collapse R wf) := by
  intro x
  induction x using wf.induction with
  | h x ih =>
    intro x' heq
    apply extensional x x'
    intro y
    constructor
    · intro hy
      have hm : collapse R wf y ∈ collapse R wf x :=
        (mem_collapse R wf).2 ⟨y, hy, rfl⟩
      rw [heq] at hm
      obtain ⟨y', hy', hh⟩ := (mem_collapse R wf).1 hm
      have : y = y' := ih y hy hh.symm
      simpa only [this] using hy'
    · intro hy'
      have hm : collapse R wf y ∈ collapse R wf x' :=
        (mem_collapse R wf).2 ⟨y, hy', rfl⟩
      rw [← heq] at hm
      obtain ⟨y', hy, hh⟩ := (mem_collapse R wf).1 hm
      have : y' = y := ih y' hy hh
      simpa only [← this] using hy

theorem rank_le (ρ : Q → Ordinal.{u})
    (decreases : ∀ {x y}, R y x → ρ y < ρ x) (x : Q) :
    ZFSet.rank (collapse R wf x) ≤ ρ x := by
  induction x using wf.induction with
  | h x ih =>
    rw [collapse_eq, ZFSet.rank_range]
    apply Ordinal.iSup_le
    intro y
    exact Order.succ_le_of_lt ((ih y.val y.property).trans_lt (decreases y.property))

def embedding (extensional : ∀ x y, (∀ z, R z x ↔ R z y) → x = y)
    (ρ : Q → Ordinal.{u}) (decreases : ∀ {x y}, R y x → ρ y < ρ x)
    (δ : Ordinal.{u}) (bounded : ∀ x, ρ x < δ) :
    Q ↪ (ZFSet.vonNeumann δ) where
  toFun x := ⟨collapse R wf x,
    ZFSet.mem_vonNeumann.2 ((rank_le R wf ρ decreases x).trans_lt (bounded x))⟩
  inj' _x _y h := injective R wf extensional (congrArg Subtype.val h)

theorem wellFounded_of_tags (ρ : Q → Ordinal.{u})
    (decreases : ∀ {x y}, R y x → ρ y < ρ x) : WellFounded R :=
  (InvImage.wf ρ Ordinal.lt_wf).mono (fun _ _ h => decreases h)

end TaggedCollapse

namespace Domination

abbrev Alpha := {a : Ordinal.{u} // a < ω_ 2}
abbrev Beta := {b : Ordinal.{u} // b < ω_ 1}

def indexEmbedding (a : Alpha.{u}) : Set.Iio a.val ↪ Beta.{u} := by
  apply Classical.choice
  apply (Cardinal.le_def _ _).1
  change #(Set.Iio a.val) ≤ #(Set.Iio (ω_ (1 : Ordinal.{u})))
  rw [Cardinal.mk_Iio_ordinal, Cardinal.mk_Iio_ordinal, Cardinal.lift_le]
  have h : a.val.card < ℵ_ (2 : Ordinal.{u}) :=
    Cardinal.lt_omega_iff_card_lt.1 a.property
  have hs : ℵ_ (2 : Ordinal.{u}) = succ (ℵ_ (1 : Ordinal.{u})) := by
    rw [Cardinal.succ_aleph]
    norm_num
  simpa only [Ordinal.card_omega] using (Order.lt_succ_iff.1 (h.trans_eq hs))

theorem countable_Iio {b : Ordinal.{u}} (hb : b < ω_ 1) : Countable (Set.Iio b) := by
  apply Cardinal.mk_le_aleph0_iff.1
  rw [Cardinal.mk_Iio_ordinal, ← Cardinal.lift_aleph0.{u+1,u}, Cardinal.lift_le]
  exact Cardinal.lt_aleph_one_iff.1 (Cardinal.lt_omega_iff_card_lt.1 hb)

def Prior (a : Alpha.{u}) (b : Beta.{u}) :=
  {g : Set.Iio a.val // (indexEmbedding a g).val < b.val}

instance prior_countable (a : Alpha.{u}) (b : Beta.{u}) : Countable (Prior a b) := by
  have := countable_Iio b.property
  let f : Prior a b → Set.Iio b.val := fun g => ⟨(indexEmbedding a g.val).val, g.property⟩
  apply Function.Injective.countable (f := f)
  intro g h heq
  apply Subtype.ext
  apply (indexEmbedding a).injective
  apply Subtype.ext
  exact congrArg (fun x : Set.Iio b.val => x.val) heq

def values (a : Alpha.{u}) : Beta.{u} → Beta.{u} :=
  (InvImage.wf (fun a : Alpha.{u} => a.val) Ordinal.lt_wf).fix
    (C := fun _ => Beta.{u} → Beta.{u})
    (fun a rec b =>
      ⟨⨆ g : Prior a b, succ (rec ⟨g.val.val, lt_trans g.val.property a.property⟩ g.val.property b).val,
       Ordinal.iSup_lt_omega_one (fun g =>
         (Cardinal.isSuccLimit_omega 1).succ_lt
           (rec ⟨g.val.val, lt_trans g.val.property a.property⟩ g.val.property b).property)⟩) a

theorem values_eq (a : Alpha.{u}) (b : Beta.{u}) :
    (values a b).val =
      ⨆ g : Prior a b, succ (values ⟨g.val.val, lt_trans g.val.property a.property⟩ b).val := by
  conv_lhs => rw [values, WellFounded.fix_eq]
  rfl

theorem eventually_lt (a : Alpha.{u}) (g : Set.Iio a.val) (b : Beta.{u})
    (hb : (indexEmbedding a g).val < b.val) :
    (values ⟨g.val, lt_trans g.property a.property⟩ b).val < (values a b).val := by
  rw [values_eq a b]
  exact (lt_succ _).trans_le (Ordinal.le_iSup _ (⟨g, hb⟩ : Prior a b))

theorem countable_exceptions (a : Alpha.{u}) (g : Set.Iio a.val) :
    {b : Beta.{u} | (values a b).val ≤ (values ⟨g.val, lt_trans g.property a.property⟩ b).val}.Countable := by
  let bound := succ (indexEmbedding a g).val
  have hb : bound < ω_ 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt (indexEmbedding a g).property
  have := countable_Iio hb
  apply Set.countable_coe_iff.1
  let f : {b : Beta.{u} | (values a b).val ≤
      (values ⟨g.val, lt_trans g.property a.property⟩ b).val} → Set.Iio bound :=
    fun b => ⟨b.val.val, Order.lt_succ_iff.2 (le_of_not_gt (fun h =>
      (eventually_lt a g b.val h).not_ge b.property))⟩
  apply Function.Injective.countable (f := f)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : Set.Iio bound => x.val) h

end Domination

namespace CountableClosures

variable {A : Type u} (R : A → A → Prop)
  (separates : ∀ a b, a ≠ b → ∃ w, ¬ (R w a ↔ R w b))

def witness (a b : A) : A := by
  classical
  exact if h : a = b then a else Classical.choose (separates a b h)

theorem witness_distinguishes {a b : A} (h : a ≠ b) :
    ¬ (R (witness R separates a b) a ↔ R (witness R separates a b) b) := by
  simpa only [witness, dite_eq_right h] using Classical.choose_spec (separates a b h)

def stage (S : Set A) : ℕ → Set A
  | 0 => S
  | n + 1 => stage S n ∪ Set.image2 (witness R separates) (stage S n) (stage S n)

def closure (S : Set A) : Set A := ⋃ n, stage R separates S n

theorem stage_mono (S : Set A) : Monotone (stage R separates S) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

theorem subset_closure (S : Set A) : S ⊆ closure R separates S :=
  fun _ hx => Set.mem_iUnion.2 ⟨0, hx⟩

theorem closure_mono : Monotone (closure R separates) := by
  intro S T hST x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
  apply Set.mem_iUnion.2 ⟨n, ?_⟩
  suffices stage R separates S n ⊆ stage R separates T n from this hn
  clear hn
  induction n with
  | zero => exact hST
  | succ n ih =>
    intro y hy
    rcases hy with hy | hy
    · exact Or.inl (ih hy)
    · rcases hy with ⟨a, ha, b, hb, rfl⟩
      exact Or.inr ⟨a, ih ha, b, ih hb, rfl⟩

theorem closure_countable {S : Set A} (hS : S.Countable) :
    (closure R separates S).Countable := by
  apply Set.countable_iUnion
  intro n
  induction n with
  | zero => exact hS
  | succ n ih => exact ih.union (ih.image2 ih _)

theorem witness_mem {S : Set A} {a b : A}
    (ha : a ∈ closure R separates S) (hb : b ∈ closure R separates S) :
    witness R separates a b ∈ closure R separates S := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1 ha
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hb
  apply Set.mem_iUnion.2 ⟨max m n + 1, ?_⟩
  exact Or.inr ⟨a, stage_mono R separates S (le_max_left _ _) hm,
    b, stage_mono R separates S (le_max_right _ _) hn, rfl⟩

theorem extensional {S : Set A} {a b : A}
    (ha : a ∈ closure R separates S) (hb : b ∈ closure R separates S)
    (heq : ∀ w ∈ closure R separates S, R w a ↔ R w b) : a = b := by
  by_contra h
  exact witness_distinguishes R separates h (heq _ (witness_mem R separates ha hb))

abbrev FiniteSeed (A : Type u) := {X : Finset A // X.Nonempty}

def entries (X : FiniteSeed A) : Set A := closure R separates X.val

theorem entries_countable (X : FiniteSeed A) : (entries R separates X).Countable :=
  closure_countable R separates X.val.countable_toSet

theorem seed_subset (X : FiniteSeed A) : (X.val : Set A) ⊆ entries R separates X :=
  subset_closure R separates X.val

theorem entries_nonempty (X : FiniteSeed A) : (entries R separates X).Nonempty :=
  X.property.to_set.mono (seed_subset R separates X)

theorem entries_mono (X Y : FiniteSeed A) (h : X.val ⊆ Y.val) :
    entries R separates X ⊆ entries R separates Y :=
  closure_mono R separates h

def enumeration (X : FiniteSeed A) : ℕ → entries R separates X :=
  let first : entries R separates X :=
    ⟨Classical.choose X.property, seed_subset R separates X (Classical.choose_spec X.property)⟩
  let e : ℕ → entries R separates X :=
    Classical.choose (Set.Countable.exists_surjective (entries_nonempty R separates X)
      (entries_countable R separates X))
  fun n => match n with | 0 => first | n + 1 => e n

theorem enumeration_surjective (X : FiniteSeed A) :
    Function.Surjective (enumeration R separates X) := by
  intro x
  obtain ⟨n, hn⟩ := Classical.choose_spec
    (Set.Countable.exists_surjective (entries_nonempty R separates X)
      (entries_countable R separates X)) x
  exact ⟨n + 1, hn⟩

theorem enumeration_singleton (x : A) :
    (enumeration R separates ⟨{x}, Finset.singleton_nonempty x⟩ 0).val = x := by
  exact Finset.mem_singleton.1 (Classical.choose_spec (Finset.singleton_nonempty x))

theorem membership_separates (D : ZFSet.{u}) (hD : D.IsTransitive) :
    ∀ a b : D, a ≠ b → ∃ w : D, ¬ (w.val ∈ a.val ↔ w.val ∈ b.val) := by
  intro a b h
  have hab : a.val ≠ b.val := fun heq => h (Subtype.ext heq)
  obtain ⟨w, hw⟩ : ∃ w, ¬ (w ∈ a.val ↔ w ∈ b.val) := by
    by_contra hn
    exact hab (ZFSet.ext (by simpa only [not_exists, not_not] using hn))
  have hwD : w ∈ D := by
    by_cases hwa : w ∈ a.val
    · exact hD a.val a.property hwa
    · have hwb : w ∈ b.val := by tauto
      exact hD b.val b.property hwb
  exact ⟨⟨w, hwD⟩, hw⟩

end CountableClosures

namespace TaggedLimit

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
  (F : ι → Type u) (f : ∀ i j, i ≤ j → F i ↪ F j)
  [DirectedSystem F (fun i j h => f i j h)]
  (R : ∀ i, F i → F i → Prop)
  (respect : ∀ i j h x y, R i x y ↔ R j (f i j h x) (f i j h y))
  (ρ : ∀ i, F i → Ordinal.{u})
  (tags : ∀ i j h x, ρ i x = ρ j (f i j h x))

def relation : DirectLimit F f → DirectLimit F f → Prop :=
  DirectLimit.lift₂ f f R (fun i j h x y => propext (respect i j h x y))

def rankTag : DirectLimit F f → Ordinal.{u} :=
  DirectLimit.lift f ρ tags

theorem relation_mk (i) (x y : F i) :
    relation F f R respect ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ ↔ R i x y := by
  rw [relation, DirectLimit.lift₂_def]

theorem rankTag_mk (i) (x : F i) :
    rankTag F f ρ tags ⟦⟨i, x⟩⟧ = ρ i x := rfl

theorem extensional (hext : ∀ i x y, (∀ z, R i z x ↔ R i z y) → x = y) :
    ∀ x y, (∀ z, relation F f R respect z x ↔ relation F f R respect z y) → x = y := by
  intro x y h
  obtain ⟨i, a, b, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ f x y
  congr 1
  congr 1
  apply hext i a b
  intro z
  exact (relation_mk F f R respect i z a).symm.trans
    ((h ⟦⟨i, z⟩⟧).trans (relation_mk F f R respect i z b))

theorem decreases (hdec : ∀ i x y, R i y x → ρ i y < ρ i x) :
    ∀ {x y}, relation F f R respect y x → rankTag F f ρ tags y < rankTag F f ρ tags x := by
  intro x y
  obtain ⟨i, a, b, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ f x y
  rw [relation_mk, rankTag_mk, rankTag_mk]
  exact hdec i a b

def embedding
    (hext : ∀ i x y, (∀ z, R i z x ↔ R i z y) → x = y)
    (hdec : ∀ i x y, R i y x → ρ i y < ρ i x)
    (δ : Ordinal.{u}) (hbound : ∀ i x, ρ i x < δ) :
    DirectLimit F f ↪ ZFSet.vonNeumann δ := by
  let rel := relation F f R respect
  let tag := rankTag F f ρ tags
  have hd : ∀ {x y}, rel y x → tag y < tag x := decreases F f R respect ρ tags hdec
  apply TaggedCollapse.embedding rel (TaggedCollapse.wellFounded_of_tags rel tag hd)
      (extensional F f R respect hext) tag hd δ
  intro x
  obtain ⟨i, a, rfl⟩ := DirectLimit.exists_eq_mk f x
  exact hbound i a

end TaggedLimit

end CHObstruction

end

end OAI

-- ===== Diagrams.lean =====

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Diagrams

abbrev Tag := (ω_ (1 : Ordinal.{u})).ToType

def tagOrdinal (t : Tag.{u}) : Ordinal.{u} := t.toOrd.val

theorem tag_lt (t : Tag.{u}) : tagOrdinal t < ω_ 1 := t.toOrd.property

abbrev Label (A : Type v) := {J : Finset A // J.Nonempty} × ℕ

namespace Label

def map {A : Type v} {B : Type w} (e : A ↪ B) (l : Label A) : Label B :=
  (⟨l.1.val.map e, l.1.property.map⟩, l.2)

def root {A : Type v} (a : A) : Label A := (⟨{a}, Finset.singleton_nonempty a⟩, 0)

@[simp] theorem map_refl {A : Type v} (l : Label A) :
    map (Function.Embedding.refl A) l = l := by
  rcases l with ⟨⟨J, hJ⟩, i⟩
  simp [map]

@[simp] theorem map_comp {A : Type u} {B : Type v} {C : Type w}
    (e : A ↪ B) (f : B ↪ C) (l : Label A) :
    map f (map e l) = map (e.trans f) l := by
  simp only [map, Finset.map_map]

@[simp] theorem map_root {A : Type v} {B : Type w} (e : A ↪ B) (a : A) :
    map e (root a) = root (e a) := by
  simp [map, root]

def congr {A : Type v} {B : Type w} (e : A ≃ B) : Label A ≃ Label B where
  toFun := map e.toEmbedding
  invFun := map e.symm.toEmbedding
  left_inv l := by
    rw [map_comp]
    have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl A := by
      ext a; exact e.symm_apply_apply a
    rw [he, map_refl]
  right_inv l := by
    rw [map_comp]
    have he : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl B := by
      ext b; exact e.apply_symm_apply b
    rw [he, map_refl]

end Label

structure Diagram (A : Type v) where
  eqv : Label A → Label A → Prop
  rel : Label A → Label A → Prop
  tag : Label A → Tag.{u}

namespace Diagram

variable {A : Type v} {B : Type w}

structure Valid (D : Diagram.{u} A) : Prop where
  equivalence : Equivalence D.eqv
  rel_congr : ∀ a a' b b', D.eqv a a' → D.eqv b b' → (D.rel a b ↔ D.rel a' b')
  tag_congr : ∀ a a', D.eqv a a' → D.tag a = D.tag a'
  decreases : ∀ a b, D.rel a b → tagOrdinal (D.tag a) < tagOrdinal (D.tag b)
  extensional : ∀ a b, (∀ z, D.rel z a ↔ D.rel z b) → D.eqv a b
  roots : ∀ a b, D.eqv (Label.root a) (Label.root b) → a = b

def restrict (D : Diagram.{u} B) (e : A ↪ B) : Diagram.{u} A where
  eqv a b := D.eqv (Label.map e a) (Label.map e b)
  rel a b := D.rel (Label.map e a) (Label.map e b)
  tag a := D.tag (Label.map e a)

@[simp] theorem restrict_refl (D : Diagram.{u} A) :
    D.restrict (Function.Embedding.refl A) = D := by
  cases D
  simp [restrict]

theorem restrict_comp {C : Type*} (D : Diagram.{u} C) (e : A ↪ B) (f : B ↪ C) :
    (D.restrict f).restrict e = D.restrict (e.trans f) := by
  simp only [restrict, Label.map_comp]

theorem valid_restrict_equiv (D : Diagram.{u} B) (hD : D.Valid) (e : A ≃ B) :
    (D.restrict e.toEmbedding).Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun a => hD.equivalence.refl _, fun h => hD.equivalence.symm h,
      fun h h' => hD.equivalence.trans h h'⟩
  · intro a a' b b' h h'
    exact hD.rel_congr _ _ _ _ h h'
  · intro a a' h
    exact hD.tag_congr _ _ h
  · intro a b h
    exact hD.decreases _ _ h
  · intro a b h
    apply hD.extensional
    intro z
    obtain ⟨z', rfl⟩ := (Label.congr e).surjective z
    exact h z'
  · intro a b h
    apply e.injective
    apply hD.roots
    simpa only [restrict, Label.map_root, Equiv.toEmbedding_apply] using h

def setoid (D : Diagram.{u} A) (hD : D.Valid) : Setoid (Label A) where
  r := D.eqv
  iseqv := hD.equivalence

abbrev Q (D : Diagram.{u} A) (hD : D.Valid) := Quotient (D.setoid hD)

def qRel (D : Diagram.{u} A) (hD : D.Valid) : D.Q hD → D.Q hD → Prop :=
  Quotient.lift₂ D.rel (fun a b a' b' h h' => propext (hD.rel_congr a a' b b' h h'))

def qTag (D : Diagram.{u} A) (hD : D.Valid) : D.Q hD → Ordinal.{u} :=
  Quotient.lift (fun a => tagOrdinal (D.tag a))
    (fun a b h => congrArg tagOrdinal (hD.tag_congr a b h))

theorem q_extensional (D : Diagram.{u} A) (hD : D.Valid) :
    ∀ x y, (∀ z, D.qRel hD z x ↔ D.qRel hD z y) → x = y := by
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | h a b =>
    intro h
    exact Quotient.sound (hD.extensional a b (fun z => h ⟦z⟧))

theorem q_decreases (D : Diagram.{u} A) (hD : D.Valid) :
    ∀ x y, D.qRel hD y x → D.qTag hD y < D.qTag hD x := by
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | h a b => exact hD.decreases b a

theorem q_bound (D : Diagram.{u} A) (hD : D.Valid) :
    ∀ x, D.qTag hD x < ω_ 1 := by
  intro x
  induction x using Quotient.inductionOn with
  | h a => exact tag_lt (D.tag a)

def qMap (D : Diagram.{u} A) (E : Diagram.{u} B) (hD : D.Valid) (hE : E.Valid)
    (e : A ↪ B) (h : D = E.restrict e) : D.Q hD ↪ E.Q hE where
  toFun := Quotient.map' (Label.map e) (fun a b hh => by
    change D.eqv a b at hh
    change E.eqv (Label.map e a) (Label.map e b)
    rw [h] at hh
    exact hh)
  inj' := by
    intro x y hxy
    induction x, y using Quotient.inductionOn₂ with
    | h a b =>
      apply Quotient.sound
      have hh := Quotient.exact hxy
      change E.eqv (Label.map e a) (Label.map e b) at hh
      change D.eqv a b
      rw [h]
      exact hh

theorem qMap_mk (D : Diagram.{u} A) (E : Diagram.{u} B) (hD : D.Valid) (hE : E.Valid)
    (e : A ↪ B) (h : D = E.restrict e) (x : Label A) :
    qMap D E hD hE e h ⟦x⟧ = ⟦Label.map e x⟧ := rfl

end Diagram

end Diagrams

namespace NoPattern

open Diagrams

variable (d : ∀ k : ℕ, Diagram.{u} (Fin k))
  (valid : ∀ k, (d k).Valid)
  (coherent : ∀ m n (e : Fin m ↪o Fin n), d m = (d n).restrict e.toEmbedding)

section FiniteStages

variable {J : Type u} [LinearOrder J]

def inclusion (X Y : Finset J) (h : X ⊆ Y) : X ↪o Y where
  toFun x := ⟨x.val, h x.property⟩
  inj' _x _y hxy := Subtype.ext (congrArg (fun z : Y => z.val) hxy)
  map_rel_iff' := Iff.rfl

def positions (X Y : Finset J) (h : X ⊆ Y) : Fin X.card ↪o Fin Y.card :=
  ((X.orderIsoOfFin rfl).toOrderEmbedding.comp (inclusion X Y h)).comp
    (Y.orderIsoOfFin rfl).symm.toOrderEmbedding

def stage (X : Finset J) : Diagram.{u} X :=
  (d X.card).restrict (X.orderIsoOfFin rfl).symm.toEquiv.toEmbedding

include valid in
theorem stage_valid (X : Finset J) : (stage d X).Valid :=
  (d X.card).valid_restrict_equiv (valid X.card) (X.orderIsoOfFin rfl).symm.toEquiv

include coherent in
theorem stage_restrict (X Y : Finset J) (h : X ⊆ Y) :
    stage d X = (stage d Y).restrict (inclusion X Y h).toEmbedding := by
  unfold stage
  rw [coherent X.card Y.card (positions X Y h), Diagram.restrict_comp,
    Diagram.restrict_comp]
  congr 1
  ext x
  exact congrArg (fun y => ((Y.orderIsoOfFin rfl).symm (inclusion X Y h y)).val)
    ((X.orderIsoOfFin rfl).apply_symm_apply x)

abbrev F (X : Finset J) := (stage d X).Q (stage_valid d valid X)

def transition (X Y : Finset J) (h : X ≤ Y) : F d valid X ↪ F d valid Y :=
  Diagram.qMap _ _ (stage_valid d valid X) (stage_valid d valid Y)
    (inclusion X Y h).toEmbedding (stage_restrict d coherent X Y h)

instance directedSystem : DirectedSystem (F d valid (J := J))
    (fun X Y h => transition d valid coherent X Y h) where
  map_self := by
    intro X x
    induction x using Quotient.inductionOn with
    | h a =>
      rw [transition, Diagram.qMap_mk]
      have he : (inclusion X X le_rfl).toEmbedding = Function.Embedding.refl X := by
        ext x; rfl
      rw [he, Label.map_refl]
  map_map := by
    intro Z Y X hXY hYZ x
    induction x using Quotient.inductionOn with
    | h a =>
      simp only [transition, Diagram.qMap_mk, Label.map_comp]
      rfl

def stageRelation (X : Finset J) : F d valid X → F d valid X → Prop :=
  (stage d X).qRel (stage_valid d valid X)

def stageTag (X : Finset J) : F d valid X → Ordinal.{u} :=
  (stage d X).qTag (stage_valid d valid X)

theorem relation_compatible (X Y : Finset J) (h : X ≤ Y) (x y : F d valid X) :
    stageRelation d valid X x y ↔ stageRelation d valid Y
      (transition d valid coherent X Y h x) (transition d valid coherent X Y h y) := by
  induction x, y using Quotient.inductionOn₂ with
  | h a b =>
    change (stage d X).rel a b ↔
      (stage d Y).rel (Label.map (inclusion X Y h).toEmbedding a)
        (Label.map (inclusion X Y h).toEmbedding b)
    rw [stage_restrict d coherent X Y h]
    rfl

theorem tag_compatible (X Y : Finset J) (h : X ≤ Y) (x : F d valid X) :
    stageTag d valid X x = stageTag d valid Y (transition d valid coherent X Y h x) := by
  induction x using Quotient.inductionOn with
  | h a =>
    change tagOrdinal ((stage d X).tag a) =
      tagOrdinal ((stage d Y).tag (Label.map (inclusion X Y h).toEmbedding a))
    rw [stage_restrict d coherent X Y h]
    rfl

abbrev Limit := DirectLimit (F d valid (J := J)) (transition d valid coherent)

def root (x : J) : Limit d valid coherent (J := J) :=
  ⟦⟨{x}, Quotient.mk _ (Label.root (⟨x, Finset.mem_singleton_self x⟩ : ({x} : Finset J)))⟩⟧

theorem root_injective : Function.Injective (root d valid coherent (J := J)) := by
  intro x y h
  obtain ⟨Z, hxZ, hyZ, heq⟩ := Quotient.exact h
  simp only [transition, Diagram.qMap_mk, Label.map_root] at heq
  have hrel := Quotient.exact heq
  have hxy := (stage_valid d valid Z).roots _ _ hrel
  exact congrArg Subtype.val hxy

def rootsEmbedding : J ↪ ZFSet.vonNeumann (ω_ (1 : Ordinal.{u})) :=
  (⟨root d valid coherent, root_injective d valid coherent⟩ : J ↪ Limit d valid coherent).trans
    (TaggedLimit.embedding (F d valid) (transition d valid coherent)
      (stageRelation d valid) (relation_compatible d valid coherent)
      (stageTag d valid) (tag_compatible d valid coherent)
      (fun X => (stage d X).q_extensional (stage_valid d valid X))
      (fun X => (stage d X).q_decreases (stage_valid d valid X))
      (ω_ 1) (fun X => (stage d X).q_bound (stage_valid d valid X)))

end FiniteStages

include d valid coherent in

theorem impossible : False := by
  let V := ZFSet.vonNeumann (ω_ (1 : Ordinal.{u}))
  let J := (succ V.card).ord.ToType
  let e : J ↪ Shrink.{u} V :=
    (rootsEmbedding d valid coherent (J := J)).trans (equivShrink V).toEmbedding
  have hle : succ V.card ≤ V.card := by
    simpa only [J, Cardinal.mk_toType, Cardinal.card_ord, ZFSet.card]
      using Cardinal.mk_le_of_injective e.injective
  exact (lt_succ V.card).not_ge hle

end NoPattern

end CHObstruction

end

end OAI

-- ===== Partition.lean =====

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace EndHomogeneous

variable {J X C : Type u} [LinearOrder J] [LinearOrder X]
  (wJ : WellFounded ((· < ·) : J → J → Prop))
  (wX : WellFounded ((· < ·) : X → X → Prop)) (c : Finset X → C)

def residual (x : X) (α : J) (f : ∀ β, β < α → X) : Set X :=
  {y | (∀ β h, f β h < y) ∧
    ∀ a : Finset {β : J // β < α},
      c (insert y (a.image (fun β => f β.val β.property))) =
        c (insert x (a.image (fun β => f β.val β.property)))}

def step (x : X) (α : J) (f : ∀ β, β < α → X) : X := by
  classical
  exact if h : (residual c x α f).Nonempty then wX.min (residual c x α f) h else x

def rep (x : X) : J → X := wJ.fix (step wX c x)

theorem rep_eq (x : X) (α : J) :
    rep wJ wX c x α = step wX c x α (fun β _ => rep wJ wX c x β) :=
  wJ.fix_eq _ α

theorem active (x : X) (α : J) (h : ∀ β < α, rep wJ wX c x β < x) :
    (∀ β < α, rep wJ wX c x β < rep wJ wX c x α) ∧
    (∀ a : Finset {β : J // β < α},
      c (insert (rep wJ wX c x α) (a.image (fun β => rep wJ wX c x β.val))) =
        c (insert x (a.image (fun β => rep wJ wX c x β.val)))) ∧
    rep wJ wX c x α ≤ x := by
  let R := residual c x α (fun β _ => rep wJ wX c x β)
  have hx : x ∈ R := ⟨h, fun _ => rfl⟩
  have hn : R.Nonempty := ⟨x, hx⟩
  have he : rep wJ wX c x α = wX.min R hn := by
    rw [rep_eq, step, dite_eq_left hn]
  rw [he]
  exact ⟨(wX.min_mem R hn).1, (wX.min_mem R hn).2, not_lt.mp (wX.not_lt_min R hx)⟩

theorem lt_of_no_stop (x : X) (α : J)
    (h : ∀ β ≤ α, rep wJ wX c x β ≠ x) : rep wJ wX c x α < x := by
  induction α using wJ.induction with
  | h α ih =>
    have hp : ∀ β < α, rep wJ wX c x β < x := by
      intro β hβ
      exact ih β hβ (fun γ hγ => h γ (hγ.trans hβ.le))
    exact lt_of_le_of_ne (active wJ wX c x α hp).2.2 (h α le_rfl)

def Stops (x : X) : Prop := ∃ α, rep wJ wX c x α = x

def first (x : X) (h : Stops wJ wX c x) : J :=
  wJ.min {α | rep wJ wX c x α = x} h

theorem first_eq (x : X) (h : Stops wJ wX c x) :
    rep wJ wX c x (first wJ wX c x h) = x := wJ.min_mem _ h

theorem before_first (x : X) (h : Stops wJ wX c x) (β : J)
    (hβ : β < first wJ wX c x h) : rep wJ wX c x β < x := by
  apply lt_of_no_stop wJ wX c
  intro γ hγ he
  exact (wJ.not_lt_min _ he) (hγ.trans_lt hβ)

def profile (x : X) (a : Finset J) : C := c (insert x (a.image (rep wJ wX c x)))

theorem equal_reps {x y : X} (α : J)
    (hx : ∀ β < α, rep wJ wX c x β < x)
    (hy : ∀ β < α, rep wJ wX c y β < y)
    (hp : profile wJ wX c x = profile wJ wX c y) :
    rep wJ wX c x α = rep wJ wX c y α := by
  induction α using wJ.induction with
  | h α ih =>
    have hr : ∀ β < α, rep wJ wX c x β = rep wJ wX c y β := by
      intro β hβ
      exact ih β hβ (fun γ hγ => hx γ (hγ.trans hβ))
        (fun γ hγ => hy γ (hγ.trans hβ))
    have hfun : (fun β (_ : β < α) => rep wJ wX c x β) =
        (fun β (_ : β < α) => rep wJ wX c y β) := by funext β hβ; exact hr β hβ
    have hR : residual c x α (fun β _ => rep wJ wX c x β) =
        residual c y α (fun β _ => rep wJ wX c y β) := by
      ext z
      change ((∀ β < α, rep wJ wX c x β < z) ∧ _) ↔
        ((∀ β < α, rep wJ wX c y β < z) ∧ _)
      have hcol (a : Finset {β : J // β < α}) :
          c (insert x (a.image (fun β => rep wJ wX c x β.val))) =
            c (insert y (a.image (fun β => rep wJ wX c y β.val))) := by
        have hh := congrFun hp (a.image Subtype.val)
        simpa only [profile, Finset.image_image, Function.comp_def] using hh
      have hf : (fun β : {β : J // β < α} => rep wJ wX c x β.val) =
          (fun β : {β : J // β < α} => rep wJ wX c y β.val) := by
        funext β; exact hr β.val β.property
      constructor
      · rintro ⟨h₁, h₂⟩
        refine ⟨fun β hβ => by rw [← hr β hβ]; exact h₁ β hβ, ?_⟩
        intro a
        calc
          _ = c (insert z (a.image (fun β => rep wJ wX c x β.val))) := by rw [hf]
          _ = c (insert x (a.image (fun β => rep wJ wX c x β.val))) := h₂ a
          _ = _ := hcol a
      · rintro ⟨h₁, h₂⟩
        refine ⟨fun β hβ => by rw [hr β hβ]; exact h₁ β hβ, ?_⟩
        intro a
        calc
          _ = c (insert z (a.image (fun β => rep wJ wX c y β.val))) := by rw [hf]
          _ = c (insert y (a.image (fun β => rep wJ wX c y β.val))) := h₂ a
          _ = _ := (hcol a).symm
    have hn : (residual c x α (fun β _ => rep wJ wX c x β)).Nonempty :=
      ⟨x, hx, fun _ => rfl⟩
    rw [rep_eq, rep_eq, step, step, dite_eq_left hn, dite_eq_left (hR ▸ hn)]
    congr 1

def stopCode (x : {x : X // Stops wJ wX c x}) : J × (Finset J → C) :=
  (first wJ wX c x.val x.property, profile wJ wX c x.val)

theorem stopCode_injective : Function.Injective (stopCode wJ wX c) := by
  intro x y h
  have hα := congrArg Prod.fst h
  have hp := congrArg Prod.snd h
  apply Subtype.ext
  rw [← first_eq wJ wX c x.val x.property, ← first_eq wJ wX c y.val y.property]
  change first wJ wX c x.val x.property = first wJ wX c y.val y.property at hα
  rw [← hα]
  exact equal_reps wJ wX c _ (before_first wJ wX c x.val x.property)
    (fun β hβ => before_first wJ wX c y.val y.property β (hα ▸ hβ)) hp

include wJ wX in

theorem exists_sequence
    (hcard : #(J × (Finset J → C)) < #X) :
    ∃ x : X, ∃ r : J ↪o X,
      (∀ α, r α < x) ∧
      ∀ α (a : Finset {β : J // β < α}),
        c (insert (r α) (a.image (fun β => r β.val))) =
          c (insert x (a.image (fun β => r β.val))) := by
  have hn : ∃ x : X, ¬ Stops wJ wX c x := by
    by_contra! hall
    let e : X ↪ {x : X // Stops wJ wX c x} :=
      ⟨fun x => ⟨x, hall x⟩, fun _ _ h => congrArg Subtype.val h⟩
    exact hcard.not_ge (Cardinal.mk_le_of_injective
      ((stopCode_injective wJ wX c).comp e.injective))
  obtain ⟨x, hx⟩ := hn
  have hl : ∀ α, rep wJ wX c x α < x := by
    intro α
    exact lt_of_no_stop wJ wX c x α (fun β _ he => hx ⟨β, he⟩)
  have hs : StrictMono (rep wJ wX c x) := by
    intro α β hαβ
    exact (active wJ wX c x β (fun γ _ => hl γ)).1 α hαβ
  refine ⟨x, OrderEmbedding.ofStrictMono _ hs, hl, ?_⟩
  intro α a
  exact (active wJ wX c x α (fun β _ => hl β)).2.1 a

end EndHomogeneous

namespace FinitePartition

def Constant {X C : Type u} (c : Finset X → C) (m : ℕ) (Y : Set X) (p : C) : Prop :=
  ∀ s : Finset X, (↑s : Set X) ⊆ Y → s.card = m → c s = p

def Homogeneous {X C : Type u} (c : Finset X → C) (m : ℕ) (Y : Set X) : Prop :=
  ∃ p, Constant c m Y p

theorem arity_step {J X C : Type u} [LinearOrder J] [LinearOrder X]
    (c : Finset X → C) (x : X) (r : J ↪o X)
    (he : ∀ α (a : Finset {β : J // β < α}),
      c (insert (r α) (a.image (fun β => r β.val))) =
        c (insert x (a.image (fun β => r β.val))))
    {m : ℕ} {Y : Set J}
    (hh : Homogeneous (fun a => c (insert x (a.image r))) m Y) :
    Homogeneous c (m + 1) (r '' Y) := by
  classical
  obtain ⟨p, hp⟩ := hh
  refine ⟨p, ?_⟩
  intro s hs hc
  let t := s.preimage r r.injective.injOn
  have ht : t.image r = s := by
    rw [Finset.image_preimage]
    exact Finset.filter_eq_self.2 (fun a ha => Set.image_subset_range r Y (hs ha))
  have htc : t.card = m + 1 := by
    rw [← Finset.card_image_of_injective t r.injective, ht, hc]
  have htn : t.Nonempty := Finset.card_pos.1 (by omega)
  let α := t.max' htn
  have hα : α ∈ t := Finset.max'_mem t htn
  have hlt : ∀ β ∈ t.erase α, β < α := by
    intro β hβ
    exact lt_of_le_of_ne (Finset.le_max' t β (Finset.mem_erase.1 hβ).2)
      (Finset.mem_erase.1 hβ).1
  let a : Finset {β : J // β < α} :=
    (t.erase α).attach.image (fun β => ⟨β.val, hlt β.val β.property⟩)
  have him : a.image (fun β => r β.val) = (t.erase α).image r := by
    dsimp [a]
    rw [Finset.image_image]
    change (t.erase α).attach.image (r ∘ Subtype.val) = _
    rw [← Finset.image_image, Finset.attach_image_val]
  have hp' : c (insert x ((t.erase α).image r)) = p := by
    apply hp
    · intro β hβ
      have hb : r β ∈ s := Finset.mem_preimage.1 (Finset.mem_erase.1 hβ).2
      obtain ⟨γ, hγ, heq⟩ := hs hb
      exact (r.injective heq) ▸ hγ
    · rw [Finset.card_erase_of_mem hα, htc, Nat.add_sub_cancel]
  calc
    c s = c (insert (r α) ((t.erase α).image r)) := by
      rw [← Finset.image_insert, Finset.insert_erase hα, ht]
    _ = c (insert x ((t.erase α).image r)) := by simpa only [him] using he α a
    _ = p := hp'

theorem power_lt {Λ ξ ζ : Cardinal.{u}} (hΛ : Λ.IsStrongLimit)
    (hinf : ℵ₀ ≤ Λ) (hξ : ξ < Λ) (hζ : ζ < Λ) : ξ ^ ζ < Λ := by
  apply lt_of_le_of_lt (Cardinal.power_le_power_right (Cardinal.cantor ξ).le)
  rw [← Cardinal.power_mul]
  exact hΛ.isStrongPrelimit (Cardinal.mul_lt_of_lt hinf hξ hζ)

theorem estimate {Λ ξ : Cardinal.{u}} (hΛ : Λ.IsStrongLimit)
    (hξinf : ℵ₀ ≤ ξ) (hξ : ξ < Λ) (m : ℕ) :
    ∀ χ, ℵ₀ ≤ χ → χ < Λ →
    ∃ μ, ℵ₀ ≤ μ ∧ μ < Λ ∧
      ∀ (X C : Type u) [LinearOrder X],
        WellFounded ((· < ·) : X → X → Prop) → #X = μ → #C ≤ ξ →
        ∀ c : Finset X → C, ∃ Y : Set X, χ ≤ #Y ∧ Homogeneous c m Y := by
  classical
  induction m with
  | zero =>
    intro χ hχinf hχ
    refine ⟨χ, hχinf, hχ, ?_⟩
    intro X C _ _ hX _ c
    refine ⟨Set.univ, ?_, c ∅, ?_⟩
    · simp only [Cardinal.mk_univ, hX, le_refl]
    · intro s _ hs
      rw [Finset.card_eq_zero.1 hs]
  | succ m ih =>
    intro χ hχinf hχ
    obtain ⟨ζ, hζinf, hζ, hζpart⟩ := ih χ hχinf hχ
    let q := max ℵ₀ (ζ * ξ ^ ζ)
    have hinf : ℵ₀ < Λ := hξinf.trans_lt hξ
    have hq : q < Λ := max_lt hinf
      (Cardinal.mul_lt_of_lt hinf.le hζ (power_lt hΛ hinf.le hξ hζ))
    refine ⟨succ q, (le_max_left _ _).trans (le_succ q), hΛ.isSuccLimit.succ_lt hq, ?_⟩
    intro X C _ wX hX hC c
    let J := ζ.ord.ToType
    have hJ : #J = ζ := by simp [J]
    have : Infinite J := Cardinal.aleph0_le_mk_iff.1 (hJ ▸ hζinf)
    have hcode : #(J × (Finset J → C)) < #X := by
      rw [Cardinal.mk_prod, Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_id,
        Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_finset_of_infinite, hJ, hX]
      apply lt_of_le_of_lt _ (lt_succ q)
      apply le_trans _ (le_max_right _ _)
      exact mul_le_mul' le_rfl (Cardinal.power_le_power_right hC)
    obtain ⟨x, r, _, he⟩ := EndHomogeneous.exists_sequence
      (wellFounded_lt (α := J)) wX c hcode
    obtain ⟨Y, hY, hh⟩ := hζpart J C
      (wellFounded_lt (α := J)) hJ hC (fun a => c (insert x (a.image r)))
    refine ⟨r '' Y, ?_, arity_step c x r he hh⟩
    rwa [Cardinal.mk_image_eq r.injective]

end FinitePartition

namespace ThresholdArithmetic

def ξ : Cardinal.{u} := (2 : Cardinal.{u}) ^ (ℵ_ 1)

theorem palette_infinite : ℵ₀ ≤ ξ.{u} :=
  (aleph0_le_aleph 1).trans (Cardinal.cantor _).le

theorem palette_lt : ξ.{u} < tailThreshold.{u} :=
  (lt_succ ξ).trans_le (Cardinal.le_beth_ord _)

theorem index_limit : IsSuccLimit (succ ξ.{u}).ord :=
  Cardinal.isSuccLimit_ord (palette_infinite.trans (le_succ ξ))

theorem strongLimit : tailThreshold.{u}.IsStrongLimit :=
  Cardinal.isStrongLimit_beth.2 index_limit.isSuccPrelimit

theorem cofinality : tailThreshold.{u}.ord.cof = succ ξ.{u} := by
  change ((Cardinal.ord ∘ Cardinal.beth) (succ ξ).ord).cof = succ ξ
  rw [Ordinal.cof_map_of_isNormal (Cardinal.isNormal_ord.comp Cardinal.isNormal_beth) index_limit]
  exact (Cardinal.isRegular_succ palette_infinite).cof_ord

theorem palette_lt_cofinality : ξ.{u} < tailThreshold.{u}.ord.cof := by
  rw [cofinality]
  exact lt_succ _

theorem endpoint_eq_hanf (hCH : CH.{u}) : endpoint.{u} = hanf (ℵ₀ : Cardinal.{u}) := by
  unfold endpoint hanf
  rw [hCH, Cardinal.succ_aleph, Cardinal.ord_aleph]
  congr 2
  norm_num

end ThresholdArithmetic

namespace FinitePartition

variable {X J C : Type u}

theorem Constant.mono {c : Finset X → C} {m : ℕ} {Y Z : Set X} {p : C}
    (hc : Constant c m Y p) (hZY : Z ⊆ Y) : Constant c m Z p :=
  fun s hs => hc s (hs.trans hZY)

theorem Constant.image [DecidableEq X] (c : Finset X → C) (e : J ↪ X) {m : ℕ} {Y : Set J} {p : C}
    (hh : Constant (fun s => c (s.image e)) m Y p) : Constant c m (e '' Y) p := by
  classical
  intro s hs hc
  let t := s.preimage e e.injective.injOn
  have ht : t.image e = s := by
    rw [Finset.image_preimage]
    exact Finset.filter_eq_self.2 (fun a ha => Set.image_subset_range e Y (hs ha))
  rw [← ht]
  apply hh
  · intro a ha
    obtain ⟨b, hb, heq⟩ := hs (Finset.mem_preimage.1 ha)
    exact (e.injective heq) ▸ hb
  · rw [← Finset.card_image_of_injective t e.injective, ht, hc]

theorem inside {Λ ξ : Cardinal.{u}} (hΛ : Λ.IsStrongLimit)
    (hξinf : ℵ₀ ≤ ξ) (hξ : ξ < Λ) (m : ℕ) (χ : Cardinal.{u})
    (hχinf : ℵ₀ ≤ χ) (hχ : χ < Λ) :
    ∃ μ < Λ, ∀ (X C : Type u), #C ≤ ξ → ∀ (Y : Set X), μ ≤ #Y →
      ∀ c : Finset X → C, ∃ Z ⊆ Y, χ ≤ #Z ∧ Homogeneous c m Z := by
  classical
  obtain ⟨μ, _, hμ, ha⟩ := estimate hΛ hξinf hξ m χ hχinf hχ
  refine ⟨μ, hμ, ?_⟩
  intro X C hC Y hY c
  obtain ⟨e⟩ : Nonempty (μ.ord.ToType ↪ Y) :=
    (Cardinal.le_def _ _).1 (by simpa only [Cardinal.mk_ord_toType] using hY)
  let f := e.trans (Function.Embedding.subtype (· ∈ Y))
  obtain ⟨Z, hZ, p, hp⟩ := ha μ.ord.ToType C wellFounded_lt (Cardinal.mk_ord_toType μ)
    hC (fun s => c (s.image f))
  refine ⟨f '' Z, ?_, ?_, p, Constant.image c f hp⟩
  · rintro _ ⟨z, _, rfl⟩
    exact (e z).property
  · rwa [Cardinal.mk_image_eq f.injective]

end FinitePartition

namespace FinitePatterns

open FinitePartition

variable {X C : Type u} (Λ ξ : Cardinal.{u}) (c : ℕ → Finset X → C)

def Prefix (n : ℕ) (p : ℕ → C) (Y : Set X) : Prop :=
  ∀ j < n, Constant (c j) j Y (p j)

def Unbounded (n : ℕ) (p : ℕ → C) : Prop :=
  ∀ χ < Λ, ∃ Y : Set X, χ ≤ #Y ∧ Prefix c n p Y

variable (hΛ : Λ.IsStrongLimit) (hξinf : ℵ₀ ≤ ξ) (hξ : ξ < Λ)
  (hcof : ξ < Λ.ord.cof) (hC : #C ≤ ξ)

include hΛ hξinf hξ hcof hC in

theorem extend (n : ℕ) (p : ℕ → C) (hg : Unbounded Λ c n p) :
    ∃ q : C, Unbounded Λ c (n + 1) (Function.update p n q) := by
  classical
  by_contra hn
  have hb : ∀ q : C, ∃ χ < Λ, ∀ Y : Set X, χ ≤ #Y →
      ¬ Prefix c (n + 1) (Function.update p n q) Y := by
    intro q
    have hq := (not_exists.mp hn) q
    unfold Unbounded at hq
    obtain ⟨χ, hχ⟩ := not_forall.mp hq
    obtain ⟨hχ, hY⟩ := Classical.not_imp.mp hχ
    exact ⟨χ, hχ, fun Y hcard hp => hY ⟨Y, hcard, hp⟩⟩
  choose b hb hfail using hb
  have hsup : (⨆ q, b q) < Λ := Cardinal.iSup_lt_of_lt_cof_ord (hC.trans_lt hcof) hb
  let χ := max ℵ₀ (⨆ q, b q)
  have hχ : χ < Λ := max_lt (hξinf.trans_lt hξ) hsup
  obtain ⟨μ, hμ, hpart⟩ := inside hΛ hξinf hξ n χ (le_max_left _ _) hχ
  obtain ⟨Y, hY, hp⟩ := hg μ hμ
  obtain ⟨Z, hZY, hZ, q, hq⟩ := hpart X C hC Y hY (c n)
  apply hfail q Z
  · exact (le_ciSup_of_le ⟨Λ, fun q hq => by obtain ⟨q, rfl⟩ := hq; exact (hb q).le⟩ q le_rfl).trans
      ((le_max_right _ _).trans hZ)
  · intro j hj
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjn | rfl
    · rw [Function.update_of_ne hjn.ne]
      exact (hp j hjn).mono hZY
    · rw [Function.update_self]
      exact hq

variable (hX : Λ ≤ #X)

include hX in
theorem initial (p : ℕ → C) : Unbounded Λ c 0 p := by
  intro χ hχ
  refine ⟨Set.univ, ?_, ?_⟩
  · simpa only [Cardinal.mk_univ] using hχ.le.trans hX
  · intro j hj
    omega

def states : (n : ℕ) → {p : ℕ → C // Unbounded Λ c n p}
  | 0 => ⟨fun _ => c 0 ∅, initial Λ c hX _⟩
  | n + 1 =>
    let s := states n
    let h := extend Λ ξ c hΛ hξinf hξ hcof hC n s.val s.property
    ⟨Function.update s.val n h.choose, h.choose_spec⟩

def colors (n : ℕ) : C := (states Λ ξ c hΛ hξinf hξ hcof hC hX (n + 1)).val n

theorem states_agree (n j : ℕ) (hj : j < n) :
    (states Λ ξ c hΛ hξinf hξ hcof hC hX n).val j =
      colors Λ ξ c hΛ hξinf hξ hcof hC hX j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
    · change Function.update _ n _ j = _
      rw [Function.update_of_ne h.ne]
      exact ih h
    · rfl

theorem colors_unbounded (n : ℕ) :
    Unbounded Λ c n (colors Λ ξ c hΛ hξinf hξ hcof hC hX) := by
  intro χ hχ
  obtain ⟨Y, hY, hp⟩ := (states Λ ξ c hΛ hξinf hξ hcof hC hX n).property χ hχ
  refine ⟨Y, hY, ?_⟩
  intro j hj
  rw [← states_agree Λ ξ c hΛ hξinf hξ hcof hC hX n j hj]
  exact hp j hj

include hΛ hξinf hξ hcof hC hX in

theorem exists_patterns :
    ∃ p : ℕ → C, ∀ k : ℕ, ∃ A : Finset X, A.card = k ∧
      ∀ j ≤ k, ∀ s ⊆ A, s.card = j → c j s = p j := by
  classical
  refine ⟨colors Λ ξ c hΛ hξinf hξ hcof hC hX, ?_⟩
  intro k
  obtain ⟨Y, hY, hp⟩ := colors_unbounded Λ ξ c hΛ hξinf hξ hcof hC hX
    (k + 1) ℵ₀ (hξinf.trans_lt hξ)
  have hi : Infinite Y := Cardinal.aleph0_le_mk_iff.1 hY
  obtain ⟨A, hA, hc⟩ := (Set.infinite_coe_iff.1 hi).exists_subset_card_eq k
  refine ⟨A, hc, ?_⟩
  intro j hj s hs hsc
  exact hp j (Nat.lt_succ_of_le hj) s ((Finset.coe_subset.2 hs).trans hA) hsc

end FinitePatterns

end CHObstruction

end

end OAI

-- ===== Colors.lean =====

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Colors

abbrev Sequence := ℕ → Bool

def equivalent (a b : Sequence) : Prop := {n | a n ≠ b n}.Finite

def eventualSetoid : Setoid Sequence where
  r := equivalent
  iseqv := ⟨by intro a; simp [equivalent], by
    intro a b h
    simpa only [equivalent, ne_comm] using h, by
    intro a b c hab hbc
    apply (hab.union hbc).subset
    intro n hn
    by_cases hab' : a n = b n
    · exact Or.inr (fun hbc' => hn (hab'.trans hbc'))
    · exact Or.inl hab' ⟩

abbrev Color := Quotient eventualSetoid

def color (a : Sequence) : Color := Quotient.mk _ a

theorem color_eq_iff (a b : Sequence) : color a = color b ↔ equivalent a b :=
  Quotient.eq

def repeatSequence (a : Sequence) : Sequence := fun i => a (Nat.unpair i).1

theorem repeat_injective : Function.Injective (fun a => color (repeatSequence a)) := by
  intro a b hab
  have h := (color_eq_iff _ _).1 hab
  funext n
  by_contra hn
  have hi : Function.Injective (Nat.pair n) := by
    intro j k heq
    have := congrArg Nat.unpair heq
    simpa only [Nat.unpair_pair, Prod.mk.injEq, true_and] using this
  have hf : (Set.range (Nat.pair n)).Finite := h.subset (by
    rintro _ ⟨m, rfl⟩
    simpa only [repeatSequence, Nat.unpair_pair, Set.mem_ofPred_eq] using hn)
  exact Set.infinite_univ ((hf.preimage hi.injOn).subset (fun _ _ => Set.mem_range_self _))

theorem cardinal : #Color = (𝔠 : Cardinal) := by
  have h : #Sequence = (𝔠 : Cardinal) := by simp [Sequence]
  apply le_antisymm
  · exact Cardinal.mk_quotient_le.trans h.le
  · exact h.symm.le.trans (Cardinal.mk_le_of_injective repeat_injective)

abbrev Palette := ULift.{u} Color

theorem palette_cardinal : #Palette.{u} = (𝔠 : Cardinal.{u}) := by
  rw [Cardinal.mk_uLift, cardinal, Cardinal.lift_continuum]

def representative (s : Color) : Sequence := Quotient.out s

theorem representative_color (s : Color) : color (representative s) = s := Quotient.out_eq s

theorem function_bound (A : Type) [Countable A] (B : Type u)
    (hB : #B ≤ (𝔠 : Cardinal.{u})) : #(A → B) ≤ (𝔠 : Cardinal.{u}) := by
  rw [Cardinal.mk_arrow, Cardinal.lift_uzero]
  have hA : Cardinal.lift.{u} #A ≤ (ℵ₀ : Cardinal.{u}) := by
    simpa only [Cardinal.lift_aleph0] using
      (Cardinal.lift_le.{u, 0}.2 (Cardinal.mk_le_aleph0 (α := A)))
  exact ((Cardinal.power_le_power_right hB).trans
    (Cardinal.power_le_power_left Cardinal.continuum_ne_zero hA)).trans_eq
    Cardinal.continuum_power_aleph0

open Diagrams

theorem diagram_bound (hCH : CH.{u}) (n : ℕ) :
    #(Diagram.{u} (Fin n)) ≤ (𝔠 : Cardinal.{u}) := by
  let A := Label (Fin n)
  have hc : Cardinal.lift.{u} #(A → A → Prop) ≤ (𝔠 : Cardinal.{u}) := by
    have h : #(A → A → Prop) ≤ (𝔠 : Cardinal) :=
      function_bound A _ (function_bound A Prop (by rw [Cardinal.mk_Prop]; exact (Cardinal.nat_lt_continuum 2).le))
    simpa only [Cardinal.lift_continuum] using
      (Cardinal.lift_le.{u, 0}.2 h)
  have ht : #(A → Tag.{u}) ≤ (𝔠 : Cardinal.{u}) :=
    function_bound A _ (by rw [Cardinal.mk_toType, Ordinal.card_omega, ← Cardinal.two_power_aleph0, hCH])
  let f : Diagram.{u} (Fin n) → ((A → A → Prop) × (A → A → Prop)) × (A → Tag.{u}) :=
    fun d => ((d.eqv, d.rel), d.tag)
  have hf : Function.Injective f := by
    intro d e h
    cases d; cases e
    simpa only [f, Prod.mk.injEq, Diagram.mk.injEq, and_assoc] using h
  apply (Cardinal.mk_le_of_injective hf).trans
  simp only [Cardinal.mk_prod, Cardinal.lift_mul, Cardinal.lift_id, Cardinal.lift_uzero]
  exact (mul_le_mul' (mul_le_mul' hc hc) ht).trans_eq (by
    rw [Cardinal.mul_eq_self Cardinal.aleph0_le_continuum,
      Cardinal.mul_eq_self Cardinal.aleph0_le_continuum])

def code (hCH : CH.{u}) : (Σ n : ℕ, Diagram.{u} (Fin (n + 1))) ↪ Palette.{u} := by
  apply Classical.choice
  apply (Cardinal.le_def _ _).1
  rw [palette_cardinal, Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun n : ℕ => #(Diagram.{u} (Fin (n + 1)))) ≤
        Cardinal.sum (fun _ : ℕ => (𝔠 : Cardinal.{u})) :=
      Cardinal.sum_le_sum _ _ (fun n => diagram_bound hCH (n + 1))
    _ = (𝔠 : Cardinal.{u}) := by
      simp only [Cardinal.sum_const, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_uzero]
      exact Cardinal.aleph0_mul_continuum

end Colors

namespace Tuples

abbrev Tuple (I : Type v) := Σ n : ℕ, Fin (n + 1) ↪ I

def sub {I : Type v} (t : Tuple I) {m : ℕ} (e : Fin (m + 1) ↪o Fin (t.1 + 1)) :
    Tuple I := ⟨m, e.toEmbedding.trans t.2⟩

@[simp] theorem sub_refl {I : Type v} (t : Tuple I) :
    sub t (OrderIso.refl _).toOrderEmbedding = t := by
  cases t
  rfl

theorem sub_comp {I : Type v} (t : Tuple I) {m k : ℕ}
    (e : Fin (m + 1) ↪o Fin (t.1 + 1)) (f : Fin (k + 1) ↪o Fin (m + 1)) :
    sub (sub t e) f = sub t (f.comp e) := rfl

end Tuples

namespace Tests

theorem embedding_refl (A : Type v) [Preorder A] :
    (OrderIso.refl A).toOrderEmbedding.toEmbedding = Function.Embedding.refl A := by
  ext x
  rfl

open Diagrams Colors Tuples

variable (hCH : CH.{u})

def Passes {n : ℕ}
    (s : ∀ m : ℕ, (Fin (m + 1) ↪o Fin (n + 1)) → Palette.{u}) : Prop :=
  ∃ d : Diagram.{u} (Fin (n + 1)), ∀ m (e : Fin (m + 1) ↪o Fin (n + 1)),
    (d.restrict e.toEmbedding).Valid ∧
      code hCH ⟨m, d.restrict e.toEmbedding⟩ = s m e

def Test {I : Type v} (c : Tuple I → Palette.{u}) (t : Tuple I) : Prop :=
  Passes hCH (fun _ e => c (sub t e))

instance emptyLabel : IsEmpty (Label (Fin 0)) := ⟨fun l => by
  obtain ⟨x, _⟩ := l.1.property
  exact Fin.elim0 x⟩

def emptyDiagram : Diagram.{u} (Fin 0) where
  eqv a := isEmptyElim a
  rel a := isEmptyElim a
  tag a := isEmptyElim a

theorem empty_valid : emptyDiagram.{u}.Valid := by
  constructor
  · exact ⟨fun a => isEmptyElim a, fun {a} => isEmptyElim a, fun {a} => isEmptyElim a⟩
  all_goals intro a; exact isEmptyElim a

theorem empty_unique (d : Diagram.{u} (Fin 0)) : d = emptyDiagram := by
  cases d
  congr <;> funext a <;> exact isEmptyElim a

theorem no_pattern (p : ℕ → Palette.{u})
    (hp : ∀ n : ℕ, Passes hCH (n := n) (fun m _ => p m)) : False := by
  choose d hd using hp
  have hvalid : ∀ n, (d n).Valid := by
    intro n
    simpa only [embedding_refl, Diagram.restrict_refl] using (hd n n (OrderIso.refl _).toOrderEmbedding).1
  have hcode : ∀ n, code hCH ⟨n, d n⟩ = p n := by
    intro n
    simpa only [embedding_refl, Diagram.restrict_refl] using (hd n n (OrderIso.refl _).toOrderEmbedding).2
  have hcoh : ∀ m n (e : Fin (m + 1) ↪o Fin (n + 1)),
      d m = (d n).restrict e.toEmbedding := by
    intro m n e
    have he := (code hCH).injective ((hcode m).trans (hd n m e).2.symm)
    exact eq_of_heq (Sigma.mk.inj_iff.1 he).2
  let allD : ∀ k : ℕ, Diagram.{u} (Fin k)
    | 0 => emptyDiagram
    | n + 1 => d n
  apply NoPattern.impossible allD
  · intro k
    cases k with
    | zero => exact empty_valid
    | succ n => exact hvalid n
  · intro m n e
    cases m with
    | zero => exact (empty_unique ((allD n).restrict e.toEmbedding)).symm
    | succ m =>
      cases n with
      | zero => exact Fin.elim0 (e 0)
      | succ n => exact hcoh m n e

end Tests

end CHObstruction

end

end OAI

-- ===== EndpointDiagrams.lean =====

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace EndpointDiagrams

open Diagrams CountableClosures Tuples

abbrev V := ZFSet.vonNeumann (ω_ (2 : Ordinal.{u}))
abbrev D := Shrink.{u} V.{u}

def element : D.{u} ≃ V.{u} := (equivShrink V).symm

def membership (a b : D.{u}) : Prop := (element a).val ∈ (element b).val

theorem separates : ∀ a b : D.{u}, a ≠ b → ∃ w, ¬ (membership w a ↔ membership w b) := by
  intro a b hab
  obtain ⟨w, hw⟩ := membership_separates V (ZFSet.isTransitive_vonNeumann _)
    (element a) (element b) (fun he => hab (element.injective he))
  refine ⟨element.symm w, ?_⟩
  simpa only [membership, Equiv.apply_symm_apply] using hw

def rank (a : D.{u}) : Domination.Alpha.{u} :=
  ⟨(element a).val.rank, ZFSet.mem_vonNeumann.1 (element a).property⟩

def seed {k : ℕ} (t : Fin k ↪ D.{u}) (J : {J : Finset (Fin k) // J.Nonempty}) :
    FiniteSeed D.{u} := ⟨J.val.map t, J.property.map⟩

def fullSeed (t : Tuple D.{u}) : FiniteSeed D.{u} := seed t.2 ⟨Finset.univ, Finset.univ_nonempty⟩

def entry {k : ℕ} (t : Fin k ↪ D.{u}) (l : Label (Fin k)) : D.{u} :=
  (enumeration membership separates (seed t l.1) l.2).val

theorem entry_mem (t : Tuple D.{u}) (l : Label (Fin (t.1 + 1))) :
    entry t.2 l ∈ entries membership separates (fullSeed t) := by
  exact entries_mono membership separates (seed t.2 l.1) (fullSeed t)
    (Finset.map_subset_map.mpr (Finset.subset_univ _))
    (enumeration membership separates (seed t.2 l.1) l.2).property

theorem entry_surjective (t : Tuple D.{u}) (x : entries membership separates (fullSeed t)) :
    ∃ l, entry t.2 l = x.val := by
  obtain ⟨n, hn⟩ := enumeration_surjective membership separates (fullSeed t) x
  exact ⟨(⟨Finset.univ, Finset.univ_nonempty⟩, n), congrArg Subtype.val hn⟩

theorem entry_root {k : ℕ} (t : Fin k ↪ D.{u}) (i : Fin k) :
    entry t (Label.root i) = t i := by
  have hs : seed t (Label.root i).1 = ⟨{t i}, Finset.singleton_nonempty _⟩ := by
    apply Subtype.ext
    exact Finset.map_singleton _ _
  unfold entry
  rw [hs]
  exact enumeration_singleton membership separates (t i)

theorem entry_comp {k m : ℕ} (t : Fin k ↪ D.{u}) (e : Fin m ↪ Fin k) (l : Label (Fin m)) :
    entry (e.trans t) l = entry t (Label.map e l) := by
  have hs : seed (e.trans t) l.1 = seed t (Label.map e l).1 := by
    apply Subtype.ext
    exact (Finset.map_map e t l.1.val).symm
  unfold entry
  rw [hs]
  rfl

def beta (b : Tag.{u}) : Domination.Beta.{u} := b.toOrd

def localTag (b : Tag.{u}) (a : D.{u}) : Tag.{u} :=
  Ordinal.ToType.mk (Domination.values (rank a) (beta b))

@[simp] theorem localTag_value (b : Tag.{u}) (a : D.{u}) :
    tagOrdinal (localTag b a) = (Domination.values (rank a) (beta b)).val := by
  exact congrArg Subtype.val (Ordinal.ToType.mk.symm_apply_apply _)

def diagram {k : ℕ} (t : Fin k ↪ D.{u}) (b : Tag.{u}) : Diagram.{u} (Fin k) where
  eqv l l' := entry t l = entry t l'
  rel l l' := membership (entry t l) (entry t l')
  tag l := localTag b (entry t l)

theorem diagram_restrict {k m : ℕ} (t : Fin k ↪ D.{u}) (e : Fin m ↪ Fin k) (b : Tag.{u}) :
    diagram (e.trans t) b = (diagram t b).restrict e := by
  unfold diagram Diagram.restrict
  congr 1 <;> funext l
  · funext l'; rw [entry_comp, entry_comp]
  · funext l'; rw [entry_comp, entry_comp]
  · rw [entry_comp]

def Good (X : FiniteSeed D.{u}) (b : Tag.{u}) : Prop :=
  ∀ a c : entries membership separates X, membership a.val c.val →
    tagOrdinal (localTag b a.val) < tagOrdinal (localTag b c.val)

theorem countable_bad (X : FiniteSeed D.{u}) : {b | ¬ Good X b}.Countable := by
  classical
  have : Countable (entries membership separates X) :=
    Set.countable_coe_iff.2 (entries_countable membership separates X)
  let bad (a c : entries membership separates X) : Set Tag.{u} :=
    if h : membership a.val c.val then
      {b | (Domination.values (rank c.val) (beta b)).val ≤
        (Domination.values (rank a.val) (beta b)).val} else ∅
  have hb : ∀ a c, (bad a c).Countable := by
    intro a c
    dsimp only [bad]
    split_ifs with h
    · have hr : (rank a.val).val < (rank c.val).val := ZFSet.rank_lt_of_mem h
      exact (Domination.countable_exceptions (rank c.val) ⟨(rank a.val).val, hr⟩).preimage
        Ordinal.ToType.mk.symm.injective
    · exact Set.countable_empty
  apply (Set.countable_iUnion (fun a => Set.countable_iUnion (hb a))).mono
  intro b h
  simp only [Good, not_forall] at h
  obtain ⟨a, c, hm, hlt⟩ := h
  exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨c, by
    simpa only [bad, dite_eq_left hm, Set.mem_ofPred_eq, localTag_value, not_lt] using hlt⟩⟩

theorem good_mono {X Y : FiniteSeed D.{u}} (hXY : X.val ⊆ Y.val) {b : Tag.{u}}
    (h : Good Y b) : Good X b := by
  intro a c hac
  exact h ⟨a.val, entries_mono membership separates X Y hXY a.property⟩
    ⟨c.val, entries_mono membership separates X Y hXY c.property⟩ hac

theorem diagram_valid (t : Tuple D.{u}) (b : Tag.{u}) (hb : Good (fullSeed t) b) :
    (diagram t.2 b).Valid := by
  constructor
  · exact ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩
  · intro a a' c c' haa hcc
    change membership _ _ ↔ membership _ _
    rw [show entry t.2 a = entry t.2 a' from haa,
      show entry t.2 c = entry t.2 c' from hcc]
  · intro a a' haa
    exact congrArg (localTag b) haa
  · intro a c hac
    exact hb ⟨entry t.2 a, entry_mem t a⟩ ⟨entry t.2 c, entry_mem t c⟩ hac
  · intro a c h
    apply CountableClosures.extensional membership separates
      (entry_mem t a) (entry_mem t c)
    intro z hz
    obtain ⟨l, hl⟩ := entry_surjective t ⟨z, hz⟩
    simpa only [diagram, hl] using h l
  · intro i j hij
    apply t.2.injective
    simpa only [diagram, entry_root] using hij

theorem sub_seed (t : Tuple D.{u}) {m : ℕ} (e : Fin (m + 1) ↪o Fin (t.1 + 1)) :
    (fullSeed (sub t e)).val ⊆ (fullSeed t).val := by
  change Finset.univ.map (e.toEmbedding.trans t.2) ⊆ Finset.univ.map t.2
  rw [← Finset.map_map]
  exact Finset.map_subset_map.mpr (Finset.subset_univ _)

def colors (hCH : CH.{u}) (t : Tuple D.{u}) (b : Tag.{u}) : Colors.Palette.{u} :=
  Colors.code hCH ⟨t.1, diagram t.2 b⟩

theorem passes (hCH : CH.{u}) (t : Tuple D.{u}) (b : Tag.{u}) (hb : Good (fullSeed t) b) :
    Tests.Test hCH (fun t => colors hCH t b) t := by
  refine ⟨diagram t.2 b, ?_⟩
  intro m e
  rw [← diagram_restrict]
  exact ⟨diagram_valid (sub t e) b (good_mono (sub_seed t e) hb), rfl⟩

theorem countable_failures (hCH : CH.{u}) (t : Tuple D.{u}) :
    {b | ¬ Tests.Test hCH (fun t => colors hCH t b) t}.Countable :=
  (countable_bad (fullSeed t)).mono (fun b h hb => h (passes hCH t b hb))

theorem cardinal : #D.{u} = endpoint.{u} := by
  change V.card = _
  rw [ZFSet.card_vonNeumann]
  apply Cardinal.preBeth_of_omega0_sq_le
  apply le_of_lt
  rw [← Cardinal.ord_aleph, Cardinal.lt_ord, pow_two, Ordinal.card_mul,
    Ordinal.card_omega0, Cardinal.aleph0_mul_aleph0]
  exact Cardinal.aleph0_lt_aleph.2 (by norm_num)

end EndpointDiagrams

end CHObstruction

end

end OAI

-- ===== TailBound.lean =====

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace TuplePatterns

open Tuples

variable {I : Type u} [LinearOrder I]

def sorted (s : Finset I) {n : ℕ} (hs : s.card = n + 1) : Tuple I :=
  ⟨n, (s.orderEmbOfFin hs).toEmbedding⟩

def support (t : Tuple I) : Finset I := Finset.univ.map t.2

omit [LinearOrder I] in
@[simp] theorem support_card (t : Tuple I) : (support t).card = t.1 + 1 := by
  simp only [support, Finset.card_map, Finset.card_univ, Fintype.card_fin]

@[simp] theorem support_sorted (s : Finset I) {n : ℕ} (hs : s.card = n + 1) :
    support (sorted s hs) = s := Finset.map_orderEmbOfFin_univ s hs

omit [LinearOrder I] in
theorem sub_support (t : Tuple I) {m : ℕ} (e : Fin (m + 1) ↪o Fin (t.1 + 1)) :
    support (sub t e) ⊆ support t := by
  change Finset.univ.map (e.toEmbedding.trans t.2) ⊆ Finset.univ.map t.2
  rw [← Finset.map_map]
  exact Finset.map_subset_map.mpr (Finset.subset_univ _)

theorem sub_sorted (s : Finset I) {n m : ℕ} (hs : s.card = n + 1)
    (e : Fin (m + 1) ↪o Fin (n + 1)) :
    sub (sorted s hs) e = sorted (support (sub (sorted s hs) e)) (support_card _) := by
  apply congrArg (Sigma.mk m)
  apply Function.Embedding.ext
  have h := Finset.orderEmbOfFin_unique' (support_card (sub (sorted s hs) e))
    (f := e.trans (s.orderEmbOfFin hs)) (fun x => Finset.mem_map.2 ⟨x, Finset.mem_univ _, rfl⟩)
  exact congrFun (congrArg (fun f : Fin (m + 1) ↪o I => (f : Fin (m + 1) → I)) h)

variable {C : Type u}

def setColor (c : Tuple I → C) (p0 : C) (s : Finset I) : C :=
  if h : s.card ≠ 0 then
    c (sorted s (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h)).symm)
  else p0

theorem setColor_sorted (c : Tuple I → C) (p0 : C) (s : Finset I) {n : ℕ}
    (hs : s.card = n + 1) : setColor c p0 s = c (sorted s hs) := by
  have hn : s.card ≠ 0 := by omega
  rw [setColor, dite_eq_left hn]
  have he : s.card - 1 = n := by omega
  subst n
  rfl

theorem sub_color (c : Tuple I → C) (p0 : C) (p : ℕ → C) (s : Finset I)
    {n : ℕ} (hs : s.card = n + 1)
    (hp : ∀ j ≤ n + 1, ∀ r ⊆ s, r.card = j → setColor c p0 r = p j)
    {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) :
    c (sub (sorted s hs) e) = p (m + 1) := by
  have hm : m + 1 ≤ n + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  have hsub : support (sub (sorted s hs) e) ⊆ s := by
    simpa only [support_sorted] using sub_support (sorted s hs) e
  rw [sub_sorted]
  rw [← setColor_sorted c p0]
  exact hp (m + 1) hm _ hsub (support_card _)

end TuplePatterns

namespace TailBound

open Tuples Diagrams Colors Tests ThresholdArithmetic

variable {I B : Type u} (hCH : CH.{u})

theorem profile_cardinal (hB : #B ≤ (ℵ_ 1 : Cardinal.{u})) : #(B → Palette.{u}) ≤ ξ.{u} := by
  rw [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_id, palette_cardinal, ← Cardinal.two_power_aleph0]
  apply (Cardinal.power_le_power_left (by simpa only [Cardinal.two_power_aleph0] using Cardinal.continuum_ne_zero) hB).trans_eq
  rw [← Cardinal.power_mul, Cardinal.mul_eq_right (Cardinal.aleph0_le_aleph 1)
    (Cardinal.aleph0_le_aleph 1) Cardinal.aleph0_ne_zero]
  rfl

theorem index_lt (hB : #B ≤ (ℵ_ 1 : Cardinal.{u})) (hunc : ¬ Countable B)
    (c : Tuple I → B → Palette.{u})
    (hbad : ∀ t, {b | ¬ Test hCH (fun t => c t b) t}.Countable) :
    #I < tailThreshold.{u} := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  by_contra! hI
  let p0 : B → Palette.{u} := fun _ => ⟨color (fun _ => false)⟩
  obtain ⟨p, hp⟩ := FinitePatterns.exists_patterns tailThreshold ξ
    (fun _ => TuplePatterns.setColor c p0) strongLimit palette_infinite palette_lt
    palette_lt_cofinality (profile_cardinal hB) hI
  choose A hcard hA using (fun n => hp (n + 1))
  let t : ℕ → Tuple I := fun n => TuplePatterns.sorted (A n) (hcard n)
  have hcount : (⋃ n, {b | ¬ Test hCH (fun t => c t b) (t n)}).Countable :=
    Set.countable_iUnion (fun n => hbad (t n))
  obtain ⟨b, hb⟩ : ∃ b : B, b ∉ ⋃ n, {b | ¬ Test hCH (fun t => c t b) (t n)} := by
    by_contra! hn
    apply hunc
    apply Set.countable_univ_iff.1
    exact hcount.mono (fun b _ => hn b)
  have hb' : ∀ n, Test hCH (fun t => c t b) (t n) := by
    intro n
    exact not_not.mp (fun hn => hb (Set.mem_iUnion.2 ⟨n, hn⟩))
  apply Tests.no_pattern hCH (fun n => p (n + 1) b)
  intro n
  have httest := hb' n
  change Passes hCH (n := n) (fun m e => c (sub (t n) e) b) at httest
  obtain ⟨d, hd⟩ := httest
  refine ⟨d, ?_⟩
  intro m e
  refine ⟨(hd m e).1, ?_⟩
  rw [(hd m e).2]
  exact congrFun (TuplePatterns.sub_color c p0 p (A n) (hcard n) (hA n) e) b

end TailBound

namespace BaseOrders

variable {B : Type u} [LinearOrder B]

theorem initial_bound (h : ∀ b : B, (Set.Iic b).Countable) :
    #B ≤ (ℵ_ 1 : Cardinal.{u}) := by
  classical
  by_cases hsmall : #B ≤ ℵ₀
  · exact hsmall.trans (Cardinal.aleph0_le_aleph 1)
  have hone : (ℵ_ 1 : Cardinal.{u}) ≤ #B := by
    rw [show (ℵ_ (1 : Ordinal) : Cardinal.{u}) = succ ℵ₀ by
      rw [← Cardinal.aleph_zero, Cardinal.succ_aleph]; simp]
    exact Order.succ_le_of_lt (lt_of_not_ge hsmall)
  obtain ⟨e⟩ : Nonempty ((ω_ 1 : Ordinal.{u}).ToType ↪ B) := by
    apply (Cardinal.le_def _ _).1
    simpa only [Cardinal.mk_toType, Ordinal.card_omega] using hone
  have hcof : ∀ b : B, ∃ i, b ≤ e i := by
    intro b
    by_contra! hb
    have he : Function.Injective (fun i => (⟨e i, (hb i).le⟩ : Set.Iic b)) :=
      fun i j hij => e.injective (congrArg Subtype.val hij)
    have := (h b).to_subtype
    have hc := (Cardinal.mk_le_of_injective he).trans (Cardinal.mk_le_aleph0 (α := Set.Iic b))
    rw [Cardinal.mk_toType, Ordinal.card_omega] at hc
    exact (Cardinal.aleph0_lt_aleph.2 (by norm_num : (0 : Ordinal) < 1)).not_ge hc
  choose ix hix using hcof
  let f : B → Σ i : (ω_ 1 : Ordinal.{u}).ToType, Set.Iic (e i) :=
    fun b => ⟨ix b, b, hix b⟩
  have hf : Function.Injective f := by
    intro b c heq
    exact congrArg (fun x : Σ i, Set.Iic (e i) => x.2.val) heq
  apply (Cardinal.mk_le_of_injective hf).trans
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun i => #(Set.Iic (e i))) ≤ Cardinal.sum (fun _ : (ω_ 1 : Ordinal.{u}).ToType =>
        (ℵ₀ : Cardinal.{u})) := by
      apply Cardinal.sum_le_sum
      intro i
      have := (h (e i)).to_subtype
      exact Cardinal.mk_le_aleph0
    _ = ℵ_ 1 := by
      rw [Cardinal.sum_const, Cardinal.mk_toType, Ordinal.card_omega, Cardinal.lift_id, Cardinal.lift_id,
        Cardinal.mul_eq_left (Cardinal.aleph0_le_aleph 1) (Cardinal.aleph0_le_aleph 1)
          Cardinal.aleph0_ne_zero]

theorem cardinal_le [Nonempty B] (h : ∀ a b : B, (Set.Icc a b).Countable) :
    #B ≤ (ℵ_ 1 : Cardinal.{u}) := by
  classical
  let p : B := Classical.arbitrary B
  have hup : #(Set.Ici p) ≤ (ℵ_ 1 : Cardinal.{u}) := by
    apply initial_bound
    intro b
    have hinj : Function.Injective (fun x : Set.Iic b =>
        (⟨x.val.val, x.val.property, x.property⟩ : Set.Icc p b.val)) :=
      fun x y heq => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : Set.Icc p b.val => z.val) heq
    have := (h p b).to_subtype
    have : Countable (Set.Iic b) := hinj.countable
    exact Set.to_countable _
  have hdn : #(Set.Iic p) ≤ (ℵ_ 1 : Cardinal.{u}) := by
    apply @initial_bound (OrderDual (Set.Iic p)) _
    intro b
    have hinj : Function.Injective (fun x : Set.Iic b =>
        (⟨x.val.val, x.property, x.val.property⟩ : Set.Icc b.val p)) :=
      fun x y heq => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : Set.Icc b.val p => z.val) heq
    have := (h b.val p).to_subtype
    have : Countable (Set.Iic b) := hinj.countable
    exact Set.to_countable _
  let f : B → Set.Ici p ⊕ Set.Iic p := fun b =>
    if hb : p ≤ b then Sum.inl ⟨b, hb⟩ else Sum.inr ⟨b, (le_of_not_ge hb)⟩
  have hf : Function.Injective f := by
    intro b c heq
    have hv := congrArg (Sum.elim Subtype.val Subtype.val) heq
    simpa [f, apply_dite] using hv
  apply (Cardinal.mk_le_of_injective hf).trans
  simpa only [Cardinal.mk_sum, Cardinal.lift_id,
    Cardinal.add_eq_self (Cardinal.aleph0_le_aleph 1)] using add_le_add hup hdn

end BaseOrders

end CHObstruction

end

end OAI

-- ===== Arrays.lean =====

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Matrix

open scoped symmDiff

variable {B : Type u}

local instance : DecidableEq B := Classical.decEq B

def bit (a : ℕ → B → Bool) (n : ℕ) (u : Finset B) (b : B) (v : Finset ℕ) : Bool :=
  a n b ^^ decide (b ∈ u) ^^ decide (n ∈ v)

theorem decompose [Countable B] (d : ℕ → B → Bool) :
    ∃ (U : ℕ → Finset B) (V : B → Finset ℕ),
      ∀ n b, (decide (b ∈ U n) ^^ decide (n ∈ V b)) = d n b := by
  classical
  obtain ⟨e⟩ := nonempty_encodable B
  let ix : B → ℕ := Encodable.encode
  have hi : Function.Injective ix := Encodable.encode_injective
  let U : ℕ → Finset B := fun n =>
    ((Finset.range (n + 1)).preimage ix (hi.injOn)).filter (fun b => d n b)
  let V : B → Finset ℕ := fun b => (Finset.range (ix b)).filter (fun n => d n b)
  refine ⟨U, V, ?_⟩
  intro n b
  simp only [U, V, Finset.mem_filter, Finset.mem_preimage, Finset.mem_range]
  by_cases h : ix b ≤ n
  · have hn : ¬ n < ix b := not_lt_of_ge h
    simp only [Nat.lt_succ_iff, h, hn, true_and, false_and, decide_false, Bool.xor_false,
      Bool.decide_coe]
  · have hn : n < ix b := lt_of_not_ge h
    simp only [Nat.lt_succ_iff, h, hn, true_and, false_and, decide_false, Bool.false_xor,
      Bool.decide_coe]

theorem normalize [Countable B] (a a' : ℕ → B → Bool) :
    ∃ (U : ℕ → Finset B) (V : B → Finset ℕ),
      ∀ n b, bit a' n (U n) b (V b) = a n b := by
  obtain ⟨U, V, h⟩ := decompose (fun n b => a n b ^^ a' n b)
  refine ⟨U, V, ?_⟩
  intro n b
  rw [bit, Bool.xor_assoc, h]
  cases a n b <;> cases a' n b <;> rfl

end Matrix

namespace Arrays

open Tuples
open scoped symmDiff

inductive Point (I B : Type u) : Type u
  | index : I → Point I B
  | base : B → Point I B
  | group : Finset B → Point I B
  | star : Finset ℕ → Point I B
  | row : Tuple I → ℕ → Finset B → Point I B
  | col : Tuple I → B → Finset ℕ → Point I B

inductive Symbol : Type
  | index | base | group | star
  | row (k n : ℕ) | col (k : ℕ) | label (s : Finset ℕ)
  | rowProjection (k n : ℕ) | colProjection (k : ℕ)
  | order | incidence | bit
  | groupAdd | starAdd | rowAct | colAct
  deriving DecidableEq, Encodable

def Symbol.arity : Symbol → ℕ
  | .index | .base | .group | .star | .row _ _ | .col _ | .label _ => 1
  | .rowProjection k _ => k + 2
  | .colProjection k => k + 3
  | .order | .incidence | .bit => 2
  | .groupAdd | .starAdd | .rowAct | .colAct => 3

def Language (n : ℕ) := {s : Symbol // s.arity = n}

instance language_countable : Countable (Σ n, Language n) := by
  have hi : Function.Injective (fun x : Σ n, Language n => x.2.val) := by
    rintro ⟨n, s, hs⟩ ⟨m, r, hr⟩ h
    dsimp at h
    subst r
    cases hs
    cases hr
    rfl
  exact hi.countable

structure Data where
  I : Type u
  B : Type u
  indexNonempty : Nonempty I
  baseNonempty : Nonempty B
  order : LinearOrder B
  dense : @DenselyOrdered B order.toLT
  noMin : @NoMinOrder B order.toLT
  noMax : @NoMaxOrder B order.toLT
  locallyCountable : ∀ a b : B, (@Set.Icc B order.toPreorder a b).Countable
  bits : Tuple I → ℕ → B → Bool

attribute [instance] Data.indexNonempty Data.baseNonempty Data.order Data.dense Data.noMin Data.noMax

abbrev Data.Carrier (M : Data.{u}) := Point M.I M.B

variable (M : Data.{u})

local instance : DecidableEq M.B := Classical.decEq M.B

def Data.rawRel : Symbol → List M.Carrier → Prop
  | .index, [.index _] => True
  | .base, [.base _] => True
  | .group, [.group _] => True
  | .star, [.star _] => True
  | .row k n, [.row t m _] => t.1 = k ∧ m = n
  | .col k, [.col t _ _] => t.1 = k
  | .label s, [.star t] => s = t
  | .rowProjection k n, (.row t m _) :: xs =>
      t.1 = k ∧ m = n ∧ xs = List.ofFn (fun i => Point.index (t.2 i))
  | .colProjection k, (.col t b _) :: x :: xs =>
      t.1 = k ∧ x = .base b ∧ xs = List.ofFn (fun i => Point.index (t.2 i))
  | .order, [.base a, .base b] => a < b
  | .incidence, [.base b, .group s] => b ∈ s
  | .bit, [.row t n s, .col t' b v] => t = t' ∧ Matrix.bit (M.bits t) n s b v = true
  | .groupAdd, [.group s, .group t, .group w] => w = s ∆ t
  | .starAdd, [.star s, .star t, .star w] => w = s ∆ t
  | .rowAct, [.row t n s, .group u, .row t' n' s'] => t' = t ∧ n' = n ∧ s' = s ∆ u
  | .colAct, [.col t b v, .star u, .col t' b' v'] => t' = t ∧ b' = b ∧ v' = v ∆ u
  | _, _ => False

def Data.rel (n : ℕ) (s : Language n) (a : Fin n → M.Carrier) : Prop :=
  M.rawRel s.val (List.ofFn a)

def Data.colors (t : Tuple M.I) (b : M.B) : Colors.Palette.{u} :=
  ⟨Colors.color (fun n => M.bits t n b)⟩

def Data.IsObject (hCH : CH.{u}) : Prop :=
  ∀ t : Tuple M.I, {b | ¬ Tests.Test hCH (fun t => M.colors t b) t}.Countable

theorem Data.countable_object (hCH : CH.{u}) [Countable M.B] : M.IsObject hCH :=
  fun _ => Set.to_countable _

theorem Data.base_bound : #M.B ≤ (ℵ_ 1 : Cardinal.{u}) :=
  BaseOrders.cardinal_le M.locallyCountable

theorem Data.uncountable_index_bound (hCH : CH.{u}) (hM : M.IsObject hCH)
    (hB : ¬ Countable M.B) : #M.I < tailThreshold.{u} :=
  TailBound.index_lt hCH M.base_bound hB M.colors hM

end Arrays

namespace Tuples

variable {I J K : Type u}

def map (f : I ↪ J) (t : Tuple I) : Tuple J := ⟨t.1, t.2.trans f⟩

@[simp] theorem map_fst (f : I ↪ J) (t : Tuple I) : (map f t).1 = t.1 := rfl

theorem map_injective (f : I ↪ J) : Function.Injective (map f) := by
  rintro ⟨n, t⟩ ⟨m, s⟩ heq
  have hn : n = m := congrArg Sigma.fst heq
  subst m
  have he : t.trans f = s.trans f := (Sigma.mk.inj heq).2 |> eq_of_heq
  congr 1
  ext i
  exact f.injective (congrArg (fun g : Fin (n + 1) ↪ J => g i) he)

@[simp] theorem map_refl (t : Tuple I) : map (Function.Embedding.refl I) t = t := by
  cases t
  rfl

@[simp] theorem map_comp (f : I ↪ J) (g : J ↪ K) (t : Tuple I) :
    map g (map f t) = map (f.trans g) t := rfl

@[simp] theorem map_sub (f : I ↪ J) (t : Tuple I) {m : ℕ}
    (e : Fin (m + 1) ↪o Fin (t.1 + 1)) : map f (sub t e) = sub (map f t) e := rfl

theorem cardinal_bound (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hI : #I ≤ κ) : #(Tuple I) ≤ κ := by
  rw [Cardinal.mk_sigma]
  have h : ∀ n : ℕ, #(Fin (n + 1) ↪ I) ≤ κ := by
    intro n
    calc
      #(Fin (n + 1) ↪ I) ≤ #(Fin (n + 1) → I) :=
        Cardinal.mk_le_of_injective DFunLike.coe_injective
      _ = #I ^ ((n + 1 : ℕ) : Cardinal.{u}) := by simp
      _ ≤ κ ^ ((n + 1 : ℕ) : Cardinal.{u}) := Cardinal.power_le_power_right hI
      _ ≤ κ := Cardinal.power_nat_le hκ
  calc
    Cardinal.sum (fun n : ℕ => #(Fin (n + 1) ↪ I)) ≤
        Cardinal.sum (fun _ : ℕ => κ) := Cardinal.sum_le_sum _ _ h
    _ = κ := by
      simp only [Cardinal.sum_const, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_uzero]
      exact Cardinal.aleph0_mul_eq hκ

end Tuples

namespace FiniteSupports

open scoped symmDiff

variable {A : Type u} {B : Type v} [DecidableEq A] [DecidableEq B]

@[simp] theorem map_symmDiff (f : A ↪ B) (s t : Finset A) :
    (s ∆ t).map f = s.map f ∆ t.map f := by
  ext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    simp only [Finset.mem_map, Function.Embedding.apply_eq_iff_eq, exists_eq_right,
      Finset.mem_symmDiff]
  · have hn : ∀ s : Finset A, b ∉ s.map f := by
      intro s hs
      obtain ⟨a, _, ha⟩ := Finset.mem_map.1 hs
      exact hb ⟨a, ha⟩
    simp only [hn, Finset.mem_symmDiff, not_false_eq_true, false_and, or_self]

@[simp] theorem bit_symmDiff (b : A) (s t : Finset A) :
    decide (b ∈ s ∆ t) = (decide (b ∈ s) ^^ decide (b ∈ t)) := by
  simp only [Finset.mem_symmDiff]
  by_cases hs : b ∈ s <;> by_cases ht : b ∈ t <;> simp [hs, ht]

@[simp] theorem bit_map (f : A ↪ B) (b : A) (s : Finset A) :
    decide (f b ∈ s.map f) = decide (b ∈ s) := by
  simp

end FiniteSupports

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B

structure Map (M N : Data.{u}) where
  index : M.I ↪ N.I
  base : M.B ↪o N.B
  rowShift : Tuple M.I → ℕ → Finset N.B
  colShift : Tuple M.I → M.B → Finset ℕ
  bit_agrees : ∀ t n b, Matrix.bit (N.bits (Tuples.map index t)) n (rowShift t n)
    (base b) (colShift t b) = M.bits t n b

def Map.onPoint (f : Map M N) : M.Carrier → N.Carrier
  | .index i => .index (f.index i)
  | .base b => .base (f.base b)
  | .group s => .group (s.map f.base.toEmbedding)
  | .star v => .star v
  | .row t n s => .row (Tuples.map f.index t) n (f.rowShift t n ∆ s.map f.base.toEmbedding)
  | .col t b v => .col (Tuples.map f.index t) (f.base b) (f.colShift t b ∆ v)

theorem Map.injective (f : Map M N) : Function.Injective f.onPoint := by
  intro x y h
  cases x <;> cases y <;> simp only [Map.onPoint, Point.index.injEq, Point.base.injEq,
    Point.group.injEq, Point.star.injEq, Point.row.injEq, Point.col.injEq,
    reduceCtorEq] at h ⊢
  · exact f.index.injective h
  · exact f.base.injective h
  · exact Finset.map_injective _ h
  · exact h
  · obtain ⟨ht, hn, hs⟩ := h
    have ht' := Tuples.map_injective f.index ht
    subst_vars
    exact ⟨rfl, rfl, Finset.map_injective _ (symmDiff_right_inj.1 hs)⟩
  · obtain ⟨ht, hb, hv⟩ := h
    have ht' := Tuples.map_injective f.index ht
    have hb' := f.base.injective hb
    subst_vars
    exact ⟨rfl, rfl, symmDiff_right_inj.1 hv⟩

def Map.toEmbedding (f : Map M N) : M.Carrier ↪ N.Carrier :=
  ⟨f.onPoint, f.injective⟩

@[simp] theorem Map.base_embedding_apply (f : Map M N) (b : M.B) :
    f.base.toEmbedding b = f.base b := rfl

theorem Map.bit_all (f : Map M N) (t : Tuple M.I) (n : ℕ) (s : Finset M.B)
    (b : M.B) (v : Finset ℕ) :
    Matrix.bit (N.bits (Tuples.map f.index t)) n
      (f.rowShift t n ∆ s.map f.base.toEmbedding) (f.base b) (f.colShift t b ∆ v) =
      Matrix.bit (M.bits t) n s b v := by
  have hb := f.bit_agrees t n b
  simp only [Matrix.bit, FiniteSupports.bit_symmDiff, Finset.mem_map,
    Map.base_embedding_apply, f.base.injective.eq_iff, exists_eq_right] at *
  rw [← hb]
  generalize N.bits (Tuples.map f.index t) n (f.base b) = a
  generalize decide (f.base b ∈ f.rowShift t n) = c
  generalize decide (b ∈ s) = d
  generalize decide (n ∈ f.colShift t b) = e
  generalize decide (n ∈ v) = g
  cases a <;> cases c <;> cases d <;> cases e <;> cases g <;> rfl

end Arrays

namespace Tuples

@[simp] theorem map_eq_iff {I J : Type u} (f : I ↪ J) (s t : Tuple I) :
    map f s = map f t ↔ s = t := (map_injective f).eq_iff

end Tuples

end CHObstruction

end

end OAI

-- ===== ArrayMaps.lean =====

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Arrays

section

open Tuples
open scoped symmDiff

variable {M N : Data.{u}} (f : Map M N)
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B

private theorem row_action_iff (t t' : Tuple M.I) (n n' : ℕ) (s u s' : Finset M.B) :
    (Tuples.map f.index t' = Tuples.map f.index t ∧ n' = n ∧
      f.rowShift t' n' ∆ s'.map f.base.toEmbedding =
        (f.rowShift t n ∆ s.map f.base.toEmbedding) ∆ u.map f.base.toEmbedding) ↔
      (t' = t ∧ n' = n ∧ s' = s ∆ u) := by
  rw [Tuples.map_eq_iff]
  constructor
  · rintro ⟨rfl, rfl, h⟩
    refine ⟨rfl, rfl, ?_⟩
    rw [symmDiff_assoc, ← FiniteSupports.map_symmDiff, symmDiff_right_inj] at h
    exact Finset.map_injective _ h
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, by rw [FiniteSupports.map_symmDiff, symmDiff_assoc]⟩

private theorem col_action_iff (t t' : Tuple M.I) (b b' : M.B) (v u v' : Finset ℕ) :
    (Tuples.map f.index t' = Tuples.map f.index t ∧ f.base b' = f.base b ∧
      f.colShift t' b' ∆ v' = (f.colShift t b ∆ v) ∆ u) ↔
      (t' = t ∧ b' = b ∧ v' = v ∆ u) := by
  rw [Tuples.map_eq_iff, f.base.injective.eq_iff]
  constructor
  · rintro ⟨rfl, rfl, h⟩
    exact ⟨rfl, rfl, by simpa only [symmDiff_assoc, symmDiff_right_inj] using h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, (symmDiff_assoc _ _ _).symm⟩

private theorem bit_relation_iff (t t' : Tuple M.I) (n : ℕ) (b : M.B)
    (s : Finset M.B) (v : Finset ℕ) :
    (Tuples.map f.index t = Tuples.map f.index t' ∧
      Matrix.bit (N.bits (Tuples.map f.index t)) n
        (f.rowShift t n ∆ s.map f.base.toEmbedding) (f.base b) (f.colShift t' b ∆ v) = true) ↔
      (t = t' ∧ Matrix.bit (M.bits t) n s b v = true) := by
  rw [Tuples.map_eq_iff]
  constructor
  · rintro ⟨rfl, hb⟩
    exact ⟨rfl, by simpa only [f.bit_all] using hb⟩
  · rintro ⟨rfl, hb⟩
    exact ⟨rfl, by simpa only [f.bit_all] using hb⟩

private theorem group_add_iff (s t w : Finset M.B) :
    w.map f.base.toEmbedding = s.map f.base.toEmbedding ∆ t.map f.base.toEmbedding ↔
      w = s ∆ t := by
  rw [← FiniteSupports.map_symmDiff]
  exact (Finset.map_injective _).eq_iff

attribute [local simp] Data.rawRel Map.onPoint group_add_iff row_action_iff
  col_action_iff bit_relation_iff

private theorem raw_map_index (xs : List M.Carrier) :
    N.rawRel (.index) (xs.map f.onPoint) ↔ M.rawRel (.index) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_base (xs : List M.Carrier) :
    N.rawRel (.base) (xs.map f.onPoint) ↔ M.rawRel (.base) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_group (xs : List M.Carrier) :
    N.rawRel (.group) (xs.map f.onPoint) ↔ M.rawRel (.group) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_star (xs : List M.Carrier) :
    N.rawRel (.star) (xs.map f.onPoint) ↔ M.rawRel (.star) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_row (k n : ℕ) (xs : List M.Carrier) :
    N.rawRel (.row k n) (xs.map f.onPoint) ↔ M.rawRel (.row k n) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_col (k : ℕ) (xs : List M.Carrier) :
    N.rawRel (.col k) (xs.map f.onPoint) ↔ M.rawRel (.col k) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_label (s : Finset ℕ) (xs : List M.Carrier) :
    N.rawRel (.label s) (xs.map f.onPoint) ↔ M.rawRel (.label s) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_order (xs : List M.Carrier) :
    N.rawRel (.order) (xs.map f.onPoint) ↔ M.rawRel (.order) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> simp
  · cases x <;> cases y <;> simp

private theorem raw_map_incidence (xs : List M.Carrier) :
    N.rawRel (.incidence) (xs.map f.onPoint) ↔ M.rawRel (.incidence) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> simp
  · cases x <;> cases y <;> simp

private theorem raw_map_bit (xs : List M.Carrier) :
    N.rawRel (.bit) (xs.map f.onPoint) ↔ M.rawRel (.bit) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> simp
    rintro rfl
    exact f.bit_all _ _ _ _ _
  · cases x <;> cases y <;> simp

private theorem raw_map_groupAdd (xs : List M.Carrier) :
    N.rawRel (.groupAdd) (xs.map f.onPoint) ↔ M.rawRel (.groupAdd) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
  · cases x <;> cases y <;> cases z <;> simp

private theorem raw_map_starAdd (xs : List M.Carrier) :
    N.rawRel (.starAdd) (xs.map f.onPoint) ↔ M.rawRel (.starAdd) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
  · cases x <;> cases y <;> cases z <;> simp

private theorem raw_map_rowAct (xs : List M.Carrier) :
    N.rawRel (.rowAct) (xs.map f.onPoint) ↔ M.rawRel (.rowAct) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
    rintro rfl rfl
    rw [symmDiff_assoc, ← FiniteSupports.map_symmDiff, symmDiff_right_inj]
    exact (Finset.map_injective _).eq_iff
  · cases x <;> cases y <;> cases z <;> simp

private theorem raw_map_colAct (xs : List M.Carrier) :
    N.rawRel (.colAct) (xs.map f.onPoint) ↔ M.rawRel (.colAct) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
    rintro rfl rfl
    rw [symmDiff_assoc, symmDiff_right_inj]
  · cases x <;> cases y <;> cases z <;> simp

private theorem tuple_list_eq_iff (t : Tuple M.I) (xs : List M.Carrier) :
    xs.map f.onPoint = List.ofFn (fun i => Point.index ((Tuples.map f.index t).2 i)) ↔
      xs = List.ofFn (fun i => Point.index (t.2 i)) := by
  have he : List.ofFn (fun i => Point.index ((Tuples.map f.index t).2 i)) =
      (List.ofFn (fun i => Point.index (t.2 i))).map f.onPoint := by
    rw [List.map_ofFn]
    rfl
  rw [he]
  exact f.injective.list_map.eq_iff

private theorem base_point_eq_iff (x : M.Carrier) (b : M.B) :
    f.onPoint x = Point.base (f.base b) ↔ x = Point.base b := by
  change f.onPoint x = f.onPoint (.base b) ↔ _
  exact f.injective.eq_iff

private theorem raw_map_rowProjection (k n : ℕ) (xs : List M.Carrier) :
    N.rawRel (.rowProjection k n) (xs.map f.onPoint) ↔ M.rawRel (.rowProjection k n) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  cases x <;> simp
  intro _ _
  simpa only [Tuples.map, List.ofFn_succ] using tuple_list_eq_iff f _ xs

private theorem raw_map_colProjection (k : ℕ) (xs : List M.Carrier) :
    N.rawRel (.colProjection k) (xs.map f.onPoint) ↔ M.rawRel (.colProjection k) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, ys⟩
  · cases x <;> simp
  cases x <;> simp
  intro _
  exact and_congr (base_point_eq_iff f y _) (by
    simpa only [Tuples.map, List.ofFn_succ] using tuple_list_eq_iff f _ ys)

theorem Map.rawRel (s : Symbol) (xs : List M.Carrier) :
    N.rawRel s (xs.map f.onPoint) ↔ M.rawRel s xs := by
  cases s with
  | index => exact raw_map_index f xs
  | base => exact raw_map_base f xs
  | group => exact raw_map_group f xs
  | star => exact raw_map_star f xs
  | row k n => exact raw_map_row f k n xs
  | col k => exact raw_map_col f k xs
  | label v => exact raw_map_label f v xs
  | rowProjection k n => exact raw_map_rowProjection f k n xs
  | colProjection k => exact raw_map_colProjection f k xs
  | order => exact raw_map_order f xs
  | incidence => exact raw_map_incidence f xs
  | bit => exact raw_map_bit f xs
  | groupAdd => exact raw_map_groupAdd f xs
  | starAdd => exact raw_map_starAdd f xs
  | rowAct => exact raw_map_rowAct f xs
  | colAct => exact raw_map_colAct f xs

theorem Map.rel (n : ℕ) (s : Language n) (a : Fin n → M.Carrier) :
    N.rel n s (f.onPoint ∘ a) ↔ M.rel n s a := by
  simpa only [Data.rel, List.map_ofFn] using f.rawRel s.val (List.ofFn a)

end

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B
local instance : DecidableEq P.B := Classical.decEq P.B

def Map.id (M : Data.{u}) : Map M M where
  index := Function.Embedding.refl _
  base := (OrderIso.refl _).toOrderEmbedding
  rowShift _ _ := ∅
  colShift _ _ := ∅
  bit_agrees t n b := by simp [Matrix.bit]

def Map.comp (g : Map N P) (f : Map M N) : Map M P where
  index := f.index.trans g.index
  base := f.base.trans g.base
  rowShift t n := g.rowShift (Tuples.map f.index t) n ∆
    (f.rowShift t n).map g.base.toEmbedding
  colShift t b := g.colShift (Tuples.map f.index t) (f.base b) ∆ f.colShift t b
  bit_agrees t n b := by
    exact (g.bit_all (Tuples.map f.index t) n (f.rowShift t n) (f.base b)
      (f.colShift t b)).trans (f.bit_agrees t n b)

@[simp] theorem Map.id_onPoint (M : Data.{u}) (x : M.Carrier) : (Map.id M).onPoint x = x := by
  have he : (OrderIso.refl M.B).toOrderEmbedding.toEmbedding = Function.Embedding.refl M.B := rfl
  cases x <;> simp [Map.id, Map.onPoint, he]

@[simp] theorem Map.comp_onPoint (g : Map N P) (f : Map M N) (x : M.Carrier) :
    (g.comp f).onPoint x = g.onPoint (f.onPoint x) := by
  have he : (f.base.trans g.base).toEmbedding = f.base.toEmbedding.trans g.base.toEmbedding := rfl
  cases x <;> simp [Map.comp, Map.onPoint, Finset.map_map, symmDiff_assoc, he]

theorem Map.ext_onPoint {f g : Map M N} (h : ∀ x, f.onPoint x = g.onPoint x) : f = g := by
  have hi : f.index = g.index := by
    ext i
    exact Point.index.inj (h (.index i))
  have hb : f.base = g.base := by
    ext b
    exact Point.base.inj (h (.base b))
  have hr : f.rowShift = g.rowShift := by
    funext t n
    have he := (Point.row.inj (h (.row t n ∅))).2.2
    simpa using he
  have hc : f.colShift = g.colShift := by
    funext t b
    have he := (Point.col.inj (h (.col t b ∅))).2.2
    simpa using he
  cases f
  cases g
  cases hi
  cases hb
  cases hr
  cases hc
  rfl

@[simp] theorem Map.comp_id (f : Map M N) : f.comp (Map.id M) = f :=
  Map.ext_onPoint (fun x => by simp)

@[simp] theorem Map.id_comp (f : Map M N) : (Map.id N).comp f = f :=
  Map.ext_onPoint (fun x => by simp)

end Arrays

end CHObstruction

end

end OAI

-- ===== ArrayEmbeddings.lean =====

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Tests

open Tuples

theorem congr {I : Type v} (hCH : CH.{u}) {c d : Tuple I → Colors.Palette.{u}}
    (t : Tuple I) (h : ∀ m (e : Fin (m + 1) ↪o Fin (t.1 + 1)), c (sub t e) = d (sub t e)) :
    Test hCH c t ↔ Test hCH d t := by
  have he : (fun m (e : Fin (m + 1) ↪o Fin (t.1 + 1)) => c (sub t e)) =
      (fun m (e : Fin (m + 1) ↪o Fin (t.1 + 1)) => d (sub t e)) := funext (fun m => funext (h m))
  exact iff_of_eq (congrArg (Passes hCH) he)

@[simp] theorem map {I J : Type u} (hCH : CH.{u}) (f : I ↪ J)
    (c : Tuple J → Colors.Palette.{u}) (t : Tuple I) :
    Test hCH c (Tuples.map f t) ↔ Test hCH (fun s => c (Tuples.map f s)) t := Iff.rfl

end Tests

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B
local instance : DecidableEq P.B := Classical.decEq P.B

def Map.colors (f : Map M N) (t : Tuple M.I) (b : N.B) : Colors.Palette.{u} :=
  ⟨Colors.color (fun n => N.bits (Tuples.map f.index t) n b ^^ decide (b ∈ f.rowShift t n))⟩

theorem color_column (a : ℕ → Bool) (v : Finset ℕ) :
    Colors.color (fun n => a n ^^ decide (n ∈ v)) = Colors.color a := by
  apply Quotient.sound
  apply v.finite_toSet.subset
  intro n hn
  by_contra h
  have h' : n ∉ v := h
  exact hn (by simp [h'])

@[simp] theorem Map.colors_base (f : Map M N) (t : Tuple M.I) (b : M.B) :
    f.colors t (f.base b) = M.colors t b := by
  apply ULift.ext
  change Colors.color _ = Colors.color _
  have he : (fun n => N.bits (Tuples.map f.index t) n (f.base b) ^^
      decide (f.base b ∈ f.rowShift t n)) =
      (fun n => M.bits t n b ^^ decide (n ∈ f.colShift t b)) := by
    funext n
    have h := f.bit_agrees t n b
    dsimp [Matrix.bit] at h
    rw [← h, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  rw [he, color_column]

def Map.exceptions (f : Map M N) (t : Tuple M.I) : Set N.B :=
  ⋃ m : ℕ, ⋃ e : Fin (m + 1) ↪o Fin (t.1 + 1), ⋃ n : ℕ,
    (f.rowShift (sub t e) n : Set N.B)

theorem Map.exceptions_countable (f : Map M N) (t : Tuple M.I) :
    (f.exceptions t).Countable := by
  classical
  apply Set.countable_iUnion
  intro m
  apply Set.countable_iUnion
  intro e
  exact Set.countable_iUnion (fun n => (f.rowShift (sub t e) n).countable_toSet)

theorem Map.test_away (f : Map M N) (hCH : CH.{u}) (t : Tuple M.I) (b : N.B)
    (hb : b ∉ f.exceptions t) :
    Tests.Test hCH (fun s => f.colors s b) t ↔
      Tests.Test hCH (fun s => N.colors s b) (Tuples.map f.index t) := by
  rw [Tests.map]
  apply Tests.congr
  intro m e
  have hn : ∀ n, b ∉ f.rowShift (sub t e) n := by
    intro n h
    apply hb
    exact Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨n, h⟩⟩⟩
  simp only [Map.colors, Data.colors, hn, decide_false, Bool.xor_false]

structure Map.Strong (hCH : CH.{u}) (f : Map M N) : Prop where
  convex : Set.OrdConnected (Set.range f.base)
  outside : ∀ (t : Tuple M.I) (b : N.B), b ∉ Set.range f.base →
    Tests.Test hCH (fun s => f.colors s b) t

@[simp] theorem Map.id_strong (hCH : CH.{u}) (M : Data.{u}) : (Map.id M).Strong hCH := by
  constructor
  · simpa only [Map.id, OrderIso.coe_toOrderEmbedding, OrderIso.coe_refl, Set.range_id] using
      (Set.ordConnected_univ : Set.OrdConnected (Set.univ : Set M.B))
  · intro t b hb
    exact (hb ⟨b, rfl⟩).elim

theorem Map.comp_colors_base (g : Map N P) (f : Map M N) (t : Tuple M.I) (b : N.B) :
    (g.comp f).colors t (g.base b) = f.colors t b := by
  apply ULift.ext
  change Colors.color _ = Colors.color _
  have he : (fun n => P.bits (Tuples.map (g.comp f).index t) n (g.base b) ^^
      decide (g.base b ∈ (g.comp f).rowShift t n)) =
      (fun n => (N.bits (Tuples.map f.index t) n b ^^ decide (b ∈ f.rowShift t n)) ^^
        decide (n ∈ g.colShift (Tuples.map f.index t) b)) := by
    funext n
    have hv : g.colShift (Tuples.map f.index t) b ∆ ∅ =
        g.colShift (Tuples.map f.index t) b := by simp
    have h := g.bit_all (Tuples.map f.index t) n (f.rowShift t n) b ∅
    simp only [Matrix.bit, Finset.notMem_empty, decide_false, Bool.xor_false, hv] at h
    change (P.bits (Tuples.map g.index (Tuples.map f.index t)) n (g.base b) ^^
      decide (g.base b ∈ g.rowShift (Tuples.map f.index t) n ∆
        (f.rowShift t n).map g.base.toEmbedding)) = _
    rw [← h, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  rw [he, color_column]

theorem Map.comp_colors_outside (g : Map N P) (f : Map M N) (t : Tuple M.I) (b : P.B)
    (hb : b ∉ Set.range g.base) :
    (g.comp f).colors t b = g.colors (Tuples.map f.index t) b := by
  have hn : ∀ n, b ∉ (f.rowShift t n).map g.base.toEmbedding := by
    intro n h
    obtain ⟨a, _, ha⟩ := Finset.mem_map.1 h
    exact hb ⟨a, ha⟩
  apply ULift.ext
  apply congrArg Colors.color
  funext n
  change (P.bits (Tuples.map g.index (Tuples.map f.index t)) n b ^^ _) = _
  congr 1
  simp only [Map.comp, Finset.mem_symmDiff, hn, not_false_eq_true, and_true, false_and, or_false]

theorem Map.Strong.comp (hCH : CH.{u}) {g : Map N P} {f : Map M N}
    (hg : g.Strong hCH) (hf : f.Strong hCH) : (g.comp f).Strong hCH := by
  constructor
  · constructor
    intro x hx y hy z hz
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := hg.convex.out (by exact ⟨f.base a, rfl⟩)
      (by exact ⟨f.base b, rfl⟩) hz
    have hc : c ∈ Set.Icc (f.base a) (f.base b) := by
      exact ⟨g.base.le_iff_le.1 hz.1, g.base.le_iff_le.1 hz.2⟩
    obtain ⟨d, rfl⟩ := hf.convex.out ⟨a, rfl⟩ ⟨b, rfl⟩ hc
    exact ⟨d, rfl⟩
  · intro t b hb
    by_cases hbg : b ∈ Set.range g.base
    · obtain ⟨c, rfl⟩ := hbg
      have hc : c ∉ Set.range f.base := by
        rintro ⟨d, rfl⟩
        exact hb ⟨d, rfl⟩
      simpa only [Map.comp_colors_base] using hf.outside t c hc
    · have h := hg.outside (Tuples.map f.index t) b hbg
      rw [Tests.map] at h
      simpa only [Map.comp_colors_outside g f _ b hbg] using h

end Arrays

namespace Tuples

variable {I J : Type u}

def mapEquiv (e : I ≃ J) : Tuple I ≃ Tuple J where
  toFun := map e.toEmbedding
  invFun := map e.symm.toEmbedding
  left_inv t := by
    have h : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl I := by ext x; simp
    rw [map_comp, h, map_refl]
  right_inv t := by
    have h : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl J := by ext x; simp
    rw [map_comp, h, map_refl]

end Tuples

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B

theorem Map.surjective (f : Map M N) (hi : Function.Surjective f.index)
    (hb : Function.Surjective f.base) : Function.Surjective f.onPoint := by
  classical
  let ei : M.I ≃ N.I := Equiv.ofBijective f.index ⟨f.index.injective, hi⟩
  let eb : M.B ≃ N.B := Equiv.ofBijective f.base ⟨f.base.injective, hb⟩
  have hfin : ∀ s : Finset N.B, ∃ v : Finset M.B, v.map f.base.toEmbedding = s := by
    intro s
    refine ⟨s.map eb.symm.toEmbedding, ?_⟩
    rw [Finset.map_map]
    have he : eb.symm.toEmbedding.trans f.base.toEmbedding = Function.Embedding.refl N.B := by
      ext b
      exact eb.apply_symm_apply b
    rw [he, Finset.map_refl]
  have htup : Function.Surjective (Tuples.map f.index) := (Tuples.mapEquiv ei).surjective
  intro p
  cases p with
  | index i => obtain ⟨j, rfl⟩ := hi i; exact ⟨.index j, rfl⟩
  | base b => obtain ⟨a, rfl⟩ := hb b; exact ⟨.base a, rfl⟩
  | group s => obtain ⟨v, rfl⟩ := hfin s; exact ⟨.group v, rfl⟩
  | star v => exact ⟨.star v, rfl⟩
  | row t n s =>
    obtain ⟨r, rfl⟩ := htup t
    obtain ⟨v, hv⟩ := hfin (f.rowShift r n ∆ s)
    exact ⟨.row r n v, by simp [Map.onPoint, hv]⟩
  | col t b v =>
    obtain ⟨r, rfl⟩ := htup t
    obtain ⟨a, rfl⟩ := hb b
    exact ⟨.col r a (f.colShift r a ∆ v), by simp [Map.onPoint]⟩

def Map.equiv (f : Map M N) (hi : Function.Surjective f.index)
    (hb : Function.Surjective f.base) : M.Carrier ≃ N.Carrier :=
  Equiv.ofBijective f.onPoint ⟨f.injective, f.surjective hi hb⟩

def countableMap [Countable M.B] (ei : M.I ≃ N.I) (eb : M.B ≃o N.B) : Map M N := by
  have h := fun t : Tuple M.I => Matrix.normalize (M.bits t)
    (fun n b => N.bits (Tuples.map ei.toEmbedding t) n (eb b))
  choose U V hUV using h
  exact {
    index := ei.toEmbedding
    base := eb.toOrderEmbedding
    rowShift := fun t n => (U t n).map eb.toOrderEmbedding.toEmbedding
    colShift := V
    bit_agrees := fun t n b => by
      simpa only [Matrix.bit, Finset.mem_map, OrderIso.coe_toOrderEmbedding,
        RelEmbedding.coe_toEmbedding, eb.injective.eq_iff, exists_eq_right] using hUV t n b }

theorem countable_isomorphic [Countable M.B] [Countable N.B] (hI : #M.I = #N.I) :
    ∃ f : Map M N, Function.Surjective f.index ∧ Function.Surjective f.base := by
  obtain ⟨ei⟩ := Cardinal.eq.1 hI
  obtain ⟨eb⟩ := Order.iso_of_countable_dense M.B N.B
  exact ⟨countableMap ei eb, ei.surjective, eb.surjective⟩

theorem Map.strong_of_surjective (f : Map M N) (hCH : CH.{u})
    (hb : Function.Surjective f.base) : f.Strong hCH := by
  constructor
  · rw [Set.range_eq_univ.2 hb]
    exact Set.ordConnected_univ
  · intro t b h
    exact (h (hb b)).elim

theorem Map.object_of_surjective (f : Map M N) (hCH : CH.{u})
    (hi : Function.Surjective f.index) (hb : Function.Surjective f.base)
    (hM : M.IsObject hCH) : N.IsObject hCH := by
  classical
  let ei : M.I ≃ N.I := Equiv.ofBijective f.index ⟨f.index.injective, hi⟩
  intro t
  obtain ⟨r, rfl⟩ := (Tuples.mapEquiv ei).surjective t
  apply ((f.exceptions_countable r).union ((hM r).image f.base)).mono
  intro b hbad
  by_cases he : b ∈ f.exceptions r
  · exact Or.inl he
  · right
    obtain ⟨a, rfl⟩ := hb b
    refine ⟨a, ?_, rfl⟩
    intro hgood
    apply hbad
    apply (f.test_away hCH r (f.base a) he).1
    simpa only [Map.colors_base] using hgood

end Arrays

namespace Tuples

def entriesList {I : Type u} (t : Tuple I) : List I := List.ofFn t.2

theorem entriesList_injective {I : Type u} : Function.Injective (@entriesList I) := by
  rintro ⟨n, a⟩ ⟨m, b⟩ h
  have hn := congrArg List.length h
  simp only [entriesList, List.length_ofFn] at hn
  have he : n = m := Nat.add_right_cancel hn
  subst m
  congr 1
  apply Function.Embedding.ext
  intro i
  have hv := congrArg (fun l : List I => l[i.val]?) h
  simpa only [entriesList, List.getElem?_ofFn, i.isLt, dite_eq_left, Option.some.injEq] using hv

end Tuples

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B

structure RawEmbedding (M N : Data.{u}) where
  toEmbedding : M.Carrier ↪ N.Carrier
  relates : ∀ s xs, N.rawRel s (xs.map toEmbedding) ↔ M.rawRel s xs
  supports : ∀ (s : Finset M.B) (b : N.B),
    N.rawRel .incidence [.base b, toEmbedding (.group s)] ↔
      ∃ a ∈ s, toEmbedding (.base a) = .base b

variable (f : RawEmbedding M N)

theorem RawEmbedding.index_exists (i : M.I) : ∃ j, f.toEmbedding (.index i) = .index j := by
  have h := (f.relates .index [.index i]).2 trivial
  cases he : f.toEmbedding (.index i) <;> simp_all [Data.rawRel]

theorem RawEmbedding.base_exists (b : M.B) : ∃ c, f.toEmbedding (.base b) = .base c := by
  have h := (f.relates .base [.base b]).2 trivial
  cases he : f.toEmbedding (.base b) <;> simp_all [Data.rawRel]

def RawEmbedding.index (i : M.I) : N.I := (f.index_exists i).choose

def RawEmbedding.base (b : M.B) : N.B := (f.base_exists b).choose

@[simp] theorem RawEmbedding.index_apply (i : M.I) :
    f.toEmbedding (.index i) = .index (f.index i) := (f.index_exists i).choose_spec

@[simp] theorem RawEmbedding.base_apply (b : M.B) :
    f.toEmbedding (.base b) = .base (f.base b) := (f.base_exists b).choose_spec

def RawEmbedding.indexEmb : M.I ↪ N.I where
  toFun := f.index
  inj' a b h := Point.index.inj (f.toEmbedding.injective (by simp only [f.index_apply, h]))

def RawEmbedding.baseEmb : M.B ↪o N.B := OrderEmbedding.ofStrictMono f.base (by
  intro a b hab
  have h := (f.relates .order [.base a, .base b]).2 hab
  simpa only [List.map_cons, List.map_nil, f.base_apply, Data.rawRel] using h)

@[simp] theorem RawEmbedding.indexEmb_apply (i : M.I) : f.indexEmb i = f.index i := rfl
@[simp] theorem RawEmbedding.baseEmb_apply (b : M.B) : f.baseEmb b = f.base b := rfl

@[simp] theorem RawEmbedding.group_apply (s : Finset M.B) :
    f.toEmbedding (.group s) = .group (s.map f.baseEmb.toEmbedding) := by
  have h := (f.relates .group [.group s]).2 trivial
  cases he : f.toEmbedding (.group s) <;> simp only [List.map_cons, List.map_nil, he,
    Data.rawRel] at h
  case group v =>
    congr 1
    ext b
    have hs := f.supports s b
    simp only [he, Data.rawRel, f.base_apply, Point.base.injEq] at hs
    simpa only [Finset.mem_map, RelEmbedding.coe_toEmbedding, RawEmbedding.baseEmb_apply] using hs

@[simp] theorem RawEmbedding.star_apply (v : Finset ℕ) : f.toEmbedding (.star v) = .star v := by
  have h := (f.relates (.label v) [.star v]).2 rfl
  cases he : f.toEmbedding (.star v) <;> simp only [List.map_cons, List.map_nil, he,
    Data.rawRel] at h
  case star w => exact congrArg Point.star h.symm

theorem RawEmbedding.row_exists (t : Tuple M.I) (n : ℕ) (s : Finset M.B) :
    ∃ v, f.toEmbedding (.row t n s) = .row (Tuples.map f.indexEmb t) n v := by
  have hu := (f.relates (.row t.1 n) [.row t n s]).2 ⟨rfl, rfl⟩
  have hp := (f.relates (.rowProjection t.1 n)
    (.row t n s :: List.ofFn (fun i => Point.index (t.2 i)))).2 ⟨rfl, rfl, rfl⟩
  cases he : f.toEmbedding (.row t n s) <;>
    simp only [List.map_cons, List.map_nil, he, Data.rawRel] at hu
  case row r m v =>
    obtain ⟨hk, rfl⟩ := hu
    simp only [List.map_cons, List.map_ofFn, Function.comp_def, he, f.index_apply, Data.rawRel, true_and] at hp
    have ht : r = Tuples.map f.indexEmb t := by
      apply Tuples.entriesList_injective
      apply (show Function.Injective (Point.index (I := N.I) (B := N.B)) from fun _ _ h => Point.index.inj h).list_map
      simp only [Tuples.entriesList, List.map_ofFn]
      exact hp.2.symm
    exact ⟨v, by rw [ht]⟩

theorem RawEmbedding.col_exists (t : Tuple M.I) (b : M.B) (v : Finset ℕ) :
    ∃ w, f.toEmbedding (.col t b v) = .col (Tuples.map f.indexEmb t) (f.base b) w := by
  have hu := (f.relates (.col t.1) [.col t b v]).2 rfl
  have hp := (f.relates (.colProjection t.1)
    (.col t b v :: .base b :: List.ofFn (fun i => Point.index (t.2 i)))).2 ⟨rfl, rfl, rfl⟩
  cases he : f.toEmbedding (.col t b v) <;>
    simp only [List.map_cons, List.map_nil, he, Data.rawRel] at hu
  case col r c w =>
    simp only [List.map_cons, List.map_ofFn, Function.comp_def, he, f.index_apply, f.base_apply, Data.rawRel,
      Point.base.injEq] at hp
    have ht : r = Tuples.map f.indexEmb t := by
      apply Tuples.entriesList_injective
      apply (show Function.Injective (Point.index (I := N.I) (B := N.B)) from fun _ _ h => Point.index.inj h).list_map
      simp only [Tuples.entriesList, List.map_ofFn]
      exact hp.2.2.symm
    exact ⟨w, by rw [ht, ← hp.2.1]⟩

def RawEmbedding.rowShift (t : Tuple M.I) (n : ℕ) : Finset N.B :=
  (f.row_exists t n ∅).choose

def RawEmbedding.colShift (t : Tuple M.I) (b : M.B) : Finset ℕ :=
  (f.col_exists t b ∅).choose

@[simp] theorem RawEmbedding.row_zero (t : Tuple M.I) (n : ℕ) :
    f.toEmbedding (.row t n ∅) = .row (Tuples.map f.indexEmb t) n (f.rowShift t n) :=
  (f.row_exists t n ∅).choose_spec

@[simp] theorem RawEmbedding.col_zero (t : Tuple M.I) (b : M.B) :
    f.toEmbedding (.col t b ∅) = .col (Tuples.map f.indexEmb t) (f.base b) (f.colShift t b) :=
  (f.col_exists t b ∅).choose_spec

@[simp] theorem RawEmbedding.row_apply (t : Tuple M.I) (n : ℕ) (s : Finset M.B) :
    f.toEmbedding (.row t n s) = .row (Tuples.map f.indexEmb t) n
      (f.rowShift t n ∆ s.map f.baseEmb.toEmbedding) := by
  obtain ⟨v, hv⟩ := f.row_exists t n s
  have h := (f.relates .rowAct [.row t n ∅, .group s, .row t n s]).2
    ⟨rfl, rfl, (bot_symmDiff s).symm⟩
  simp only [List.map_cons, List.map_nil, f.row_zero, f.group_apply, hv, Data.rawRel,
    true_and] at h
  rw [hv, h]

@[simp] theorem RawEmbedding.col_apply (t : Tuple M.I) (b : M.B) (v : Finset ℕ) :
    f.toEmbedding (.col t b v) = .col (Tuples.map f.indexEmb t) (f.base b)
      (f.colShift t b ∆ v) := by
  obtain ⟨w, hw⟩ := f.col_exists t b v
  have h := (f.relates .colAct [.col t b ∅, .star v, .col t b v]).2
    ⟨rfl, rfl, (bot_symmDiff v).symm⟩
  simp only [List.map_cons, List.map_nil, f.col_zero, f.star_apply, hw, Data.rawRel,
    true_and] at h
  rw [hw, h]

def RawEmbedding.toMap : Map M N where
  index := f.indexEmb
  base := f.baseEmb
  rowShift := f.rowShift
  colShift := f.colShift
  bit_agrees t n b := by
    have h := f.relates .bit [.row t n ∅, .col t b ∅]
    simp only [List.map_cons, List.map_nil, f.row_zero, f.col_zero, Data.rawRel,
      true_and] at h
    have he : Matrix.bit (M.bits t) n ∅ b ∅ = M.bits t n b := by simp [Matrix.bit]
    rw [he] at h
    exact Bool.eq_iff_iff.2 h

@[simp] theorem RawEmbedding.toMap_onPoint (x : M.Carrier) :
    f.toMap.onPoint x = f.toEmbedding x := by
  cases x <;> simp [RawEmbedding.toMap, Map.onPoint]

end Arrays

end CHObstruction

end

end OAI

-- ===== Subarrays.lean =====

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace BaseOrders

variable {B : Type u} [LinearOrder B] [DenselyOrdered B] [NoMinOrder B]
  [NoMaxOrder B] [Nonempty B]

theorem small_hull (loc : ∀ a b : B, (Set.Icc a b).Countable)
    (A : Set B) (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    ∃ S : Set B, A ⊆ S ∧ S.OrdConnected ∧ Nonempty S ∧
      NoMinOrder S ∧ NoMaxOrder S ∧ DenselyOrdered S ∧ #S ≤ κ := by
  classical
  let p : B := Classical.arbitrary B
  let T : Set B := A ∪ {p}
  let lo : B → B := fun x => (exists_lt x).choose
  let hi : B → B := fun x => (exists_gt x).choose
  have hlo (x : B) : lo x < x := (exists_lt x).choose_spec
  have hhi (x : B) : x < hi x := (exists_gt x).choose_spec
  let S : Set B := {x | ∃ a : T, ∃ b : T, lo a < x ∧ x < hi b}
  have hTS : T ⊆ S := fun x hx => ⟨⟨x, hx⟩, ⟨x, hx⟩, hlo x, hhi x⟩
  have hc : S.OrdConnected := by
    constructor
    rintro x ⟨a, b, hax, hxb⟩ y ⟨c, d, hcy, hyd⟩ z ⟨hxz, hzy⟩
    exact ⟨a, d, hax.trans_le hxz, hzy.trans_lt hyd⟩
  have hmin : NoMinOrder S := ⟨by
    rintro ⟨x, a, b, hax, hxb⟩
    obtain ⟨y, hay, hyx⟩ := exists_between hax
    exact ⟨⟨y, a, b, hay, hyx.trans hxb⟩, hyx⟩⟩
  have hmax : NoMaxOrder S := ⟨by
    rintro ⟨x, a, b, hax, hxb⟩
    obtain ⟨y, hxy, hyb⟩ := exists_between hxb
    exact ⟨⟨y, a, b, hax.trans hxy, hyb⟩, hxy⟩⟩
  have hd : DenselyOrdered S := ⟨by
    intro x y hxy
    obtain ⟨z, hxz, hzy⟩ := exists_between hxy
    exact ⟨⟨z, hc.out x.property y.property ⟨hxz.le, hzy.le⟩⟩, hxz, hzy⟩⟩
  refine ⟨S, Set.Subset.trans Set.subset_union_left hTS, hc,
    ⟨⟨p, hTS (Or.inr rfl)⟩⟩, hmin, hmax, hd, ?_⟩
  have hT : #T ≤ κ := by
    apply (Cardinal.mk_union_le A {p}).trans
    simpa only [Cardinal.mk_singleton, Cardinal.add_eq_self hκ] using
      add_le_add hA (Cardinal.one_le_aleph0.trans hκ)
  have he : S = ⋃ ab : T × T, Set.Ioo (lo ab.1) (hi ab.2) := by
    ext x
    simp only [S, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_Ioo]
    exact ⟨fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩, fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩⟩
  rw [he]
  apply Cardinal.mk_iUnion_le_sum_mk.trans
  have hb (ab : T × T) : #(Set.Ioo (lo ab.1) (hi ab.2)) ≤ κ :=
    (Cardinal.mk_le_aleph0_iff.2 ((loc _ _).mono Set.Ioo_subset_Icc_self)).trans hκ
  apply (Cardinal.sum_le_sum _ _ hb).trans
  simp only [Cardinal.sum_const, Cardinal.mk_prod, Cardinal.lift_id]
  calc
    (#T * #T) * κ ≤ (κ * κ) * κ := mul_le_mul' (mul_le_mul' hT hT) le_rfl
    _ = κ := by rw [Cardinal.mul_eq_self hκ, Cardinal.mul_eq_self hκ]

end BaseOrders

namespace Arrays

open Tuples
open scoped symmDiff

variable (M : Data.{u})

def Data.restrict (J : Set M.I) (S : Set M.B) [Nonempty J] [Nonempty S]
    [DenselyOrdered S] [NoMinOrder S] [NoMaxOrder S] : Data.{u} where
  I := J
  B := S
  indexNonempty := inferInstance
  baseNonempty := inferInstance
  order := inferInstance
  dense := inferInstance
  noMin := inferInstance
  noMax := inferInstance
  locallyCountable a b := (M.locallyCountable a b).preimage Subtype.val_injective
  bits t n b := M.bits (Tuples.map (Function.Embedding.subtype J) t) n b

variable {M}
variable (J : Set M.I) (S : Set M.B) [Nonempty J] [Nonempty S]
  [DenselyOrdered S] [NoMinOrder S] [NoMaxOrder S]

local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq S := Classical.decEq S

def Data.restrictMap : Map (M.restrict J S) M where
  index := Function.Embedding.subtype J
  base := OrderEmbedding.subtype S
  rowShift _ _ := ∅
  colShift _ _ := ∅
  bit_agrees _ _ _ := by simp only [Matrix.bit, Finset.notMem_empty, decide_false, Bool.xor_false]; rfl

@[simp] theorem Data.restrictMap_colors (t : Tuple J) (b : M.B) :
    (M.restrictMap J S).colors t b = M.colors (Tuples.map (Function.Embedding.subtype J) t) b := by
  simp only [Map.colors, Data.restrictMap, Finset.notMem_empty, decide_false, Bool.xor_false,
    Data.colors]
  rfl

theorem Data.restrict_object (hCH : CH.{u}) (hM : M.IsObject hCH) :
    (M.restrict J S).IsObject hCH := by
  intro t
  have hc := (hM (Tuples.map (Function.Embedding.subtype J) t)).preimage
    (Subtype.val_injective (p := fun b => b ∈ S))
  apply hc.mono
  intro b hb hh
  apply hb
  exact (Tests.map hCH (Function.Embedding.subtype J) (fun r => M.colors r b) t).mp hh

theorem Data.restrict_strong (hCH : CH.{u}) (hS : S.OrdConnected)
    (hbad : ∀ t : Tuple J, {b | ¬ Tests.Test hCH
      (fun r => M.colors r b) (Tuples.map (Function.Embedding.subtype J) t)} ⊆ S) :
    (M.restrictMap J S).Strong hCH := by
  have he : Set.range (M.restrictMap J S).base = S := by
    change Set.range (Subtype.val : S → M.B) = S
    exact Subtype.range_coe_subtype
  constructor
  · rw [he]; exact hS
  · intro t b hb
    rw [he] at hb
    have ht := not_not.1 (fun h => hb (hbad t h))
    have hm := (Tests.map hCH (Function.Embedding.subtype J) (fun r => M.colors r b) t).mp ht
    exact (Tests.congr hCH t (fun _ _ => Data.restrictMap_colors J S _ b)).mpr hm

theorem Data.cardinal_le (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (hI : #M.I ≤ κ) (hB : #M.B ≤ κ) : #M.Carrier ≤ κ := by
  let enc : M.Carrier → M.I ⊕ M.B ⊕ Finset M.B ⊕ Finset ℕ ⊕
      (Tuple M.I × ℕ × Finset M.B) ⊕ (Tuple M.I × M.B × Finset ℕ)
    | .index i => .inl i
    | .base b => .inr (.inl b)
    | .group s => .inr (.inr (.inl s))
    | .star v => .inr (.inr (.inr (.inl v)))
    | .row t n s => .inr (.inr (.inr (.inr (.inl (t, n, s)))))
    | .col t b v => .inr (.inr (.inr (.inr (.inr (t, b, v)))))
  have he : Function.Injective enc := by
    intro a b h
    cases a <;> cases b <;> simp_all [enc]
  apply (Cardinal.mk_le_of_injective he).trans
  simp only [Cardinal.mk_sum, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_uzero,
    Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.mk_finset_of_infinite]
  have ht := Tuples.cardinal_bound κ hκ hI
  calc
    #M.I + (#M.B + (#M.B + (ℵ₀ +
      (#(Tuple M.I) * (ℵ₀ * #M.B) + #(Tuple M.I) * (#M.B * ℵ₀))))) ≤
      κ + (κ + (κ + (κ + (κ * (κ * κ) + κ * (κ * κ))))) := by gcongr
    _ = κ := by simp only [Cardinal.mul_eq_self hκ, Cardinal.add_eq_self hκ]

theorem Data.cardinal_eq : #M.Carrier = max (max #M.I #M.B) ℵ₀ := by
  apply le_antisymm
  · exact M.cardinal_le _ (le_max_right _ _) ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_left _ _))
  · apply max_le
    · exact max_le (Cardinal.mk_le_of_injective (fun _ _ h => Point.index.inj h))
        (Cardinal.mk_le_of_injective (fun _ _ h => Point.base.inj h))
    · have h := Cardinal.mk_le_of_injective (f := fun v : ULift.{u} (Finset ℕ) =>
          Point.star (I := M.I) (B := M.B) v.down) (fun a b h => ULift.ext _ _ (Point.star.inj h))
      simpa only [Cardinal.mk_uLift, Cardinal.mk_finset_of_infinite, Cardinal.mk_nat,
        Cardinal.lift_aleph0] using h

end Arrays

end CHObstruction

end

end OAI

-- ===== ArrayIsomorphisms.lean =====

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B
local instance : DecidableEq P.B := Classical.decEq P.B

structure RawIso (M N : Data.{u}) where
  toEquiv : M.Carrier ≃ N.Carrier
  relates : ∀ s xs, N.rawRel s (xs.map toEquiv) ↔ M.rawRel s xs

variable (e : RawIso M N)

theorem RawIso.base_surjective_point (b : N.B) : ∃ a, e.toEquiv (.base a) = .base b := by
  obtain ⟨x, hx⟩ := e.toEquiv.surjective (.base b)
  have h := (e.relates .base [x]).1 (by simp only [List.map_cons, List.map_nil, hx, Data.rawRel])
  cases x <;> simp only [Data.rawRel] at h
  case base a => exact ⟨a, hx⟩

theorem RawIso.index_surjective_point (b : N.I) : ∃ a, e.toEquiv (.index a) = .index b := by
  obtain ⟨x, hx⟩ := e.toEquiv.surjective (.index b)
  have h := (e.relates .index [x]).1 (by simp only [List.map_cons, List.map_nil, hx, Data.rawRel])
  cases x <;> simp only [Data.rawRel] at h
  case index a => exact ⟨a, hx⟩

def RawIso.toRawEmbedding : RawEmbedding M N where
  toEmbedding := e.toEquiv.toEmbedding
  relates := e.relates
  supports s b := by
    obtain ⟨a, ha⟩ := e.base_surjective_point b
    have hr := e.relates .incidence [.base a, .group s]
    simp only [List.map_cons, List.map_nil, ha] at hr
    change N.rawRel .incidence [.base b, e.toEquiv (.group s)] ↔ a ∈ s at hr
    change N.rawRel .incidence [.base b, e.toEquiv (.group s)] ↔ _
    rw [hr]
    constructor
    · intro h; exact ⟨a, h, ha⟩
    · rintro ⟨c, hc, he⟩
      have hca : c = a := Point.base.inj (e.toEquiv.injective (he.trans ha.symm))
      exact hca ▸ hc

def RawIso.toMap : Map M N := e.toRawEmbedding.toMap

theorem RawIso.toMap_onPoint (x : M.Carrier) : e.toMap.onPoint x = e.toEquiv x :=
  e.toRawEmbedding.toMap_onPoint x

theorem RawIso.base_surjective : Function.Surjective e.toMap.base := by
  intro b
  obtain ⟨a, ha⟩ := e.base_surjective_point b
  refine ⟨a, Point.base.inj (I := N.I) ?_⟩
  exact (e.toMap_onPoint (.base a)).trans ha

theorem RawIso.index_surjective : Function.Surjective e.toMap.index := by
  intro b
  obtain ⟨a, ha⟩ := e.index_surjective_point b
  refine ⟨a, Point.index.inj (B := N.B) ?_⟩
  exact (e.toMap_onPoint (.index a)).trans ha

theorem Map.factor (f : Map M P) (g : Map N P)
    (h : ∀ x : M.Carrier, ∃ y, g.onPoint y = f.onPoint x) :
    ∃ k : Map M N, g.comp k = f := by
  let ef : M.Carrier → N.Carrier := fun x => (h x).choose
  have hef (x) : g.onPoint (ef x) = f.onPoint x := (h x).choose_spec
  have hinj : Function.Injective ef := by
    intro a b hab
    apply f.injective
    rw [← hef a, ← hef b, hab]
  let r : RawEmbedding M N := {
    toEmbedding := ⟨ef, hinj⟩
    relates := by
      intro s xs
      have he : (xs.map ef).map g.onPoint = xs.map f.onPoint := by
        rw [List.map_map]
        exact List.map_congr_left (fun x _ => hef x)
      change N.rawRel s (xs.map ef) ↔ M.rawRel s xs
      rw [← g.rawRel s (xs.map ef), he, f.rawRel]
    supports := by
      intro s b
      have hr := g.rawRel .incidence [.base b, ef (.group s)]
      simp only [List.map_cons, List.map_nil] at hr
      rw [hef] at hr
      change g.base b ∈ s.map f.base.toEmbedding ↔
        N.rawRel .incidence [.base b, ef (.group s)] at hr
      change N.rawRel .incidence [.base b, ef (.group s)] ↔
        ∃ a ∈ s, ef (.base a) = .base b
      rw [← hr]
      constructor
      · intro hb
        obtain ⟨a, has, ha⟩ := Finset.mem_map.1 hb
        refine ⟨a, has, g.injective ?_⟩
        rw [hef]
        exact congrArg Point.base ha
      · rintro ⟨a, has, ha⟩
        refine Finset.mem_map.2 ⟨a, has, ?_⟩
        have he := hef (.base a)
        rw [ha] at he
        exact Point.base.inj he.symm }
  refine ⟨r.toMap, Map.ext_onPoint (fun x => ?_)⟩
  rw [Map.comp_onPoint, r.toMap_onPoint]
  exact hef x

theorem Map.Strong.factor (hCH : CH.{u}) {f : Map M P} {g : Map N P} {k : Map M N}
    (hf : f.Strong hCH) (he : g.comp k = f) : k.Strong hCH := by
  have hb (a : M.B) : g.base (k.base a) = f.base a := by
    have h := congrArg (fun l : Map M P => l.base a) he
    exact h
  constructor
  · constructor
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ z ⟨haz, hzb⟩
    have hgz : g.base z ∈ Set.Icc (f.base a) (f.base b) := by
      rw [← hb, ← hb]
      exact ⟨g.base.monotone haz, g.base.monotone hzb⟩
    obtain ⟨c, hc⟩ := hf.convex.out ⟨a, rfl⟩ ⟨b, rfl⟩ hgz
    exact ⟨c, g.base.injective ((hb c).trans hc)⟩
  · intro t b hnb
    have hn : g.base b ∉ Set.range f.base := by
      rintro ⟨a, ha⟩
      exact hnb ⟨a, g.base.injective ((hb a).trans ha)⟩
    have ht := hf.outside t (g.base b) hn
    rw [← he] at ht
    simpa only [Map.comp_colors_base] using ht

end Arrays

namespace CardinalTools

theorem union_le {X A : Type u} (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (hA : #A ≤ κ) (s : A → Set X) (hs : ∀ a, #(s a) ≤ κ) : #(⋃ a, s a) ≤ κ := by
  apply Cardinal.mk_iUnion_le_sum_mk.trans
  apply (Cardinal.sum_le_sum _ _ hs).trans
  simpa only [Cardinal.sum_const, Cardinal.lift_id, Cardinal.mul_eq_self hκ] using
    (mul_le_mul' hA (le_refl κ))

end CardinalTools

namespace Arrays

open Tuples
open scoped symmDiff

variable {M : Data.{u}}
local instance : DecidableEq M.I := Classical.decEq M.I
local instance : DecidableEq M.B := Classical.decEq M.B

def Point.indexSupport : M.Carrier → Finset M.I
  | .index i => {i}
  | .row t _ _ | .col t _ _ => (Finset.univ.map t.2)
  | _ => ∅

def Point.baseSupport : M.Carrier → Finset M.B
  | .base b | .col _ b _ => {b}
  | .group s | .row _ _ s => s
  | _ => ∅

theorem Data.restrictMap_range (J : Set M.I) (S : Set M.B) [Nonempty J] [Nonempty S]
    [DenselyOrdered S] [NoMinOrder S] [NoMaxOrder S] (x : M.Carrier)
    (hi : ↑x.indexSupport ⊆ J) (hb : ↑x.baseSupport ⊆ S) :
    x ∈ Set.range (M.restrictMap J S).onPoint := by
  classical
  have ht (t : Tuple M.I) (h : ↑((Finset.univ.map t.2)) ⊆ J) :
      ∃ r : Tuple J, Tuples.map (Function.Embedding.subtype J) r = t := by
    let r : Tuple J := ⟨t.1, ⟨fun i => ⟨t.2 i, h (Finset.mem_map.2 ⟨i, Finset.mem_univ i, rfl⟩)⟩,
      fun a b he => t.2.injective (congrArg Subtype.val he)⟩⟩
    exact ⟨r, rfl⟩
  have hs (s : Finset M.B) (h : ↑s ⊆ S) :
      (s.subtype (· ∈ S)).map (OrderEmbedding.subtype S).toEmbedding = s :=
    Finset.subtype_map_of_mem (p := fun x => x ∈ S) (fun _ ha => h ha)
  cases x with
  | index i => exact ⟨.index ⟨i, hi (Finset.mem_singleton_self i)⟩, rfl⟩
  | base b => exact ⟨.base ⟨b, hb (Finset.mem_singleton_self b)⟩, rfl⟩
  | group s => exact ⟨.group (s.subtype (· ∈ S)), congrArg Point.group (hs s hb)⟩
  | star v => exact ⟨.star v, rfl⟩
  | row t n s =>
    obtain ⟨r, hr⟩ := ht t hi
    refine ⟨.row r n (s.subtype (· ∈ S)), ?_⟩
    change Point.row (Tuples.map (Function.Embedding.subtype J) r) n
      (∅ ∆ (s.subtype (· ∈ S)).map (OrderEmbedding.subtype S).toEmbedding) = _
    rw [hr, hs s hb]
    simp
  | col t b v =>
    obtain ⟨r, hr⟩ := ht t hi
    refine ⟨.col r ⟨b, hb (Finset.mem_singleton_self b)⟩ v, ?_⟩
    change Point.col (Tuples.map (Function.Embedding.subtype J) r) b (∅ ∆ v) = _
    rw [hr]
    simp

theorem Data.small_subarray (M : Data.{u}) (hCH : CH.{u}) (hM : M.IsObject hCH)
    (A : Set M.Carrier) :
    ∃ N : Data.{u}, ∃ f : Map N M, N.IsObject hCH ∧ f.Strong hCH ∧
      A ⊆ Set.range f.onPoint ∧ #N.Carrier ≤ #A + ℵ₀ := by
  classical
  let κ : Cardinal.{u} := #A + ℵ₀
  have hκ : ℵ₀ ≤ κ := le_add_self
  have hA : #A ≤ κ := le_self_add
  let p : M.I := Classical.arbitrary M.I
  let J : Set M.I := (⋃ a : A, (a.val.indexSupport : Set M.I)) ∪ {p}
  have hJ : #J ≤ κ := by
    apply (Cardinal.mk_union_le _ _).trans
    apply Cardinal.add_le_of_le hκ
    · exact CardinalTools.union_le κ hκ hA _ (fun a =>
        (Cardinal.mk_le_aleph0_iff.2 (a.val.indexSupport.countable_toSet)).trans hκ)
    · simpa only [Cardinal.mk_singleton] using Cardinal.one_le_aleph0.trans hκ
  let : Nonempty J := ⟨⟨p, Or.inr rfl⟩⟩
  let T : Set M.B := (⋃ a : A, (a.val.baseSupport : Set M.B)) ∪
    (⋃ t : Tuple J, {b | ¬ Tests.Test hCH (fun r => M.colors r b)
      (Tuples.map (Function.Embedding.subtype J) t)})
  have hT : #T ≤ κ := by
    apply (Cardinal.mk_union_le _ _).trans
    apply Cardinal.add_le_of_le hκ
    · exact CardinalTools.union_le κ hκ hA _ (fun a =>
        (Cardinal.mk_le_aleph0_iff.2 (a.val.baseSupport.countable_toSet)).trans hκ)
    · exact CardinalTools.union_le κ hκ (Tuples.cardinal_bound κ hκ hJ) _
        (fun t => (Cardinal.mk_le_aleph0_iff.2 (hM _)).trans hκ)
  obtain ⟨S, hTS, hc, hn, hmin, hmax, hd, hS⟩ :=
    BaseOrders.small_hull M.locallyCountable T κ hκ hT
  let : Nonempty S := hn
  let : NoMinOrder S := hmin
  let : NoMaxOrder S := hmax
  let : DenselyOrdered S := hd
  refine ⟨M.restrict J S, M.restrictMap J S, M.restrict_object J S hCH hM,
    M.restrict_strong J S hCH hc ?_, ?_, ?_⟩
  · intro t b hb
    exact hTS (Or.inr (Set.mem_iUnion.2 ⟨t, hb⟩))
  · intro x hx
    apply Data.restrictMap_range J S x
    · intro i hi
      exact Or.inl (Set.mem_iUnion.2 ⟨⟨x, hx⟩, hi⟩)
    · intro b hb
      exact hTS (Or.inl (Set.mem_iUnion.2 ⟨⟨x, hx⟩, hb⟩))
  · exact Data.cardinal_le κ hκ hJ hS

end Arrays

end CHObstruction

end

end OAI

-- ===== DirectedLimits.lean =====

namespace OAI

/-!
# Directed limits of finite-support arrays

The index, base and six-sorted carrier are constructed as directed limits.
Finite tuples and supports can be represented in a common stage. Compatible
row and column actions give the limit its relational interpretation, and
convexity supplies local countability and the strong-embedding properties.
-/

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace LimitTools

variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  {F : J → Type u} (f : ∀ i j, i ≤ j → F i ↪ F j) [DirectedSystem F (f · · ·)]
  (inj : ∀ i j h, Function.Injective (f i j h))

abbrev Limit := DirectLimit F f

def of (i : J) : F i ↪ Limit f := ⟨fun x => ⟦⟨i, x⟩⟧, DirectLimit.mk_injective f inj i⟩

omit [Nonempty J] in
@[simp] theorem of_map (i j : J) (h : i ≤ j) (x : F i) :
    of f inj j (f i j h x) = of f inj i x := by
  exact DirectLimit.mk_apply (f := f) i j x h

theorem common {A : Type v} [Finite A] (x : A → Limit f) (i : J) :
    ∃ j, i ≤ j ∧ ∃ y : A → F j, ∀ a, of f inj j (y a) = x a := by
  classical
  let r (a : A) : Σ j, F j := Classical.choose (Quotient.exists_rep (x a))
  have hr (a : A) : (⟦r a⟧ : Limit f) = x a := Classical.choose_spec (Quotient.exists_rep (x a))
  let _ := Fintype.ofFinite A
  obtain ⟨j, hj⟩ := (insert i (Finset.univ.image (fun a => (r a).1))).exists_le
  have hij : i ≤ j := hj i (Finset.mem_insert_self _ _)
  have ha (a : A) : (r a).1 ≤ j := hj _ (Finset.mem_insert_of_mem (Finset.mem_image.2
    ⟨a, Finset.mem_univ a, rfl⟩))
  exact ⟨j, hij, fun a => f _ _ (ha a) (r a).2,
    fun a => (of_map f inj _ _ _ _).trans (hr a)⟩

end LimitTools

namespace Arrays
namespace System

variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]

structure Data where
  obj : J → Arrays.Data.{u}
  map : ∀ i j, i ≤ j → Map (obj i) (obj j)
  map_id : ∀ i, map i i le_rfl = Map.id (obj i)
  map_comp : ∀ i j k (h : i ≤ j) (h' : j ≤ k),
    (map j k h').comp (map i j h) = map i k (h.trans h')

namespace Data

open Tuples

variable (S : Data (J := J))

def indexMap (i j : J) (h : i ≤ j) : (S.obj i).I ↪ (S.obj j).I := (S.map i j h).index

def baseMap (i j : J) (h : i ≤ j) : (S.obj i).B ↪ (S.obj j).B := (S.map i j h).base.toEmbedding

def pointMap (i j : J) (h : i ≤ j) : (S.obj i).Carrier ↪ (S.obj j).Carrier :=
  (S.map i j h).toEmbedding

instance indexSystem : DirectedSystem (fun i => (S.obj i).I) (S.indexMap · · ·) where
  map_self := by intro i x; change (S.map i i le_rfl).index x = x; rw [S.map_id]; rfl
  map_map := by
    intro k j i h h' x
    exact congrArg (fun f : Map (S.obj i) (S.obj k) => f.index x) (S.map_comp i j k h h')

instance baseSystem : DirectedSystem (fun i => (S.obj i).B) (S.baseMap · · ·) where
  map_self := by intro i x; change (S.map i i le_rfl).base x = x; rw [S.map_id]; rfl
  map_map := by
    intro k j i h h' x
    exact congrArg (fun f : Map (S.obj i) (S.obj k) => f.base x) (S.map_comp i j k h h')

instance pointSystem : DirectedSystem (fun i => (S.obj i).Carrier) (S.pointMap · · ·) where
  map_self := by intro i x; change (S.map i i le_rfl).onPoint x = x; rw [S.map_id, Map.id_onPoint]
  map_map := by
    intro k j i h h' x
    change (S.map j k h').onPoint ((S.map i j h).onPoint x) = _
    rw [← Map.comp_onPoint, S.map_comp]
    rfl

abbrev I := DirectLimit (fun i => (S.obj i).I) S.indexMap
abbrev B := DirectLimit (fun i => (S.obj i).B) S.baseMap
abbrev X := DirectLimit (fun i => (S.obj i).Carrier) S.pointMap

def index (i : J) : (S.obj i).I ↪ S.I :=
  LimitTools.of S.indexMap (fun a b h => (S.map a b h).index.injective) i

def base (i : J) : (S.obj i).B ↪ S.B :=
  LimitTools.of S.baseMap (fun a b h => (S.map a b h).base.injective) i

def point (i : J) : (S.obj i).Carrier ↪ S.X :=
  LimitTools.of S.pointMap (fun a b h => (S.map a b h).injective) i

omit [Nonempty J] in
@[simp] theorem index_map (i j : J) (h : i ≤ j) (x : (S.obj i).I) :
    S.index j ((S.map i j h).index x) = S.index i x := LimitTools.of_map S.indexMap _ i j h x

omit [Nonempty J] in
@[simp] theorem base_map (i j : J) (h : i ≤ j) (x : (S.obj i).B) :
    S.base j ((S.map i j h).base x) = S.base i x := LimitTools.of_map S.baseMap _ i j h x

omit [Nonempty J] in
@[simp] theorem point_map (i j : J) (h : i ≤ j) (x : (S.obj i).Carrier) :
    S.point j ((S.map i j h).onPoint x) = S.point i x := LimitTools.of_map S.pointMap _ i j h x

instance : Nonempty S.I := ⟨S.index (Classical.arbitrary J) (Classical.arbitrary _)⟩
instance : Nonempty S.B := ⟨S.base (Classical.arbitrary J) (Classical.arbitrary _)⟩

def le : S.B → S.B → Prop := DirectLimit.lift₂ S.baseMap S.baseMap (fun _ a b => a ≤ b)
  (fun i j h _a _b => propext (S.map i j h).base.le_iff_le.symm)

omit [Nonempty J] in
@[simp] theorem le_base (i : J) (a b : (S.obj i).B) : S.le (S.base i a) (S.base i b) ↔ a ≤ b := by
  unfold le
  change DirectLimit.lift₂ S.baseMap S.baseMap (fun _ a b => a ≤ b) _ ⟦⟨i, a⟩⟧ ⟦⟨i, b⟩⟧ ↔ _
  rw [DirectLimit.lift₂_def]

instance leInstance : LE S.B := ⟨S.le⟩
instance ltInstance : LT S.B := ⟨fun a b => S.le a b ∧ ¬ S.le b a⟩

instance order : LinearOrder S.B where
  le := S.le
  lt := fun a b => S.le a b ∧ ¬ S.le b a
  lt_iff_le_not_ge := by intros; rfl
  le_refl := DirectLimit.induction _ (fun i a => (S.le_base i a a).2 le_rfl)
  le_trans := by
    intro a b c
    induction a, b, c using DirectLimit.induction₃ S.baseMap with
    | ih i a b c =>
      change S.le (S.base i a) (S.base i b) → S.le (S.base i b) (S.base i c) → _
      rw [S.le_base, S.le_base]
      intro h h'; exact (S.le_base i a c).2 (h.trans h')
  le_antisymm := by
    intro a b
    induction a, b using DirectLimit.induction₂ S.baseMap with
    | ih i a b =>
      change S.le (S.base i a) (S.base i b) → S.le (S.base i b) (S.base i a) → _
      rw [le_base, le_base]
      intro h h'; exact congrArg (S.base i) (le_antisymm h h')
  le_total := by
    intro a b
    induction a, b using DirectLimit.induction₂ S.baseMap with
    | ih i a b =>
      change S.le (S.base i a) (S.base i b) ∨ S.le (S.base i b) (S.base i a)
      rw [le_base, le_base]; exact le_total a b
  toDecidableLE := Classical.decRel _

instance preorder : Preorder S.B := S.order.toPartialOrder.toPreorder

def baseOrder (i : J) : (S.obj i).B ↪o S.B where
  toEmbedding := S.base i
  map_rel_iff' := by
    intro a b
    exact S.le_base i a b

omit [Nonempty J] in
@[simp] theorem tuple_map (i j : J) (h : i ≤ j) (t : Tuple (S.obj i).I) :
    Tuples.map (S.index j) (Tuples.map (S.map i j h).index t) = Tuples.map (S.index i) t := by
  rw [Tuples.map_comp]
  congr 1
  ext x
  exact S.index_map i j h x

omit [Nonempty J] in
@[simp] theorem finset_map (i j : J) (h : i ≤ j) (s : Finset (S.obj i).B) :
    (s.map (S.map i j h).base.toEmbedding).map (S.base j) = s.map (S.base i) := by
  rw [Finset.map_map]
  congr 1
  ext x
  exact S.base_map i j h x

theorem tuple_exists (t : Tuple S.I) (i : J) :
    ∃ j, i ≤ j ∧ ∃ r : Tuple (S.obj j).I, Tuples.map (S.index j) r = t := by
  obtain ⟨j, hij, y, hy⟩ := LimitTools.common S.indexMap
    (fun a b h => (S.map a b h).index.injective) (fun a => t.2 a) i
  have hinj : Function.Injective y := by
    intro a b h
    apply t.2.injective
    rw [← hy a, ← hy b, h]
  exact ⟨j, hij, ⟨t.1, ⟨y, hinj⟩⟩, by
    cases t with
    | mk k t =>
      change (⟨k, _⟩ : Tuple S.I) = ⟨k, t⟩
      congr 1
      exact Function.Embedding.ext hy⟩

theorem finset_exists (s : Finset S.B) (i : J) :
    ∃ j, i ≤ j ∧ ∃ r : Finset (S.obj j).B, r.map (S.base j) = s := by
  classical
  obtain ⟨j, hij, y, hy⟩ := LimitTools.common S.baseMap
    (fun a b h => (S.map a b h).base.injective) (fun a : s => (a : S.B)) i
  refine ⟨j, hij, Finset.univ.image y, ?_⟩
  ext b
  simp only [Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ⟨c, rfl⟩, he⟩
    have hc : S.base j (y c) = (c : S.B) := hy c
    rw [hc] at he
    exact he ▸ c.property
  · intro hb
    exact ⟨y ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, hy ⟨b, hb⟩⟩

open scoped symmDiff
local instance : DecidableEq S.B := Classical.decEq _
local instance (i : J) : DecidableEq (S.obj i).B := Classical.decEq _
local instance (i : J) : DecidableEq (Tuple (S.obj i).I) := Classical.decEq _

def shapeAt (i : J) : (S.obj i).Carrier → Point S.I S.B
  | .index a => .index (S.index i a)
  | .base b => .base (S.base i b)
  | .group s => .group (s.map (S.base i))
  | .star v => .star v
  | .row t n _ => .row (Tuples.map (S.index i) t) n ∅
  | .col t b _ => .col (Tuples.map (S.index i) t) (S.base i b) ∅

omit [Nonempty J] in
theorem shapeAt_map (i j : J) (h : i ≤ j) (x : (S.obj i).Carrier) :
    S.shapeAt j ((S.map i j h).onPoint x) = S.shapeAt i x := by
  cases x <;> simp only [Map.onPoint, shapeAt, index_map, base_map, tuple_map, finset_map]

def shape : S.X → Point S.I S.B := DirectLimit.lift S.pointMap S.shapeAt
  (fun i j h x => (S.shapeAt_map i j h x).symm)

omit [Nonempty J] in
@[simp] theorem shape_point (i : J) (x : (S.obj i).Carrier) :
    S.shape (S.point i x) = S.shapeAt i x := rfl

def rowDiffAt (i : J) : (S.obj i).Carrier → (S.obj i).Carrier → Option (Finset S.B)
  | .row t n s, .row r m q => if t = r ∧ n = m then some ((s ∆ q).map (S.base i)) else none
  | _, _ => none

def colDiffAt (i : J) : (S.obj i).Carrier → (S.obj i).Carrier → Option (Finset ℕ)
  | .col t b v, .col r c w => if t = r ∧ b = c then some (v ∆ w) else none
  | _, _ => none

omit [Nonempty J] in
theorem rowDiffAt_map (i j : J) (h : i ≤ j) (x y : (S.obj i).Carrier) :
    S.rowDiffAt j ((S.map i j h).onPoint x) ((S.map i j h).onPoint y) = S.rowDiffAt i x y := by
  classical
  cases x <;> cases y <;> simp only [Map.onPoint, rowDiffAt]
  case row.row t n s r m q =>
    by_cases ht : t = r
    · subst r
      by_cases hn : n = m
      · subst m
        simp only [and_self, ↓reduceIte]
        rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, bot_symmDiff,
          ← FiniteSupports.map_symmDiff, finset_map]
      · simp only [hn, and_false, ↓reduceIte]
    · simp only [(Tuples.map_injective (S.map i j h).index).eq_iff, ht, false_and, ↓reduceIte]

omit [IsDirectedOrder J] [Nonempty J] in
theorem colDiffAt_map (i j : J) (h : i ≤ j) (x y : (S.obj i).Carrier) :
    S.colDiffAt j ((S.map i j h).onPoint x) ((S.map i j h).onPoint y) = S.colDiffAt i x y := by
  classical
  cases x <;> cases y <;> simp only [Map.onPoint, colDiffAt]
  case col.col t b v r c w =>
    by_cases ht : t = r
    · subst r
      by_cases hb : b = c
      · subst c
        simp only [and_self, ↓reduceIte]
        rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, bot_symmDiff]
      · simp only [(S.map i j h).base.injective.eq_iff, hb, and_false, ↓reduceIte]
    · simp only [(Tuples.map_injective (S.map i j h).index).eq_iff, ht, false_and, ↓reduceIte]

def rowDiff : S.X → S.X → Option (Finset S.B) :=
  DirectLimit.lift₂ S.pointMap S.pointMap S.rowDiffAt (fun i j h x y => (S.rowDiffAt_map i j h x y).symm)

def colDiff : S.X → S.X → Option (Finset ℕ) :=
  DirectLimit.lift₂ S.pointMap S.pointMap S.colDiffAt (fun i j h x y => (S.colDiffAt_map i j h x y).symm)

omit [Nonempty J] in
@[simp] theorem rowDiff_point (i : J) (x y : (S.obj i).Carrier) :
    S.rowDiff (S.point i x) (S.point i y) = S.rowDiffAt i x y := by
  exact DirectLimit.lift₂_def S.pointMap S.pointMap S.rowDiffAt _ i x y

omit [Nonempty J] in
@[simp] theorem colDiff_point (i : J) (x y : (S.obj i).Carrier) :
    S.colDiff (S.point i x) (S.point i y) = S.colDiffAt i x y := by
  exact DirectLimit.lift₂_def S.pointMap S.pointMap S.colDiffAt _ i x y

omit [Nonempty J] in
theorem rowDiff_refl_at (i : J) (t : Tuple (S.obj i).I) (n : ℕ) (s q : Finset (S.obj i).B) :
    S.rowDiff (S.point i (.row t n s)) (S.point i (.row t n q)) =
      some ((s ∆ q).map (S.base i)) := by
  simp only [rowDiff_point, rowDiffAt, and_self, ↓reduceIte]

omit [Nonempty J] in
theorem colDiff_refl_at (i : J) (t : Tuple (S.obj i).I) (b : (S.obj i).B) (v w : Finset ℕ) :
    S.colDiff (S.point i (.col t b v)) (S.point i (.col t b w)) = some (v ∆ w) := by
  simp only [colDiff_point, colDiffAt, and_self, ↓reduceIte]

omit [Nonempty J] in
theorem rowDiff_zero {x y : S.X} (h : S.rowDiff x y = some ∅) : x = y := by
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    change S.rowDiff (S.point i x) (S.point i y) = some ∅ at h
    rw [rowDiff_point] at h
    cases x <;> cases y <;> simp only [rowDiffAt] at h
    all_goals try contradiction
    case row.row t n s r m q =>
      split_ifs at h with he
      · obtain ⟨rfl, rfl⟩ := he
        have hs : s = q := Finset.symmDiff_eq_empty.1 (by
          have hh := Option.some.inj h
          simpa using hh)
        subst q
        rfl

omit [Nonempty J] in
theorem colDiff_zero {x y : S.X} (h : S.colDiff x y = some ∅) : x = y := by
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    change S.colDiff (S.point i x) (S.point i y) = some ∅ at h
    rw [colDiff_point] at h
    cases x <;> cases y <;> simp only [colDiffAt] at h
    all_goals try contradiction
    case col.col t b v r c w =>
      split_ifs at h with he
      · obtain ⟨rfl, rfl⟩ := he
        have hv : v = w := Finset.symmDiff_eq_empty.1 (Option.some.inj h)
        subst w
        rfl

omit [Nonempty J] in
theorem rowDiff_symm (x y : S.X) : S.rowDiff x y = S.rowDiff y x := by
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    change S.rowDiff (S.point i x) (S.point i y) = S.rowDiff (S.point i y) (S.point i x)
    rw [rowDiff_point, rowDiff_point]
    cases x <;> cases y <;> simp only [rowDiffAt]
    case row.row t n s r m q =>
      by_cases ht : t = r <;> by_cases hn : n = m <;>
        simp_all [symmDiff_comm, eq_comm]

omit [Nonempty J] in
theorem colDiff_symm (x y : S.X) : S.colDiff x y = S.colDiff y x := by
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    change S.colDiff (S.point i x) (S.point i y) = S.colDiff (S.point i y) (S.point i x)
    rw [colDiff_point, colDiff_point]
    cases x <;> cases y <;> simp only [colDiffAt]
    case col.col t b v r c w =>
      by_cases ht : t = r <;> by_cases hb : b = c <;>
        simp_all [symmDiff_comm, eq_comm]

omit [Nonempty J] in
theorem rowDiff_trans {x y z : S.X} {s q : Finset S.B}
    (h : S.rowDiff x y = some s) (h' : S.rowDiff y z = some q) :
    S.rowDiff x z = some (s ∆ q) := by
  induction x, y, z using DirectLimit.induction₃ S.pointMap with
  | ih i x y z =>
    change S.rowDiff (S.point i x) (S.point i y) = some s at h
    change S.rowDiff (S.point i y) (S.point i z) = some q at h'
    change S.rowDiff (S.point i x) (S.point i z) = _
    rw [rowDiff_point] at h h' ⊢
    cases x <;> cases y <;> simp only [rowDiffAt] at h
    all_goals try contradiction
    case row.row t n a r m b =>
      split_ifs at h with he
      · obtain ⟨rfl, rfl⟩ := he
        cases z <;> simp only [rowDiffAt] at h'
        all_goals try contradiction
        case row t' n' c =>
          split_ifs at h' with he'
          · obtain ⟨rfl, rfl⟩ := he'
            have hs := Option.some.inj h
            have hq := Option.some.inj h'
            subst s; subst q
            simp only [rowDiffAt, and_self, ↓reduceIte, ← FiniteSupports.map_symmDiff,
              symmDiff_assoc, symmDiff_symmDiff_cancel_left]

omit [Nonempty J] in
theorem colDiff_trans {x y z : S.X} {v w : Finset ℕ}
    (h : S.colDiff x y = some v) (h' : S.colDiff y z = some w) :
    S.colDiff x z = some (v ∆ w) := by
  induction x, y, z using DirectLimit.induction₃ S.pointMap with
  | ih i x y z =>
    change S.colDiff (S.point i x) (S.point i y) = some v at h
    change S.colDiff (S.point i y) (S.point i z) = some w at h'
    change S.colDiff (S.point i x) (S.point i z) = _
    rw [colDiff_point] at h h' ⊢
    cases x <;> cases y <;> simp only [colDiffAt] at h
    all_goals try contradiction
    case col.col t b a r c d =>
      split_ifs at h with he
      · obtain ⟨rfl, rfl⟩ := he
        cases z <;> simp only [colDiffAt] at h'
        all_goals try contradiction
        case col t' b' e =>
          split_ifs at h' with he'
          · obtain ⟨rfl, rfl⟩ := he'
            have hv := Option.some.inj h
            have hw := Option.some.inj h'
            subst v; subst w
            simp only [colDiffAt, and_self, ↓reduceIte, symmDiff_assoc, symmDiff_symmDiff_cancel_left]

omit [Nonempty J] in
theorem rowDiff_unique {o x y : S.X} {s : Finset S.B}
    (hx : S.rowDiff o x = some s) (hy : S.rowDiff o y = some s) : x = y := by
  apply S.rowDiff_zero
  have h := S.rowDiff_trans ((S.rowDiff_symm x o).trans hx) hy
  simpa only [symmDiff_self, Finset.bot_eq_empty] using h

omit [Nonempty J] in
theorem colDiff_unique {o x y : S.X} {v : Finset ℕ}
    (hx : S.colDiff o x = some v) (hy : S.colDiff o y = some v) : x = y := by
  apply S.colDiff_zero
  have h := S.colDiff_trans ((S.colDiff_symm x o).trans hx) hy
  simpa only [symmDiff_self, Finset.bot_eq_empty] using h

omit [Nonempty J] in

theorem shapeAt_row {i : J} {x : (S.obj i).Carrier} {t : Tuple S.I} {n : ℕ}
    (h : S.shapeAt i x = .row t n ∅) :
    ∃ r s, x = .row r n s ∧ Tuples.map (S.index i) r = t := by
  cases x <;> simp only [shapeAt] at h
  all_goals try contradiction
  case row r m s =>
    obtain ⟨ht, rfl, _⟩ := Point.row.inj h
    exact ⟨r, s, rfl, ht⟩

omit [Nonempty J] in
theorem shapeAt_col {i : J} {x : (S.obj i).Carrier} {t : Tuple S.I} {b : S.B}
    (h : S.shapeAt i x = .col t b ∅) :
    ∃ r c v, x = .col r c v ∧ Tuples.map (S.index i) r = t ∧ S.base i c = b := by
  cases x <;> simp only [shapeAt] at h
  all_goals try contradiction
  case col r c v =>
    obtain ⟨ht, hb, _⟩ := Point.col.inj h
    exact ⟨r, c, v, rfl, ht, hb⟩

omit [Nonempty J] in
theorem rowDiff_exists {x y : S.X} {t : Tuple S.I} {n : ℕ}
    (hx : S.shape x = .row t n ∅) (hy : S.shape y = .row t n ∅) :
    ∃ s, S.rowDiff x y = some s := by
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    obtain ⟨r, s, rfl, hr⟩ := S.shapeAt_row (i := i) (x := x) hx
    obtain ⟨r', q, rfl, hr'⟩ := S.shapeAt_row (i := i) (x := y) hy
    have he : r = r' := Tuples.map_injective (S.index i) (hr.trans hr'.symm)
    subst r'
    exact ⟨_, S.rowDiff_refl_at i r n s q⟩

omit [Nonempty J] in
theorem colDiff_exists {x y : S.X} {t : Tuple S.I} {b : S.B}
    (hx : S.shape x = .col t b ∅) (hy : S.shape y = .col t b ∅) :
    ∃ v, S.colDiff x y = some v := by
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    obtain ⟨r, c, v, rfl, hr, hc⟩ := S.shapeAt_col (i := i) (x := x) hx
    obtain ⟨r', c', w, rfl, hr', hc'⟩ := S.shapeAt_col (i := i) (x := y) hy
    have he : r = r' := Tuples.map_injective (S.index i) (hr.trans hr'.symm)
    have he' : c = c' := (S.base i).injective (hc.trans hc'.symm)
    subst r'; subst c'
    exact ⟨_, S.colDiff_refl_at i r c v w⟩

omit [Nonempty J] in
@[simp] theorem base_lt (i : J) (a b : (S.obj i).B) :
    S.base i a < S.base i b ↔ a < b := by
  change (S.le (S.base i a) (S.base i b) ∧ ¬ S.le (S.base i b) (S.base i a)) ↔ _
  rw [le_base, le_base, lt_iff_le_not_ge]

instance dense : DenselyOrdered S.B where
  dense := by
    intro a b
    induction a, b using DirectLimit.induction₂ S.baseMap with
    | ih i a b =>
      intro h
      have hab : a < b := (S.base_lt i a b).1 h
      obtain ⟨c, hac, hcb⟩ := exists_between hab
      exact ⟨S.base i c, (S.base_lt i a c).2 hac, (S.base_lt i c b).2 hcb⟩

instance noMin : NoMinOrder S.B where
  exists_lt := by
    intro a
    induction a using DirectLimit.induction S.baseMap with
    | ih i a =>
      obtain ⟨b, hb⟩ := exists_lt a
      exact ⟨S.base i b, (S.base_lt i b a).2 hb⟩

instance noMax : NoMaxOrder S.B where
  exists_gt := by
    intro a
    induction a using DirectLimit.induction S.baseMap with
    | ih i a =>
      obtain ⟨b, hb⟩ := exists_gt a
      exact ⟨S.base i b, (S.base_lt i a b).2 hb⟩

theorem rowOrigin_exists (t : Tuple S.I) (n : ℕ) :
    ∃ x, S.shape x = .row t n ∅ := by
  obtain ⟨i, _, r, hr⟩ := S.tuple_exists t (Classical.arbitrary J)
  exact ⟨S.point i (.row r n ∅), congrArg (fun t => Point.row t n ∅) hr⟩

def rowOrigin (t : Tuple S.I) (n : ℕ) : S.X := (S.rowOrigin_exists t n).choose

@[simp] theorem rowOrigin_shape (t : Tuple S.I) (n : ℕ) :
    S.shape (S.rowOrigin t n) = .row t n ∅ := (S.rowOrigin_exists t n).choose_spec

theorem colOrigin_exists (t : Tuple S.I) (b : S.B) :
    ∃ x, S.shape x = .col t b ∅ := by
  induction b using DirectLimit.induction S.baseMap with
  | ih i b =>
    obtain ⟨j, hij, r, hr⟩ := S.tuple_exists t i
    refine ⟨S.point j (.col r ((S.map i j hij).base b) ∅), ?_⟩
    change Point.col (Tuples.map (S.index j) r) (S.base j ((S.map i j hij).base b)) ∅ = _
    rw [hr, S.base_map]
    rfl

def colOrigin (t : Tuple S.I) (b : S.B) : S.X := (S.colOrigin_exists t b).choose

@[simp] theorem colOrigin_shape (t : Tuple S.I) (b : S.B) :
    S.shape (S.colOrigin t b) = .col t b ∅ := (S.colOrigin_exists t b).choose_spec

theorem row_translate_exists {o : S.X} {t : Tuple S.I} {n : ℕ}
    (ho : S.shape o = .row t n ∅) (s : Finset S.B) :
    ∃ x, S.shape x = .row t n ∅ ∧ S.rowDiff o x = some s := by
  induction o using DirectLimit.induction S.pointMap with
  | ih i o =>
    obtain ⟨r, a, rfl, hr⟩ := S.shapeAt_row (i := i) (x := o) ho
    obtain ⟨j, hij, q, hq⟩ := S.finset_exists s i
    let f := S.map i j hij
    let r' := Tuples.map f.index r
    let a' := f.rowShift r n ∆ a.map f.base.toEmbedding
    refine ⟨S.point j (.row r' n (a' ∆ q)), ?_, ?_⟩
    · change Point.row (Tuples.map (S.index j) r') n ∅ = _
      rw [show Tuples.map (S.index j) r' = t from (S.tuple_map i j hij r).trans hr]
    · change S.rowDiff (S.point i (.row r n a)) (S.point j (.row r' n (a' ∆ q))) = _
      rw [← S.point_map i j hij (.row r n a)]
      change S.rowDiff (S.point j (.row r' n a')) (S.point j (.row r' n (a' ∆ q))) = _
      rw [S.rowDiff_refl_at, symmDiff_symmDiff_cancel_left, hq]

omit [Nonempty J] in
theorem col_translate_exists {o : S.X} {t : Tuple S.I} {b : S.B}
    (ho : S.shape o = .col t b ∅) (v : Finset ℕ) :
    ∃ x, S.shape x = .col t b ∅ ∧ S.colDiff o x = some v := by
  induction o using DirectLimit.induction S.pointMap with
  | ih i o =>
    obtain ⟨r, c, w, rfl, hr, hc⟩ := S.shapeAt_col (i := i) (x := o) ho
    refine ⟨S.point i (.col r c (w ∆ v)), ?_, ?_⟩
    · change Point.col (Tuples.map (S.index i) r) (S.base i c) ∅ = _
      rw [hr, hc]
    · change S.colDiff (S.point i (.col r c w)) (S.point i (.col r c (w ∆ v))) = _
      rw [S.colDiff_refl_at, symmDiff_symmDiff_cancel_left]

def rowPoint (t : Tuple S.I) (n : ℕ) (s : Finset S.B) : S.X :=
  (S.row_translate_exists (S.rowOrigin_shape t n) s).choose

def colPoint (t : Tuple S.I) (b : S.B) (v : Finset ℕ) : S.X :=
  (S.col_translate_exists (S.colOrigin_shape t b) v).choose

@[simp] theorem rowPoint_shape (t : Tuple S.I) (n : ℕ) (s : Finset S.B) :
    S.shape (S.rowPoint t n s) = .row t n ∅ :=
  (S.row_translate_exists (S.rowOrigin_shape t n) s).choose_spec.1

@[simp] theorem rowPoint_diff (t : Tuple S.I) (n : ℕ) (s : Finset S.B) :
    S.rowDiff (S.rowOrigin t n) (S.rowPoint t n s) = some s :=
  (S.row_translate_exists (S.rowOrigin_shape t n) s).choose_spec.2

@[simp] theorem colPoint_shape (t : Tuple S.I) (b : S.B) (v : Finset ℕ) :
    S.shape (S.colPoint t b v) = .col t b ∅ :=
  (S.col_translate_exists (S.colOrigin_shape t b) v).choose_spec.1

@[simp] theorem colPoint_diff (t : Tuple S.I) (b : S.B) (v : Finset ℕ) :
    S.colDiff (S.colOrigin t b) (S.colPoint t b v) = some v :=
  (S.col_translate_exists (S.colOrigin_shape t b) v).choose_spec.2

def bitAt (i : J) : (S.obj i).Carrier → (S.obj i).Carrier → Bool
  | .row t n s, .col r b v => if t = r then Matrix.bit ((S.obj i).bits t) n s b v else false
  | _, _ => false

omit [IsDirectedOrder J] [Nonempty J] in
theorem bitAt_map (i j : J) (h : i ≤ j) (x y : (S.obj i).Carrier) :
    S.bitAt j ((S.map i j h).onPoint x) ((S.map i j h).onPoint y) = S.bitAt i x y := by
  cases x <;> cases y <;> simp only [Map.onPoint, bitAt]
  case row.col t n s r b v =>
    by_cases ht : t = r
    · subst r
      simp only [↓reduceIte]
      exact (S.map i j h).bit_all t n s b v
    · simp only [Tuples.map_eq_iff, ht, ↓reduceIte]

def bit : S.X → S.X → Bool := DirectLimit.lift₂ S.pointMap S.pointMap S.bitAt
  (fun i j h x y => (S.bitAt_map i j h x y).symm)

omit [Nonempty J] in
@[simp] theorem bit_point (i : J) (x y : (S.obj i).Carrier) :
    S.bit (S.point i x) (S.point i y) = S.bitAt i x y := by
  exact DirectLimit.lift₂_def S.pointMap S.pointMap S.bitAt _ i x y

omit [Nonempty J] in
theorem bit_row_change {o x c : S.X} {t : Tuple S.I} {n : ℕ} {b : S.B} {s : Finset S.B}
    (ho : S.shape o = .row t n ∅) (hx : S.shape x = .row t n ∅)
    (hc : S.shape c = .col t b ∅) (hd : S.rowDiff o x = some s) :
    S.bit x c = (S.bit o c ^^ decide (b ∈ s)) := by
  induction o, x, c using DirectLimit.induction₃ S.pointMap with
  | ih i o x c =>
    obtain ⟨r, a, rfl, hr⟩ := S.shapeAt_row (i := i) (x := o) ho
    obtain ⟨r', q, rfl, hr'⟩ := S.shapeAt_row (i := i) (x := x) hx
    obtain ⟨r'', d, v, rfl, hr'', hb⟩ := S.shapeAt_col (i := i) (x := c) hc
    have h1 := Tuples.map_injective (S.index i) (hr'.trans hr.symm)
    have h2 := Tuples.map_injective (S.index i) (hr''.trans hr.symm)
    subst r'; subst r''
    change S.rowDiff (S.point i (.row r n a)) (S.point i (.row r n q)) = some s at hd
    rw [S.rowDiff_refl_at] at hd
    have hs := Option.some.inj hd
    subst s; subst b
    change S.bit (S.point i (.row r n q)) (S.point i (.col r d v)) =
      (S.bit (S.point i (.row r n a)) (S.point i (.col r d v)) ^^ _)
    simp only [bit_point, bitAt, ↓reduceIte, Matrix.bit, FiniteSupports.bit_symmDiff,
      Finset.mem_map, (S.base i).injective.eq_iff, exists_eq_right]
    generalize (S.obj i).bits r n d = z
    generalize decide (d ∈ a) = p
    generalize decide (d ∈ q) = q'
    generalize decide (n ∈ v) = w
    cases z <;> cases p <;> cases q' <;> cases w <;> rfl

omit [Nonempty J] in
theorem bit_col_change {r o x : S.X} {t : Tuple S.I} {n : ℕ} {b : S.B} {v : Finset ℕ}
    (hr : S.shape r = .row t n ∅) (ho : S.shape o = .col t b ∅)
    (hx : S.shape x = .col t b ∅) (hd : S.colDiff o x = some v) :
    S.bit r x = (S.bit r o ^^ decide (n ∈ v)) := by
  induction r, o, x using DirectLimit.induction₃ S.pointMap with
  | ih i r o x =>
    obtain ⟨t', a, rfl, ht⟩ := S.shapeAt_row (i := i) (x := r) hr
    obtain ⟨t'', c, q, rfl, ht', hb⟩ := S.shapeAt_col (i := i) (x := o) ho
    obtain ⟨t''', d, w, rfl, ht'', hb'⟩ := S.shapeAt_col (i := i) (x := x) hx
    have h1 := Tuples.map_injective (S.index i) (ht'.trans ht.symm)
    have h2 := Tuples.map_injective (S.index i) (ht''.trans ht.symm)
    have h3 := (S.base i).injective (hb'.trans hb.symm)
    subst t''; subst t'''; subst d
    change S.colDiff (S.point i (.col t' c q)) (S.point i (.col t' c w)) = some v at hd
    rw [S.colDiff_refl_at] at hd
    have hv := Option.some.inj hd
    subst v
    change S.bit (S.point i (.row t' n a)) (S.point i (.col t' c w)) =
      (S.bit (S.point i (.row t' n a)) (S.point i (.col t' c q)) ^^ _)
    simp only [bit_point, bitAt, ↓reduceIte, Matrix.bit, FiniteSupports.bit_symmDiff]
    generalize (S.obj i).bits t' n c = z
    generalize decide (c ∈ a) = p
    generalize decide (n ∈ q) = q'
    generalize decide (n ∈ w) = w'
    cases z <;> cases p <;> cases q' <;> cases w' <;> rfl

variable (hconv : ∀ i j (h : i ≤ j), Set.OrdConnected (Set.range (S.map i j h).base))

include hconv in
omit [Nonempty J] in
theorem base_convex (i : J) : Set.OrdConnected (Set.range (S.base i)) := by
  constructor
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ c hc
  induction c using DirectLimit.induction S.baseMap with
  | ih j c =>
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have ha := S.base_map i k hik a
    have hb := S.base_map i k hik b
    have hcc := S.base_map j k hjk c
    change S.base i a ≤ S.base j c ∧ S.base j c ≤ S.base i b at hc
    rw [← ha, ← hb, ← hcc] at hc
    have h : (S.map j k hjk).base c ∈
        Set.Icc ((S.map i k hik).base a) ((S.map i k hik).base b) := by
      exact ⟨(S.le_base k _ _).1 hc.1, (S.le_base k _ _).1 hc.2⟩
    obtain ⟨d, hd⟩ := (hconv i k hik).out ⟨a, rfl⟩ ⟨b, rfl⟩ h
    refine ⟨d, ?_⟩
    change S.base i d = S.base j c
    rw [← S.base_map i k hik d, hd, S.base_map]

omit [Nonempty J] in
include hconv in
theorem locallyCountable (a b : S.B) : (Set.Icc a b).Countable := by
  induction a, b using DirectLimit.induction₂ S.baseMap with
  | ih i a b =>
    have h : Set.Icc (S.base i a) (S.base i b) ⊆
        S.base i '' Set.Icc a b := by
      intro c hc
      obtain ⟨d, rfl⟩ := (S.base_convex hconv i).out ⟨a, rfl⟩ ⟨b, rfl⟩ hc
      exact ⟨d, ⟨(S.le_base i a d).1 hc.1, (S.le_base i d b).1 hc.2⟩, rfl⟩
    exact (((S.obj i).locallyCountable a b).image (S.base i)).mono h

def limitData : Arrays.Data.{u} where
  I := S.I
  B := S.B
  indexNonempty := inferInstance
  baseNonempty := inferInstance
  order := S.order
  dense := S.dense
  noMin := S.noMin
  noMax := S.noMax
  locallyCountable := S.locallyCountable hconv
  bits t n b := S.bit (S.rowOrigin t n) (S.colOrigin t b)

def rowShift (i : J) (t : Tuple (S.obj i).I) (n : ℕ) : Finset S.B :=
  (S.rowDiff_exists (S.rowOrigin_shape (Tuples.map (S.index i) t) n)
    (show S.shape (S.point i (.row t n ∅)) = .row (Tuples.map (S.index i) t) n ∅ from rfl)).choose

def colShift (i : J) (t : Tuple (S.obj i).I) (b : (S.obj i).B) : Finset ℕ :=
  (S.colDiff_exists (S.colOrigin_shape (Tuples.map (S.index i) t) (S.base i b))
    (show S.shape (S.point i (.col t b ∅)) =
      .col (Tuples.map (S.index i) t) (S.base i b) ∅ from rfl)).choose

@[simp] theorem rowShift_spec (i : J) (t : Tuple (S.obj i).I) (n : ℕ) :
    S.rowDiff (S.rowOrigin (Tuples.map (S.index i) t) n) (S.point i (.row t n ∅)) =
      some (S.rowShift i t n) :=
  (S.rowDiff_exists (S.rowOrigin_shape (Tuples.map (S.index i) t) n)
    (show S.shape (S.point i (.row t n ∅)) = .row (Tuples.map (S.index i) t) n ∅ from rfl)).choose_spec

@[simp] theorem colShift_spec (i : J) (t : Tuple (S.obj i).I) (b : (S.obj i).B) :
    S.colDiff (S.colOrigin (Tuples.map (S.index i) t) (S.base i b)) (S.point i (.col t b ∅)) =
      some (S.colShift i t b) :=
  (S.colDiff_exists (S.colOrigin_shape (Tuples.map (S.index i) t) (S.base i b))
    (show S.shape (S.point i (.col t b ∅)) =
      .col (Tuples.map (S.index i) t) (S.base i b) ∅ from rfl)).choose_spec

def toLimit (i : J) : Map (S.obj i) (S.limitData hconv) where
  index := S.index i
  base := S.baseOrder i
  rowShift := S.rowShift i
  colShift := S.colShift i
  bit_agrees t n b := by
    have hr := S.bit_row_change (S.rowOrigin_shape (Tuples.map (S.index i) t) n)
      (show S.shape (S.point i (.row t n ∅)) = _ from rfl)
      (show S.shape (S.point i (.col t b ∅)) = _ from rfl) (S.rowShift_spec i t n)
    have hc := S.bit_col_change (S.rowOrigin_shape (Tuples.map (S.index i) t) n)
      (S.colOrigin_shape (Tuples.map (S.index i) t) (S.base i b))
      (show S.shape (S.point i (.col t b ∅)) = _ from rfl) (S.colShift_spec i t b)
    rw [hc] at hr
    simp only [bit_point, bitAt, ↓reduceIte, Matrix.bit, Finset.notMem_empty,
      decide_false, Bool.xor_false] at hr
    change (S.bit (S.rowOrigin (Tuples.map (S.index i) t) n)
      (S.colOrigin (Tuples.map (S.index i) t) (S.base i b)) ^^
      decide (S.base i b ∈ S.rowShift i t n) ^^ decide (n ∈ S.colShift i t b)) = _
    rw [Bool.xor_right_comm]
    exact hr.symm

theorem rowShift_comp (i j : J) (h : i ≤ j) (t : Tuple (S.obj i).I) (n : ℕ) :
    S.rowShift j (Tuples.map (S.map i j h).index t) n ∆
      ((S.map i j h).rowShift t n).map (S.base j) = S.rowShift i t n := by
  let f := S.map i j h
  have hd := S.rowDiff_refl_at j (Tuples.map f.index t) n ∅ (f.rowShift t n)
  simp only [← Finset.bot_eq_empty, bot_symmDiff] at hd
  have he := S.rowDiff_trans (S.rowShift_spec j (Tuples.map f.index t) n) hd
  have hp : S.point j (.row (Tuples.map f.index t) n (f.rowShift t n)) =
      S.point i (.row t n ∅) := by
    have hp := S.point_map i j h (.row t n ∅)
    simp only [Map.onPoint, Finset.map_empty] at hp
    simpa only [f, ← Finset.bot_eq_empty, symmDiff_bot] using hp
  rw [hp, show Tuples.map (S.index j) (Tuples.map f.index t) = Tuples.map (S.index i) t from
    S.tuple_map i j h t, S.rowShift_spec] at he
  exact (Option.some.inj he).symm

theorem colShift_comp (i j : J) (h : i ≤ j) (t : Tuple (S.obj i).I) (b : (S.obj i).B) :
    S.colShift j (Tuples.map (S.map i j h).index t) ((S.map i j h).base b) ∆
      (S.map i j h).colShift t b = S.colShift i t b := by
  let f := S.map i j h
  have hd := S.colDiff_refl_at j (Tuples.map f.index t) (f.base b) ∅ (f.colShift t b)
  simp only [← Finset.bot_eq_empty, bot_symmDiff] at hd
  have he := S.colDiff_trans (S.colShift_spec j (Tuples.map f.index t) (f.base b)) hd
  have hp : S.point j (.col (Tuples.map f.index t) (f.base b) (f.colShift t b)) =
      S.point i (.col t b ∅) := by
    have hp := S.point_map i j h (.col t b ∅)
    simp only [Map.onPoint] at hp
    simpa only [f, ← Finset.bot_eq_empty, symmDiff_bot] using hp
  rw [hp, show Tuples.map (S.index j) (Tuples.map f.index t) = Tuples.map (S.index i) t from
    S.tuple_map i j h t, show S.base j (f.base b) = S.base i b from S.base_map i j h b,
    S.colShift_spec] at he
  exact (Option.some.inj he).symm

theorem toLimit_comp (i j : J) (h : i ≤ j) :
    (S.toLimit hconv j).comp (S.map i j h) = S.toLimit hconv i := by
  apply Map.ext_onPoint
  intro x
  rw [Map.comp_onPoint]
  cases x with
  | index a =>
    change Point.index (S.index j ((S.map i j h).index a)) = Point.index (S.index i a)
    rw [S.index_map]
  | base b =>
    change Point.base (S.base j ((S.map i j h).base b)) = Point.base (S.base i b)
    rw [S.base_map]
  | group s =>
    change Point.group ((s.map (S.map i j h).base.toEmbedding).map (S.base j)) =
      Point.group (s.map (S.base i))
    rw [S.finset_map]
  | star v => rfl
  | row t n s =>
    change Point.row (Tuples.map (S.index j) (Tuples.map (S.map i j h).index t)) n
      (S.rowShift j (Tuples.map (S.map i j h).index t) n ∆
        ((S.map i j h).rowShift t n ∆ s.map (S.map i j h).base.toEmbedding).map (S.base j)) =
      Point.row (Tuples.map (S.index i) t) n (S.rowShift i t n ∆ s.map (S.base i))
    rw [S.tuple_map, FiniteSupports.map_symmDiff, ← symmDiff_assoc, S.rowShift_comp, S.finset_map]
  | col t b v =>
    change Point.col (Tuples.map (S.index j) (Tuples.map (S.map i j h).index t))
      (S.base j ((S.map i j h).base b))
      (S.colShift j (Tuples.map (S.map i j h).index t) ((S.map i j h).base b) ∆
        ((S.map i j h).colShift t b ∆ v)) =
      Point.col (Tuples.map (S.index i) t) (S.base i b) (S.colShift i t b ∆ v)
    rw [S.tuple_map, S.base_map, ← symmDiff_assoc, S.colShift_comp]

theorem toLimit_covers (x : (S.limitData hconv).Carrier) :
    ∃ i y, (S.toLimit hconv i).onPoint y = x := by
  change Point S.I S.B at x
  cases x with
  | index a =>
    induction a using DirectLimit.induction S.indexMap with
    | ih i a => exact ⟨i, .index a, rfl⟩
  | base b =>
    induction b using DirectLimit.induction S.baseMap with
    | ih i b => exact ⟨i, .base b, rfl⟩
  | group s =>
    obtain ⟨i, _, r, hr⟩ := S.finset_exists s (Classical.arbitrary J)
    exact ⟨i, .group r, congrArg Point.group hr⟩
  | star v => exact ⟨Classical.arbitrary J, .star v, rfl⟩
  | row t n s =>
    obtain ⟨⟨i, x⟩, hx⟩ := Quotient.exists_rep (S.rowPoint t n s)
    change S.point i x = S.rowPoint t n s at hx
    have hshape : S.shapeAt i x = .row t n ∅ := by rw [← S.shape_point, hx, S.rowPoint_shape]
    obtain ⟨r, a, rfl, hr⟩ := S.shapeAt_row hshape
    have hd := S.rowDiff_trans (S.rowShift_spec i r n) (S.rowDiff_refl_at i r n ∅ a)
    simp only [← Finset.bot_eq_empty, bot_symmDiff] at hd
    rw [hr, hx, S.rowPoint_diff] at hd
    refine ⟨i, .row r n a, ?_⟩
    change Point.row (Tuples.map (S.index i) r) n
      (S.rowShift i r n ∆ a.map (S.base i)) = .row t n s
    rw [hr, ← Option.some.inj hd]
  | col t b v =>
    obtain ⟨⟨i, x⟩, hx⟩ := Quotient.exists_rep (S.colPoint t b v)
    change S.point i x = S.colPoint t b v at hx
    have hshape : S.shapeAt i x = .col t b ∅ := by rw [← S.shape_point, hx, S.colPoint_shape]
    obtain ⟨r, c, a, rfl, hr, hc⟩ := S.shapeAt_col hshape
    have hd := S.colDiff_trans (S.colShift_spec i r c) (S.colDiff_refl_at i r c ∅ a)
    simp only [← Finset.bot_eq_empty, bot_symmDiff] at hd
    rw [hr, hc, hx, S.colPoint_diff] at hd
    refine ⟨i, .col r c a, ?_⟩
    change Point.col (Tuples.map (S.index i) r) (S.base i c) (S.colShift i r c ∆ a) = .col t b v
    rw [hr, hc, ← Option.some.inj hd]

def underlying : S.X → (S.limitData hconv).Carrier :=
  DirectLimit.lift S.pointMap (fun i => (S.toLimit hconv i).onPoint) (by
    intro i j h x
    simpa only [pointMap, Map.toEmbedding, Function.Embedding.coeFn_mk, Map.comp_onPoint] using
      (congrArg (fun f : Map _ _ => f.onPoint x) (S.toLimit_comp hconv i j h)).symm)

@[simp] theorem underlying_point (i : J) (x : (S.obj i).Carrier) :
    S.underlying hconv (S.point i x) = (S.toLimit hconv i).onPoint x := rfl

theorem underlying_bijective : Function.Bijective (S.underlying hconv) := by
  constructor
  · intro x y
    induction x, y using DirectLimit.induction₂ S.pointMap with
    | ih i x y =>
      intro h
      exact congrArg (S.point i) ((S.toLimit hconv i).injective h)
  · intro x
    obtain ⟨i, y, hy⟩ := S.toLimit_covers hconv x
    exact ⟨S.point i y, hy⟩

def equivalence : S.X ≃ (S.limitData hconv).Carrier :=
  Equiv.ofBijective (S.underlying hconv) (S.underlying_bijective hconv)

@[simp] theorem equivalence_point (i : J) (x : (S.obj i).Carrier) :
    S.equivalence hconv (S.point i x) = (S.toLimit hconv i).onPoint x := rfl

@[simp] theorem equivalence_symm_stage (i : J) (x : (S.obj i).Carrier) :
    (S.equivalence hconv).symm ((S.toLimit hconv i).onPoint x) = S.point i x :=
  (S.equivalence hconv).symm_apply_apply (S.point i x)

theorem common_points {A : Type v} [Finite A] (x : A → (S.limitData hconv).Carrier) (i : J) :
    ∃ j, i ≤ j ∧ ∃ y : A → (S.obj j).Carrier, ∀ a, (S.toLimit hconv j).onPoint (y a) = x a := by
  obtain ⟨j, hij, y, hy⟩ := LimitTools.common S.pointMap
    (fun a b h => (S.map a b h).injective) (fun a => (S.equivalence hconv).symm (x a)) i
  refine ⟨j, hij, y, fun a => ?_⟩
  exact (congrArg (S.equivalence hconv) (hy a)).trans ((S.equivalence hconv).apply_symm_apply (x a))

variable {hCH : CH.{u}}

theorem toLimit_strong
    (hstrong : ∀ i j h, (S.map i j h).Strong hCH) (i : J) :
    (S.toLimit hconv i).Strong hCH := by
  constructor
  · exact S.base_convex hconv i
  · intro t b hb
    induction b using DirectLimit.induction S.baseMap with
    | ih j b =>
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      let c := (S.map j k hjk).base b
      have hc : c ∉ Set.range (S.map i k hik).base := by
        rintro ⟨a, ha⟩
        apply hb
        refine ⟨a, ?_⟩
        change S.base i a = S.base j b
        rw [← S.base_map i k hik a, ha, S.base_map]
      have ht := (hstrong i k hik).outside t c hc
      have he : ∀ r : Tuple (S.obj i).I,
          (S.toLimit hconv i).colors r (S.base j b) = (S.map i k hik).colors r c := by
        intro r
        rw [← S.toLimit_comp hconv i k hik, ← S.base_map j k hjk b]
        exact Map.comp_colors_base _ _ r c
      change Tests.Test hCH (fun r => (S.toLimit hconv i).colors r (S.base j b)) t
      simpa only [he] using ht

theorem limit_object (hobj : ∀ i, (S.obj i).IsObject hCH)
    (hstrong : ∀ i j h, (S.map i j h).Strong hCH) :
    (S.limitData hconv).IsObject hCH := by
  intro t
  obtain ⟨i, _, r, hr⟩ := S.tuple_exists t (Classical.arbitrary J)
  let f := S.toLimit hconv i
  have hf : f.Strong hCH := S.toLimit_strong hconv hstrong i
  have hbad := ((hobj i r).image f.base).union (f.exceptions_countable r)
  apply hbad.mono
  intro b hb
  by_cases hex : b ∈ f.exceptions r
  · exact Or.inr hex
  · left
    have ht : ¬ Tests.Test hCH (fun s => f.colors s b) r := by
      intro h
      apply hb
      have he := (f.test_away hCH r b hex).1 h
      change Tests.Test hCH (fun s => (S.limitData hconv).colors s b) (Tuples.map (S.index i) r) at he
      exact hr ▸ he
    by_cases hbase : b ∈ Set.range f.base
    · obtain ⟨c, rfl⟩ := hbase
      exact ⟨c, by simpa only [Set.mem_ofPred_eq, Map.colors_base] using ht, rfl⟩
    · exact (ht (hf.outside r b hbase)).elim

variable {N : Arrays.Data.{u}} (q : ∀ i, Map (S.obj i) N)
  (hq : ∀ i j h, (q j).comp (S.map i j h) = q i)

def liftPoint : S.X → N.Carrier := DirectLimit.lift S.pointMap (fun i => (q i).onPoint)
  (fun i j h x => by
    simpa only [pointMap, Map.toEmbedding, Function.Embedding.coeFn_mk, Map.comp_onPoint] using (congrArg (fun f : Map _ _ => f.onPoint x) (hq i j h)).symm)

omit [Nonempty J] in
@[simp] theorem liftPoint_point (i : J) (x : (S.obj i).Carrier) :
    S.liftPoint q hq (S.point i x) = (q i).onPoint x := rfl

omit [Nonempty J] in
theorem liftPoint_injective : Function.Injective (S.liftPoint q hq) := by
  intro x y
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    intro h
    exact congrArg (S.point i) ((q i).injective h)

def liftFunction (x : (S.limitData hconv).Carrier) : N.Carrier :=
  S.liftPoint q hq ((S.equivalence hconv).symm x)

@[simp] theorem liftFunction_stage (i : J) (x : (S.obj i).Carrier) :
    S.liftFunction hconv q hq ((S.toLimit hconv i).onPoint x) = (q i).onPoint x := by
  rw [liftFunction, equivalence_symm_stage, liftPoint_point]

theorem liftFunction_injective : Function.Injective (S.liftFunction hconv q hq) :=
  (S.liftPoint_injective q hq).comp (S.equivalence hconv).symm.injective

def liftRaw : RawEmbedding (S.limitData hconv) N where
  toEmbedding := ⟨S.liftFunction hconv q hq, S.liftFunction_injective hconv q hq⟩
  relates s xs := by
    obtain ⟨i, _, y, hy⟩ := S.common_points hconv (fun a : Fin xs.length => xs.get a) (Classical.arbitrary J)
    have he : (List.ofFn y).map (S.toLimit hconv i).onPoint = xs := by
      rw [List.map_ofFn]
      have hfun : (fun a => (S.toLimit hconv i).onPoint (y a)) = xs.get := funext hy
      change List.ofFn (fun a => (S.toLimit hconv i).onPoint (y a)) = xs
      rw [hfun, List.ofFn_get]
    rw [← he, List.map_map]
    have he' : (fun a => S.liftFunction hconv q hq ((S.toLimit hconv i).onPoint a)) =
        (q i).onPoint := funext (S.liftFunction_stage hconv q hq i)
    change N.rawRel s ((List.ofFn y).map (fun a => S.liftFunction hconv q hq
      ((S.toLimit hconv i).onPoint a))) ↔ _
    rw [he', (q i).rawRel, (S.toLimit hconv i).rawRel]
  supports s b := by
    obtain ⟨i, _, r, hr⟩ := S.finset_exists s (Classical.arbitrary J)
    subst s
    have hg : S.liftFunction hconv q hq (.group (r.map (S.base i))) =
        .group (r.map (q i).base.toEmbedding) := S.liftFunction_stage hconv q hq i (.group r)
    have hb (a : (S.obj i).B) : S.liftFunction hconv q hq (.base (S.base i a)) =
        .base ((q i).base a) := S.liftFunction_stage hconv q hq i (.base a)
    change N.rawRel .incidence [.base b, S.liftFunction hconv q hq (.group (r.map (S.base i)))] ↔ _
    rw [hg]
    change b ∈ r.map (q i).base.toEmbedding ↔
      ∃ c ∈ r.map (S.base i), S.liftFunction hconv q hq (.base c) = .base b
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, hab⟩
      refine ⟨S.base i a, ⟨a, ha, rfl⟩, ?_⟩
      rw [hb]
      exact congrArg Point.base hab
    · rintro ⟨c, ⟨a, ha, rfl⟩, he⟩
      exact ⟨a, ha, Point.base.inj ((hb a).symm.trans he)⟩

def liftMap : Map (S.limitData hconv) N := (S.liftRaw hconv q hq).toMap

@[simp] theorem liftMap_stage (i : J) (x : (S.obj i).Carrier) :
    (S.liftMap hconv q hq).onPoint ((S.toLimit hconv i).onPoint x) = (q i).onPoint x := by
  rw [liftMap, RawEmbedding.toMap_onPoint]
  exact S.liftFunction_stage hconv q hq i x

@[simp] theorem liftMap_comp (i : J) :
    (S.liftMap hconv q hq).comp (S.toLimit hconv i) = q i := by
  apply Map.ext_onPoint
  intro x
  rw [Map.comp_onPoint, S.liftMap_stage]

include hq in

theorem liftMap_strong (hs : ∀ i, (q i).Strong hCH) :
    (S.liftMap hconv q hq).Strong hCH := by
  let g := S.liftMap hconv q hq
  have hbase (i : J) (a : (S.obj i).B) : g.base (S.base i a) = (q i).base a :=
    congrArg (fun f : Map _ _ => f.base a) (S.liftMap_comp hconv q hq i)
  constructor
  · constructor
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩ b hb
    induction a, c using DirectLimit.induction₂ S.baseMap with
    | ih i a c =>
      change g.base (S.base i a) ≤ b ∧ b ≤ g.base (S.base i c) at hb
      rw [hbase, hbase] at hb
      obtain ⟨d, hd⟩ := (hs i).convex.out ⟨a, rfl⟩ ⟨c, rfl⟩ hb
      exact ⟨S.base i d, (hbase i d).trans hd⟩
  · intro t b hb
    obtain ⟨i, _, r, hr⟩ := S.tuple_exists t (Classical.arbitrary J)
    have hb' : b ∉ Set.range (q i).base := by
      rintro ⟨a, ha⟩
      exact hb ⟨S.base i a, (hbase i a).trans ha⟩
    have ht := (hs i).outside r b hb'
    have he (s : Tuple (S.obj i).I) :
        (q i).colors s b = g.colors (Tuples.map (S.index i) s) b := by
      rw [← S.liftMap_comp hconv q hq i]
      exact Map.comp_colors_outside g (S.toLimit hconv i) s b hb
    rw [← hr]
    change Tests.Test hCH (fun s : Tuple S.I => g.colors s b) (Tuples.map (S.index i) r)
    apply (Tests.map hCH (S.index i) (fun s : Tuple S.I => g.colors s b) r).2
    exact (Tests.congr hCH r (fun m e => he (Tuples.sub r e))).1 ht

end Data
end System
end Arrays

end CHObstruction

end

end OAI

-- ===== AEC.lean =====

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace RelModel

variable {L : ℕ → Type} {M N P : RelModel.{u} L}

def Iso.refl (M : RelModel.{u} L) : M.Iso M := ⟨Equiv.refl _, fun _ _ _ => Iff.rfl⟩

def Iso.symm (e : M.Iso N) : N.Iso M where
  toEquiv := e.toEquiv.symm
  map_rel n s a := by
    have h := e.map_rel n s (e.toEquiv.symm ∘ a)
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm

def Iso.trans (e : M.Iso N) (f : N.Iso P) : M.Iso P where
  toEquiv := e.toEquiv.trans f.toEquiv
  map_rel n s a := (e.map_rel n s a).trans (f.map_rel n s (e.toEquiv ∘ a))

theorem IsSubstructure.antisymm (h : M.IsSubstructure N) (k : N.IsSubstructure M) : M = N := by
  obtain ⟨A, r⟩ := M
  obtain ⟨B, s⟩ := N
  have he : A = B := ZFSet.ext (fun x => ⟨fun hx => h.subset hx, fun hx => k.subset hx⟩)
  subst B
  congr 1
  funext n c a
  exact propext (h.restrict n c a)

end RelModel

namespace Arrays

open Tuples

variable {M N : Data.{u}}

theorem Data.rawRel_length (s : Symbol) (xs : List M.Carrier) (h : M.rawRel s xs) :
    xs.length = s.arity := by
  unfold Data.rawRel at h
  split at h <;> simp_all [Symbol.arity]

def rawIsoOfTyped (e : M.Carrier ≃ N.Carrier)
    (he : ∀ n (s : Language n) a, N.rel n s (e ∘ a) ↔ M.rel n s a) : RawIso M N where
  toEquiv := e
  relates s xs := by
    by_cases hl : xs.length = s.arity
    · have h := he xs.length ⟨s, hl.symm⟩ xs.get
      simpa only [Data.rel, List.ofFn_get, ← List.map_ofFn] using h
    · constructor
      · intro h
        exact (hl ((List.length_map (f := e) (as := xs)).symm.trans (N.rawRel_length s _ h))).elim
      · intro h
        exact (hl (M.rawRel_length s xs h)).elim

structure Presentation (R : RelModel.{u} Language) where
  data : Data.{u}
  equiv : data.Carrier ≃ R.carrier
  relates : ∀ n (s : Language n) a, R.rel n s (equiv ∘ a) ↔ data.rel n s a

namespace Presentation

variable {R T V : RelModel.{u} Language} (P : Presentation R)

def transport (e : R.Iso T) : Presentation T where
  data := P.data
  equiv := P.equiv.trans e.toEquiv
  relates n s a := (e.map_rel n s (P.equiv ∘ a)).symm.trans (P.relates n s a)

theorem relates_symm (n : ℕ) (s : Language n) (a : Fin n → R.carrier) :
    R.rel n s a ↔ P.data.rel n s (P.equiv.symm ∘ a) := by
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using P.relates n s (P.equiv.symm ∘ a)

def comparison (Q : Presentation R) : RawIso P.data Q.data :=
  rawIsoOfTyped (P.equiv.trans Q.equiv.symm) (fun n s a => by
    have h := Q.relates_symm n s (P.equiv ∘ a)
    exact h.symm.trans (P.relates n s a))

@[simp] theorem comparison_onPoint (Q : Presentation R) (x : P.data.Carrier) :
    (P.comparison Q).toMap.onPoint x = Q.equiv.symm (P.equiv x) :=
  (P.comparison Q).toMap_onPoint x

theorem comparison_strong (Q : Presentation R) (hCH : CH.{u}) :
    (P.comparison Q).toMap.Strong hCH :=
  (P.comparison Q).toMap.strong_of_surjective hCH (P.comparison Q).base_surjective

theorem object_iff (Q : Presentation R) (hCH : CH.{u}) :
    P.data.IsObject hCH ↔ Q.data.IsObject hCH := by
  constructor
  · intro h
    exact (P.comparison Q).toMap.object_of_surjective hCH
      (P.comparison Q).index_surjective (P.comparison Q).base_surjective h
  · intro h
    exact (Q.comparison P).toMap.object_of_surjective hCH
      (Q.comparison P).index_surjective (Q.comparison P).base_surjective h

def isoOfMap (Q : Presentation T) (f : Map P.data Q.data)
    (hf : Function.Surjective f.onPoint) : R.Iso T where
  toEquiv := P.equiv.symm.trans ((Equiv.ofBijective f.onPoint ⟨f.injective, hf⟩).trans Q.equiv)
  map_rel n s a := by
    have h := (P.relates_symm n s a).trans (f.rel n s (P.equiv.symm ∘ a)).symm
    exact h.trans (Q.relates n s (f.onPoint ∘ P.equiv.symm ∘ a)).symm

def Inclusion (Q : Presentation T) (f : Map P.data Q.data) : Prop :=
  ∀ x, (Q.equiv (f.onPoint x)).val = (P.equiv x).val

theorem inclusion_unique {Q : Presentation T} {f g : Map P.data Q.data}
    (hf : P.Inclusion Q f) (hg : P.Inclusion Q g) : f = g := by
  apply Map.ext_onPoint
  intro x
  apply Q.equiv.injective
  apply Subtype.ext
  exact (hf x).trans (hg x).symm

theorem inclusion_refl : P.Inclusion P (Map.id P.data) := by
  intro x
  rw [Map.id_onPoint]

theorem Inclusion.comp {P : Presentation R} {Q : Presentation T} {O : Presentation V}
    {f : Map P.data Q.data} {g : Map Q.data O.data}
    (hg : Q.Inclusion O g) (hf : P.Inclusion Q f) : P.Inclusion O (g.comp f) := by
  intro x
  rw [Map.comp_onPoint]
  exact (hg (f.onPoint x)).trans (hf x)

theorem inclusion_comparison (Q : Presentation R) : P.Inclusion Q (P.comparison Q).toMap := by
  intro x
  rw [comparison_onPoint, Equiv.apply_symm_apply]

theorem Inclusion.substructure {Q : Presentation T} {f : Map P.data Q.data}
    (hf : P.Inclusion Q f) : R.IsSubstructure T := by
  have hsub : R.carrier ⊆ T.carrier := by
    intro x hx
    have he := hf (P.equiv.symm ⟨x, hx⟩)
    simp only [Equiv.apply_symm_apply] at he
    exact he ▸ (Q.equiv (f.onPoint (P.equiv.symm ⟨x, hx⟩))).property
  refine ⟨hsub, fun n s a => ?_⟩
  have he : (fun i => (⟨(a i).val, hsub (a i).property⟩ : T.carrier)) =
      Q.equiv ∘ f.onPoint ∘ P.equiv.symm ∘ a := by
    funext i
    apply Subtype.ext
    change (a i).val = (Q.equiv (f.onPoint (P.equiv.symm (a i)))).val
    simpa only [Equiv.apply_symm_apply] using (hf (P.equiv.symm (a i))).symm
  rw [he, Q.relates, f.rel, ← P.relates_symm]

end Presentation

variable (hCH : CH.{u})

def classData : ClassData.{u} Language where
  objects R := ∃ P : Presentation R, P.data.IsObject hCH
  strong R T := ∃ (P : Presentation R) (Q : Presentation T),
    P.data.IsObject hCH ∧ Q.data.IsObject hCH ∧
    ∃ f : Map P.data Q.data, f.Strong hCH ∧ P.Inclusion Q f

namespace AEC

variable {hCH : CH.{u}} {R T V : RelModel.{u} Language}

abbrev Object (R : RelModel.{u} Language) := (classData hCH).objects R
abbrev Strong (R T : RelModel.{u} Language) := (classData hCH).strong R T

theorem strong_objects (h : Strong (hCH := hCH) R T) : Object (hCH := hCH) R ∧ Object (hCH := hCH) T := by
  obtain ⟨P, Q, hp, hq, f, hf, he⟩ := h
  exact ⟨⟨P, hp⟩, ⟨Q, hq⟩⟩

theorem object_presentation (h : Object (hCH := hCH) R) (P : Presentation R) : P.data.IsObject hCH := by
  obtain ⟨Q, hq⟩ := h
  exact (Q.object_iff P hCH).1 hq

theorem strong_rebase (h : Strong (hCH := hCH) R T) (P : Presentation R) (Q : Presentation T) :
    ∃ f : Map P.data Q.data, f.Strong hCH ∧ P.Inclusion Q f := by
  obtain ⟨P', Q', hp, hq, f, hf, he⟩ := h
  refine ⟨(Q'.comparison Q).toMap.comp (f.comp (P.comparison P').toMap),
    (Q'.comparison_strong Q hCH).comp hCH (hf.comp hCH (P.comparison_strong P' hCH)), ?_⟩
  exact (Q'.inclusion_comparison Q).comp (he.comp (P.inclusion_comparison P'))

theorem strong_of {P : Presentation R} {Q : Presentation T}
    (hp : P.data.IsObject hCH) (hq : Q.data.IsObject hCH)
    (f : Map P.data Q.data) (hf : f.Strong hCH) (he : P.Inclusion Q f) : Strong (hCH := hCH) R T :=
  ⟨P, Q, hp, hq, f, hf, he⟩

theorem refl (h : Object (hCH := hCH) R) : Strong (hCH := hCH) R R := by
  obtain ⟨P, hp⟩ := h
  exact strong_of hp hp (Map.id P.data) (Map.id_strong hCH _) P.inclusion_refl

theorem substructure (h : Strong (hCH := hCH) R T) : R.IsSubstructure T := by
  obtain ⟨P, Q, hp, hq, f, hf, he⟩ := h
  exact he.substructure P

theorem antisymm (h : Strong (hCH := hCH) R T) (k : Strong (hCH := hCH) T R) : R = T :=
  (substructure h).antisymm (substructure k)

theorem trans (h : Strong (hCH := hCH) R T) (k : Strong (hCH := hCH) T V) : Strong (hCH := hCH) R V := by
  obtain ⟨P, Q, hp, hq, f, hf, he⟩ := h
  obtain ⟨O, ho⟩ := (strong_objects k).2
  obtain ⟨g, hg, he'⟩ := strong_rebase k Q O
  exact strong_of hp ho (g.comp f) (hg.comp hCH hf) (he'.comp he)

theorem iso_objects (h : Object (hCH := hCH) R) (e : R.Iso T) : Object (hCH := hCH) T := by
  obtain ⟨P, hp⟩ := h
  exact ⟨P.transport e, hp⟩

theorem iso_strong {R' T' : RelModel.{u} Language} (h : Strong (hCH := hCH) R T)
    (e : R.Iso R') (f : T.Iso T')
    (he : ∀ x : R.carrier, (e.toEquiv x).val =
      (f.toEquiv ⟨x.val, (substructure h).subset x.property⟩).val) :
    Strong (hCH := hCH) R' T' := by
  obtain ⟨P, Q, hp, hq, g, hg, hinc⟩ := h
  refine strong_of (P := P.transport e) (Q := Q.transport f) hp hq g hg ?_
  intro x
  change (f.toEquiv (Q.equiv (g.onPoint x))).val = (e.toEquiv (P.equiv x)).val
  rw [he]
  congr 2
  exact Subtype.ext (hinc x)

theorem coherence (hsub : R.IsSubstructure T) (h : Strong (hCH := hCH) R V)
    (k : Strong (hCH := hCH) T V) : Strong (hCH := hCH) R T := by
  obtain ⟨P, O, hp, ho, f, hf, he⟩ := h
  obtain ⟨Q, hq⟩ := (strong_objects k).1
  obtain ⟨g, hg, he'⟩ := strong_rebase k Q O
  have hr : ∀ x : P.data.Carrier, ∃ y, g.onPoint y = f.onPoint x := by
    intro x
    let y : T.carrier := ⟨(P.equiv x).val, hsub.subset (P.equiv x).property⟩
    refine ⟨Q.equiv.symm y, O.equiv.injective (Subtype.ext ?_)⟩
    rw [he', he, Equiv.apply_symm_apply]
  obtain ⟨l, hl⟩ := f.factor g hr
  refine strong_of hp hq l (hf.factor hCH hl) ?_
  intro x
  have hv := congrArg (fun m : Map P.data O.data => (O.equiv (m.onPoint x)).val) hl
  rw [Map.comp_onPoint] at hv
  rw [he', he] at hv
  exact hv

end AEC

namespace Coding

variable {X : Type u} {A : ZFSet.{u}}

theorem cardinal (e : X ≃ A) : #X = A.card := by
  apply Cardinal.lift_injective.{u+1}
  simpa only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_lift] using (Cardinal.lift_mk_eq'.2 ⟨e⟩)

def universeEquiv (X : Type u) : X ≃ Ordinal.toZFSet (#X).ord := Classical.choice (by
  apply Cardinal.lift_mk_eq'.1
  simp only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_lift, Ordinal.card_toZFSet, Cardinal.card_ord])

def rangeEquiv (f : X → ZFSet.{u}) (hf : Function.Injective f) : X ≃ ZFSet.range f :=
  Equiv.ofBijective (fun x => ⟨f x, ZFSet.mem_range.2 ⟨x, rfl⟩⟩) ⟨
    fun _ _ h => hf (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha⟩ := ZFSet.mem_range.1 hx
      exact ⟨a, Subtype.ext ha⟩⟩

def model (M : Data.{u}) (A : ZFSet.{u}) (e : M.Carrier ≃ A) : RelModel.{u} Language where
  carrier := A
  rel n s a := M.rel n s (e.symm ∘ a)

def presentation (M : Data.{u}) (A : ZFSet.{u}) (e : M.Carrier ≃ A) : Presentation (model M A e) where
  data := M
  equiv := e
  relates n s a := by
    change M.rel n s (fun i => e.symm (e (a i))) ↔ _
    simp only [Equiv.symm_apply_apply]

def coded (M : Data.{u}) : RelModel.{u} Language := model M _ (universeEquiv M.Carrier)

def codedPresentation (M : Data.{u}) : Presentation (coded M) :=
  presentation M _ (universeEquiv M.Carrier)

theorem coded_cardinal (M : Data.{u}) : (coded M).carrier.card = #M.Carrier :=
  (cardinal (universeEquiv M.Carrier)).symm

end Coding

namespace AEC

section

variable {hCH : CH.{u}} {R : RelModel.{u} Language}

theorem small (h : Object (hCH := hCH) R) (A : ZFSet.{u}) (hA : A ⊆ R.carrier) :
    ∃ T, Object (hCH := hCH) T ∧ Strong (hCH := hCH) T R ∧
      A ⊆ T.carrier ∧ T.carrier.card ≤ A.card + ℵ₀ := by
  obtain ⟨P, hp⟩ := h
  let S : Set P.data.Carrier := {x | (P.equiv x).val ∈ A}
  let e : S ≃ A := Equiv.ofBijective (fun x => ⟨(P.equiv x.val).val, x.property⟩) ⟨by
    intro a b hab
    apply Subtype.ext
    apply P.equiv.injective
    have hh : (P.equiv a.val).val = (P.equiv b.val).val := congrArg (fun z : A => z.val) hab
    exact Subtype.ext hh, by
    rintro ⟨a, ha⟩
    let x := P.equiv.symm ⟨a, hA ha⟩
    have hx : x ∈ S := by change (P.equiv x).val ∈ A; simpa only [x, Equiv.apply_symm_apply] using ha
    exact ⟨⟨x, hx⟩, Subtype.ext (by simp only [x, Equiv.apply_symm_apply])⟩⟩
  obtain ⟨M, f, hm, hf, hs, hc⟩ := P.data.small_subarray hCH hp S
  let z : M.Carrier → ZFSet.{u} := fun x => (P.equiv (f.onPoint x)).val
  have hz : Function.Injective z := Subtype.val_injective.comp (P.equiv.injective.comp f.injective)
  let eqv := Coding.rangeEquiv z hz
  let T := Coding.model M (ZFSet.range z) eqv
  let Q := Coding.presentation M (ZFSet.range z) eqv
  refine ⟨T, ⟨Q, hm⟩, strong_of (P := Q) (Q := P) hm hp f hf (fun x => rfl), ?_, ?_⟩
  · intro a ha
    have hx : P.equiv.symm ⟨a, hA ha⟩ ∈ S := by
      change (P.equiv (P.equiv.symm _)).val ∈ A
      simpa only [Equiv.apply_symm_apply] using ha
    obtain ⟨x, hx⟩ := hs hx
    exact ZFSet.mem_range.2 ⟨x, by change (P.equiv (f.onPoint x)).val = a; rw [hx]; simp⟩
  · change (ZFSet.range z).card ≤ A.card + ℵ₀
    rw [← Coding.cardinal eqv, ← Coding.cardinal e]
    exact hc

end

variable {hCH : CH.{u}}

theorem directed_union {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (F : J → RelModel.{u} Language) (ho : ∀ i, Object (hCH := hCH) (F i))
    (hs : ∀ i j, i ≤ j → Strong (hCH := hCH) (F i) (F j)) :
    ∃ U, Object (hCH := hCH) U ∧ RelModel.IsUnion F U ∧
      (∀ i, Strong (hCH := hCH) (F i) U) ∧
      (∀ N, Object (hCH := hCH) N → (∀ i, Strong (hCH := hCH) (F i) N) → Strong (hCH := hCH) U N) := by
  classical
  let P (i : J) : Presentation (F i) := (ho i).choose
  have hp (i : J) : (P i).data.IsObject hCH := (ho i).choose_spec
  let maps (i j : J) (h : i ≤ j) : Map (P i).data (P j).data :=
    (strong_rebase (hs i j h) (P i) (P j)).choose
  have hm (i j : J) (h : i ≤ j) : (maps i j h).Strong hCH :=
    (strong_rebase (hs i j h) (P i) (P j)).choose_spec.1
  have hi (i j : J) (h : i ≤ j) : (P i).Inclusion (P j) (maps i j h) :=
    (strong_rebase (hs i j h) (P i) (P j)).choose_spec.2
  let S : System.Data (J := J) := {
    obj := fun i => (P i).data
    map := maps
    map_id := fun i => (P i).inclusion_unique (hi i i le_rfl) (P i).inclusion_refl
    map_comp := fun i j k h h' => (P i).inclusion_unique ((hi j k h').comp (hi i j h)) (hi i k (h.trans h')) }
  have hconv : ∀ i j h, (Set.range (S.map i j h).base).OrdConnected := fun i j h => (hm i j h).convex
  let A : ZFSet.{u} := ZFSet.iUnion (fun i => (F i).carrier)
  let stage (i : J) (x : (S.obj i).Carrier) : A :=
    ⟨((P i).equiv x).val, ZFSet.mem_iUnion.2 ⟨i, ((P i).equiv x).property⟩⟩
  let val : S.X → A := DirectLimit.lift S.pointMap stage (by
    intro i j h x
    apply Subtype.ext
    exact (hi i j h x).symm)
  have hv (i : J) (x : (S.obj i).Carrier) : val (S.point i x) = stage i x := rfl
  have hinj : Function.Injective val := by
    intro x y
    induction x, y using DirectLimit.induction₂ S.pointMap with
    | ih i x y =>
      intro h
      apply congrArg (S.point i)
      apply (P i).equiv.injective
      apply Subtype.ext
      exact congrArg (fun z : A => z.val) h
  have hsurj : Function.Surjective val := by
    intro a
    obtain ⟨i, hai⟩ := ZFSet.mem_iUnion.1 a.property
    refine ⟨S.point i ((P i).equiv.symm ⟨a.val, hai⟩), ?_⟩
    rw [hv]
    apply Subtype.ext
    change ((P i).equiv ((P i).equiv.symm ⟨a.val, hai⟩)).val = a.val
    simp only [Equiv.apply_symm_apply]
  let e : (S.limitData hconv).Carrier ≃ A :=
    (S.equivalence hconv).symm.trans (Equiv.ofBijective val ⟨hinj, hsurj⟩)
  have he (i : J) (x : (S.obj i).Carrier) :
      e ((S.toLimit hconv i).onPoint x) = stage i x := by
    change val ((S.equivalence hconv).symm ((S.toLimit hconv i).onPoint x)) = _
    rw [S.equivalence_symm_stage, hv]
  let U := Coding.model (S.limitData hconv) A e
  let Q := Coding.presentation (S.limitData hconv) A e
  have hu : Q.data.IsObject hCH := S.limit_object hconv hp hm
  have hstage (i : J) : Strong (hCH := hCH) (F i) U :=
    strong_of (P := P i) (Q := Q) (hp i) hu (S.toLimit hconv i)
      (S.toLimit_strong hconv hm i) (fun x => congrArg Subtype.val (he i x))
  refine ⟨U, ⟨Q, hu⟩, ⟨fun i => substructure (hstage i), ?_⟩, hstage, ?_⟩
  · intro x
    exact ZFSet.mem_iUnion.1 x.property
  · intro N hn hc
    obtain ⟨O, ho'⟩ := hn
    let q (i : J) : Map (S.obj i) O.data := (strong_rebase (hc i) (P i) O).choose
    have hq_strong (i : J) : (q i).Strong hCH := (strong_rebase (hc i) (P i) O).choose_spec.1
    have hq_inc (i : J) : (P i).Inclusion O (q i) := (strong_rebase (hc i) (P i) O).choose_spec.2
    have hq (i j : J) (h : i ≤ j) : (q j).comp (S.map i j h) = q i :=
      (P i).inclusion_unique ((hq_inc j).comp (hi i j h)) (hq_inc i)
    let f := S.liftMap hconv q hq
    refine strong_of hu ho' f (S.liftMap_strong hconv q hq hq_strong) ?_
    intro x
    obtain ⟨i, y, rfl⟩ := S.toLimit_covers hconv x
    change (O.equiv ((S.liftMap hconv q hq).onPoint ((S.toLimit hconv i).onPoint y))).val =
      (e ((S.toLimit hconv i).onPoint y)).val
    rw [S.liftMap_stage, he]
    exact hq_inc i y

theorem lsBound : (classData hCH).LSBound ℵ₀ := by
  refine ⟨le_rfl, ?_, ?_⟩
  · simpa only [Cardinal.lift_le_aleph0] using (Cardinal.mk_le_aleph0 (α := Σ n, Language n))
  · exact fun R h A ha => small h A ha

theorem isAEC : (classData hCH).IsAEC where
  strong_objects := strong_objects
  refl := refl
  antisymm := antisymm
  trans := trans
  substructure := substructure
  iso_objects h e := iso_objects h e.some
  iso_strong := iso_strong
  coherence := coherence
  chain_union γ hγ F ho hs := by
    let : Nonempty γ.ToType := Ordinal.nonempty_toType_iff.2 hγ
    exact directed_union F ho hs
  downward := ⟨ℵ₀, lsBound⟩

theorem hasLSNumber : (classData hCH).HasLSNumber ℵ₀ :=
  ⟨lsBound, fun _ h => h.1⟩

end AEC
end Arrays

end CHObstruction

end

end OAI

-- ===== Main.lean =====

namespace OAI

/-!
# A CH obstruction to a prescribed categoricity threshold

Under CH, a countable relational language admits an abstract elementary class
with least Löwenheim–Skolem number `aleph0`, two nonisomorphic models of size
`beth (omega 2) = hanf aleph0`, and categoricity, including existence, at every
cardinal at least `tailThreshold`. Distinct base cardinalities separate the
endpoint models, while finite-support row and column translations establish
the included categoricity tail.
-/

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Arrays

open Tuples

variable (hCH : CH.{u})

namespace Existence

abbrev RationalBase := ULift.{u} ℚ

instance : DenselyOrdered RationalBase.{u} where
  dense a b h := by
    obtain ⟨c, hc, hd⟩ := exists_between (show a.down < b.down from h)
    exact ⟨⟨c⟩, hc, hd⟩

instance : NoMinOrder RationalBase.{u} where
  exists_lt a := by
    obtain ⟨b, hb⟩ := exists_lt a.down
    exact ⟨⟨b⟩, hb⟩

instance : NoMaxOrder RationalBase.{u} where
  exists_gt a := by
    obtain ⟨b, hb⟩ := exists_gt a.down
    exact ⟨⟨b⟩, hb⟩

def countableData (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) : Data.{u} where
  I := μ.ord.ToType
  B := RationalBase
  indexNonempty := by
    have : Infinite μ.ord.ToType := Cardinal.aleph0_le_mk_iff.1 (by simpa using hμ)
    infer_instance
  baseNonempty := inferInstance
  order := inferInstance
  dense := inferInstance
  noMin := inferInstance
  noMax := inferInstance
  locallyCountable _ _ := Set.to_countable _
  bits _ _ _ := false

theorem countableData_object (hCH : CH.{u}) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    (countableData μ hμ).IsObject hCH := by
  have : Countable (countableData μ hμ).B := by change Countable RationalBase; infer_instance
  exact Data.countable_object _ _

theorem countableData_index (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    #(countableData μ hμ).I = μ := by
  change #μ.ord.ToType = μ
  simp only [Cardinal.mk_toType, Cardinal.card_ord]

theorem countableData_cardinal (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    #(countableData μ hμ).Carrier = μ := by
  rw [Data.cardinal_eq, countableData_index]
  change max (max μ #RationalBase.{u}) ℵ₀ = μ
  rw [max_eq_left ((Cardinal.mk_le_aleph0 (α := RationalBase.{u})).trans hμ), max_eq_left hμ]

theorem models (hCH : CH.{u}) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    ∃ R, AEC.Object (hCH := hCH) R ∧ R.carrier.card = μ := by
  refine ⟨Coding.coded (countableData μ hμ),
    ⟨Coding.codedPresentation _, countableData_object hCH μ hμ⟩, ?_⟩
  rw [Coding.coded_cardinal, countableData_cardinal]

end Existence

namespace Categoricity

theorem aleph_one_lt : (ℵ_ 1 : Cardinal.{u}) < tailThreshold.{u} :=
  (Cardinal.cantor _).trans ThresholdArithmetic.palette_lt

theorem index_eq (M : Data.{u}) {μ : Cardinal.{u}} (hμ : tailThreshold.{u} ≤ μ)
    (hM : #M.Carrier = μ) : #M.I = μ := by
  have hi : #M.I ≤ μ := (Cardinal.mk_le_of_injective (fun _ _ h => Point.index.inj h)).trans_eq hM
  apply le_antisymm hi
  by_contra! hn
  have hb : #M.B < μ := M.base_bound.trans_lt (aleph_one_lt.trans_le hμ)
  have hz : ℵ₀ < μ := (Cardinal.aleph0_le_aleph 1).trans_lt (aleph_one_lt.trans_le hμ)
  have hc := max_lt (max_lt hn hb) hz
  rw [← M.cardinal_eq, hM] at hc
  exact hc.false

theorem countable (M : Data.{u}) (hCH : CH.{u}) (ho : M.IsObject hCH)
    {μ : Cardinal.{u}} (hμ : tailThreshold.{u} ≤ μ) (hM : #M.Carrier = μ) : Countable M.B := by
  by_contra hn
  have hh := M.uncountable_index_bound hCH ho hn
  rw [index_eq M hμ hM] at hh
  exact hh.not_ge hμ

theorem tail (hCH : CH.{u}) (μ : Cardinal.{u}) (hμ : tailThreshold.{u} ≤ μ) :
    (classData hCH).Categorical μ := by
  refine ⟨Existence.models hCH μ
    ((Cardinal.aleph0_le_aleph 1).trans (aleph_one_lt.le.trans hμ)), ?_⟩
  intro R T hr ht hc hd
  obtain ⟨P, hp⟩ := hr
  obtain ⟨Q, hq⟩ := ht
  have hpc : #P.data.Carrier = μ := (Coding.cardinal P.equiv).trans hc
  have hqc : #Q.data.Carrier = μ := (Coding.cardinal Q.equiv).trans hd
  have := countable P.data hCH hp hμ hpc
  have := countable Q.data hCH hq hμ hqc
  obtain ⟨f, hi, hb⟩ := countable_isomorphic
    ((index_eq P.data hμ hpc).trans (index_eq Q.data hμ hqc).symm)
  exact ⟨P.isoOfMap Q f (f.surjective hi hb)⟩

end Categoricity

namespace EndpointModels

open Diagrams
open Existence

abbrev Base := Tag.{u} ×ₗ RationalBase.{u}

instance tag_nonempty : Nonempty Tag.{u} := Ordinal.nonempty_toType_iff.2 (Ordinal.omega_pos 1).ne'

theorem tag_initial_countable (b : Tag.{u}) : (Set.Iic b).Countable := by
  have : Countable (Set.Iio b) := by
    apply Cardinal.mk_le_aleph0_iff.1
    apply Cardinal.lt_aleph_one_iff.1
    simpa only [Cardinal.mk_toType, Ordinal.card_omega] using
      (Cardinal.mk_Iio_lt b (by simp [Tag]))
  have h : Set.Iic b = insert b (Set.Iio b) := by
    ext x
    simp only [Set.mem_Iic, Set.mem_insert_iff, Set.mem_Iio, le_iff_eq_or_lt]
  rw [h]
  exact (Set.to_countable (Set.Iio b)).insert b

theorem locallyCountable (a b : Base.{u}) : (Set.Icc a b).Countable := by
  have := (tag_initial_countable (ofLex b).1).to_subtype
  let f : Set.Icc a b → Set.Iic (ofLex b).1 × RationalBase.{u} :=
    fun x => (⟨(ofLex x.val).1, Prod.Lex.monotone_fst _ _ x.property.2⟩, (ofLex x.val).2)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply ofLex.injective
    exact Prod.ext (congrArg (fun z : Set.Iic (ofLex b).1 × RationalBase.{u} => z.1.val) h)
      (congrArg (fun z : Set.Iic (ofLex b).1 × RationalBase.{u} => z.2) h)
  exact Set.countable_coe_iff.1 hf.countable

theorem base_cardinal : #Base.{u} = (ℵ_ 1 : Cardinal.{u}) := by
  rw [Cardinal.mk_congr (ofLex : Base.{u} ≃ _), Cardinal.mk_prod]
  simp [Tag, RationalBase]

def baseEquiv : Base.{u} ≃ Tag.{u} := Classical.choice (Cardinal.eq.1 (by
  rw [base_cardinal, Cardinal.mk_toType, Ordinal.card_omega]))

theorem endpoint_infinite : ℵ₀ ≤ endpoint.{u} := Cardinal.aleph0_le_beth _

theorem base_le_endpoint : (ℵ_ 1 : Cardinal.{u}) ≤ endpoint.{u} := by
  apply (Cardinal.aleph.monotone (by norm_num : (1 : Ordinal.{u}) ≤ 2)).trans
  change ℵ_ 2 ≤ beth (ω_ 2)
  rw [← Cardinal.ord_aleph]
  exact Cardinal.le_beth_ord _

def data (hCH : CH.{u}) : Data.{u} where
  I := EndpointDiagrams.D
  B := Base
  indexNonempty := by
    have : Infinite EndpointDiagrams.D.{u} := Cardinal.aleph0_le_mk_iff.1
      (EndpointDiagrams.cardinal.symm ▸ endpoint_infinite)
    infer_instance
  baseNonempty := inferInstance
  order := inferInstance
  dense := inferInstance
  noMin := inferInstance
  noMax := inferInstance
  locallyCountable := locallyCountable
  bits t n b := Colors.representative (EndpointDiagrams.colors hCH t (baseEquiv b)).down n

theorem data_colors (hCH : CH.{u}) (t : Tuples.Tuple EndpointDiagrams.D.{u}) (b : Base.{u}) :
    (data hCH).colors t b = EndpointDiagrams.colors hCH t (baseEquiv b) := by
  apply ULift.ext
  exact Colors.representative_color _

theorem object (hCH : CH.{u}) : (data hCH).IsObject hCH := by
  intro t
  have h := (EndpointDiagrams.countable_failures hCH t).preimage baseEquiv.injective
  apply h.mono
  intro b hb ht
  apply hb
  apply (Tests.congr hCH t (fun _ _ => data_colors hCH _ b)).mpr ht

theorem cardinal (hCH : CH.{u}) : #(data hCH).Carrier = endpoint.{u} := by
  rw [Data.cardinal_eq]
  change max (max #EndpointDiagrams.D.{u} #Base.{u}) ℵ₀ = endpoint.{u}
  rw [EndpointDiagrams.cardinal, base_cardinal, max_eq_left base_le_endpoint,
    max_eq_left endpoint_infinite]

theorem twoModels (hCH : CH.{u}) : (classData hCH).TwoModels endpoint.{u} := by
  let M := countableData endpoint endpoint_infinite
  let N := data hCH
  let P := Coding.codedPresentation M
  let Q := Coding.codedPresentation N
  refine ⟨Coding.coded M, Coding.coded N,
    ⟨P, countableData_object hCH endpoint endpoint_infinite⟩, ⟨Q, object hCH⟩, ?_, ?_, ?_⟩
  · rw [Coding.coded_cardinal]
    exact countableData_cardinal endpoint endpoint_infinite
  · rw [Coding.coded_cardinal]
    exact cardinal hCH
  · rintro ⟨e⟩
    let f := (P.transport e).comparison Q
    have : Countable (P.transport e).data.B := by change Countable RationalBase; infer_instance
    have : Countable N.B := f.base_surjective.countable
    have hc := Cardinal.mk_le_aleph0 (α := N.B)
    change #Base.{u} ≤ ℵ₀ at hc
    rw [base_cardinal] at hc
    exact (Cardinal.aleph0_lt_aleph.2 (by norm_num : (0 : Ordinal.{u}) < 1)).not_ge hc

end EndpointModels

end Arrays

theorem main_proof (hCH : CH.{u}) :
    ∃ (L : ℕ → Type), Countable (Σ n, L n) ∧
      ∃ K : ClassData.{u} L, K.IsAEC ∧ K.HasLSNumber ℵ₀ ∧
        endpoint = hanf (ℵ₀ : Cardinal.{u}) ∧ K.TwoModels endpoint ∧
        ∀ μ, tailThreshold ≤ μ → K.Categorical μ := by
  refine ⟨Arrays.Language, Arrays.language_countable, Arrays.classData hCH,
    Arrays.AEC.isAEC, Arrays.AEC.hasLSNumber, ThresholdArithmetic.endpoint_eq_hanf hCH,
    Arrays.EndpointModels.twoModels hCH, Arrays.Categoricity.tail hCH⟩

theorem endpoint_lt_tailThreshold : endpoint.{u} < tailThreshold.{u} := by
  apply Cardinal.beth_strictMono
  rw [← Cardinal.ord_aleph]
  apply Cardinal.ord_strictMono
  have hs : (ℵ_ (2 : Ordinal.{u})) = succ (ℵ_ (1 : Ordinal.{u})) := by
    rw [Cardinal.succ_aleph]
    norm_num
  apply lt_of_le_of_lt _ (lt_succ _)
  rw [hs]
  exact Order.succ_le_of_lt (Cardinal.cantor _)

theorem prescribed_transfer_fails (hCH : CH.{u}) :
    ∃ (L : ℕ → Type), Countable (Σ n, L n) ∧
      ∃ K : ClassData.{u} L, K.IsAEC ∧ K.HasLSNumber ℵ₀ ∧
        hanf (ℵ₀ : Cardinal.{u}) < succ tailThreshold ∧
        K.Categorical (succ tailThreshold) ∧ ¬ K.Categorical (hanf ℵ₀) := by
  obtain ⟨L, hL, K, hK, hLS, he, ht, hc⟩ := main_proof hCH
  refine ⟨L, hL, K, hK, hLS, ?_, hc _ (le_succ _), ?_⟩
  · rw [← he]
    exact endpoint_lt_tailThreshold.trans (lt_succ _)
  · rw [← he]
    obtain ⟨M, N, hm, hn, hmc, hnc, hne⟩ := ht
    exact fun h => hne (h.2 M N hm hn hmc hnc)

end CHObstruction

end

end OAI


universe u
open OAI.CHObstruction Cardinal Ordinal Order

theorem solution (hCH : CH.{u}) :
    ∃ (L : ℕ → Type), Countable (Σ n, L n) ∧
      ∃ K : ClassData.{u} L, K.IsAEC ∧ K.HasLSNumber ℵ₀ ∧
        endpoint = hanf (ℵ₀ : Cardinal.{u}) ∧ K.TwoModels endpoint ∧
        ∀ μ, tailThreshold ≤ μ → K.Categorical μ :=
  OAI.CHObstruction.main_proof hCH
