-- Prove2me | solution 1 for Grunbaum2003.exists_computable_scheme_representatives_of_realizability_decider
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T07:16:04.832587+00:00
-- url     : https://prove2.me/submissions/6428d3c9-9255-4779-9dd0-4192ac366575

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_SchemeRealizes
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false



namespace Grunbaum2003

/-- The existing finite-sublists primitive-recursion proof, reused locally. -/
theorem primrec_list_sublists {α : Type} [Primcodable α] :
    Primrec (@List.sublists' α) := by
  have hFold : Primrec (fun l : List α =>
      l.foldr (fun a r => r ++ r.map (List.cons a)) [[]]) := by
    apply Primrec.list_foldr
      (h := fun (_ : List α) (p : α × List (List α)) => p.2 ++ p.2.map (List.cons p.1))
      Primrec.id (Primrec.const [[]])
    change Primrec (fun p : List α × (α × List (List α)) =>
      p.2.2 ++ p.2.2.map (List.cons p.2.1))
    exact Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  apply hFold.of_eq
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, List.sublists'_cons, ih]

theorem primrec_list_product {α β : Type} [Primcodable α] [Primcodable β] :
    Primrec₂ (@List.product α β) := by
  have h : Primrec (fun p : List α × List β =>
      p.1.flatMap (fun a => p.2.map (fun b => (a, b)))) := by
    apply Primrec.list_flatMap Primrec.fst
    apply Primrec.list_map (Primrec.snd.comp Primrec.fst)
    exact ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
  exact h

theorem primrec_list_mem {α : Type} [Primcodable α] [DecidableEq α] :
    PrimrecRel (fun (a : α) (L : List α) => a ∈ L) := by
  have h : PrimrecRel (fun (L : List α) (a : α) => ∃ b ∈ L, b = a) :=
    Primrec.eq.exists_mem_list
  exact (h.of_eq (fun L a => by simp)).swap

theorem primrec_bounded_list_forall {X A : Type} [Primcodable X] [Primcodable A]
    {L : X → List A} {P : X → A → Prop}
    (hL : Primrec L) (hP : PrimrecRel P) :
    PrimrecPred (fun x => ∀ a ∈ L x, P x a) :=
  hP.swap.forall_mem_list.comp hL Primrec.id

theorem primrec_bounded_list_exists {X A : Type} [Primcodable X] [Primcodable A]
    {L : X → List A} {P : X → A → Prop}
    (hL : Primrec L) (hP : PrimrecRel P) :
    PrimrecPred (fun x => ∃ a ∈ L x, P x a) :=
  hP.swap.exists_mem_list.comp hL Primrec.id

end Grunbaum2003




namespace Grunbaum2003

/-- Bounded list iteration preserves computability even when the step is merely
computable, rather than primitive recursive. This is used for filtering by the
separate, explicitly assumed realizability decision function. -/
theorem computable_list_foldl {A B C : Type*} [Primcodable A] [Primcodable B]
    [Primcodable C] {f : A → List B} {g : A → C} {h : A → C × B → C}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun c b => h a (c, b)) (g a)) := by
  let G (a : A) (s : List B × C) : List B × C :=
    List.casesOn s.1 s (fun b l => (l, h a (s.2, b)))
  have hG : Computable₂ G := by
    have hHead : Computable (fun t : A × (List B × C) => t.2.1.head?) :=
      Primrec.list_head?.to_comp.comp (Computable.fst.comp Computable.snd)
    have hTail : Computable (fun u : (A × (List B × C)) × B => u.1.2.1.tail) :=
      Primrec.list_tail.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
    have hNew : Computable (fun u : (A × (List B × C)) × B => h u.1.1 (u.1.2.2, u.2)) :=
      hh.comp (Computable.fst.comp Computable.fst)
        ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)
    have hCase := Computable.option_casesOn hHead Computable.snd (hTail.pair hNew).to₂
    exact (hCase.of_eq (g := fun t : A × (List B × C) => G t.1 t.2) (fun ⟨a, l, c⟩ => by cases l <;> rfl)).to₂
  have hI : Computable (fun a => Nat.rec (motive := fun _ => List B × C) (f a, g a)
      (fun _ s => G a s) (f a).length) :=
    Computable.nat_rec (Computable.list_length.comp hf) (hf.pair hg)
      (hG.comp Computable.fst (Computable.snd.comp Computable.snd)).to₂
  have hRec (a : A) (l : List B) (c : C) (n : ℕ) :
      Nat.rec (motive := fun _ => List B × C) (l, c) (fun _ s => G a s) n = (G a)^[n] (l, c) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        change G a (Nat.rec (motive := fun _ => List B × C) (l, c) (fun _ s => G a s) n) = _
        rw [ih, Function.iterate_succ_apply']
  have hEval (a : A) (l : List B) (c : C) (n : ℕ) :
      (G a)^[n] (l, c) =
        (l.drop n, (l.take n).foldl (fun c b => h a (c, b)) c) := by
    induction n generalizing l c with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply]
        cases l <;> simp only [G, ih,
          List.drop_nil, List.take_nil, List.foldl_nil, List.drop_succ_cons,
          List.take_succ_cons, List.foldl_cons]
  apply (Computable.snd.comp hI).of_eq
  intro a
  rw [hRec, hEval]
  simp only [List.take_length]

theorem computable_list_foldr {A B C : Type*} [Primcodable A] [Primcodable B]
    [Primcodable C] {f : A → List B} {g : A → C} {h : A → B × C → C}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldr (fun b c => h a (b, c)) (g a)) := by
  have h := computable_list_foldl (Computable.list_reverse.comp hf) hg
    ((hh.comp Computable.fst ((Computable.snd.pair Computable.fst).comp Computable.snd)).to₂)
  exact h.of_eq (fun a => by simp only [List.foldl_reverse])

/-- Filtering by an explicitly supplied computable Boolean test is computable.
No computability of realizability is inferred from its classical decidability. -/
theorem computable_list_filter {A B : Type*} [Primcodable A] [Primcodable B]
    {f : A → List B} {p : A → B → Bool} (hf : Computable f) (hp : Computable₂ p) :
    Computable (fun a => (f a).filter (p a)) := by
  have hStep : Computable (fun t : A × (B × List B) =>
      cond (p t.1 t.2.1) (t.2.1 :: t.2.2) t.2.2) :=
    Computable.cond (hp.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.list_cons.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)) (Computable.snd.comp Computable.snd)
  have h := computable_list_foldr hf (Computable.const []) hStep.to₂
  apply h.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b l ih =>
      simp only [List.foldr_cons, List.filter_cons, ih]
      cases p a b <;> rfl

end Grunbaum2003




namespace Grunbaum2003

/-- The existing maximal pairwise-sublist algorithm is primitive recursive
when its finite relation test is primitive recursive. -/
theorem primrec_list_pwFilter {A : Type*} [Primcodable A] {R : A → A → Prop}
    [DecidableRel R] (hR : PrimrecRel R) : Primrec (fun L : List A => L.pwFilter R) := by
  unfold List.pwFilter
  apply Primrec.list_foldr
    (h := fun (_ : List A) (p : A × List A) =>
      if ∀ b ∈ p.2, R p.1 b then p.1 :: p.2 else p.2)
    Primrec.id (Primrec.const [])
  change Primrec (fun t : List A × (A × List A) =>
    if ∀ b ∈ t.2.2, R t.2.1 b then t.2.1 :: t.2.2 else t.2.2)
  exact Primrec.ite
    (hR.swap.forall_mem_list.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

/-- Pruning an equivalence relation retains a representative of every input
class; the retained list is a sublist of the original finite list. -/
theorem pwFilter_complement_covers {A : Type*} {R : A → A → Prop}
    [DecidableRel R] (hR : Equivalence R) (L : List A) :
    (L.pwFilter (fun a b => ¬ R a b)) ⊆ L ∧
      ∀ a ∈ L, ∃ b ∈ L.pwFilter (fun a b => ¬ R a b), R a b := by
  classical
  refine ⟨List.pwFilter_subset L, ?_⟩
  intro a ha
  by_contra h
  have hAll : ∀ b ∈ L.pwFilter (fun a b => ¬ R a b), ¬ R a b := by
    intro b hb hab
    exact h ⟨b, hb, hab⟩
  have hNegTrans : ∀ {x y z : A}, (¬ R x z) → (¬ R x y) ∨ (¬ R y z) := by
    intro x y z hxz
    by_cases hxy : R x y
    · exact Or.inr (fun hyz => hxz (hR.trans hxy hyz))
    · exact Or.inl hxy
  have hOrig := (List.forall_mem_pwFilter (R := fun x y : A => ¬ R x y) hNegTrans a L).mp hAll
  exact hOrig a ha (hR.refl a)

/-- The same pruning algorithm has at most one list position per equivalence
class, including repeated equal input values. -/
theorem pwFilter_complement_unique_indices {A : Type*} {R : A → A → Prop}
    [DecidableRel R] (hR : Equivalence R) (L : List A)
    (i j : Fin (L.pwFilter (fun a b => ¬ R a b)).length)
    (hij : R ((L.pwFilter (fun a b => ¬ R a b)).get i)
      ((L.pwFilter (fun a b => ¬ R a b)).get j)) : i = j := by
  have hPair := List.pairwise_pwFilter (R := fun a b => ¬ R a b) L
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hPair.rel_get_of_lt hlt) hij
  · exact (hPair.rel_get_of_lt hgt) (hR.symm hij)

end Grunbaum2003




namespace Grunbaum2003

/-- The primitive recursive class-pruning program is uniform in an external
parameter, such as the common vertex count of incidence schemes. -/
theorem primrec_parameterized_pwFilter {K A : Type*} [Primcodable K] [Primcodable A]
    {R : K → A → A → Prop} [∀ k, DecidableRel (R k)]
    (hR : PrimrecRel (fun p : K × A => fun b => R p.1 p.2 b)) :
    Primrec₂ (fun k (L : List A) => L.pwFilter (R k)) := by
  unfold List.pwFilter
  apply Primrec.list_foldr
    (h := fun (p : K × List A) (s : A × List A) =>
      if ∀ b ∈ s.2, R p.1 s.1 b then s.1 :: s.2 else s.2)
    Primrec.snd (Primrec.const [])
  change Primrec (fun t : (K × List A) × (A × List A) =>
    if ∀ b ∈ t.2.2, R t.1.1 t.2.1 b then t.2.1 :: t.2.2 else t.2.2)
  exact Primrec.ite
    (hR.swap.forall_mem_list.comp (Primrec.snd.comp Primrec.snd)
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)))
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

end Grunbaum2003




namespace Grunbaum2003

private def relationEntry (A : List (List Bool)) (i j : ℕ) : Bool :=
  (A.getD i []).getD j false

private theorem relationEntry_eq_get (A : List (List Bool))
    (i j : Fin A.length) :
    relationEntry A i.val j.val = ((A.get i)[j.val]?).getD false := by
  unfold relationEntry
  rw [List.getD_eq_get A [] i, List.getD_eq_getElem?_getD]

private def relationCertificate (A B : List (List Bool)) (R : List (ℕ × ℕ)) : Prop :=
  (∀ i ∈ List.range A.length, ∃ j ∈ List.range B.length, (i, j) ∈ R) ∧
  (∀ j ∈ List.range B.length, ∃ i ∈ List.range A.length, (i, j) ∈ R) ∧
  ∀ p ∈ R, ∀ q ∈ R,
    (p.1 = q.1 ↔ p.2 = q.2) ∧
      relationEntry A p.1 q.1 = relationEntry B p.2 q.2

private instance relationCertificate_decidable (A B : List (List Bool)) (R : List (ℕ × ℕ)) :
    Decidable (relationCertificate A B R) := by
  unfold relationCertificate
  infer_instance

/-- Exhaustive finite relation-isomorphism test on row indices. Missing row/column entries are
false, so arbitrary ragged Boolean matrices denote total finite binary relations. -/
def finiteRelationIsoCheck (A B : List (List Bool)) : Bool :=
  decide (∃ R ∈ ((List.range A.length).product (List.range B.length)).sublists',
    relationCertificate A B R)

/-- Correctness for exactly the original row-index/absent-entry interpretation; no order,
square-matrix, or realizability assumptions are needed. -/
theorem finiteRelationIsoCheck_eq_true_iff (A B : List (List Bool)) :
    finiteRelationIsoCheck A B = true ↔
      ∃ e : Fin A.length ≃ Fin B.length, ∀ i j,
        ((A.get i)[j.val]?).getD false =
          ((B.get (e i))[(e j).val]?).getD false := by
  classical
  unfold finiteRelationIsoCheck
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨R, _, hTotalA, hTotalB, hGraph⟩
    have hExists (i : Fin A.length) : ∃ j : Fin B.length, (i.val, j.val) ∈ R := by
      obtain ⟨j, hj, hij⟩ := hTotalA i.val (List.mem_range.mpr i.isLt)
      exact ⟨⟨j, List.mem_range.mp hj⟩, hij⟩
    choose f hf using hExists
    have hfInj : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      exact ((hGraph (i.val, (f i).val) (hf i) (j.val, (f j).val) (hf j)).1).mpr
        (congrArg Fin.val hij)
    have hfSurj : Function.Surjective f := by
      intro j
      obtain ⟨i, hi, hij⟩ := hTotalB j.val (List.mem_range.mpr j.isLt)
      let i' : Fin A.length := ⟨i, List.mem_range.mp hi⟩
      refine ⟨i', Fin.ext ?_⟩
      exact ((hGraph (i, (f i').val) (hf i') (i, j.val) hij).1).mp rfl
    refine ⟨Equiv.ofBijective f ⟨hfInj, hfSurj⟩, ?_⟩
    intro i j
    change ((A.get i)[j.val]?).getD false = ((B.get (f i))[(f j).val]?).getD false
    have h := (hGraph (i.val, (f i).val) (hf i) (j.val, (f j).val) (hf j)).2
    rw [relationEntry_eq_get A i j, relationEntry_eq_get B (f i) (f j)] at h
    exact h
  · rintro ⟨e, he⟩
    let f : ℕ → ℕ := fun i => if hi : i < A.length then (e ⟨i, hi⟩).val else 0
    let base := (List.range A.length).product (List.range B.length)
    let R := base.filter (fun p => p.2 == f p.1)
    have hMem (p : ℕ × ℕ) : p ∈ R ↔
        p.1 < A.length ∧ p.2 < B.length ∧ p.2 = f p.1 := by
      rcases p with ⟨i, j⟩
      have hProduct : (i, j) ∈ base ↔ i < A.length ∧ j < B.length :=
        List.mem_product.trans (and_congr List.mem_range List.mem_range)
      simp only [R, List.mem_filter, hProduct, beq_iff_eq, and_assoc]
    refine ⟨R, List.mem_sublists'.mpr List.filter_sublist, ?_, ?_, ?_⟩
    · intro i hi
      have hi' : i < A.length := List.mem_range.mp hi
      let i' : Fin A.length := ⟨i, hi'⟩
      refine ⟨(e i').val, List.mem_range.mpr (e i').isLt,
        (hMem _).mpr ⟨hi', (e i').isLt, ?_⟩⟩
      simp only [f, dif_pos hi']
      rfl
    · intro j hj
      have hj' : j < B.length := List.mem_range.mp hj
      let j' : Fin B.length := ⟨j, hj'⟩
      let i' := e.symm j'
      refine ⟨i'.val, List.mem_range.mpr i'.isLt,
        (hMem _).mpr ⟨i'.isLt, hj', ?_⟩⟩
      have hfi : f i'.val = (e i').val := by simp only [f, dif_pos i'.isLt]
      rw [hfi]
      exact (congrArg Fin.val (e.apply_symm_apply j')).symm
    · intro p hp q hq
      obtain ⟨hpA, _, hpf⟩ := (hMem p).mp hp
      obtain ⟨hqA, _, hqf⟩ := (hMem q).mp hq
      let ip : Fin A.length := ⟨p.1, hpA⟩
      let iq : Fin A.length := ⟨q.1, hqA⟩
      have hp₂ : p.2 = (e ip).val := by
        rw [hpf]
        simp only [f, dif_pos hpA]
        rfl
      have hq₂ : q.2 = (e iq).val := by
        rw [hqf]
        simp only [f, dif_pos hqA]
        rfl
      constructor
      · constructor
        · intro hpq
          have hi : ip = iq := Fin.ext hpq
          exact hp₂.trans ((congrArg (fun i : Fin A.length => (e i).val) hi).trans hq₂.symm)
        · intro hpq
          have heq : e ip = e iq := Fin.ext (hp₂.symm.trans (hpq.trans hq₂))
          exact congrArg Fin.val (e.injective heq)
      · have h := he ip iq
        rw [← relationEntry_eq_get A ip iq,
          ← relationEntry_eq_get B (e ip) (e iq)] at h
        rw [hp₂, hq₂]
        exact h

private theorem primrec_relationEntry_comp {α : Type} [Primcodable α]
    {A : α → List (List Bool)} {i j : α → ℕ}
    (hA : Primrec A) (hi : Primrec i) (hj : Primrec j) :
    Primrec (fun x => relationEntry (A x) (i x) (j x)) := by
  unfold relationEntry
  exact (Primrec.list_getD false).comp ((Primrec.list_getD []).comp hA hi) hj

private abbrev IsoData := (List (List Bool) × List (List Bool)) × List (ℕ × ℕ)

private theorem primrec_relationTotalA : PrimrecPred (fun x : IsoData =>
    ∀ i ∈ List.range x.1.1.length, ∃ j ∈ List.range x.1.2.length, (i, j) ∈ x.2) := by
    apply primrec_bounded_list_forall
      (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)))
    change PrimrecPred (fun y : IsoData × ℕ =>
      ∃ j ∈ List.range y.1.1.2.length, (y.2, j) ∈ y.1.2)
    apply primrec_bounded_list_exists
      (Primrec.list_range.comp (Primrec.list_length.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
    change PrimrecPred (fun z : (IsoData × ℕ) × ℕ => (z.1.2, z.2) ∈ z.1.1.2)
    exact primrec_list_mem.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))

private theorem primrec_relationTotalB : PrimrecPred (fun x : IsoData =>
    ∀ j ∈ List.range x.1.2.length, ∃ i ∈ List.range x.1.1.length, (i, j) ∈ x.2) := by
    apply primrec_bounded_list_forall
      (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))
    change PrimrecPred (fun y : IsoData × ℕ =>
      ∃ i ∈ List.range y.1.1.1.length, (i, y.2) ∈ y.1.2)
    apply primrec_bounded_list_exists
      (Primrec.list_range.comp (Primrec.list_length.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
    change PrimrecPred (fun z : (IsoData × ℕ) × ℕ => (z.2, z.1.2) ∈ z.1.1.2)
    exact primrec_list_mem.comp (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))

private abbrev IsoGraphData := (IsoData × (ℕ × ℕ)) × (ℕ × ℕ)

private theorem primrec_relationGraphIff : PrimrecPred (fun z : IsoGraphData =>
    z.1.2.1 = z.2.1 ↔ z.1.2.2 = z.2.2) := by
  have hp₁ : Primrec (fun z : IsoGraphData => z.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hp₂ : Primrec (fun z : IsoGraphData => z.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hq₁ : Primrec (fun z : IsoGraphData => z.2.1) := Primrec.fst.comp Primrec.snd
  have hq₂ : Primrec (fun z : IsoGraphData => z.2.2) := Primrec.snd.comp Primrec.snd
  apply (Primrec.eq.comp ((Primrec.eq.comp hp₁ hq₁).decide)
    ((Primrec.eq.comp hp₂ hq₂).decide)).of_eq
  intro z
  exact decide_eq_decide

private theorem primrec_relationGraphEntry : PrimrecPred (fun z : IsoGraphData =>
    relationEntry z.1.1.1.1 z.1.2.1 z.2.1 = relationEntry z.1.1.1.2 z.1.2.2 z.2.2) := by
  have hp₁ : Primrec (fun z : IsoGraphData => z.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hp₂ : Primrec (fun z : IsoGraphData => z.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hq₁ : Primrec (fun z : IsoGraphData => z.2.1) := Primrec.fst.comp Primrec.snd
  have hq₂ : Primrec (fun z : IsoGraphData => z.2.2) := Primrec.snd.comp Primrec.snd
  have hA : Primrec (fun z : IsoGraphData => z.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hB : Primrec (fun z : IsoGraphData => z.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  exact Primrec.eq.comp
    (primrec_relationEntry_comp hA hp₁ hq₁)
    (primrec_relationEntry_comp hB hp₂ hq₂)

private theorem primrec_relationGraph : PrimrecPred (fun x : IsoData =>
    ∀ p ∈ x.2, ∀ q ∈ x.2,
      (p.1 = q.1 ↔ p.2 = q.2) ∧
        relationEntry x.1.1 p.1 q.1 = relationEntry x.1.2 p.2 q.2) := by
  apply primrec_bounded_list_forall Primrec.snd
  change PrimrecPred (fun y : IsoData × (ℕ × ℕ) => ∀ q ∈ y.1.2,
    (y.2.1 = q.1 ↔ y.2.2 = q.2) ∧
      relationEntry y.1.1.1 y.2.1 q.1 = relationEntry y.1.1.2 y.2.2 q.2)
  apply primrec_bounded_list_forall (Primrec.snd.comp Primrec.fst)
  exact primrec_relationGraphIff.and primrec_relationGraphEntry

private theorem primrec_relationCertificate :
    PrimrecPred (fun x : IsoData => relationCertificate x.1.1 x.1.2 x.2) :=
  primrec_relationTotalA.and (primrec_relationTotalB.and primrec_relationGraph)

/-- Primitive recursion of the actual finite search, independent of realizability. -/
theorem primrec_finiteRelationIsoCheck : Primrec₂ finiteRelationIsoCheck := by
  have hCandidates : Primrec (fun x : List (List Bool) × List (List Bool) =>
      ((List.range x.1.length).product (List.range x.2.length)).sublists') :=
    primrec_list_sublists.comp (primrec_list_product.comp
      (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
      (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd)))
  have h : PrimrecPred (fun x : List (List Bool) × List (List Bool) =>
      ∃ R ∈ ((List.range x.1.length).product (List.range x.2.length)).sublists',
        relationCertificate x.1 x.2 R) :=
    primrec_bounded_list_exists hCandidates primrec_relationCertificate
  exact h.decide

end Grunbaum2003




open scoped BigOperators

namespace Grunbaum2003

lemma extremePoints_eq_exposedSingletons_sr {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
  classical
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_setOf_eq]
    have hx_in_P : x ∈ P := extremePoints_subset hx
    have hx_ext : IsExtreme ℝ P {x} := isExtreme_singleton.mpr hx
    have hx_not_in : x ∉ convexHull ℝ (V0 \ {x}) := by
      intro hx_in
      have h_sub : convexHull ℝ (V0 \ {x}) ⊆ P := by
        rw [hP_eq]
        exact convexHull_mono Set.diff_subset
      have hx_ext' : IsExtreme ℝ (convexHull ℝ (V0 \ {x})) {x} :=
        hx_ext.mono h_sub (Set.singleton_subset_iff.mpr hx_in)
      have hx_ep : x ∈ (convexHull ℝ (V0 \ {x})).extremePoints ℝ :=
        isExtreme_singleton.mp hx_ext'
      have hx_diff : x ∈ V0 \ {x} := extremePoints_convexHull_subset hx_ep
      exact hx_diff.2 rfl
    have hC_conv : Convex ℝ (convexHull ℝ (V0 \ {x})) := convex_convexHull ℝ _
    have hC_closed : IsClosed (convexHull ℝ (V0 \ {x})) :=
      ((hV0_fin.diff).isCompact_convexHull ℝ).isClosed
    obtain ⟨l, u, hlu, hux⟩ := geometric_hahn_banach_closed_point hC_conv hC_closed hx_not_in
    intro _
    refine ⟨l, ?_⟩
    apply Set.Subset.antisymm
    · rintro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      refine ⟨hx_in_P, ?_⟩
      have h_le : P ⊆ {z : Fin d → ℝ | l z ≤ l x} := by
        rw [hP_eq]
        refine convexHull_min ?_ ?_
        · intro s hs
          change l s ≤ l x
          by_cases hsx : s = x
          · rw [hsx]
          · have hs_diff : s ∈ V0 \ {x} := ⟨hs, hsx⟩
            exact le_of_lt ((hlu s (subset_convexHull ℝ _ hs_diff)).trans hux)
        · intro z1 hz1 z2 hz2 a b ha hb hab
          change l z1 ≤ l x at hz1
          change l z2 ≤ l x at hz2
          change l (a • z1 + b • z2) ≤ l x
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          have hb_eq : b = 1 - a := by linarith
          subst hb_eq
          nlinarith
      intro z hz
      exact h_le hz
    · rintro y ⟨hyP, hymax⟩
      rw [Set.mem_singleton_iff]
      have hly : l x ≤ l y := hymax x hx_in_P
      rw [hP_eq] at hyP
      let Vfin := hV0_fin.toFinset
      have hVfin : (Vfin : Set (Fin d → ℝ)) = V0 := hV0_fin.coe_toFinset
      rw [← hVfin] at hyP
      obtain ⟨w, hw0, hw1, rfl⟩ := Finset.mem_convexHull'.mp hyP
      have h_sum_nonneg : ∀ s ∈ Vfin, 0 ≤ w s * (l x - l s) := by
        intro s hs
        refine mul_nonneg (hw0 s hs) ?_
        by_cases hsx : s = x
        · subst hsx; linarith
        · have hs_diff : s ∈ V0 \ {x} := ⟨hV0_fin.mem_toFinset.mp hs, hsx⟩
          have hls := hlu s (subset_convexHull ℝ _ hs_diff)
          linarith
      have h_sum_le : ∑ s ∈ Vfin, w s * (l x - l s) ≤ 0 := by
        have h_eq : ∑ s ∈ Vfin, w s * (l x - l s) = l x - l (∑ s ∈ Vfin, w s • s) := by
          rw [map_sum]
          simp_rw [map_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
            hw1, one_mul]
        linarith
      have h_all_zero : ∀ s ∈ Vfin, w s * (l x - l s) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg h_sum_nonneg).mp
          (le_antisymm h_sum_le (Finset.sum_nonneg h_sum_nonneg))
      have hw_zero_of_ne : ∀ s ∈ Vfin, s ≠ x → w s = 0 := by
        intro s hs hsx
        have hs_diff : s ∈ V0 \ {x} := ⟨hV0_fin.mem_toFinset.mp hs, hsx⟩
        have hls := (hlu s (subset_convexHull ℝ _ hs_diff)).trans hux
        have h_z := h_all_zero s hs
        rcases mul_eq_zero.mp h_z with hw_z | hl_z
        · exact hw_z
        · linarith
      calc ∑ s ∈ Vfin, w s • s
          = ∑ s ∈ Vfin, w s • x := by
            refine Finset.sum_congr rfl (fun s hs => ?_)
            by_cases hsx : s = x
            · subst hsx; rfl
            · simp [hw_zero_of_ne s hs hsx]
        _ = (∑ s ∈ Vfin, w s) • x := (Finset.sum_smul).symm
        _ = x := by rw [hw1, one_smul]
  · intro x hx
    exact exposedPoints_subset_extremePoints (mem_exposedPoints_iff_exposed_singleton.mpr hx)

theorem polytope_face_eq_convexHull_exposed_vertices_sr (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ F : PolytopeFace P,
        F.val = convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}) := by
  rcases hP.1 with ⟨V0, hV0_fin, _, hP_eq⟩
  have hExtEq : P.extremePoints ℝ = {x : Fin d → ℝ | IsExposed ℝ P {x}} :=
    extremePoints_eq_exposedSingletons_sr P hP
  have hVertFin : {x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite := by
    rw [← hExtEq, hP_eq]
    exact hV0_fin.subset extremePoints_convexHull_subset
  refine ⟨hVertFin, ?_⟩
  intro F
  have hP_comp : IsCompact P := hP_eq ▸ hV0_fin.isCompact_convexHull ℝ
  have hP_conv : Convex ℝ P := hP_eq ▸ convex_convexHull ℝ V0
  have hF_comp : IsCompact F.val := F.property.isCompact hP_comp
  have hF_conv : Convex ℝ F.val := F.property.convex hP_conv
  have hF_ext : F.val.extremePoints ℝ = F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} := by
    rw [F.property.isExtreme.extremePoints_eq, ← hExtEq]
  have h_km := closure_convexHull_extremePoints hF_comp hF_conv
  rw [hF_ext] at h_km
  have h_closed : IsClosed (convexHull ℝ (F.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) :=
    ((hVertFin.subset Set.inter_subset_right).isCompact_convexHull ℝ).isClosed
  rw [h_closed.closure_eq] at h_km
  exact h_km.symm

noncomputable def schemeVertSet {d k : ℕ} {P : Set (Fin d → ℝ)}
    (V : Fin k → (Fin d → ℝ)) (F : PolytopeFace P) : Finset ℕ :=
  by
    classical
    exact (Finset.univ.filter (fun i : Fin k => V i ∈ F.val)).map ⟨Fin.val, Fin.val_injective⟩

theorem coe_schemeVertSet {d k : ℕ} {P : Set (Fin d → ℝ)}
    (V : Fin k → (Fin d → ℝ)) (F : PolytopeFace P) :
    (schemeVertSet V F : Set ℕ) = {n : ℕ | ∃ i : Fin k, i.val = n ∧ V i ∈ F.val} := by
  classical
  ext n
  simp [schemeVertSet, and_comm]

theorem schemeVertSet_le_iff {d k : ℕ} {P : Set (Fin d → ℝ)}
    (hPd : IsDPolytope P)
    (V : Fin k → (Fin d → ℝ)) (hV_range : Set.range V = {x | IsExposed ℝ P {x}})
    (F₁ F₂ : PolytopeFace P) :
    F₁ ≤ F₂ ↔ schemeVertSet V F₁ ⊆ schemeVertSet V F₂ := by
  constructor
  · intro hle n hn
    rw [ ← Finset.mem_coe, coe_schemeVertSet ] at hn ⊢
    rcases hn with ⟨i, rfl, hi⟩
    exact ⟨i, rfl, hle hi⟩
  · intro hsub
    have hHull := (polytope_face_eq_convexHull_exposed_vertices_sr d P hPd).2 F₁
    rw [← hV_range] at hHull
    obtain ⟨⟨Vset, _, _, hPhull⟩, _⟩ := hPd
    have hF2_conv : Convex ℝ F₂.val := by
      refine F₂.2.convex ?_
      rw [hPhull]
      exact convex_convexHull ℝ _
    change F₁.val ⊆ F₂.val
    rw [hHull]
    refine convexHull_min ?_ hF2_conv
    rintro x ⟨hxF1, i, rfl⟩
    have hi1 : i.val ∈ (schemeVertSet V F₁ : Set ℕ) := by
      rw [coe_schemeVertSet]
      exact ⟨i, rfl, hxF1⟩
    have hi2 : i.val ∈ (schemeVertSet V F₂ : Set ℕ) := hsub hi1
    rw [coe_schemeVertSet] at hi2
    rcases hi2 with ⟨j, hj, hjF2⟩
    have hij : j = i := Fin.ext hj
    subst hij
    exact hjF2

theorem mem_range_schemeVertSet_iff {d k : ℕ} {P : Set (Fin d → ℝ)} {S : List (List ℕ)}
    (V : Fin k → (Fin d → ℝ)) (hV_range : Set.range V = {x | IsExposed ℝ P {x}})
    (hS : ∀ J : Finset ℕ,
      (∃ L ∈ S, L.toFinset = J) ↔
        ∃ F : Set (Fin d → ℝ), IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧
          (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F})
    (J : Finset ℕ) :
    (∃ F : PolytopeFace P, schemeVertSet V F = J) ↔
      J = ∅ ∨ J = Finset.range k ∨ (∃ L ∈ S, L.toFinset = J) := by
  have hVP : ∀ i : Fin k, V i ∈ P := by
    intro i
    have hVi : V i ∈ Set.range V := Set.mem_range_self i
    rw [hV_range] at hVi
    exact hVi.subset (Set.mem_singleton (V i))
  have hTopSet : ({n : ℕ | ∃ i : Fin k, i.val = n ∧ V i ∈ P} : Set ℕ) =
      (Finset.range k : Set ℕ) := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
    constructor
    · rintro ⟨i, rfl, _⟩
      exact i.isLt
    · intro hn
      exact ⟨⟨n, hn⟩, rfl, hVP ⟨n, hn⟩⟩
  constructor
  · rintro ⟨F, rfl⟩
    rcases F.val.eq_empty_or_nonempty with hEmp | hNe
    · left
      rw [← Finset.coe_inj, coe_schemeVertSet, hEmp]
      simp
    · by_cases hFP : F.val = P
      · right; left
        rw [← Finset.coe_inj, coe_schemeVertSet, hFP, hTopSet]
      · right; right
        rw [hS]
        exact ⟨F.val, F.2, hNe, hFP, coe_schemeVertSet V F⟩
  · rintro (rfl | rfl | hLS)
    · refine ⟨⟨∅, fun h => (Set.not_nonempty_empty h).elim⟩, ?_⟩
      rw [← Finset.coe_inj, coe_schemeVertSet]
      simp
    · refine ⟨⟨P, fun _ => ⟨0, by simp⟩⟩, ?_⟩
      rw [← Finset.coe_inj, coe_schemeVertSet, hTopSet]
    · obtain ⟨Fset, hFe, _, _, hJeq⟩ := (hS J).mp hLS
      refine ⟨⟨Fset, hFe⟩, ?_⟩
      rw [← Finset.coe_inj, coe_schemeVertSet, hJeq]

/-- Grünbaum (2003), §3.2 & §5.5 (Theorem 5.5.2, p. 91): any two polytopes that realize
the same vertex-face incidence scheme `S` on `k` vertices have order-isomorphic face posets. -/
theorem schemeRealizes_unique_combinatorial_type (d₁ d₂ k : ℕ) (S : List (List ℕ))
    (P : Set (Fin d₁ → ℝ)) (Q : Set (Fin d₂ → ℝ))
    (hP : SchemeRealizes k S P) (hQ : SchemeRealizes k S Q) :
    Nonempty (PolytopeFace P ≃o PolytopeFace Q) := by
  classical
  rcases hP with ⟨hPd, VP, _, hVP_range, hSP⟩
  rcases hQ with ⟨hQd, VQ, _, hVQ_range, hSQ⟩
  have hFwd : ∀ F : PolytopeFace P, ∃ G : PolytopeFace Q,
      schemeVertSet VQ G = schemeVertSet VP F := by
    intro F
    rw [mem_range_schemeVertSet_iff VQ hVQ_range hSQ,
      ← mem_range_schemeVertSet_iff VP hVP_range hSP]
    exact ⟨F, rfl⟩
  have hBwd : ∀ G : PolytopeFace Q, ∃ F : PolytopeFace P,
      schemeVertSet VP F = schemeVertSet VQ G := by
    intro G
    rw [mem_range_schemeVertSet_iff VP hVP_range hSP,
      ← mem_range_schemeVertSet_iff VQ hVQ_range hSQ]
    exact ⟨G, rfl⟩
  let toFun : PolytopeFace P → PolytopeFace Q := fun F => Classical.choose (hFwd F)
  have htoFun : ∀ F : PolytopeFace P, schemeVertSet VQ (toFun F) = schemeVertSet VP F :=
    fun F => Classical.choose_spec (hFwd F)
  let invFun : PolytopeFace Q → PolytopeFace P := fun G => Classical.choose (hBwd G)
  have hinvFun : ∀ G : PolytopeFace Q, schemeVertSet VP (invFun G) = schemeVertSet VQ G :=
    fun G => Classical.choose_spec (hBwd G)
  have hLeft : Function.LeftInverse invFun toFun := by
    intro F
    apply le_antisymm
    · rw [schemeVertSet_le_iff hPd VP hVP_range, hinvFun, htoFun]
    · rw [schemeVertSet_le_iff hPd VP hVP_range, hinvFun, htoFun]
  have hRight : Function.RightInverse invFun toFun := by
    intro G
    apply le_antisymm
    · rw [schemeVertSet_le_iff hQd VQ hVQ_range, htoFun, hinvFun]
    · rw [schemeVertSet_le_iff hQd VQ hVQ_range, htoFun, hinvFun]
  exact ⟨{
    toFun := toFun
    invFun := invFun
    left_inv := hLeft
    right_inv := hRight
    map_rel_iff' := by
      intro F₁ F₂
      change toFun F₁ ≤ toFun F₂ ↔ F₁ ≤ F₂
      rw [schemeVertSet_le_iff hQd VQ hVQ_range, htoFun, htoFun,
        ← schemeVertSet_le_iff hPd VP hVP_range]
  }⟩

end Grunbaum2003




namespace Grunbaum2003

/-- Any exposed face of a finite hull is the hull of its incident input points.
The input need not be an irredundant vertex list. -/
theorem exposedFace_eq_convexHull_incident_range {d n : ℕ}
    (v : Fin n → Fin d → ℝ) {F : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F) :
    F = convexHull ℝ (F ∩ Set.range v) := by
  have hPcomp : IsCompact (convexHull ℝ (Set.range v)) :=
    (Set.finite_range v).isCompact_convexHull ℝ
  have hFcomp : IsCompact F := hF.isCompact hPcomp
  have hFconv : Convex ℝ F := hF.convex (convex_convexHull ℝ (Set.range v))
  have hExtRange : F.extremePoints ℝ ⊆ Set.range v := by
    intro x hx
    rw [hF.isExtreme.extremePoints_eq] at hx
    exact extremePoints_convexHull_subset hx.2
  have hExtFin : (F.extremePoints ℝ).Finite := (Set.finite_range v).subset hExtRange
  have hKM := closure_convexHull_extremePoints hFcomp hFconv
  rw [(hExtFin.isCompact_convexHull ℝ).isClosed.closure_eq] at hKM
  apply Set.Subset.antisymm
  · apply hKM.symm.subset.trans
    apply convexHull_mono
    intro x hx
    exact ⟨extremePoints_subset hx, hExtRange hx⟩
  · exact convexHull_min Set.inter_subset_left hFconv

/-- Containment of finite-hull faces is exactly containment of their incident
input-label sets. This provides the order embedding used by finite certificates. -/
theorem exposedFace_subset_iff_incident_labels {d n : ℕ}
    (v : Fin n → Fin d → ℝ) {F G : Set (Fin d → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (Set.range v)) F)
    (hG : IsExposed ℝ (convexHull ℝ (Set.range v)) G) :
    F ⊆ G ↔ ∀ i : Fin n, v i ∈ F → v i ∈ G := by
  constructor
  · intro h i hi
    exact h hi
  · intro h
    rw [exposedFace_eq_convexHull_incident_range v hF,
      exposedFace_eq_convexHull_incident_range v hG]
    apply convexHull_mono
    rintro x ⟨hx, i, rfl⟩
    exact ⟨h i hx, ⟨i, rfl⟩⟩

/-- A finite rational/linear support certificate realizes a face and certifies
its exact input-label incidence set. -/
theorem exposedFace_of_label_maximizers {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (s : Set (Fin n)) (hs : s.Nonempty)
    (l : (Fin d → ℝ) →L[ℝ] ℝ) (b : ℝ)
    (hbound : ∀ i : Fin n, l (v i) ≤ b)
    (heq : ∀ i : Fin n, l (v i) = b ↔ i ∈ s) :
    IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' s)) ∧
      ∀ i : Fin n, v i ∈ convexHull ℝ (v '' s) ↔ i ∈ s := by
  let P := convexHull ℝ (Set.range v)
  let F := l.toExposed P
  have hPbound : ∀ x ∈ P, l x ≤ b := by
    have hconv : Convex ℝ {x : Fin d → ℝ | l x ≤ b} := by
      intro x hx y hy a c ha hc hac
      change l (a • x + c • y) ≤ b
      rw [map_add, map_smul, map_smul]
      change a * l x + c * l y ≤ b
      calc a * l x + c * l y ≤ a * b + c * b :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hc)
        _ = b := by rw [← add_mul, hac, one_mul]
    exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact hbound i) hconv
  have hFlabels : ∀ i : Fin n, v i ∈ F ↔ i ∈ s := by
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj⟩ := hs
      have hbj : l (v j) = b := (heq j).mpr hj
      have hbi : b ≤ l (v i) := by
        rw [← hbj]
        exact hi.2 (v j) (subset_convexHull ℝ _ (Set.mem_range_self j))
      exact (heq i).mp (le_antisymm (hbound i) hbi)
    · intro hi
      refine ⟨subset_convexHull ℝ _ (Set.mem_range_self i), ?_⟩
      intro x hx
      rw [(heq i).mpr hi]
      exact hPbound x hx
  have hInc : F ∩ Set.range v = v '' s := by
    ext x
    constructor
    · rintro ⟨hx, i, rfl⟩
      exact ⟨i, (hFlabels i).mp hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(hFlabels i).mpr hi, Set.mem_range_self i⟩
  have hFhull : F = convexHull ℝ (v '' s) := by
    calc F = convexHull ℝ (F ∩ Set.range v) :=
          exposedFace_eq_convexHull_incident_range v
            (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
      _ = convexHull ℝ (v '' s) := congrArg (convexHull ℝ) hInc
  constructor
  · rw [← hFhull]
    exact (ContinuousLinearMap.toExposed.isExposed (l := l) (A := P))
  · intro i
    rw [← hFhull]
    exact hFlabels i

/-- A complete finite incidence certificate identifies the actual exposed-face
poset. The two certificate obligations concern only its finite label family. -/
theorem exposedFaces_orderIso_of_incidence_certificate {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (family : Finset (Finset (Fin n)))
    (hSound : ∀ F : Set (Fin d → ℝ),
      IsExposed ℝ (convexHull ℝ (Set.range v)) F →
      ∀ s : Finset (Fin n), (∀ i : Fin n, i ∈ s ↔ v i ∈ F) → s ∈ family)
    (hComplete : ∀ s ∈ family,
      IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (s : Set (Fin n)))) ∧
        ∀ i : Fin n, v i ∈ convexHull ℝ (v '' (s : Set (Fin n))) ↔ i ∈ s) :
    Nonempty ({F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ≃o
      ↥family) := by
  classical
  let f : {F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ↪o ↥family := {
    toFun := fun F => ⟨Finset.univ.filter (fun i => v i ∈ F.val),
      hSound F.val F.property _ (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and])⟩
    inj' := by
      intro F G h
      have hfg : (Finset.univ.filter fun i => v i ∈ F.val) =
          (Finset.univ.filter fun i => v i ∈ G.val) := congrArg Subtype.val h
      have hi : ∀ i : Fin n, v i ∈ F.val ↔ v i ∈ G.val := by
        intro i
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          (Finset.ext_iff.mp hfg i)
      apply Subtype.ext
      apply Set.Subset.antisymm
      · exact (exposedFace_subset_iff_incident_labels v F.property G.property).mpr
          (fun i hv => (hi i).mp hv)
      · exact (exposedFace_subset_iff_incident_labels v G.property F.property).mpr
          (fun i hv => (hi i).mpr hv)
    map_rel_iff' := by
      intro F G
      change (Finset.univ.filter (fun i => v i ∈ F.val)) ⊆
        (Finset.univ.filter (fun i => v i ∈ G.val)) ↔ F.val ⊆ G.val
      simpa only [Finset.subset_iff, Finset.mem_filter,
        Finset.mem_univ, true_and] using
        (exposedFace_subset_iff_incident_labels v F.property G.property).symm }
  have hf : Function.Surjective f := by
    intro s
    refine ⟨⟨convexHull ℝ (v '' (s.val : Set (Fin n))), (hComplete s.val s.property).1⟩, ?_⟩
    apply Subtype.ext
    ext i
    change i ∈ Finset.univ.filter (fun i => v i ∈ convexHull ℝ (v '' (s.val : Set (Fin n)))) ↔
      i ∈ s.val
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (hComplete s.val s.property).2 i
  exact ⟨OrderIso.ofSurjective f hf⟩

/-- The complete certificate isomorphism retains the actual vertex incidences. -/
theorem exposedFaces_orderIso_of_incidence_certificate_with_incidence {d n : ℕ}
    (v : Fin n → Fin d → ℝ) (family : Finset (Finset (Fin n)))
    (hSound : ∀ F : Set (Fin d → ℝ),
      IsExposed ℝ (convexHull ℝ (Set.range v)) F →
      ∀ s : Finset (Fin n), (∀ i : Fin n, i ∈ s ↔ v i ∈ F) → s ∈ family)
    (hComplete : ∀ s ∈ family,
      IsExposed ℝ (convexHull ℝ (Set.range v)) (convexHull ℝ (v '' (s : Set (Fin n)))) ∧
        ∀ i : Fin n, v i ∈ convexHull ℝ (v '' (s : Set (Fin n))) ↔ i ∈ s) :
    ∃ Φ : {F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ≃o ↥family,
      ∀ F i, i ∈ (Φ F).val ↔ v i ∈ F.val := by
  classical
  let f : {F : Set (Fin d → ℝ) // IsExposed ℝ (convexHull ℝ (Set.range v)) F} ↪o ↥family := {
    toFun := fun F => ⟨Finset.univ.filter (fun i => v i ∈ F.val),
      hSound F.val F.property _ (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and])⟩
    inj' := by
      intro F G h
      have hfg : (Finset.univ.filter fun i => v i ∈ F.val) =
          (Finset.univ.filter fun i => v i ∈ G.val) := congrArg Subtype.val h
      have hi : ∀ i : Fin n, v i ∈ F.val ↔ v i ∈ G.val := by
        intro i
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          (Finset.ext_iff.mp hfg i)
      apply Subtype.ext
      apply Set.Subset.antisymm
      · exact (exposedFace_subset_iff_incident_labels v F.property G.property).mpr
          (fun i hv => (hi i).mp hv)
      · exact (exposedFace_subset_iff_incident_labels v G.property F.property).mpr
          (fun i hv => (hi i).mpr hv)
    map_rel_iff' := by
      intro F G
      change (Finset.univ.filter (fun i => v i ∈ F.val)) ⊆
        (Finset.univ.filter (fun i => v i ∈ G.val)) ↔ F.val ⊆ G.val
      simpa only [Finset.subset_iff, Finset.mem_filter,
        Finset.mem_univ, true_and] using
        (exposedFace_subset_iff_incident_labels v F.property G.property).symm }
  have hf : Function.Surjective f := by
    intro s
    refine ⟨⟨convexHull ℝ (v '' (s.val : Set (Fin n))), (hComplete s.val s.property).1⟩, ?_⟩
    apply Subtype.ext
    ext i
    change i ∈ Finset.univ.filter (fun i => v i ∈ convexHull ℝ (v '' (s.val : Set (Fin n)))) ↔
      i ∈ s.val
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (hComplete s.val s.property).2 i
  refine ⟨OrderIso.ofSurjective f hf, ?_⟩
  intro F i
  change i ∈ Finset.univ.filter (fun i => v i ∈ F.val) ↔ v i ∈ F.val
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Grunbaum2003




open scoped BigOperators

namespace Grunbaum2003

noncomputable section

private def supportFunctional {d : ℕ} (a : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ({ toFun := fun x => ∑ t, a t * x t
     map_add' := by
       intro x y
       simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
     map_smul' := by
       intro c x
       simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
       exact Finset.sum_congr rfl (fun t _ => mul_left_comm (a t) c (x t))
    } : (Fin d → ℝ) →ₗ[ℝ] ℝ).toContinuousLinearMap

private theorem supportFunctional_apply {d : ℕ} (a x : Fin d → ℝ) :
    supportFunctional a x = ∑ t, a t * x t := rfl

private theorem exists_support_coefficients {d : ℕ} (l : (Fin d → ℝ) →L[ℝ] ℝ) :
    ∃ a : Fin d → ℝ, ∀ x : Fin d → ℝ, l x = ∑ t, a t * x t := by
  refine ⟨fun t => l (fun j => if t = j then 1 else 0), ?_⟩
  intro x
  simpa only [ContinuousLinearMap.coe_coe, smul_eq_mul, mul_comm] using l.toLinearMap.pi_apply_eq_sum_univ x

/-- Converting the natural-number incidence set to its finitely indexed form.
The explicit bound is essential for the reverse implication. -/
theorem incidence_set_eq_iff {d k : ℕ} (V : Fin k → Fin d → ℝ)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range k) (F : Set (Fin d → ℝ)) :
    (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F} ↔
      ∀ i : Fin k, V i ∈ F ↔ i.val ∈ J := by
  constructor
  · intro h i
    constructor
    · intro hi
      have hn : i.val ∈ (J : Set ℕ) := by rw [h]; exact ⟨i, rfl, hi⟩
      exact hn
    · intro hi
      have hn : i.val ∈ (J : Set ℕ) := hi
      rw [h] at hn
      obtain ⟨j, hji, hjF⟩ := hn
      have hji' : j = i := Fin.ext hji
      exact hji' ▸ hjF
  · intro h
    ext n
    constructor
    · intro hn
      have hnk : n < k := Finset.mem_range.mp (hJ hn)
      exact ⟨⟨n, hnk⟩, rfl, (h ⟨n, hnk⟩).mpr hn⟩
    · rintro ⟨i, rfl, hi⟩
      exact (h i).mp hi

/-- A nonempty proper bounded label set is the incidence of an actual exposed
face exactly when finitely many bilinear support equalities/inequalities hold. -/
theorem proper_face_incidence_iff_support_coefficients {d k : ℕ}
    (V : Fin k → Fin d → ℝ) (P : Set (Fin d → ℝ))
    (hPgen : P = convexHull ℝ (Set.range V))
    (J : Finset ℕ) (hJ : J ⊆ Finset.range k) (hJne : J.Nonempty)
    (hJproper : J ≠ Finset.range k) :
    (∃ F : Set (Fin d → ℝ), IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧
      (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F}) ↔
    ∃ (a : Fin d → ℝ) (b : ℝ),
      (∀ i : Fin k, (∑ t, a t * V i t) ≤ b) ∧
      (∀ i : Fin k, (∑ t, a t * V i t) = b ↔ i.val ∈ J) := by
  have hVP (i : Fin k) : V i ∈ P := by rw [hPgen]; exact subset_convexHull ℝ _ (Set.mem_range_self i)
  constructor
  · rintro ⟨F, hF, hFne, hFproper, hInc⟩
    have hAt := (incidence_set_eq_iff V J hJ F).mp hInc
    obtain ⟨n, hn⟩ := hJne
    let i : Fin k := ⟨n, Finset.mem_range.mp (hJ hn)⟩
    have hiF : V i ∈ F := (hAt i).mpr hn
    obtain ⟨l, hl⟩ := hF hFne
    have hiMax : V i ∈ P ∧ ∀ x ∈ P, l x ≤ l (V i) := by
      simpa only [hl, Set.mem_ofPred_eq] using hiF
    obtain ⟨a, ha⟩ := exists_support_coefficients l
    refine ⟨a, l (V i), ?_, ?_⟩
    · intro j
      rw [← ha]
      exact hiMax.2 (V j) (hVP j)
    · intro j
      rw [← ha]
      constructor
      · intro hj
        apply (hAt j).mp
        rw [hl]
        exact ⟨hVP j, by rw [hj]; exact hiMax.2⟩
      · intro hj
        have hjF := (hAt j).mpr hj
        rw [hl] at hjF
        exact le_antisymm (hiMax.2 _ (hVP j)) (hjF.2 _ (hVP i))
  · rintro ⟨a, b, hbound, heq⟩
    let s : Set (Fin k) := {i | i.val ∈ J}
    have hs : s.Nonempty := by
      obtain ⟨n, hn⟩ := hJne
      exact ⟨⟨n, Finset.mem_range.mp (hJ hn)⟩, hn⟩
    obtain ⟨hF, hAt⟩ := exposedFace_of_label_maximizers V s hs
      (supportFunctional a) b (by simpa only [supportFunctional_apply] using hbound)
        (by simpa only [supportFunctional_apply, s, Set.mem_ofPred_eq] using heq)
    let F := convexHull ℝ (V '' s)
    have hFne : F.Nonempty := hs.image V |>.convexHull
    have hInc : (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F} :=
      (incidence_set_eq_iff V J hJ F).mpr hAt
    refine ⟨F, hPgen ▸ hF, hFne, ?_, hInc⟩
    intro hFP
    apply hJproper
    apply Finset.Subset.antisymm hJ
    intro n hn
    let i : Fin k := ⟨n, Finset.mem_range.mp hn⟩
    apply (hAt i).mp
    change V i ∈ F
    rw [hFP]
    exact hVP i

/-- Proper nonempty face incidences of a finite hull are nonempty proper bounded
sets of labels. This is valid even if the finite input list is redundant. -/
theorem proper_face_incidence_bounds {d k : ℕ}
    (V : Fin k → Fin d → ℝ) (P : Set (Fin d → ℝ))
    (hPgen : P = convexHull ℝ (Set.range V))
    (J : Finset ℕ) (F : Set (Fin d → ℝ))
    (hF : IsExposed ℝ P F) (hFne : F.Nonempty) (hFP : F ≠ P)
    (hInc : (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ V i ∈ F}) :
    J ⊆ Finset.range k ∧ J.Nonempty ∧ J ≠ Finset.range k := by
  have hJ : J ⊆ Finset.range k := by
    intro n hn
    have hn' : n ∈ (J : Set ℕ) := hn
    rw [hInc] at hn'
    obtain ⟨i, rfl, _⟩ := hn'
    exact Finset.mem_range.mpr i.isLt
  have hAt := (incidence_set_eq_iff V J hJ F).mp hInc
  have hF' : IsExposed ℝ (convexHull ℝ (Set.range V)) F := hPgen ▸ hF
  have hFhull := exposedFace_eq_convexHull_incident_range V (F := F) hF' 
  have hIncNe : (F ∩ Set.range V).Nonempty :=
    convexHull_nonempty_iff.mp (hFhull ▸ hFne)
  obtain ⟨_, hxF, i, rfl⟩ := hIncNe
  refine ⟨hJ, ⟨i.val, (hAt i).mp hxF⟩, ?_⟩
  intro hJall
  apply hFP
  apply Set.Subset.antisymm hF.subset
  rw [hPgen]
  apply convexHull_min ?_ (hF.convex (by rw [hPgen]; exact convex_convexHull ℝ _))
  rintro _ ⟨j, rfl⟩
  apply (hAt j).mpr
  rw [hJall]
  exact Finset.mem_range.mpr j.isLt

/-- Irredundancy of a finite generator is exactly a strict linear support
certificate at that generator; the singleton-body case is included. -/
theorem singleton_exposed_iff_strict_support_coefficients {d k : ℕ}
    (V : Fin k → Fin d → ℝ) (P : Set (Fin d → ℝ))
    (hPgen : P = convexHull ℝ (Set.range V)) (hV : Function.Injective V) (i : Fin k) :
    IsExposed ℝ P {V i} ↔
      ∃ a : Fin d → ℝ, ∀ j : Fin k, j ≠ i →
        (∑ t, a t * V j t) < ∑ t, a t * V i t := by
  have hVP (j : Fin k) : V j ∈ P := by
    rw [hPgen]
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
  constructor
  · intro hi
    obtain ⟨l, hl⟩ := hi (Set.singleton_nonempty (V i))
    have hiMax : ∀ x ∈ P, l x ≤ l (V i) := by
      have hVi : V i ∈ ({V i} : Set (Fin d → ℝ)) := Set.mem_singleton _
      rw [hl] at hVi
      exact hVi.2
    obtain ⟨a, ha⟩ := exists_support_coefficients l
    refine ⟨a, ?_⟩
    intro j hji
    rw [← ha, ← ha]
    apply lt_of_le_of_ne (hiMax _ (hVP j))
    intro heq
    have hjF : V j ∈ ({V i} : Set (Fin d → ℝ)) := by
      rw [hl]
      refine ⟨hVP j, ?_⟩
      rw [heq]
      exact hiMax
    exact hji (hV (Set.mem_singleton_iff.mp hjF))
  · rintro ⟨a, ha⟩
    have hbound : ∀ j : Fin k, supportFunctional a (V j) ≤ supportFunctional a (V i) := by
      intro j
      rw [supportFunctional_apply, supportFunctional_apply]
      by_cases hji : j = i
      · rw [hji]
      · exact (ha j hji).le
    have heq : ∀ j : Fin k,
        supportFunctional a (V j) = supportFunctional a (V i) ↔ j ∈ ({i} : Set (Fin k)) := by
      intro j
      rw [supportFunctional_apply, supportFunctional_apply]
      change _ ↔ j = i
      constructor
      · intro h
        by_contra hji
        exact (ne_of_lt (ha j hji)) h
      · intro hji
        rw [hji]
    have h := (exposedFace_of_label_maximizers V ({i} : Set (Fin k))
      (Set.singleton_nonempty i) (supportFunctional a) (supportFunctional a (V i)) hbound heq).1
    rw [hPgen]
    simpa only [Set.image_singleton, convexHull_singleton] using h

/-- Exact realizability characterization by a finite vertex configuration and
finite support-vector tests. All face-incidence quantifiers range over the
explicit powerset of k labels. This is a semantic producer for the existing
computable-representatives frontier, not a decision procedure. -/
theorem exists_schemeRealizes_iff_finite_support_certificates (d k : ℕ)
    (S : List (List ℕ)) :
    (∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ↔
    ∃ V : Fin k → Fin d → ℝ,
      0 < k ∧ Function.Injective V ∧ affineSpan ℝ (Set.range V) = ⊤ ∧
      (∀ i : Fin k, ∃ a : Fin d → ℝ, ∀ j : Fin k, j ≠ i →
        (∑ t, a t * V j t) < ∑ t, a t * V i t) ∧
      (∀ L ∈ S, ∀ n ∈ L, n < k) ∧
      ∀ J ∈ (Finset.range k).powerset,
        (∃ L ∈ S, L.toFinset = J) ↔
          J.Nonempty ∧ J ≠ Finset.range k ∧
            ∃ (a : Fin d → ℝ) (b : ℝ),
              (∀ i : Fin k, (∑ t, a t * V i t) ≤ b) ∧
              (∀ i : Fin k, (∑ t, a t * V i t) = b ↔ i.val ∈ J) := by
  classical
  constructor
  · rintro ⟨P, hP, V, hV, hRange, hFaces⟩
    have hVP : Set.range V ⊆ P := by
      intro x hx
      rw [hRange] at hx
      exact hx.subset (Set.mem_singleton x)
    have hPgen : P = convexHull ℝ (Set.range V) := by
      have h := (polytope_face_eq_convexHull_exposed_vertices d P hP).2 ⟨P, IsExposed.refl P⟩
      rw [← hRange, Set.inter_eq_right.mpr hVP] at h
      exact h
    have hPne : P.Nonempty := by
      obtain ⟨W, _, hWne, hPW⟩ := hP.1
      rw [hPW]
      exact hWne.convexHull
    have hVne : (Set.range V).Nonempty := convexHull_nonempty_iff.mp (hPgen ▸ hPne)
    obtain ⟨_, i, rfl⟩ := hVne
    refine ⟨V, lt_of_le_of_lt (Nat.zero_le i.val) i.isLt, hV, ?_, ?_, ?_, ?_⟩
    · rw [← affineSpan_convexHull, ← hPgen]
      exact hP.2
    · intro j
      apply (singleton_exposed_iff_strict_support_coefficients V P hPgen hV j).mp
      have hj : V j ∈ Set.range V := Set.mem_range_self j
      rw [hRange] at hj
      exact hj
    · intro L hL n hn
      obtain ⟨F, hF, hFne, hFP, hInc⟩ := (hFaces L.toFinset).mp ⟨L, hL, rfl⟩
      have hBounds := proper_face_incidence_bounds V P hPgen L.toFinset F hF hFne hFP hInc
      exact Finset.mem_range.mp (hBounds.1 (List.mem_toFinset.mpr hn))
    · intro J hJpow
      have hJ : J ⊆ Finset.range k := Finset.mem_powerset.mp hJpow
      constructor
      · intro hJS
        obtain ⟨F, hF, hFne, hFP, hInc⟩ := (hFaces J).mp hJS
        have hBounds := proper_face_incidence_bounds V P hPgen J F hF hFne hFP hInc
        refine ⟨hBounds.2.1, hBounds.2.2, ?_⟩
        exact (proper_face_incidence_iff_support_coefficients V P hPgen J hJ
          hBounds.2.1 hBounds.2.2).mp ⟨F, hF, hFne, hFP, hInc⟩
      · rintro ⟨hJne, hJproper, hCert⟩
        exact (hFaces J).mpr ((proper_face_incidence_iff_support_coefficients V P hPgen J
          hJ hJne hJproper).mpr hCert)
  · rintro ⟨V, hk, hV, hSpan, hVertices, hBound, hRows⟩
    let P := convexHull ℝ (Set.range V)
    have hP : IsDPolytope P := by
      refine ⟨⟨Set.range V, Set.finite_range V,
        ⟨V ⟨0, hk⟩, ⟨⟨0, hk⟩, rfl⟩⟩, rfl⟩, ?_⟩
      rw [affineSpan_convexHull]
      exact hSpan
    have hVertex (i : Fin k) : IsExposed ℝ P {V i} :=
      (singleton_exposed_iff_strict_support_coefficients V P rfl hV i).mpr (hVertices i)
    have hRange : Set.range V = {x | IsExposed ℝ P {x}} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact hVertex i
      · intro hx
        have hExt := exposedPoints_subset_extremePoints
          (mem_exposedPoints_iff_exposed_singleton.mpr hx)
        exact extremePoints_convexHull_subset hExt
    refine ⟨P, hP, V, hV, hRange, ?_⟩
    intro J
    by_cases hJ : J ⊆ Finset.range k
    · constructor
      · intro hJS
        obtain ⟨hJne, hJproper, hCert⟩ := (hRows J (Finset.mem_powerset.mpr hJ)).mp hJS
        exact (proper_face_incidence_iff_support_coefficients V P rfl J hJ hJne hJproper).mpr hCert
      · rintro ⟨F, hF, hFne, hFP, hInc⟩
        have hBounds := proper_face_incidence_bounds V P rfl J F hF hFne hFP hInc
        apply (hRows J (Finset.mem_powerset.mpr hJ)).mpr
        exact ⟨hBounds.2.1, hBounds.2.2,
          (proper_face_incidence_iff_support_coefficients V P rfl J hJ
            hBounds.2.1 hBounds.2.2).mp ⟨F, hF, hFne, hFP, hInc⟩⟩
    · constructor
      · rintro ⟨L, hLS, rfl⟩
        apply False.elim
        apply hJ
        intro n hn
        exact Finset.mem_range.mpr (hBound L hLS n (List.mem_toFinset.mp hn))
      · rintro ⟨F, hF, hFne, hFP, hInc⟩
        exact (hJ (proper_face_incidence_bounds V P rfl J F hF hFne hFP hInc).1).elim

end
end Grunbaum2003





namespace Grunbaum2003

/-- Empty-face membership is determined by the full face order alone. -/
theorem face_orderIso_empty_iff {d e : ℕ} {P : Set (Fin d → ℝ)}
    {Q : Set (Fin e → ℝ)} (φ : PolytopeFace P ≃o PolytopeFace Q)
    (F : PolytopeFace P) : (φ F).val = ∅ ↔ F.val = ∅ := by
  constructor
  · intro h
    have hle : φ F ≤ φ ⟨∅, isExposed_empty⟩ := by
      change (φ F).val ⊆ _
      rw [h]
      exact Set.empty_subset _
    exact Set.Subset.antisymm ((φ.le_iff_le).mp hle) (Set.empty_subset _)
  · intro h
    have hle : F ≤ φ.symm ⟨∅, isExposed_empty⟩ := by
      change F.val ⊆ _
      rw [h]
      exact Set.empty_subset _
    have hle' := φ.monotone hle
    rw [φ.apply_symm_apply] at hle'
    exact Set.Subset.antisymm hle' (Set.empty_subset _)

theorem face_orderIso_nonempty_iff {d e : ℕ} {P : Set (Fin d → ℝ)}
    {Q : Set (Fin e → ℝ)} (φ : PolytopeFace P ≃o PolytopeFace Q)
    (F : PolytopeFace P) : (φ F).val.Nonempty ↔ F.val.Nonempty := by
  simpa only [Set.nonempty_iff_ne_empty] using not_congr (face_orderIso_empty_iff φ F)

/-- The full face is also determined by the full face order alone. -/
theorem face_orderIso_full_iff {d e : ℕ} {P : Set (Fin d → ℝ)}
    {Q : Set (Fin e → ℝ)} (φ : PolytopeFace P ≃o PolytopeFace Q)
    (F : PolytopeFace P) : (φ F).val = Q ↔ F.val = P := by
  let topP : PolytopeFace P := ⟨P, IsExposed.refl P⟩
  let topQ : PolytopeFace Q := ⟨Q, IsExposed.refl Q⟩
  have hTop : φ topP = topQ := by
    apply le_antisymm
    · exact (φ topP).property.subset
    · have hle : φ.symm topQ ≤ topP := (φ.symm topQ).property.subset
      have hle' := φ.monotone hle
      rwa [φ.apply_symm_apply] at hle'
  constructor
  · intro h
    have hEq : φ F = topQ := Subtype.ext h
    exact congrArg Subtype.val (φ.injective (hEq.trans hTop.symm))
  · intro h
    have hEq : F = topP := Subtype.ext h
    rw [hEq, hTop]

/-- A full face-order isomorphism sends a singleton vertex face to a singleton.
The finite-hull face theorem supplies an incident vertex in the image; its
nonempty pullback inside a singleton must be the entire singleton. -/
theorem face_orderIso_singleton_image {d e : ℕ} {P : Set (Fin d → ℝ)}
    {Q : Set (Fin e → ℝ)} (hQ : IsDPolytope Q)
    (φ : PolytopeFace P ≃o PolytopeFace Q) (x : Fin d → ℝ)
    (hx : IsExposed ℝ P {x}) :
    ∃ y : Fin e → ℝ, IsExposed ℝ Q {y} ∧ (φ ⟨{x}, hx⟩).val = {y} := by
  let X : PolytopeFace P := ⟨{x}, hx⟩
  have hNe : (φ X).val.Nonempty :=
    (face_orderIso_nonempty_iff φ X).mpr (Set.singleton_nonempty x)
  have hHull := (polytope_face_eq_convexHull_exposed_vertices e Q hQ).2 (φ X)
  have hIncNe : ((φ X).val ∩ {y | IsExposed ℝ Q {y}}).Nonempty :=
    convexHull_nonempty_iff.mp (hHull ▸ hNe)
  obtain ⟨y, hyF, hy⟩ := hIncNe
  let Y : PolytopeFace Q := ⟨{y}, hy⟩
  have hYX : Y ≤ φ X := Set.singleton_subset_iff.mpr hyF
  have hPre : φ.symm Y ≤ X := by
    have h := φ.symm.monotone hYX
    rwa [φ.symm_apply_apply] at h
  have hPreNe : (φ.symm Y).val.Nonempty := by
    apply (face_orderIso_nonempty_iff φ (φ.symm Y)).mp
    rw [φ.apply_symm_apply]
    exact Set.singleton_nonempty y
  obtain ⟨z, hz⟩ := hPreNe
  have hzx : z = x := Set.mem_singleton_iff.mp (hPre hz)
  have hxPre : x ∈ (φ.symm Y).val := hzx ▸ hz
  have hPreEq : φ.symm Y = X := by
    apply Subtype.ext
    exact Set.Subset.antisymm hPre (Set.singleton_subset_iff.mpr hxPre)
  refine ⟨y, hy, ?_⟩
  have hImage : φ X = Y := by rw [← hPreEq, φ.apply_symm_apply]
  exact congrArg Subtype.val hImage

/-- Relative to the actual vertex enumerations of two realizations, every full
face-order isomorphism induces one permutation preserving every incidence. -/
theorem face_orderIso_vertex_permutation {d e k : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)} (hQ : IsDPolytope Q)
    (p : Fin k → Fin d → ℝ) (q : Fin k → Fin e → ℝ)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hpRange : Set.range p = {x | IsExposed ℝ P {x}})
    (hqRange : Set.range q = {x | IsExposed ℝ Q {x}})
    (φ : PolytopeFace P ≃o PolytopeFace Q) :
    ∃ σ : Equiv.Perm (Fin k), ∀ (F : PolytopeFace P) (i : Fin k),
      p i ∈ F.val ↔ q (σ i) ∈ (φ F).val := by
  classical
  have hpEx (i : Fin k) : IsExposed ℝ P {p i} := by
    have h : p i ∈ Set.range p := Set.mem_range_self i
    rw [hpRange] at h
    exact h
  have hMap : ∀ i : Fin k, ∃ j : Fin k, (φ ⟨{p i}, hpEx i⟩).val = {q j} := by
    intro i
    obtain ⟨y, hy, hImage⟩ := face_orderIso_singleton_image hQ φ (p i) (hpEx i)
    have hyRange : y ∈ Set.range q := hqRange.symm ▸ hy
    obtain ⟨j, rfl⟩ := hyRange
    exact ⟨j, hImage⟩
  choose f hf using hMap
  have hfInj : Function.Injective f := by
    intro i j hij
    apply hp
    have hImage : φ ⟨{p i}, hpEx i⟩ = φ ⟨{p j}, hpEx j⟩ := by
      apply Subtype.ext
      rw [hf i, hf j, hij]
    exact Set.singleton_injective (congrArg Subtype.val (φ.injective hImage))
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective f ⟨hfInj, Finite.surjective_of_injective hfInj⟩
  refine ⟨σ, ?_⟩
  intro F i
  have h := φ.map_rel_iff (a := ⟨{p i}, hpEx i⟩) (b := F)
  change (φ ⟨{p i}, hpEx i⟩).val ⊆ (φ F).val ↔ {p i} ⊆ F.val at h
  rw [hf i] at h
  dsimp only [σ, Equiv.ofBijective]
  simpa only [Set.singleton_subset_iff, Equiv.coe_fn_mk] using h.symm

end Grunbaum2003




namespace Grunbaum2003

/-- The actual face poset of a realization is exactly the finite row-incidence
code, completed by its empty and full faces. This is an order isomorphism of
point-set faces, not just an abstract type associated to the scheme. -/
theorem schemeRealizes_face_orderIso_code {d k : ℕ} {S : List (List ℕ)}
    {P : Set (Fin d → ℝ)} (h : SchemeRealizes k S P) :
    Nonempty (PolytopeFace P ≃o
      {J : Finset ℕ // J = ∅ ∨ J = Finset.range k ∨ ∃ L ∈ S, L.toFinset = J}) := by
  classical
  obtain ⟨hP, V, hV, hRange, hFaces⟩ := h
  let f : PolytopeFace P ↪o
      {J : Finset ℕ // J = ∅ ∨ J = Finset.range k ∨ ∃ L ∈ S, L.toFinset = J} := {
    toFun := fun F => ⟨schemeVertSet V F,
      (mem_range_schemeVertSet_iff V hRange hFaces _).mp ⟨F, rfl⟩⟩
    inj' := by
      intro F G hFG
      have hEq := congrArg Subtype.val hFG
      apply le_antisymm
      · exact (schemeVertSet_le_iff hP V hRange F G).mpr (le_of_eq hEq)
      · exact (schemeVertSet_le_iff hP V hRange G F).mpr (le_of_eq hEq.symm)
    map_rel_iff' := by
      intro F G
      exact (schemeVertSet_le_iff hP V hRange F G).symm }
  have hf : Function.Surjective f := by
    intro J
    obtain ⟨F, hF⟩ := (mem_range_schemeVertSet_iff V hRange hFaces J.val).mpr J.property
    exact ⟨F, Subtype.ext hF⟩
  exact ⟨OrderIso.ofSurjective f hf⟩

end Grunbaum2003




namespace Grunbaum2003

private theorem val_mem_finset_map {k : ℕ} (J : Finset (Fin k)) (i : Fin k) :
    i.val ∈ J.map Fin.valEmbedding ↔ i ∈ J := by
  constructor
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    exact (Fin.ext hji) ▸ hj
  · intro hi
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩

private theorem perm_mem_finset_map {k : ℕ} (σ : Equiv.Perm (Fin k))
    (J : Finset (Fin k)) (i : Fin k) : σ i ∈ J.map σ.toEmbedding ↔ i ∈ J := by
  constructor
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    exact (σ.injective hji) ▸ hj
  · intro hi
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩

private theorem val_map_subset_range {k : ℕ} (J : Finset (Fin k)) :
    J.map Fin.valEmbedding ⊆ Finset.range k := by
  intro n hn
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hn
  exact Finset.mem_range.mpr i.isLt

private theorem scheme_row_transport {d e k : ℕ}
    {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (p : Fin k → Fin d → ℝ) (q : Fin k → Fin e → ℝ)
    (S T : List (List ℕ)) (φ : PolytopeFace P ≃o PolytopeFace Q)
    (σ : Equiv.Perm (Fin k))
    (hInc : ∀ (F : PolytopeFace P) (i : Fin k), p i ∈ F.val ↔ q (σ i) ∈ (φ F).val)
    (hS : ∀ J : Finset ℕ, (∃ L ∈ S, L.toFinset = J) ↔
      ∃ F : Set (Fin d → ℝ), IsExposed ℝ P F ∧ F.Nonempty ∧ F ≠ P ∧
        (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ p i ∈ F})
    (hT : ∀ J : Finset ℕ, (∃ L ∈ T, L.toFinset = J) ↔
      ∃ G : Set (Fin e → ℝ), IsExposed ℝ Q G ∧ G.Nonempty ∧ G ≠ Q ∧
        (J : Set ℕ) = {n | ∃ i : Fin k, i.val = n ∧ q i ∈ G})
    (J : Finset (Fin k)) :
    (∃ L ∈ S, L.toFinset = J.map Fin.valEmbedding) →
      ∃ L ∈ T, L.toFinset = (J.map σ.toEmbedding).map Fin.valEmbedding := by
  intro hJS
  obtain ⟨F, hF, hFne, hFproper, hNat⟩ := (hS _).mp hJS
  let X : PolytopeFace P := ⟨F, hF⟩
  have hAt := (incidence_set_eq_iff p _ (val_map_subset_range J) F).mp hNat
  have hTarget : ∀ j : Fin k,
      q j ∈ (φ X).val ↔ j.val ∈ (J.map σ.toEmbedding).map Fin.valEmbedding := by
    intro j
    obtain ⟨i, rfl⟩ := σ.surjective j
    calc
      q (σ i) ∈ (φ X).val ↔ p i ∈ X.val := (hInc X i).symm
      _ ↔ i.val ∈ J.map Fin.valEmbedding := hAt i
      _ ↔ i ∈ J := val_mem_finset_map J i
      _ ↔ σ i ∈ J.map σ.toEmbedding := (perm_mem_finset_map σ J i).symm
      _ ↔ (σ i).val ∈ (J.map σ.toEmbedding).map Fin.valEmbedding :=
        (val_mem_finset_map (J.map σ.toEmbedding) (σ i)).symm
  apply (hT _).mpr
  exact ⟨(φ X).val, (φ X).property,
    (face_orderIso_nonempty_iff φ X).mpr hFne,
    fun h => hFproper ((face_orderIso_full_iff φ X).mp h),
    (incidence_set_eq_iff q _ (val_map_subset_range (J.map σ.toEmbedding)) (φ X).val).mpr hTarget⟩

/-- A full face-order isomorphism induces a permutation carrying exactly the
normalized vertex-face row family. The chosen permutation comes from the actual
isomorphism and its singleton images, including empty/full face handling. -/
theorem schemeRealizes_normalized_rows_permutation {d e k : ℕ}
    {S T : List (List ℕ)} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hSP : SchemeRealizes k S P) (hTQ : SchemeRealizes k T Q)
    (φ : PolytopeFace P ≃o PolytopeFace Q) :
    ∃ σ : Equiv.Perm (Fin k), ∀ J : Finset (Fin k),
      (∃ L ∈ S, L.toFinset = J.map Fin.valEmbedding) ↔
        (∃ L ∈ T, L.toFinset = (J.map σ.toEmbedding).map Fin.valEmbedding) := by
  classical
  obtain ⟨hP, p, hp, hpRange, hS⟩ := hSP
  obtain ⟨hQ, q, hq, hqRange, hT⟩ := hTQ
  obtain ⟨σ, hInc⟩ := face_orderIso_vertex_permutation hQ p q hp hq hpRange hqRange φ
  have hInv : ∀ (G : PolytopeFace Q) (j : Fin k),
      q j ∈ G.val ↔ p (σ.symm j) ∈ (φ.symm G).val := by
    intro G j
    simpa only [φ.apply_symm_apply, σ.apply_symm_apply] using
      (hInc (φ.symm G) (σ.symm j)).symm
  refine ⟨σ, ?_⟩
  intro J
  constructor
  · exact scheme_row_transport p q S T φ σ hInc hS hT J
  · intro hJT
    have hJS := scheme_row_transport q p T S φ.symm σ.symm hInv hT hS
      (J.map σ.toEmbedding) hJT
    have hBack : (J.map σ.toEmbedding).map σ.symm.toEmbedding = J := by
      ext i
      have h := (perm_mem_finset_map σ.symm (J.map σ.toEmbedding) (σ i)).trans
        (perm_mem_finset_map σ J i)
      simpa only [σ.symm_apply_apply] using h
    simpa only [hBack] using hJS

end Grunbaum2003




namespace Grunbaum2003

/-- Canonical ordered label rows for the full face code: normalized proper rows
plus empty and full labels, each drawn once from sublists of `range k`. -/
def incidenceRows (k : ℕ) (S : List (List ℕ)) : List (List ℕ) :=
  ((List.range k).sublists').filter (fun R =>
    R = [] ∨ R = List.range k ∨ ∃ L ∈ S, L.toFinset = R.toFinset)

/-- The explicit finite inclusion matrix of the normalized incidence code. -/
def incidenceMatrix (k : ℕ) (S : List (List ℕ)) : List (List Bool) :=
  (incidenceRows k S).map (fun A => (incidenceRows k S).map (fun B => decide (A ⊆ B)))

private theorem primrec_incidence_sublists {A : Type} [Primcodable A] :
    Primrec (@List.sublists' A) := by
  have hFold : Primrec (fun l : List A => l.foldr (fun a r => r ++ r.map (List.cons a)) [[]]) := by
    apply Primrec.list_foldr
      (h := fun (_ : List A) (p : A × List (List A)) => p.2 ++ p.2.map (List.cons p.1))
      Primrec.id (Primrec.const [[]])
    change Primrec (fun p : List A × (A × List (List A)) =>
      p.2.2 ++ p.2.2.map (List.cons p.2.1))
    exact Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  apply hFold.of_eq
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, List.sublists'_cons, ih]

private theorem primrec_nat_mem_list : PrimrecRel (fun n : ℕ => fun L : List ℕ => n ∈ L) :=
  PrimrecRel.of_eq Primrec.eq.exists_mem_list.swap (by intro n L; simp)

private theorem primrec_list_subset : PrimrecRel (fun A B : List ℕ => A ⊆ B) :=
  PrimrecRel.of_eq primrec_nat_mem_list.forall_mem_list (by intro A B; rfl)

private theorem primrec_row_set_eq : PrimrecRel (fun A B : List ℕ => A.toFinset = B.toFinset) := by
  have hBoth : PrimrecRel (fun A B : List ℕ => A ⊆ B ∧ B ⊆ A) := by
    change PrimrecPred (fun p : List ℕ × List ℕ => p.1 ⊆ p.2 ∧ p.2 ⊆ p.1)
    exact primrec_list_subset.and primrec_list_subset.swap
  apply PrimrecRel.of_eq hBoth
  intro A B
  constructor
  · rintro ⟨hAB, hBA⟩
    apply Finset.Subset.antisymm
    · intro n hn
      exact List.mem_toFinset.mpr (hAB (List.mem_toFinset.mp hn))
    · intro n hn
      exact List.mem_toFinset.mpr (hBA (List.mem_toFinset.mp hn))
  · intro h
    constructor
    · intro n hn
      have hn' : n ∈ A.toFinset := List.mem_toFinset.mpr hn
      rw [h] at hn'
      exact List.mem_toFinset.mp hn'
    · intro n hn
      have hn' : n ∈ B.toFinset := List.mem_toFinset.mpr hn
      rw [← h] at hn'
      exact List.mem_toFinset.mp hn'

theorem primrec_incidenceRows : Primrec₂ incidenceRows := by
  have hTest : PrimrecRel (fun p : ℕ × List (List ℕ) => fun R : List ℕ =>
      R = [] ∨ R = List.range p.1 ∨ ∃ L ∈ p.2, L.toFinset = R.toFinset) :=
    (Primrec.eq.comp Primrec.snd (Primrec.const [])).or
      ((Primrec.eq.comp Primrec.snd (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst))).or
        (primrec_row_set_eq.exists_mem_list.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  have hRows : Primrec (fun p : ℕ × List (List ℕ) => (List.range p.1).sublists') :=
    primrec_incidence_sublists.comp (Primrec.list_range.comp Primrec.fst)
  exact (hTest.swap.listFilter.comp hRows Primrec.id).to₂

theorem primrec_incidenceMatrix : Primrec₂ incidenceMatrix := by
  have hRows : Primrec (fun p : ℕ × List (List ℕ) => incidenceRows p.1 p.2) := primrec_incidenceRows
  have hInner : Primrec (fun t : (ℕ × List (List ℕ)) × List ℕ =>
      (incidenceRows t.1.1 t.1.2).map (fun B => decide (t.2 ⊆ B))) :=
    Primrec.list_map (hRows.comp Primrec.fst)
      (primrec_list_subset.decide.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_map hRows hInner.to₂).to₂

theorem mem_incidenceRows_iff (k : ℕ) (S : List (List ℕ)) (R : List ℕ) :
    R ∈ incidenceRows k S ↔ R.Sublist (List.range k) ∧
      (R = [] ∨ R = List.range k ∨ ∃ L ∈ S, L.toFinset = R.toFinset) := by
  simp only [incidenceRows, List.mem_filter, List.mem_sublists', decide_eq_true_eq]

theorem incidenceRows_nodup (k : ℕ) (S : List (List ℕ)) : (incidenceRows k S).Nodup :=
  (List.nodup_sublists'.mpr (List.nodup_range : (List.range k).Nodup)).filter _

/-- Canonical row positions really denote distinct label sets. -/
theorem incidenceRows_toFinset_injective (k : ℕ) (S : List (List ℕ))
    {R T : List ℕ} (hR : R ∈ incidenceRows k S) (hT : T ∈ incidenceRows k S)
    (hEq : R.toFinset = T.toFinset) : R = T := by
  have hRs := ((mem_incidenceRows_iff k S R).mp hR).1
  have hTs := ((mem_incidenceRows_iff k S T).mp hT).1
  have hRn : R.Nodup := (List.nodup_range : (List.range k).Nodup).sublist hRs
  have hTn : T.Nodup := (List.nodup_range : (List.range k).Nodup).sublist hTs
  have hPerm : R.Perm T := by
    have h := List.toFinset_eq_iff_perm_dedup.mp hEq
    simpa only [hRn.dedup, hTn.dedup] using h
  exact ((List.nodup_range : (List.range k).Nodup).perm_iff_eq_of_sublist hRs hTs).mp hPerm

/-- Every realized scheme has bounded row entries. -/
theorem schemeRealizes_rows_bounded {d k : ℕ} {S : List (List ℕ)}
    {P : Set (Fin d → ℝ)} (h : SchemeRealizes k S P) :
    ∀ L ∈ S, ∀ n ∈ L, n < k := by
  obtain ⟨hP, V, hV, hRange, hFaces⟩ := h
  intro L hL n hn
  obtain ⟨F, hF, hFne, hFP, hInc⟩ := (hFaces L.toFinset).mp ⟨L, hL, rfl⟩
  have hn' : n ∈ (L.toFinset : Set ℕ) := List.mem_toFinset.mpr hn
  rw [hInc] at hn'
  obtain ⟨i, hi, _⟩ := hn'
  exact hi ▸ i.isLt

/-- The canonical list includes exactly the completed scheme's label sets. -/
theorem incidenceRows_toFinset_iff (k : ℕ) (S : List (List ℕ))
    (hBound : ∀ L ∈ S, ∀ n ∈ L, n < k) (J : Finset ℕ) :
    (∃ R ∈ incidenceRows k S, R.toFinset = J) ↔
      J = ∅ ∨ J = Finset.range k ∨ ∃ L ∈ S, L.toFinset = J := by
  constructor
  · rintro ⟨R, hR, rfl⟩
    rcases ((mem_incidenceRows_iff k S R).mp hR).2 with hnil | hfull | hrow
    · left
      rw [hnil]
      rfl
    · right; left
      rw [hfull]
      exact List.toFinset_range k
    · exact Or.inr (Or.inr hrow)
  · rintro (rfl | rfl | ⟨L, hL, rfl⟩)
    · refine ⟨[], (mem_incidenceRows_iff k S []).mpr ⟨List.nil_sublist _, Or.inl rfl⟩, rfl⟩
    · refine ⟨List.range k, (mem_incidenceRows_iff k S _).mpr ⟨List.Sublist.refl _, Or.inr (Or.inl rfl)⟩,
        List.toFinset_range k⟩
    · let R := (List.range k).filter (fun n => n ∈ L)
      have hEq : R.toFinset = L.toFinset := by
        ext n
        simp only [List.mem_toFinset, R, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨And.right, fun hn => ⟨hBound L hL n hn, hn⟩⟩
      refine ⟨R, (mem_incidenceRows_iff k S R).mpr ⟨List.filter_sublist,
        Or.inr (Or.inr ⟨L, hL, hEq.symm⟩)⟩, hEq⟩

end Grunbaum2003




namespace Grunbaum2003

private theorem list_subset_iff_finset_subset (A B : List ℕ) :
    A ⊆ B ↔ A.toFinset ⊆ B.toFinset := by
  constructor
  · intro h n hn
    exact List.mem_toFinset.mpr (h (List.mem_toFinset.mp hn))
  · intro h n hn
    exact List.mem_toFinset.mp (h (List.mem_toFinset.mpr hn))

/-- Canonical row positions enumerate the actual point-set faces bijectively,
with their inclusion relation. No order on the numeric indices is substituted
for the face relation. -/
theorem schemeRealizes_rows_equiv_faces {d k : ℕ} {S : List (List ℕ)}
    {P : Set (Fin d → ℝ)} (hP : SchemeRealizes k S P) :
    ∃ e : Fin (incidenceRows k S).length ≃ PolytopeFace P,
      ∀ i j, ((incidenceRows k S).get i ⊆ (incidenceRows k S).get j) ↔ e i ≤ e j := by
  classical
  let rows := incidenceRows k S
  let C := {J : Finset ℕ // J = ∅ ∨ J = Finset.range k ∨ ∃ L ∈ S, L.toFinset = J}
  have hBound := schemeRealizes_rows_bounded hP
  let f : Fin rows.length → C := fun i => ⟨(rows.get i).toFinset,
    (incidenceRows_toFinset_iff k S hBound _).mp ⟨rows.get i, List.get_mem rows i, rfl⟩⟩
  have hfInj : Function.Injective f := by
    intro i j hij
    apply (incidenceRows_nodup k S).injective_get
    exact incidenceRows_toFinset_injective k S (List.get_mem rows i) (List.get_mem rows j)
      (congrArg Subtype.val hij)
  have hfSurj : Function.Surjective f := by
    intro J
    obtain ⟨R, hR, hSet⟩ := (incidenceRows_toFinset_iff k S hBound J.val).mpr J.property
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hR
    refine ⟨i, Subtype.ext ?_⟩
    change (rows.get i).toFinset = J.val
    rw [hi]
    exact hSet
  let ec : Fin rows.length ≃ C := Equiv.ofBijective f ⟨hfInj, hfSurj⟩
  obtain ⟨Φ⟩ := schemeRealizes_face_orderIso_code hP
  let e : Fin rows.length ≃ PolytopeFace P := ec.trans Φ.symm.toEquiv
  have he (i : Fin rows.length) : (Φ (e i)).val = (rows.get i).toFinset := by
    have hFace : Φ (e i) = ec i := by
      change Φ (Φ.symm (ec i)) = ec i
      exact Φ.apply_symm_apply (ec i)
    rw [hFace]
    exact congrArg Subtype.val (congrFun (Equiv.coe_ofBijective f ⟨hfInj, hfSurj⟩) i)
  refine ⟨e, ?_⟩
  intro i j
  rw [list_subset_iff_finset_subset]
  have h := Φ.le_iff_le (x := e i) (y := e j)
  change (Φ (e i)).val ⊆ (Φ (e j)).val ↔ e i ≤ e j at h
  rw [he i, he j] at h
  exact h

@[simp] theorem incidenceMatrix_length (k : ℕ) (S : List (List ℕ)) :
    (incidenceMatrix k S).length = (incidenceRows k S).length := by
  simp only [incidenceMatrix, List.length_map]

/-- The matrix reader agrees exactly with inclusion of the indexed canonical
rows; absent-entry defaults are never used on these square matrices. -/
theorem incidenceMatrix_entry (k : ℕ) (S : List (List ℕ))
    (i j : Fin (incidenceMatrix k S).length) :
    (((incidenceMatrix k S).get i)[j.val]?).getD false =
      decide ((incidenceRows k S).get (finCongr (incidenceMatrix_length k S) i) ⊆
        (incidenceRows k S).get (finCongr (incidenceMatrix_length k S) j)) := by
  have hi : i.val < (incidenceRows k S).length := by
    simpa only [incidenceMatrix_length] using i.isLt
  have hj : j.val < (incidenceRows k S).length := by
    simpa only [incidenceMatrix_length] using j.isLt
  change (((incidenceRows k S).map (fun A =>
      (incidenceRows k S).map (fun B => decide (A ⊆ B))))[i.val]'(by
        simpa only [List.length_map] using hi))[j.val]?.getD false =
    decide ((incidenceRows k S)[i.val]'hi ⊆ (incidenceRows k S)[j.val]'hj)
  rw [List.getElem_map, List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

/-- The actual finite inclusion matrix presents the actual full face poset.
This is the semantic input consumed by the finite relation-isomorphism checker. -/
theorem schemeRealizes_matrix_equiv_faces {d k : ℕ} {S : List (List ℕ)}
    {P : Set (Fin d → ℝ)} (hP : SchemeRealizes k S P) :
    ∃ e : Fin (incidenceMatrix k S).length ≃ PolytopeFace P,
      ∀ i j, (((incidenceMatrix k S).get i)[j.val]?).getD false = true ↔ e i ≤ e j := by
  obtain ⟨er, hr⟩ := schemeRealizes_rows_equiv_faces hP
  let ec := finCongr (incidenceMatrix_length k S)
  refine ⟨ec.trans er, ?_⟩
  intro i j
  rw [incidenceMatrix_entry, decide_eq_true_eq]
  simpa only [Equiv.trans_apply] using hr (ec i) (ec j)

end Grunbaum2003




namespace Grunbaum2003

/-- Any scheme realized by Q is realized by every polytope with an isomorphic
full face poset. The vertex enumeration is transported by the permutation
induced by that particular order isomorphism. -/
theorem schemeRealizes_transfer_of_face_orderIso {d e k : ℕ}
    {S T : List (List ℕ)} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hSP : SchemeRealizes k S P) (hTQ : SchemeRealizes k T Q)
    (φ : PolytopeFace P ≃o PolytopeFace Q) : SchemeRealizes k T P := by
  classical
  obtain ⟨hP, p, hp, hpRange, hSFaces⟩ := hSP
  obtain ⟨hQ, q, hq, hqRange, hTFaces⟩ := hTQ
  obtain ⟨σ, hInc⟩ := face_orderIso_vertex_permutation hQ p q hp hq hpRange hqRange φ
  let v : Fin k → Fin d → ℝ := p ∘ σ.symm
  have hv : Function.Injective v := hp.comp σ.symm.injective
  have hvRange : Set.range v = {x | IsExposed ℝ P {x}} := by
    rw [show Set.range v = Set.range p by
      change Set.range (p ∘ σ.symm) = Set.range p
      rw [Set.range_comp, σ.symm.surjective.range_eq, Set.image_univ]]
    exact hpRange
  have hInc' (F : PolytopeFace P) (j : Fin k) :
      v j ∈ F.val ↔ q j ∈ (φ F).val := by
    simpa only [v, Function.comp_apply, σ.apply_symm_apply] using hInc F (σ.symm j)
  have hLabels (F : PolytopeFace P) :
      {n : ℕ | ∃ j : Fin k, j.val = n ∧ v j ∈ F.val} =
        {n : ℕ | ∃ j : Fin k, j.val = n ∧ q j ∈ (φ F).val} := by
    ext n
    change (∃ j : Fin k, j.val = n ∧ v j ∈ F.val) ↔
      (∃ j : Fin k, j.val = n ∧ q j ∈ (φ F).val)
    simp_rw [hInc' F]
  refine ⟨hP, v, hv, hvRange, ?_⟩
  intro J
  constructor
  · intro hJT
    obtain ⟨G, hG, hGne, hGproper, hJ⟩ := (hTFaces J).mp hJT
    let F : PolytopeFace P := φ.symm ⟨G, hG⟩
    have hFne : F.val.Nonempty := by
      apply (face_orderIso_nonempty_iff φ F).mp
      simpa only [F, φ.apply_symm_apply] using hGne
    have hFproper : F.val ≠ P := by
      intro hFull
      have h := (face_orderIso_full_iff φ F).mpr hFull
      exact hGproper (by simpa only [F, φ.apply_symm_apply] using h)
    refine ⟨F.val, F.property, hFne, hFproper, ?_⟩
    have h : {n : ℕ | ∃ j : Fin k, j.val = n ∧ v j ∈ F.val} =
        {n : ℕ | ∃ j : Fin k, j.val = n ∧ q j ∈ G} := by
      simpa only [F, φ.apply_symm_apply] using hLabels F
    exact hJ.trans h.symm
  · rintro ⟨F, hF, hFne, hFproper, hJ⟩
    let X : PolytopeFace P := ⟨F, hF⟩
    have hGne : (φ X).val.Nonempty := (face_orderIso_nonempty_iff φ X).mpr hFne
    have hGproper : (φ X).val ≠ Q :=
      fun h => hFproper ((face_orderIso_full_iff φ X).mp h)
    exact (hTFaces J).mpr ⟨(φ X).val, (φ X).property, hGne, hGproper,
      hJ.trans (hLabels X)⟩

/-- Isomorphism of two realizing face posets transports a representative to
EVERY realization of the original scheme, as required by the existing child. -/
theorem schemeRealizes_transfer_all_of_face_orderIso {d e r k : ℕ}
    {S T : List (List ℕ)} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hSP : SchemeRealizes k S P) (hTQ : SchemeRealizes k T Q)
    (φ : PolytopeFace P ≃o PolytopeFace Q)
    {R : Set (Fin r → ℝ)} (hSR : SchemeRealizes k S R) : SchemeRealizes k T R := by
  obtain ⟨ψ⟩ := schemeRealizes_unique_combinatorial_type r d k S R P hSR hSP
  exact schemeRealizes_transfer_of_face_orderIso hSR hTQ (ψ.trans φ)

end Grunbaum2003




theorem bounded_scheme_has_candidate (k : ℕ) (S : List (List ℕ))
    (hBound : ∀ L ∈ S, ∀ n ∈ L, n < k) :
    ∃ T ∈ ((List.range k).sublists').sublists',
      ∀ J : Finset ℕ,
        (∃ L ∈ T, L.toFinset = J) ↔ (∃ L ∈ S, L.toFinset = J) := by
  classical
  let rows := (List.range k).sublists'
  let T := rows.filter (fun R => ∃ L ∈ S, L.toFinset = R.toFinset)
  refine ⟨T, List.mem_sublists'.mpr (List.filter_sublist), ?_⟩
  intro J
  constructor
  · rintro ⟨L, hL, rfl⟩
    simpa only [T, List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hL).2
  · rintro ⟨L, hL, rfl⟩
    let R := (List.range k).filter (fun n => n ∈ L)
    have hR : R.toFinset = L.toFinset := by
      ext n
      simp only [List.mem_toFinset, R, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨And.right, fun hn => ⟨hBound L hL n hn, hn⟩⟩
    refine ⟨R, List.mem_filter.mpr ⟨?_, by simpa only [decide_eq_true_eq] using (show ∃ L₀ ∈ S, L₀.toFinset = R.toFinset from ⟨L, hL, hR.symm⟩)⟩, hR⟩
    exact List.mem_sublists'.mpr (List.filter_sublist)

theorem primrec_sublists' {α : Type} [Primcodable α] :
    Primrec (@List.sublists' α) := by
  have hFold : Primrec (fun l : List α =>
      l.foldr (fun a r => r ++ r.map (List.cons a)) [[]]) := by
    apply Primrec.list_foldr (h := fun (_ : List α) (p : α × List (List α)) => p.2 ++ p.2.map (List.cons p.1)) Primrec.id (Primrec.const [[]])
    change Primrec (fun p : List α × (α × List (List α)) =>
      p.2.2 ++ p.2.2.map (List.cons p.2.1))
    exact Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd))
  apply hFold.of_eq
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, List.sublists'_cons, ih]

theorem primrec_scheme_candidates : Primrec (fun k : ℕ => ((List.range k).sublists').sublists') :=
  primrec_sublists'.comp (primrec_sublists'.comp Primrec.list_range)


namespace Grunbaum2003

theorem schemeRealizes_has_candidate {d k : ℕ} {S : List (List ℕ)}
    {P : Set (Fin d → ℝ)} (h : SchemeRealizes k S P) :
    ∃ T ∈ ((List.range k).sublists').sublists',
      ∀ Q : Set (Fin d → ℝ), SchemeRealizes k S Q → SchemeRealizes k T Q := by
  have hBound : ∀ L ∈ S, ∀ n ∈ L, n < k := by
    obtain ⟨hP, V, hV, hRange, hFaces⟩ := h
    intro L hL n hn
    obtain ⟨F, hF, hFne, hFP, hInc⟩ := (hFaces L.toFinset).mp ⟨L, hL, rfl⟩
    have hn' : n ∈ (L.toFinset : Set ℕ) := List.mem_toFinset.mpr hn
    rw [hInc] at hn'
    obtain ⟨i, hi, _⟩ := hn'
    exact hi ▸ i.isLt
  obtain ⟨T, hT, hRows⟩ := bounded_scheme_has_candidate k S hBound
  refine ⟨T, hT, ?_⟩
  rintro Q ⟨hQ, V, hV, hRange, hFaces⟩
  exact ⟨hQ, V, hV, hRange, fun J => (hRows J).trans (hFaces J)⟩

end Grunbaum2003




namespace Grunbaum2003

/-- A finite exhaustive check of isomorphism of the completed incidence codes. -/
def schemeTypeIsoCheck (k : ℕ) (S T : List (List ℕ)) : Bool :=
  finiteRelationIsoCheck (incidenceMatrix k S) (incidenceMatrix k T)

theorem primrec_schemeTypeIsoCheck :
    Primrec (fun t : (ℕ × List (List ℕ)) × List (List ℕ) =>
      schemeTypeIsoCheck t.1.1 t.1.2 t.2) :=
  primrec_finiteRelationIsoCheck.comp
    (primrec_incidenceMatrix.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (primrec_incidenceMatrix.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

/-- This equivalence holds on every code, including malformed/unrealizable
ones; the relation checker is an exact finite binary-relation isomorphism test. -/
theorem schemeTypeIsoCheck_equivalence (k : ℕ) :
    Equivalence (fun S T => schemeTypeIsoCheck k S T = true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    apply (finiteRelationIsoCheck_eq_true_iff _ _).mpr
    exact ⟨Equiv.refl _, fun _ _ => rfl⟩
  · intro S T h
    obtain ⟨σ, hσ⟩ := (finiteRelationIsoCheck_eq_true_iff _ _).mp h
    apply (finiteRelationIsoCheck_eq_true_iff _ _).mpr
    refine ⟨σ.symm, ?_⟩
    intro i j
    simpa only [σ.apply_symm_apply] using (hσ (σ.symm i) (σ.symm j)).symm
  · intro S T U hST hTU
    obtain ⟨σ, hσ⟩ := (finiteRelationIsoCheck_eq_true_iff _ _).mp hST
    obtain ⟨τ, hτ⟩ := (finiteRelationIsoCheck_eq_true_iff _ _).mp hTU
    apply (finiteRelationIsoCheck_eq_true_iff _ _).mpr
    refine ⟨σ.trans τ, ?_⟩
    intro i j
    simpa only [Equiv.trans_apply] using (hσ i j).trans (hτ (σ i) (σ j))

/-- On actual realizations, the computed finite-code relation is exactly
isomorphism of the full point-set face posets. -/
theorem schemeTypeIsoCheck_iff_face_orderIso {d e k : ℕ}
    {S T : List (List ℕ)} {P : Set (Fin d → ℝ)} {Q : Set (Fin e → ℝ)}
    (hSP : SchemeRealizes k S P) (hTQ : SchemeRealizes k T Q) :
    schemeTypeIsoCheck k S T = true ↔ Nonempty (PolytopeFace P ≃o PolytopeFace Q) := by
  classical
  obtain ⟨α, hα⟩ := schemeRealizes_matrix_equiv_faces hSP
  obtain ⟨β, hβ⟩ := schemeRealizes_matrix_equiv_faces hTQ
  rw [schemeTypeIsoCheck, finiteRelationIsoCheck_eq_true_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    let ePQ : PolytopeFace P ≃ PolytopeFace Q := α.symm.trans (σ.trans β)
    refine ⟨{ toEquiv := ePQ, map_rel_iff' := ?_ }⟩
    intro F G
    change ePQ F ≤ ePQ G ↔ F ≤ G
    calc
      ePQ F ≤ ePQ G ↔
          (((incidenceMatrix k T).get (σ (α.symm F)))[(σ (α.symm G)).val]?).getD false = true := by
        simpa only [ePQ, Equiv.trans_apply] using (hβ (σ (α.symm F)) (σ (α.symm G))).symm
      _ ↔ (((incidenceMatrix k S).get (α.symm F))[(α.symm G).val]?).getD false = true := by
        rw [hσ (α.symm F) (α.symm G)]
      _ ↔ F ≤ G := by simpa only [α.apply_symm_apply] using hα (α.symm F) (α.symm G)
  · rintro ⟨φ⟩
    let σ := α.trans (φ.toEquiv.trans β.symm)
    refine ⟨σ, ?_⟩
    intro i j
    apply Bool.eq_iff_iff.mpr
    calc
      (((incidenceMatrix k S).get i)[j.val]?).getD false = true ↔ α i ≤ α j := hα i j
      _ ↔ φ (α i) ≤ φ (α j) := φ.le_iff_le.symm
      _ ↔ β (σ i) ≤ β (σ j) := by
        change (φ (α i) ≤ φ (α j)) ↔
          β (β.symm (φ (α i))) ≤ β (β.symm (φ (α j)))
        rw [β.apply_symm_apply, β.apply_symm_apply]
      _ ↔ (((incidenceMatrix k T).get (σ i))[(σ j).val]?).getD false = true := (hβ (σ i) (σ j)).symm

/-- Effective class pruning is uniform in the vertex count. -/
theorem primrec_scheme_class_prune :
    Primrec₂ (fun k (L : List (List (List ℕ))) =>
      L.pwFilter (fun S T => ¬ schemeTypeIsoCheck k S T = true)) := by
  have hR : PrimrecRel (fun p : ℕ × List (List ℕ) => fun T =>
      ¬ schemeTypeIsoCheck p.1 p.2 T = true) :=
    (Primrec.eq.comp primrec_schemeTypeIsoCheck (Primrec.const true)).not
  exact primrec_parameterized_pwFilter hR

end Grunbaum2003




namespace Grunbaum2003

/-- The concrete program: filter the explicit finite candidate list by D, then
keep one representative of each computed full-face-poset isomorphism class.
D is an explicit external algorithm parameter, not a classical realization test. -/
private def representativeList (D : ℕ → ℕ → List (List ℕ) → Bool) (d k : ℕ) :
    List (List (List ℕ)) :=
  ((((List.range k).sublists').sublists').filter (D d k)).pwFilter
    (fun S T => ¬ schemeTypeIsoCheck k S T = true)

/-- Conditional closure of the EXISTING representatives interface. The only
unconstructed input is the uniform computable realizability decision function;
all finite coding, equivalence checking, pruning, and geometric transport are
provided by the proof. This is not an unconditional proof of either mission. -/
theorem exists_computable_scheme_representatives_of_realizability_decider
    (D : ℕ → ℕ → List (List ℕ) → Bool)
    (hDComp : Computable (fun z : (ℕ × ℕ) × List (List ℕ) => D z.1.1 z.1.2 z.2))
    (hDCorrect : ∀ d k S, D d k S = true ↔
      ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) :
    ∃ E : ℕ → ℕ → List (List (List ℕ)), Computable₂ E ∧
      ∀ d k : ℕ,
        (∀ S ∈ E d k, ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P) ∧
        (∀ S₀ : List (List ℕ), (∃ P₀ : Set (Fin d → ℝ), SchemeRealizes k S₀ P₀) →
          ∃ S ∈ E d k, ∀ P : Set (Fin d → ℝ),
            SchemeRealizes k S₀ P → SchemeRealizes k S P) ∧
        (∀ i j : Fin (E d k).length, ∀ P Q : Set (Fin d → ℝ),
          SchemeRealizes k ((E d k).get i) P →
          SchemeRealizes k ((E d k).get j) Q →
          Nonempty (PolytopeFace P ≃o PolytopeFace Q) → i = j) := by
  have hCandidates : Computable (fun p : ℕ × ℕ => ((List.range p.2).sublists').sublists') :=
    primrec_scheme_candidates.to_comp.comp Computable.snd
  have hFiltered : Computable (fun p : ℕ × ℕ =>
      (((List.range p.2).sublists').sublists').filter (D p.1 p.2)) :=
    computable_list_filter hCandidates hDComp
  have hE : Computable₂ (representativeList D) :=
    primrec_scheme_class_prune.to_comp.comp Computable.snd hFiltered
  refine ⟨representativeList D, hE, ?_⟩
  intro d k
  let L := (((List.range k).sublists').sublists').filter (D d k)
  have hSub : representativeList D d k ⊆ L := List.pwFilter_subset L
  have hSound : ∀ S ∈ representativeList D d k,
      ∃ P : Set (Fin d → ℝ), SchemeRealizes k S P := by
    intro S hS
    exact (hDCorrect d k S).mp (List.mem_filter.mp (hSub hS)).2
  refine ⟨hSound, ?_, ?_⟩
  · rintro S₀ ⟨P₀, hS₀⟩
    obtain ⟨T, hTmem, hTAll⟩ := schemeRealizes_has_candidate hS₀
    have hT₀ : SchemeRealizes k T P₀ := hTAll P₀ hS₀
    have hTL : T ∈ L := List.mem_filter.mpr
      ⟨hTmem, (hDCorrect d k T).mpr ⟨P₀, hT₀⟩⟩
    obtain ⟨U, hU, hTU⟩ := (pwFilter_complement_covers (schemeTypeIsoCheck_equivalence k) L).2 T hTL
    have hUE : U ∈ representativeList D d k := hU
    obtain ⟨Q, hUQ⟩ := hSound U hUE
    obtain ⟨φ⟩ := (schemeTypeIsoCheck_iff_face_orderIso hT₀ hUQ).mp hTU
    refine ⟨U, hUE, ?_⟩
    intro P hS₀P
    exact schemeRealizes_transfer_all_of_face_orderIso hT₀ hUQ φ (hTAll P hS₀P)
  · intro i j P Q hP hQ hIso
    have hSame := (schemeTypeIsoCheck_iff_face_orderIso hP hQ).mpr hIso
    exact pwFilter_complement_unique_indices (schemeTypeIsoCheck_equivalence k) L i j hSame

end Grunbaum2003


theorem solution
    (D : ℕ → ℕ → List (List ℕ) → Bool)
    (hDComp : Computable (fun z : (ℕ × ℕ) × List (List ℕ) => D z.1.1 z.1.2 z.2))
    (hDCorrect : ∀ d k S, D d k S = true ↔
      ∃ P : Set (Fin d → ℝ), Grunbaum2003.SchemeRealizes k S P) :
    ∃ E : ℕ → ℕ → List (List (List ℕ)), Computable₂ E ∧
      ∀ d k : ℕ,
        (∀ S ∈ E d k, ∃ P : Set (Fin d → ℝ), Grunbaum2003.SchemeRealizes k S P) ∧
        (∀ S₀ : List (List ℕ), (∃ P₀ : Set (Fin d → ℝ), Grunbaum2003.SchemeRealizes k S₀ P₀) →
          ∃ S ∈ E d k, ∀ P : Set (Fin d → ℝ),
            Grunbaum2003.SchemeRealizes k S₀ P → Grunbaum2003.SchemeRealizes k S P) ∧
        (∀ i j : Fin (E d k).length, ∀ P Q : Set (Fin d → ℝ),
          Grunbaum2003.SchemeRealizes k ((E d k).get i) P →
          Grunbaum2003.SchemeRealizes k ((E d k).get j) Q →
          Nonempty (Grunbaum2003.PolytopeFace P ≃o Grunbaum2003.PolytopeFace Q) → i = j) :=
  Grunbaum2003.exists_computable_scheme_representatives_of_realizability_decider D hDComp hDCorrect
