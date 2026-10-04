-- Prove2me | solution 1 for MSKleene.collapse_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-08T15:22:49.208974+00:00
-- url     : https://prove2.me/submissions/0816facd-f993-4106-9d5a-fb2514fecd48

import Definitions.Def_MSKleene_SubstFam
import Definitions.Def_MSKleene_Subterm

open MSKleene
open Classical

private theorem ofArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (ts : TermVec sig X w), TermVec.ofArgs (TermVec.toArgs ts) = ts
  | [], .nil => rfl
  | _ :: _, .cons t ts => congrArg (TermVec.cons t) (ofArgs_toArgs ts)

private theorem hom_app {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {w : List S} {s : S}
    (σ : sig w s) (ts : TermVec sig X w) :
    g.toFun s (Term.app σ ts) = A.op σ (Args.map g.toFun (TermVec.toArgs ts)) := by
  calc
    g.toFun s (Term.app σ ts) =
        g.toFun s ((freeAlgebra sig X).op σ (TermVec.toArgs ts)) := by
          simp only [freeAlgebra]
          rw [ofArgs_toArgs]
    _ = A.op σ (Args.map g.toFun (TermVec.toArgs ts)) :=
      g.map_op σ (TermVec.toArgs ts)

mutual
noncomputable def collapseTerm {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    {s : S} → Term sig X s → Term sig X s
  | s, .var x =>
      if h : s = u then
        if g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z) then
          h.symm ▸ Term.var z
        else Term.var x
      else Term.var x
  | s, .app σ ts =>
      if h : s = u then
        if g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z) then
          h.symm ▸ Term.var z
        else Term.app σ (collapseVec g z ts)
      else Term.app σ (collapseVec g z ts)
noncomputable def collapseVec {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    {w : List S} → TermVec sig X w → TermVec sig X w
  | [], .nil => .nil
  | _ :: _, .cons t ts => .cons (collapseTerm g z t) (collapseVec g z ts)
end

private theorem collapse_term_preserves_hom {S : Type} {sig : Signature S}
    {X : SSet S} {A : Algebra sig} (g : Hom (freeAlgebra sig X) A)
    {u : S} (z : X u) :
    ∀ {s : S} (t : Term sig X s),
      g.toFun s (collapseTerm g z t) = g.toFun s t :=
  @Term.rec _ _ _
    (motive_1 := fun s t => g.toFun s (collapseTerm g z t) = g.toFun s t)
    (motive_2 := fun w ts =>
      Args.map g.toFun (TermVec.toArgs (collapseVec g z ts)) =
        Args.map g.toFun (TermVec.toArgs ts))
    (fun {s} x => by
      rw [collapseTerm]
      split
      next h =>
        split
        next heq =>
          cases h
          exact heq.symm
        next _ => rfl
      next _ => rfl)
    (fun {w} {s} σ ts ih => by
      rw [collapseTerm]
      split
      next h =>
        split
        next heq =>
          cases h
          exact heq.symm
        next _ =>
          rw [hom_app, hom_app]
          exact congrArg (A.op σ) ih
      next _ =>
        rw [hom_app, hom_app]
        exact congrArg (A.op σ) ih)
    rfl
    (fun _ _ iht ihv => congrArg₂ Prod.mk iht ihv)

private theorem collapse_vec_preserves_hom {S : Type} {sig : Signature S}
    {X : SSet S} {A : Algebra sig} (g : Hom (freeAlgebra sig X) A)
    {u : S} (z : X u) :
    ∀ {w : List S} (ts : TermVec sig X w),
      Args.map g.toFun (TermVec.toArgs (collapseVec g z ts)) =
        Args.map g.toFun (TermVec.toArgs ts) :=
  @TermVec.rec _ _ _
    (motive_1 := fun s t => g.toFun s (collapseTerm g z t) = g.toFun s t)
    (motive_2 := fun w ts =>
      Args.map g.toFun (TermVec.toArgs (collapseVec g z ts)) =
        Args.map g.toFun (TermVec.toArgs ts))
    (fun {s} x => by
      rw [collapseTerm]
      split
      next h =>
        split
        next heq =>
          cases h
          exact heq.symm
        next _ => rfl
      next _ => rfl)
    (fun {w} {s} σ ts ih => by
      rw [collapseTerm]
      split
      next h =>
        split
        next heq =>
          cases h
          exact heq.symm
        next _ =>
          rw [hom_app, hom_app]
          exact congrArg (A.op σ) ih
      next _ =>
        rw [hom_app, hom_app]
        exact congrArg (A.op σ) ih)
    rfl
    (fun _ _ iht ihv => congrArg₂ Prod.mk iht ihv)

theorem collapse_preserves_hom {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    (∀ {s : S} (t : Term sig X s),
        g.toFun s (collapseTerm g z t) = g.toFun s t) ∧
    (∀ {w : List S} (ts : TermVec sig X w),
        Args.map g.toFun (TermVec.toArgs (collapseVec g z ts)) =
          Args.map g.toFun (TermVec.toArgs ts)) :=
  ⟨collapse_term_preserves_hom g z, collapse_vec_preserves_hom g z⟩

private theorem min_var {S : Type} {sig : Signature S} {X : SSet S}
    {s : S} (x : X s) : Min (⟨s, Term.var x⟩ : STerm sig X) := by
  intro a ha
  rcases ha with ⟨w, σ, ts, heq, _⟩
  cases heq

/-- A nonminimal node surviving the collapse cannot have the distinguished
sort and the distinguished homomorphic value. -/
theorem collapse_nonminimal_not_target {S : Type} {sig : Signature S}
    {X : SSet S} {A : Algebra sig} (g : Hom (freeAlgebra sig X) A)
    {u : S} (z : X u) {s : S} (t : Term sig X s)
    (hn : ¬ Min (⟨s, collapseTerm g z t⟩ : STerm sig X)) :
    ¬ ∃ h : s = u,
      g.toFun u (h ▸ collapseTerm g z t) = g.toFun u (Term.var z) := by
  cases t with
  | var x =>
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z)
        · have hcollapse : collapseTerm g z (Term.var x) = h.symm ▸ Term.var z := by
            simp [collapseTerm, h, heq]
          rw [hcollapse] at hn
          cases h
          exact (hn (min_var z)).elim
        · have hcollapse : collapseTerm g z (Term.var x) = Term.var x := by
            simp [collapseTerm, h, heq]
          rw [hcollapse] at hn
          exact (hn (min_var x)).elim
      · have hcollapse : collapseTerm g z (Term.var x) = Term.var x := by
          simp [collapseTerm, h]
        rw [hcollapse] at hn
        exact (hn (min_var x)).elim
  | app σ ts =>
      by_cases h : s = u
      · by_cases hne : g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z)
        · have hcollapse : collapseTerm g z (Term.app σ ts) = h.symm ▸ Term.var z := by
            simp [collapseTerm, h, hne]
          rw [hcollapse] at hn
          cases h
          exact (hn (min_var z)).elim
        · have hcollapse :
              collapseTerm g z (Term.app σ ts) =
                Term.app σ (collapseVec g z ts) := by
            simp [collapseTerm, h, hne]
          rw [hcollapse]
          rintro ⟨h', heq⟩
          cases h
          have hc :
              g.toFun u (Term.app σ (collapseVec g z ts)) =
                g.toFun u (Term.app σ ts) := by
              rw [hom_app, hom_app]
              exact congrArg (A.op σ) (collapse_vec_preserves_hom g z ts)
          exact hne (hc.symm.trans (by simpa using heq))
      · have hcollapse :
            collapseTerm g z (Term.app σ ts) =
              Term.app σ (collapseVec g z ts) := by
          simp [collapseTerm, h]
        rw [hcollapse]
        rintro ⟨h, _⟩
        contradiction

mutual
noncomputable def collapsePackTerm {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    {s : S} → Term sig X s → Term sig X s × List (Term sig X u)
  | s, .var x =>
      if h : s = u then
        if g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z) then
          (h.symm ▸ Term.var z, [h ▸ Term.var x])
        else (Term.var x, [])
      else (Term.var x, [])
  | s, .app σ ts =>
      if h : s = u then
        if g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z) then
          (h.symm ▸ Term.var z, [h ▸ Term.app σ ts])
        else
          let r := collapsePackVec g z ts
          (Term.app σ r.1, r.2)
      else
        let r := collapsePackVec g z ts
        (Term.app σ r.1, r.2)
noncomputable def collapsePackVec {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    {w : List S} → TermVec sig X w → TermVec sig X w × List (Term sig X u)
  | [], .nil => (.nil, [])
  | _ :: _, .cons t ts =>
      let rt := collapsePackTerm g z t
      let rv := collapsePackVec g z ts
      (.cons rt.1 rv.1, rt.2 ++ rv.2)
end

theorem collapsePackTerm_correct {S : Type} {sig : Signature S}
    {X : SSet S} {A : Algebra sig} (g : Hom (freeAlgebra sig X) A)
    {u : S} (z : X u) :
    ∀ {s : S} (t : Term sig X s) (rest : List (Term sig X u)),
      Term.substFamAux z (collapsePackTerm g z t).1
          ((collapsePackTerm g z t).2 ++ rest) = (t, rest) :=
  @Term.rec _ _ _
    (motive_1 := fun _ t => ∀ rest,
      Term.substFamAux z (collapsePackTerm g z t).1
          ((collapsePackTerm g z t).2 ++ rest) = (t, rest))
    (motive_2 := fun _ ts => ∀ rest,
      TermVec.substFamAux z (collapsePackVec g z ts).1
          ((collapsePackVec g z ts).2 ++ rest) = (ts, rest))
    (fun {s} x rest => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z)
        · cases h
          have heq' : g.toFun u (Term.var x) = g.toFun u (Term.var z) := by
            simpa using heq
          simp [collapsePackTerm, Term.substFamAux, heq']
        · have hx : h ▸ x ≠ z := by
            intro hx
            apply heq
            cases h
            cases hx
            rfl
          simp [collapsePackTerm, Term.substFamAux, h, heq, hx]
      · simp [collapsePackTerm, Term.substFamAux, h])
    (fun {w} {s} σ ts ih rest => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z)
        · cases h
          have heq' : g.toFun u (Term.app σ ts) = g.toFun u (Term.var z) := by
            simpa using heq
          simp [collapsePackTerm, Term.substFamAux, heq']
        · simp [collapsePackTerm, Term.substFamAux, h, heq, ih rest]
      · simp [collapsePackTerm, Term.substFamAux, h, ih rest])
    (fun rest => rfl)
    (fun t ts iht ihv rest => by
      simp [collapsePackVec, TermVec.substFamAux, List.append_assoc,
        iht ((collapsePackVec g z ts).2 ++ rest), ihv rest])

theorem collapsePackTerm_length {S : Type} {sig : Signature S}
    {X : SSet S} {A : Algebra sig} (g : Hom (freeAlgebra sig X) A)
    {u : S} (z : X u) :
    ∀ {s : S} (t : Term sig X s),
      (collapsePackTerm g z t).2.length = Term.occ z (collapsePackTerm g z t).1 :=
  @Term.rec _ _ _
    (motive_1 := fun _ t =>
      (collapsePackTerm g z t).2.length = Term.occ z (collapsePackTerm g z t).1)
    (motive_2 := fun _ ts =>
      (collapsePackVec g z ts).2.length = TermVec.occ z (collapsePackVec g z ts).1)
    (fun {s} x => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z)
        · cases h
          have heq' : g.toFun u (Term.var x) = g.toFun u (Term.var z) := by
            simpa using heq
          simp [collapsePackTerm, Term.occ, heq']
        · have hx : h ▸ x ≠ z := by
            intro hx
            apply heq
            cases h
            cases hx
            rfl
          simp [collapsePackTerm, Term.occ, h, heq, hx]
      · simp [collapsePackTerm, Term.occ, h])
    (fun {w} {s} σ ts ih => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z)
        · cases h
          have heq' : g.toFun u (Term.app σ ts) = g.toFun u (Term.var z) := by
            simpa using heq
          simp [collapsePackTerm, Term.occ, heq']
        · simp [collapsePackTerm, Term.occ, h, heq, ih]
      · simp [collapsePackTerm, Term.occ, h, ih])
    rfl
    (fun _ _ iht ihv => by
      simp [collapsePackVec, TermVec.occ, List.length_append, iht, ihv])

theorem collapsePackVec_correct {S : Type} {sig : Signature S}
    {X : SSet S} {A : Algebra sig} (g : Hom (freeAlgebra sig X) A)
    {u : S} (z : X u) :
    ∀ {w : List S} (ts : TermVec sig X w) (rest : List (Term sig X u)),
      TermVec.substFamAux z (collapsePackVec g z ts).1
          ((collapsePackVec g z ts).2 ++ rest) = (ts, rest) :=
  @TermVec.rec _ _ _
    (motive_1 := fun _ t => ∀ rest,
      Term.substFamAux z (collapsePackTerm g z t).1
          ((collapsePackTerm g z t).2 ++ rest) = (t, rest))
    (motive_2 := fun _ ts => ∀ rest,
      TermVec.substFamAux z (collapsePackVec g z ts).1
          ((collapsePackVec g z ts).2 ++ rest) = (ts, rest))
    (fun {s} x rest => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z)
        · cases h
          have heq' : g.toFun u (Term.var x) = g.toFun u (Term.var z) := by
            simpa using heq
          simp [collapsePackTerm, Term.substFamAux, heq']
        · have hx : h ▸ x ≠ z := by
            intro hx
            apply heq
            cases h
            cases hx
            rfl
          simp [collapsePackTerm, Term.substFamAux, h, heq, hx]
      · simp [collapsePackTerm, Term.substFamAux, h])
    (fun {w} {s} σ ts ih rest => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z)
        · cases h
          have heq' : g.toFun u (Term.app σ ts) = g.toFun u (Term.var z) := by
            simpa using heq
          simp [collapsePackTerm, Term.substFamAux, heq']
        · simp [collapsePackTerm, Term.substFamAux, h, heq, ih rest]
      · simp [collapsePackTerm, Term.substFamAux, h, ih rest])
    (fun rest => rfl)
    (fun t ts iht ihv rest => by
      simp [collapsePackVec, TermVec.substFamAux, List.append_assoc,
        iht ((collapsePackVec g z ts).2 ++ rest), ihv rest])


open MSKleene
open Classical

theorem collapsePackTerm_state {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    ∀ {s : S} (t : Term sig X s) (q : Term sig X u),
      q ∈ (collapsePackTerm g z t).2 →
        g.toFun u q = g.toFun u (Term.var z) :=
  @Term.rec _ _ _
    (motive_1 := fun _ t => ∀ q,
      q ∈ (collapsePackTerm g z t).2 →
        g.toFun u q = g.toFun u (Term.var z))
    (motive_2 := fun _ ts => ∀ q,
      q ∈ (collapsePackVec g z ts).2 →
        g.toFun u q = g.toFun u (Term.var z))
    (fun {s} x q hq => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z)
        · simp [collapsePackTerm, h, heq] at hq
          subst q
          exact heq
        · simp [collapsePackTerm, h, heq] at hq
      · simp [collapsePackTerm, h] at hq)
    (fun {w} {s} σ ts ih q hq => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z)
        · simp [collapsePackTerm, h, heq] at hq
          subst q
          exact heq
        · simp [collapsePackTerm, h, heq] at hq
          exact ih q hq
      · simp [collapsePackTerm, h] at hq
        exact ih q hq)
    (fun q hq => by simp [collapsePackVec] at hq)
    (fun t ts iht ihv q hq => by
      simp only [collapsePackVec, List.mem_append] at hq
      exact hq.elim (iht q) (ihv q))

theorem collapsePackVec_length {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    ∀ {w : List S} (ts : TermVec sig X w),
      (collapsePackVec g z ts).2.length = TermVec.occ z (collapsePackVec g z ts).1
  | [], .nil => rfl
  | _ :: _, .cons t ts => by
      simp [collapsePackVec, TermVec.occ, List.length_append,
        collapsePackTerm_length g z t, collapsePackVec_length g z ts]

theorem collapsePackVec_state {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    ∀ {w : List S} (ts : TermVec sig X w) (q : Term sig X u),
      q ∈ (collapsePackVec g z ts).2 →
        g.toFun u q = g.toFun u (Term.var z)
  | [], .nil, q, hq => by simp [collapsePackVec] at hq
  | _ :: _, .cons t ts, q, hq => by
      simp only [collapsePackVec, List.mem_append] at hq
      exact hq.elim (collapsePackTerm_state g z t q)
        (collapsePackVec_state g z ts q)

theorem collapsePackTerm_subterm {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    ∀ {s : S} (t : Term sig X s) (q : Term sig X u),
      q ∈ (collapsePackTerm g z t).2 →
        SubtermLE (⟨u, q⟩ : STerm sig X) ⟨s, t⟩ :=
  @Term.rec _ _ _
    (motive_1 := fun s t => ∀ q,
      q ∈ (collapsePackTerm g z t).2 →
        SubtermLE (⟨u, q⟩ : STerm sig X) ⟨s, t⟩)
    (motive_2 := fun _ ts => ∀ q,
      q ∈ (collapsePackVec g z ts).2 →
        ∃ a : STerm sig X, TermVec.Mem a.2 ts ∧
          SubtermLE (⟨u, q⟩ : STerm sig X) a)
    (fun {s} x q hq => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z)
        · simp [collapsePackTerm, h, heq] at hq
          subst q
          cases h
          exact Relation.ReflTransGen.refl
        · simp [collapsePackTerm, h, heq] at hq
      · simp [collapsePackTerm, h] at hq)
    (fun {w} {s} σ ts ih q hq => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z)
        · simp [collapsePackTerm, h, heq] at hq
          subst q
          cases h
          exact Relation.ReflTransGen.refl
        · simp [collapsePackTerm, h, heq] at hq
          rcases ih q hq with ⟨a, ha, hqa⟩
          exact hqa.trans (Relation.ReflTransGen.single ⟨w, σ, ts, rfl, ha⟩)
      · simp [collapsePackTerm, h] at hq
        rcases ih q hq with ⟨a, ha, hqa⟩
        exact hqa.trans (Relation.ReflTransGen.single ⟨w, σ, ts, rfl, ha⟩))
    (fun q hq => by simp [collapsePackVec] at hq)
    (fun t ts iht ihv q hq => by
      simp only [collapsePackVec, List.mem_append] at hq
      rcases hq with hq | hq
      · exact ⟨⟨_, t⟩, TermVec.Mem.head t ts, iht q hq⟩
      · rcases ihv q hq with ⟨a, ha, hqa⟩
        exact ⟨a, TermVec.Mem.tail t ha, hqa⟩)


open MSKleene
open Classical

private def localSTerm {S : Type} {sig : Signature S} {X : SSet S}
    {s : S} (t : Term sig X s) : STerm sig X := ⟨s, t⟩

private theorem local_ofArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (ts : TermVec sig X w), TermVec.ofArgs (TermVec.toArgs ts) = ts
  | [], .nil => rfl
  | _ :: _, .cons t ts => congrArg (TermVec.cons t) (local_ofArgs_toArgs ts)

private theorem local_hom_app {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {w : List S} {s : S}
    (σ : sig w s) (ts : TermVec sig X w) :
    g.toFun s (Term.app σ ts) = A.op σ (Args.map g.toFun (TermVec.toArgs ts)) := by
  calc
    g.toFun s (Term.app σ ts) =
        g.toFun s ((freeAlgebra sig X).op σ (TermVec.toArgs ts)) := by
          simp only [freeAlgebra]
          rw [local_ofArgs_toArgs]
    _ = A.op σ (Args.map g.toFun (TermVec.toArgs ts)) :=
      g.map_op σ (TermVec.toArgs ts)

theorem collapsePackTerm_hom {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    (∀ {s : S} (t : Term sig X s),
      g.toFun s (collapsePackTerm g z t).1 = g.toFun s t) ∧
    (∀ {w : List S} (ts : TermVec sig X w),
      Args.map g.toFun (TermVec.toArgs (collapsePackVec g z ts).1) =
        Args.map g.toFun (TermVec.toArgs ts)) := by
  let motiveT := fun (s : S) (t : Term sig X s) =>
    g.toFun s (collapsePackTerm g z t).1 = g.toFun s t
  let motiveV := fun (w : List S) (ts : TermVec sig X w) =>
    Args.map g.toFun (TermVec.toArgs (collapsePackVec g z ts).1) =
      Args.map g.toFun (TermVec.toArgs ts)
  have ht : ∀ {s : S} (t : Term sig X s), motiveT s t :=
    @Term.rec _ _ _ motiveT motiveV
      (fun {s} x => by
        dsimp [motiveT]
        by_cases h : s = u
        · by_cases heq : g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z)
          · cases h
            have heq' : g.toFun u (Term.var x) = g.toFun u (Term.var z) := by
              simpa using heq
            simpa [collapsePackTerm, heq'] using heq'.symm
          · simp [collapsePackTerm, h, heq]
        · simp [collapsePackTerm, h])
      (fun {w} {s} σ ts ih => by
        dsimp [motiveT, motiveV] at ih ⊢
        by_cases h : s = u
        · by_cases heq : g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z)
          · cases h
            have heq' : g.toFun u (Term.app σ ts) = g.toFun u (Term.var z) := by
              simpa using heq
            simpa [collapsePackTerm, heq'] using heq'.symm
          · simp only [collapsePackTerm, dif_pos h, if_neg heq]
            rw [local_hom_app, local_hom_app]
            exact congrArg (A.op σ) ih
        · simp only [collapsePackTerm, dif_neg h]
          rw [local_hom_app, local_hom_app]
          exact congrArg (A.op σ) ih)
      (by rfl)
      (fun t ts iht ihv => by
        dsimp [motiveT, motiveV] at iht ihv ⊢
        simp only [collapsePackVec, TermVec.toArgs, Args.map]
        exact congrArg₂ Prod.mk iht ihv)
  have hv : ∀ {w : List S} (ts : TermVec sig X w), motiveV w ts :=
    @TermVec.rec _ _ _ motiveT motiveV
      (fun {s} x => by
        dsimp [motiveT]
        by_cases h : s = u
        · by_cases heq : g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z)
          · cases h
            have heq' : g.toFun u (Term.var x) = g.toFun u (Term.var z) := by
              simpa using heq
            simpa [collapsePackTerm, heq'] using heq'.symm
          · simp [collapsePackTerm, h, heq]
        · simp [collapsePackTerm, h])
      (fun {w} {s} σ ts ih => by
        dsimp [motiveT, motiveV] at ih ⊢
        by_cases h : s = u
        · by_cases heq : g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z)
          · cases h
            have heq' : g.toFun u (Term.app σ ts) = g.toFun u (Term.var z) := by
              simpa using heq
            simpa [collapsePackTerm, heq'] using heq'.symm
          · simp only [collapsePackTerm, dif_pos h, if_neg heq]
            rw [local_hom_app, local_hom_app]
            exact congrArg (A.op σ) ih
        · simp only [collapsePackTerm, dif_neg h]
          rw [local_hom_app, local_hom_app]
          exact congrArg (A.op σ) ih)
      (by rfl)
      (fun t ts iht ihv => by
        dsimp [motiveT, motiveV] at iht ihv ⊢
        simp only [collapsePackVec, TermVec.toArgs, Args.map]
        exact congrArg₂ Prod.mk iht ihv)
  exact ⟨ht, hv⟩

private theorem local_min_var {S : Type} {sig : Signature S} {X : SSet S}
    {s : S} (x : X s) : Min (⟨s, Term.var x⟩ : STerm sig X) := by
  intro a ha
  rcases ha with ⟨w, σ, ts, heq, _⟩
  cases heq

private theorem no_nonminimal_below_var {S : Type} {sig : Signature S}
    {X : SSet S} {s : S} (x : X s) (M : STerm sig X)
    (hle : SubtermLE M ⟨s, Term.var x⟩) (hM : ¬ Min M) : False := by
  cases hle with
  | refl => exact hM (local_min_var x)
  | tail _ himm =>
      rcases himm with ⟨w, σ, ts, heq, _⟩
      cases heq

private theorem app_nonminimal {S : Type} {sig : Signature S} {X : SSet S}
    {w : List S} {s : S} (σ : sig w s) (ts : TermVec sig X w)
    (h : w ≠ []) : ¬ Min (⟨s, Term.app σ ts⟩ : STerm sig X) := by
  intro hmin
  cases ts with
  | nil => exact h rfl
  | @cons t w q qs =>
      exact hmin ⟨t, q⟩ ⟨t :: w, σ, .cons q qs, rfl, TermVec.Mem.head q qs⟩

private theorem local_min_nil {S : Type} {sig : Signature S} {X : SSet S}
    {s : S} (σ : sig [] s) :
    Min (⟨s, Term.app σ TermVec.nil⟩ : STerm sig X) := by
  intro a ha
  rcases ha with ⟨w, τ, ts, heq, hmem⟩
  cases heq
  cases hmem

theorem collapsePack_correspond {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    ∀ {s : S} (t : Term sig X s) (M : STerm sig X),
      SubtermLE M ⟨s, (collapsePackTerm g z t).1⟩ → ¬ Min M →
      ∃ N : STerm sig X, SubtermLE N ⟨s, t⟩ ∧ ¬ Min N ∧
        ∃ h : N.1 = M.1,
          g.toFun M.1 (h ▸ N.2) = g.toFun M.1 M.2 :=
  @Term.rec _ _ _
    (motive_1 := fun s t => ∀ M : STerm sig X,
      SubtermLE M ⟨s, (collapsePackTerm g z t).1⟩ → ¬ Min M →
      ∃ N : STerm sig X, SubtermLE N ⟨s, t⟩ ∧ ¬ Min N ∧
        ∃ h : N.1 = M.1,
          g.toFun M.1 (h ▸ N.2) = g.toFun M.1 M.2)
    (motive_2 := fun _ ts => ∀ {r : S} (a : Term sig X r)
        {m : S} (M : Term sig X m),
      TermVec.Mem a (collapsePackVec g z ts).1 →
      SubtermLE (localSTerm M) (localSTerm a) → ¬ Min (localSTerm M) →
      ∃ (r : S) (b : Term sig X r), TermVec.Mem b ts ∧
        ∃ (q : S) (N : Term sig X q),
          SubtermLE (localSTerm N) (localSTerm b) ∧
          ¬ Min (localSTerm N) ∧
          ∃ h : q = m,
            g.toFun m (h ▸ N) = g.toFun m M)
    (fun {s} x M hle hM => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z)
        · cases h
          simp [collapsePackTerm, heq] at hle
          exact (no_nonminimal_below_var z M hle hM).elim
        · simp [collapsePackTerm, h, heq] at hle
          exact (no_nonminimal_below_var x M hle hM).elim
      · simp [collapsePackTerm, h] at hle
        exact (no_nonminimal_below_var x M hle hM).elim)
    (fun {w} {s} σ ts ih M hle hM => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z)
        · cases h
          simp [collapsePackTerm, heq] at hle
          exact (no_nonminimal_below_var z M hle hM).elim
        · have hp : (collapsePackTerm g z (Term.app σ ts)).1 =
              Term.app σ (collapsePackVec g z ts).1 := by
            simp [collapsePackTerm, h, heq]
          rw [hp] at hle
          cases hle with
          | refl =>
              have hw : w ≠ [] := by
                intro hw
                subst w
                cases ts
                exact hM (local_min_nil σ)
              refine ⟨⟨s, Term.app σ ts⟩, Relation.ReflTransGen.refl,
                app_nonminimal σ ts hw, rfl, ?_⟩
              simpa [hp] using ((collapsePackTerm_hom g z).1 (Term.app σ ts)).symm
          | tail hpre himm =>
              rcases himm with ⟨w', τ, us, happ, hmem⟩
              cases happ
              rcases ih _ M.2 hmem hpre hM with ⟨r, b, hb, q, N, hNb, hN, hEq⟩
              exact ⟨localSTerm N,
                hNb.trans (Relation.ReflTransGen.single ⟨w, σ, ts, rfl, hb⟩),
                hN, hEq⟩
      · have hp : (collapsePackTerm g z (Term.app σ ts)).1 =
            Term.app σ (collapsePackVec g z ts).1 := by
          simp [collapsePackTerm, h]
        rw [hp] at hle
        cases hle with
        | refl =>
            have hw : w ≠ [] := by
              intro hw
              subst w
              cases ts
              exact hM (local_min_nil σ)
            refine ⟨⟨s, Term.app σ ts⟩, Relation.ReflTransGen.refl,
              app_nonminimal σ ts hw, rfl, ?_⟩
            simpa [hp] using ((collapsePackTerm_hom g z).1 (Term.app σ ts)).symm
        | tail hpre himm =>
            rcases himm with ⟨w', τ, us, happ, hmem⟩
            cases happ
            rcases ih _ M.2 hmem hpre hM with ⟨r, b, hb, q, N, hNb, hN, hEq⟩
            exact ⟨localSTerm N,
              hNb.trans (Relation.ReflTransGen.single ⟨w, σ, ts, rfl, hb⟩),
              hN, hEq⟩)
    (fun {r} a {m} M hmem hle hM => by
      cases hmem)
    (fun tSort w t ts iht ihv {r} a {m} M hmem hle hM => by
      simp only [collapsePackVec] at hmem
      revert hle
      cases hmem with
      | head =>
          intro hle
          rcases iht (localSTerm M) hle hM with ⟨N, hNle, hN, hEq⟩
          exact ⟨_, t, TermVec.Mem.head t ts, N.1, N.2, hNle, hN, hEq⟩
      | tail q htail =>
          intro hle
          rcases ihv a M htail hle hM with ⟨r, b, hb, q, N, hNle, hN, hEq⟩
          exact ⟨r, b, TermVec.Mem.tail t hb, q, N, hNle, hN, hEq⟩)


open MSKleene
open Classical

theorem collapsePack_fst {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    (∀ {s : S} (t : Term sig X s),
      (collapsePackTerm g z t).1 = collapseTerm g z t) ∧
    (∀ {w : List S} (ts : TermVec sig X w),
      (collapsePackVec g z ts).1 = collapseVec g z ts) := by
  let motiveT : ∀ s : S, Term sig X s → Prop := fun _ t =>
    (collapsePackTerm g z t).1 = collapseTerm g z t
  let motiveV : ∀ w : List S, TermVec sig X w → Prop := fun _ ts =>
    (collapsePackVec g z ts).1 = collapseVec g z ts
  have ht : ∀ {s : S} (t : Term sig X s), motiveT s t :=
    @Term.rec _ _ _ motiveT motiveV
      (fun {s} x => by
        dsimp [motiveT]
        by_cases h : s = u
        · by_cases heq : g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z)
          · simp [collapsePackTerm, collapseTerm, h, heq]
          · simp [collapsePackTerm, collapseTerm, h, heq]
        · simp [collapsePackTerm, collapseTerm, h])
      (fun {w} {s} σ ts ih => by
        dsimp [motiveT, motiveV] at ih ⊢
        by_cases h : s = u
        · by_cases heq : g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z)
          · simp [collapsePackTerm, collapseTerm, h, heq]
          · simp [collapsePackTerm, collapseTerm, h, heq, ih]
        · simp [collapsePackTerm, collapseTerm, h, ih])
      rfl
      (fun t ts iht ihv => by
        dsimp [motiveT, motiveV] at iht ihv ⊢
        simp [collapsePackVec, collapseVec, iht, ihv])
  have hv : ∀ {w : List S} (ts : TermVec sig X w), motiveV w ts :=
    @TermVec.rec _ _ _ motiveT motiveV
      (fun {s} x => by
        dsimp [motiveT]
        by_cases h : s = u
        · by_cases heq : g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z)
          · simp [collapsePackTerm, collapseTerm, h, heq]
          · simp [collapsePackTerm, collapseTerm, h, heq]
        · simp [collapsePackTerm, collapseTerm, h])
      (fun {w} {s} σ ts ih => by
        dsimp [motiveT, motiveV] at ih ⊢
        by_cases h : s = u
        · by_cases heq : g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z)
          · simp [collapsePackTerm, collapseTerm, h, heq]
          · simp [collapsePackTerm, collapseTerm, h, heq, ih]
        · simp [collapsePackTerm, collapseTerm, h, ih])
      rfl
      (fun t ts iht ihv => by
        dsimp [motiveT, motiveV] at iht ihv ⊢
        simp [collapsePackVec, collapseVec, iht, ihv])
  exact ⟨ht, hv⟩

private theorem global_min_var {S : Type} {sig : Signature S} {X : SSet S}
    {s : S} (x : X s) : Min (⟨s, Term.var x⟩ : STerm sig X) := by
  intro a ha
  rcases ha with ⟨w, σ, ts, heq, _⟩
  cases heq

private theorem global_no_nonminimal_below_var {S : Type} {sig : Signature S}
    {X : SSet S} {s : S} (x : X s) (M : STerm sig X)
    (hle : SubtermLE M ⟨s, Term.var x⟩) (hM : ¬ Min M) : False := by
  cases hle with
  | refl => exact hM (global_min_var x)
  | tail _ himm =>
      rcases himm with ⟨w, σ, ts, heq, _⟩
      cases heq

theorem collapsePack_no_target {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    ∀ {s : S} (t : Term sig X s) (M : STerm sig X),
      SubtermLE M ⟨s, (collapsePackTerm g z t).1⟩ → ¬ Min M →
      ¬ ∃ h : M.1 = u,
        g.toFun u (h ▸ M.2) = g.toFun u (Term.var z) :=
  @Term.rec _ _ _
    (motive_1 := fun s t => ∀ M : STerm sig X,
      SubtermLE M ⟨s, (collapsePackTerm g z t).1⟩ → ¬ Min M →
      ¬ ∃ h : M.1 = u,
        g.toFun u (h ▸ M.2) = g.toFun u (Term.var z))
    (motive_2 := fun _ ts => ∀ {r : S} (a : Term sig X r)
        {m : S} (M : Term sig X m),
      TermVec.Mem a (collapsePackVec g z ts).1 →
      SubtermLE ⟨m, M⟩ ⟨r, a⟩ → ¬ Min ⟨m, M⟩ →
      ¬ ∃ h : m = u,
        g.toFun u (h ▸ M) = g.toFun u (Term.var z))
    (fun {s} x M hle hM => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.var x) = g.toFun u (Term.var z)
        · cases h
          simp [collapsePackTerm, heq] at hle
          exact (global_no_nonminimal_below_var z M hle hM).elim
        · simp [collapsePackTerm, h, heq] at hle
          exact (global_no_nonminimal_below_var x M hle hM).elim
      · simp [collapsePackTerm, h] at hle
        exact (global_no_nonminimal_below_var x M hle hM).elim)
    (fun {w} {s} σ ts ih M hle hM => by
      by_cases h : s = u
      · by_cases heq : g.toFun u (h ▸ Term.app σ ts) = g.toFun u (Term.var z)
        · cases h
          simp [collapsePackTerm, heq] at hle
          exact (global_no_nonminimal_below_var z M hle hM).elim
        · have hp : (collapsePackTerm g z (Term.app σ ts)).1 =
              Term.app σ (collapsePackVec g z ts).1 := by
            simp [collapsePackTerm, h, heq]
          rw [hp] at hle
          cases hle with
          | refl =>
              rw [← hp] at hM ⊢
              rw [(collapsePack_fst g z).1 (Term.app σ ts)] at hM ⊢
              exact collapse_nonminimal_not_target g z (Term.app σ ts) hM
          | tail hpre himm =>
              rcases himm with ⟨w', τ, us, happ, hmem⟩
              cases happ
              exact ih _ M.2 hmem hpre hM
      · have hp : (collapsePackTerm g z (Term.app σ ts)).1 =
            Term.app σ (collapsePackVec g z ts).1 := by
          simp [collapsePackTerm, h]
        rw [hp] at hle
        cases hle with
        | refl =>
            rw [← hp] at hM ⊢
            rw [(collapsePack_fst g z).1 (Term.app σ ts)] at hM ⊢
            exact collapse_nonminimal_not_target g z (Term.app σ ts) hM
        | tail hpre himm =>
            rcases himm with ⟨w', τ, us, happ, hmem⟩
            cases happ
            exact ih _ M.2 hmem hpre hM)
    (fun {r} a {m} M hmem hle hM => by cases hmem)
    (fun tSort w t ts iht ihv {r} a {m} M hmem hle hM => by
      simp only [collapsePackVec] at hmem
      revert hle
      cases hmem with
      | head =>
          intro hle
          exact iht ⟨m, M⟩ hle hM
      | tail q htail =>
          intro hle
          exact ihv a M htail hle hM)

theorem collapsePackVec_mem_origin {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    ∀ {w : List S} (ts : TermVec sig X w) {r : S} (a : Term sig X r),
      TermVec.Mem a (collapsePackVec g z ts).1 →
      ∃ b : Term sig X r, TermVec.Mem b ts ∧
        a = (collapsePackTerm g z b).1
  | [], .nil, r, a, hmem => by cases hmem
  | _ :: _, .cons t ts, r, a, hmem => by
      simp only [collapsePackVec] at hmem
      cases hmem with
      | head => exact ⟨t, TermVec.Mem.head t ts, rfl⟩
      | tail q htail =>
          rcases collapsePackVec_mem_origin g z ts a htail with ⟨b, hb, heq⟩
          exact ⟨b, TermVec.Mem.tail t hb, heq⟩

theorem collapsePackVec_subterm {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    ∀ {w : List S} (ts : TermVec sig X w) (q : Term sig X u),
      q ∈ (collapsePackVec g z ts).2 →
      ∃ (r : S) (a : Term sig X r), TermVec.Mem a ts ∧
        SubtermLE (⟨u, q⟩ : STerm sig X) ⟨r, a⟩
  | [], .nil, q, hq => by simp [collapsePackVec] at hq
  | _ :: _, .cons t ts, q, hq => by
      simp only [collapsePackVec, List.mem_append] at hq
      rcases hq with hq | hq
      · exact ⟨_, t, TermVec.Mem.head t ts, collapsePackTerm_subterm g z t q hq⟩
      · rcases collapsePackVec_subterm g z ts q hq with ⟨r, a, ha, hqa⟩
        exact ⟨r, a, TermVec.Mem.tail t ha, hqa⟩


open MSKleene
open Classical

private theorem final_ofArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (ts : TermVec sig X w), TermVec.ofArgs (TermVec.toArgs ts) = ts
  | [], .nil => rfl
  | _ :: _, .cons t ts => congrArg (TermVec.cons t) (final_ofArgs_toArgs ts)

private theorem final_hom_app {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {w : List S} {s : S}
    (σ : sig w s) (ts : TermVec sig X w) :
    g.toFun s (Term.app σ ts) = A.op σ (Args.map g.toFun (TermVec.toArgs ts)) := by
  calc
    g.toFun s (Term.app σ ts) =
        g.toFun s ((freeAlgebra sig X).op σ (TermVec.toArgs ts)) := by
          simp only [freeAlgebra]
          rw [final_ofArgs_toArgs]
    _ = A.op σ (Args.map g.toFun (TermVec.toArgs ts)) :=
      g.map_op σ (TermVec.toArgs ts)

private theorem final_min_var {S : Type} {sig : Signature S} {X : SSet S}
    {s : S} (x : X s) : Min (⟨s, Term.var x⟩ : STerm sig X) := by
  intro a ha
  rcases ha with ⟨w, σ, ts, heq, _⟩
  cases heq

theorem solution {S : Type} (sig : Signature S) (X : SSet S)
    (A : Algebra sig) (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) {s : S}
    (R : Term sig X s) (hR : ¬ Min (⟨s, R⟩ : STerm sig X)) :
    ∃ (P : Term sig X s) (qs : Fin (Term.occ z P) → Term sig X u),
      R = substFam z P qs
    ∧ g.toFun s P = g.toFun s R
    ∧ (∀ α, SubtermLT (⟨u, qs α⟩ : STerm sig X) ⟨s, R⟩
            ∧ g.toFun u (qs α) = g.toFun u (Term.var z))
    ∧ (∀ M : STerm sig X, SubtermLT M ⟨s, P⟩ → ¬ Min M →
        (¬ ∃ h : M.1 = u, g.toFun u (h ▸ M.2) = g.toFun u (Term.var z))
        ∧ (∃ N : STerm sig X, SubtermLT N ⟨s, R⟩ ∧ ¬ Min N
            ∧ ∃ h : N.1 = M.1, g.toFun M.1 (h ▸ N.2) = g.toFun M.1 M.2)) := by
  cases R with
  | var x => exact (hR (final_min_var x)).elim
  | @app w s σ ts =>
      let pv := collapsePackVec g z ts
      let P : Term sig X s := Term.app σ pv.1
      have hlen : pv.2.length = Term.occ z P := by
        simpa [pv, P, Term.occ] using collapsePackVec_length g z ts
      let f : Fin pv.2.length → Term sig X u := fun i => pv.2.get i
      let qs : Fin (Term.occ z P) → Term sig X u :=
        fun i => f (Fin.cast hlen.symm i)
      have hof : List.ofFn qs = pv.2 := by
        calc
          List.ofFn qs = List.ofFn f := (List.ofFn_congr hlen f).symm
          _ = pv.2 := List.ofFn_get _
      have hc := collapsePackVec_correct g z ts []
      simp only [List.append_nil] at hc
      refine ⟨P, qs, ?_, ?_, ?_, ?_⟩
      · unfold substFam
        rw [hof]
        change Term.app σ ts = (Term.substFamAux z (Term.app σ pv.1) pv.2).1
        simp only [Term.substFamAux]
        exact congrArg (fun us => Term.app σ us) (congrArg Prod.fst hc).symm
      · change g.toFun s (Term.app σ pv.1) = g.toFun s (Term.app σ ts)
        rw [final_hom_app, final_hom_app]
        exact congrArg (A.op σ) ((collapsePackTerm_hom g z).2 ts)
      · intro α
        have hmem : qs α ∈ pv.2 := by
          dsimp [qs, f]
          exact List.get_mem _ _
        constructor
        · rcases collapsePackVec_subterm g z ts (qs α) hmem with ⟨r, a, ha, hqa⟩
          exact Relation.TransGen.tail' hqa ⟨w, σ, ts, rfl, ha⟩
        · exact collapsePackVec_state g z ts (qs α) hmem
      · intro M hMP hM
        change SubtermLT M ⟨s, Term.app σ pv.1⟩ at hMP
        have hsplit : ∃ a : STerm sig X,
            SubtermLE M a ∧ ImmSub a ⟨s, Term.app σ pv.1⟩ := by
          cases hMP with
          | single himm => exact ⟨M, Relation.ReflTransGen.refl, himm⟩
          | tail hpre himm => exact ⟨_, hpre.to_reflTransGen, himm⟩
        rcases hsplit with ⟨a, hMa, haP⟩
        rcases haP with ⟨w', τ, us, happ, hmem⟩
        cases happ
        rcases collapsePackVec_mem_origin g z ts a.2 hmem with ⟨b, hb, hab⟩
        have haEq : a = (⟨a.1, (collapsePackTerm g z b).1⟩ : STerm sig X) := by
          change (⟨a.1, a.2⟩ : Σ r : S, Term sig X r) =
            ⟨a.1, (collapsePackTerm g z b).1⟩
          exact congrArg
            (fun q : Term sig X a.1 => (⟨a.1, q⟩ : Σ r : S, Term sig X r)) hab
        rw [haEq] at hMa
        constructor
        · exact collapsePack_no_target g z b M hMa hM
        · rcases collapsePack_correspond g z b M hMa hM with
            ⟨N, hNb, hN, hEq⟩
          exact ⟨N, Relation.TransGen.tail' hNb ⟨w, σ, ts, rfl, hb⟩,
            hN, hEq⟩
