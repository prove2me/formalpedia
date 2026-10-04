-- Prove2me | solution 1 for MSKleene.subst_inv
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-08T13:14:35.066423+00:00
-- url     : https://prove2.me/submissions/d3c6048d-4667-46ff-8b45-62b2a2db8f47

import Definitions.Def_MSKleene_SubstFam

open MSKleene

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

private theorem subst_aux_hom {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {u : S} (z : X u) :
    ∀ {s : S} (t : Term sig X s) (l : List (Term sig X u)),
      (∀ q ∈ l, g.toFun u q = g.toFun u (Term.var z)) →
      g.toFun s (Term.substFamAux z t l).1 = g.toFun s t ∧
        ∀ q ∈ (Term.substFamAux z t l).2,
          g.toFun u q = g.toFun u (Term.var z) :=
  @Term.rec _ _ _
    (motive_1 := fun s t => ∀ l : List (Term sig X u),
      (∀ q ∈ l, g.toFun u q = g.toFun u (Term.var z)) →
      g.toFun s (Term.substFamAux z t l).1 = g.toFun s t ∧
        ∀ q ∈ (Term.substFamAux z t l).2,
          g.toFun u q = g.toFun u (Term.var z))
    (motive_2 := fun w ts => ∀ l : List (Term sig X u),
      (∀ q ∈ l, g.toFun u q = g.toFun u (Term.var z)) →
      Args.map g.toFun (TermVec.toArgs (TermVec.substFamAux z ts l).1) =
          Args.map g.toFun (TermVec.toArgs ts) ∧
        ∀ q ∈ (TermVec.substFamAux z ts l).2,
          g.toFun u q = g.toFun u (Term.var z))
    (fun {s} x l hl => by
      simp only [Term.substFamAux]
      split
      next hsort =>
        cases hsort
        split
        next hx =>
          have hx' : x = z := by simpa using hx
          subst x
          cases l with
          | nil => simp
          | cons q l =>
            constructor
            · simpa using hl q (by simp)
            · intro r hr
              exact hl r (by simp [hr])
        next _ => exact ⟨rfl, hl⟩
      next _ => exact ⟨rfl, hl⟩)
    (fun σ ts ih l hl => by
      change
        g.toFun _ (Term.app σ (TermVec.substFamAux z ts l).1) =
            g.toFun _ (Term.app σ ts) ∧
          ∀ q ∈ (TermVec.substFamAux z ts l).2,
            g.toFun u q = g.toFun u (Term.var z)
      have h := ih l hl
      exact ⟨by rw [hom_app, hom_app, h.1], h.2⟩)
    (fun l hl => ⟨rfl, hl⟩)
    (fun t ts iht ihv l hl => by
      change
        Args.map g.toFun
              (TermVec.toArgs
                (.cons (Term.substFamAux z t l).1
                  (TermVec.substFamAux z ts (Term.substFamAux z t l).2).1)) =
            Args.map g.toFun (TermVec.toArgs (.cons t ts)) ∧
          ∀ q ∈ (TermVec.substFamAux z ts (Term.substFamAux z t l).2).2,
            g.toFun u q = g.toFun u (Term.var z)
      have ht := iht l hl
      have hv := ihv (Term.substFamAux z t l).2 ht.2
      exact ⟨congrArg₂ Prod.mk ht.1 hv.1, hv.2⟩)

/-- Replacing occurrences by terms with the same homomorphic image preserves
the image of the whole term. -/
theorem solution {S : Type} (sig : Signature S) (X : SSet S) (A : Algebra sig)
    (g : Hom (freeAlgebra sig X) A) {u s : S} (z : X u) (P : Term sig X s)
    (qs : Fin (Term.occ z P) → Term sig X u)
    (hq : ∀ α, g.toFun u (qs α) = g.toFun u (Term.var z)) :
    g.toFun s (substFam z P qs) = g.toFun s P := by
  apply (subst_aux_hom g z P (List.ofFn qs) ?_).1
  intro q hmem
  rw [List.mem_ofFn'] at hmem
  rcases hmem with ⟨i, rfl⟩
  exact hq i
