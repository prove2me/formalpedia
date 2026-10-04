-- Prove2me | solution 1 for MSKleene.rec_closed_reg
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T07:38:14.418336+00:00
-- url     : https://prove2.me/submissions/9a03a500-62f0-4a51-b47f-5c7053242b70

import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_RegAlgebra
import Theorems.Thm_MSKleene_rec_op
import Theorems.Thm_MSKleene_rec_iter
import Theorems.Thm_MSKleene_rec_subst_single
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma

open MSKleene

namespace MSKleene

private def productAlgebra {S : Type} {sig : Signature S}
    (B C : Algebra sig) : Algebra sig where
  carrier := fun r => B.carrier r × C.carrier r
  op := fun σ qs =>
    (B.op σ (Args.map (fun _ q => q.1) qs),
      C.op σ (Args.map (fun _ q => q.2) qs))

private def pairHom {S : Type} {sig : Signature S} {A B C : Algebra sig}
    (f : Hom A B) (g : Hom A C) : Hom A (productAlgebra B C) where
  toFun := fun r a => (f.toFun r a, g.toFun r a)
  map_op := by
    intro w r σ qs
    apply Prod.ext
    · change f.toFun r (A.op σ qs) =
        B.op σ (Args.map (fun _ q => q.1)
          (Args.map (fun t a => (f.toFun t a, g.toFun t a)) qs))
      rw [f.map_op]
      exact congrArg (B.op σ)
        (Args.map_comp (fun _ q => q.1)
          (fun t a => (f.toFun t a, g.toFun t a)) qs)
    · change g.toFun r (A.op σ qs) =
        C.op σ (Args.map (fun _ q => q.2)
          (Args.map (fun t a => (f.toFun t a, g.toFun t a)) qs))
      rw [g.map_op]
      exact congrArg (C.op σ)
        (Args.map_comp (fun _ q => q.2)
          (fun t a => (f.toFun t a, g.toFun t a)) qs)

private theorem finite_fiber {S : Type} {Y : SSet S}
    (hY : SFinite Y) (r : S) : Finite (Y r) := by
  letI : Finite (Sigma Y) := hY
  apply Finite.of_injective (fun y : Y r => Sigma.mk r y)
  intro a b hab
  exact eq_of_heq (Sigma.mk.inj hab).2

private theorem rec_empty {S : Type} [Finite S] {sig : Signature S}
    (A : Algebra sig) (s : S) : sRecognizable A s ∅ := by
  let B : Algebra sig :=
    { carrier := fun _ => PUnit
      op := fun _ _ => PUnit.unit }
  let f : Hom A B :=
    { toFun := fun _ _ => PUnit.unit
      map_op := by intros; rfl }
  refine ⟨B, ?_, f, ∅, ?_⟩
  · show Finite (Σ _ : S, PUnit)
    infer_instance
  · simp

private theorem rec_union {S : Type} [Finite S] {sig : Signature S}
    {A : Algebra sig} {s : S} {L K : Set (A.carrier s)}
    (hL : sRecognizable A s L) (hK : sRecognizable A s K) :
    sRecognizable A s (L ∪ K) := by
  rcases hL with ⟨B, hB, f, M, hf⟩
  rcases hK with ⟨C, hC, g, N, hg⟩
  let D := productAlgebra B C
  let h := pairHom f g
  refine ⟨D, ?_, h, {q | q.1 ∈ M ∨ q.2 ∈ N}, ?_⟩
  · letI finB (r : S) : Finite (B.carrier r) := finite_fiber hB r
    letI finC (r : S) : Finite (C.carrier r) := finite_fiber hC r
    show Finite (Σ r, B.carrier r × C.carrier r)
    infer_instance
  · ext a
    change f.toFun s a ∈ M ∨ g.toFun s a ∈ N ↔ a ∈ L ∪ K
    rw [Set.mem_union]
    exact or_congr (Set.ext_iff.mp hf a) (Set.ext_iff.mp hg a)

end MSKleene

theorem solution {S : Type} [Finite S] (sig : MSKleene.Signature S)
    (Z : MSKleene.SSet S) (hZ : MSKleene.SFinite Z)
    {w : List S} {s : S} (sym : MSKleene.regSig sig Z w s)
    (Ls : MSKleene.Args (fun s => Set (MSKleene.Term sig Z s)) w)
    (hLs : MSKleene.Args.All
      (fun s L => MSKleene.sRecognizable (MSKleene.freeAlgebra sig Z) s L) Ls) :
    MSKleene.sRecognizable (MSKleene.freeAlgebra sig Z) s
      ((MSKleene.regPowerAlgebra sig Z).op sym Ls) := by
  cases sym with
  | base σ =>
      exact MSKleene.rec_op sig Z hZ σ Ls hLs
  | empty =>
      change MSKleene.sRecognizable (MSKleene.freeAlgebra sig Z) s ∅
      exact MSKleene.rec_empty (MSKleene.freeAlgebra sig Z) s
  | iter r z =>
      simpa [MSKleene.regPowerAlgebra] using
        (MSKleene.rec_iter sig Z z Ls.1 hLs.1)
  | plus =>
      change MSKleene.sRecognizable (MSKleene.freeAlgebra sig Z) s
        (Ls.1 ∪ Ls.2.1)
      exact MSKleene.rec_union hLs.1 hLs.2.1
  | subst t r z =>
      simpa [MSKleene.regPowerAlgebra] using
        (MSKleene.rec_subst_single sig Z hZ z Ls.1 Ls.2.1 hLs.1 hLs.2.1)
