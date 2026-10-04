-- Prove2me | solution 1 for MSKleene.rec_subset_reg
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T09:28:46.007635+00:00
-- url     : https://prove2.me/submissions/3d560e84-79b7-4628-8f1a-bbb204b2d3b8

import Definitions.Def_MSKleene_AuxLang
import Theorems.Thm_MSKleene_main_claim
import Theorems.Thm_MSKleene_free_universal
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum

namespace MSKleene

private theorem Args.map_equiv_symm {S : Type} {A B : SSet S}
    (e : (s : S) → A s ≃ B s) :
  ∀ {w : List S} (args : Args A w),
      Args.map (fun s => (e s).symm) (Args.map (fun s => e s) args) = args
  | [], _ => rfl
  | _ :: _, (a, rest) => by
      change ((e _).symm (e _ a),
        Args.map (fun s => (e s).symm) (Args.map (fun s => e s) rest)) =
          (a, rest)
      rw [Equiv.symm_apply_apply]
      exact congrArg (Prod.mk a) (Args.map_equiv_symm e rest)

private theorem finite_fiber_of_sfinite {S : Type} {Y : SSet S}
    (hY : SFinite Y) (s : S) : Finite (Y s) := by
  letI : Finite (Σ t, Y t) := hY
  apply Finite.of_injective (fun y : Y s => Sigma.mk s y)
  intro a b hab
  exact eq_of_heq (Sigma.mk.inj hab).2

private def RegExpr.emptyR {S : Type} {sig : Signature S} {Z : SSet S}
    (s : S) : RegExpr sig Z s :=
  .app (.empty s) .nil

private def RegExpr.plusR {S : Type} {sig : Signature S} {Z : SSet S}
    {s : S} (R Q : RegExpr sig Z s) : RegExpr sig Z s :=
  .app (.plus s) (.cons R (.cons Q .nil))

private def RegExpr.sumR {S : Type} {sig : Signature S} {Z : SSet S}
    {s : S} : List (RegExpr sig Z s) → RegExpr sig Z s
  | [] => .emptyR s
  | R :: Rs => R.plusR (RegExpr.sumR Rs)

@[simp] private theorem interp_emptyR {S : Type} {sig : Signature S}
    {Z : SSet S} (s : S) :
    interpExpr sig Z s (RegExpr.emptyR s) = ∅ := rfl

@[simp] private theorem interp_plusR {S : Type} {sig : Signature S}
    {Z : SSet S} {s : S} (R Q : RegExpr sig Z s) :
    interpExpr sig Z s (R.plusR Q) =
      interpExpr sig Z s R ∪ interpExpr sig Z s Q := rfl

private theorem interp_sumR {S : Type} {sig : Signature S} {Z : SSet S}
    {s : S} (Rs : List (RegExpr sig Z s)) :
    interpExpr sig Z s (RegExpr.sumR Rs) =
      {P | ∃ R ∈ Rs, P ∈ interpExpr sig Z s R} := by
  induction Rs with
  | nil => simp [RegExpr.sumR]
  | cons R Rs ih =>
      simp only [RegExpr.sumR, interp_plusR, ih]
      ext P
      simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons]
      constructor
      · rintro (hP | hP)
        · exact ⟨R, Or.inl rfl, hP⟩
        · rcases hP with ⟨Q, hQ, hPQ⟩
          exact ⟨Q, Or.inr hQ, hPQ⟩
      · rintro ⟨Q, hQ, hPQ⟩
        rcases hQ with rfl | hQ
        · exact Or.inl hPQ
        · exact Or.inr ⟨Q, hQ, hPQ⟩

private theorem relabel_vars_empty {S : Type} {sig : Signature S}
    {X : SSet S} (ctx : KleeneCtx sig X) :
    ∀ {s : S} (P : Term sig X s),
      Term.varsIn (ctx.inXC (fun _ => ∅))
        (Term.relabel (extIncl X (fun r => Fin (ctx.n r))) P) :=
  @Term.rec _ _ _
    (motive_1 := fun _ P =>
      Term.varsIn (ctx.inXC (fun _ => ∅))
        (Term.relabel (extIncl X (fun r => Fin (ctx.n r))) P))
    (motive_2 := fun _ Ps =>
      TermVec.varsAllIn (ctx.inXC (fun _ => ∅))
        (TermVec.relabel (extIncl X (fun r => Fin (ctx.n r))) Ps))
    (fun _ => trivial)
    (fun _ _ hPs => hPs)
    trivial
    (fun _ _ hP hPs => ⟨hP, hPs⟩)

private theorem preimage_relabel_of_vars_empty {S : Type}
    {sig : Signature S} {X : SSet S} (ctx : KleeneCtx sig X) :
    ∀ {s : S} (Q : Term sig ctx.Z s),
      Term.varsIn (ctx.inXC (fun _ => ∅)) Q →
        ∃ P : Term sig X s,
          Term.relabel (extIncl X (fun r => Fin (ctx.n r))) P = Q :=
  @Term.rec _ _ _
    (motive_1 := fun s Q =>
      Term.varsIn (ctx.inXC (fun _ => ∅)) Q →
        ∃ P : Term sig X s,
          Term.relabel (extIncl X (fun r => Fin (ctx.n r))) P = Q)
    (motive_2 := fun w Qs =>
      TermVec.varsAllIn (ctx.inXC (fun _ => ∅)) Qs →
        ∃ Ps : TermVec sig X w,
          TermVec.relabel (extIncl X (fun r => Fin (ctx.n r))) Ps = Qs)
    (fun z hz => by
      cases z with
      | inl x => exact ⟨Term.var x, rfl⟩
      | inr m => exact hz.elim)
    (fun σ Qs ih hvars => by
      rcases ih hvars with ⟨Ps, hPs⟩
      exact ⟨Term.app σ Ps, congrArg (Term.app σ) hPs⟩)
    (fun _ => ⟨TermVec.nil, rfl⟩)
    (fun Q Qs ihQ ihQs hvars => by
      rcases ihQ hvars.1 with ⟨P, hP⟩
      rcases ihQs hvars.2 with ⟨Ps, hPs⟩
      exact ⟨TermVec.cons P Ps, congrArg₂ TermVec.cons hP hPs⟩)

private theorem hHom_relabel {S : Type} {sig : Signature S} {X : SSet S}
    (ctx : KleeneCtx sig X) :
    ∀ {s : S} (P : Term sig X s),
      ctx.hHom.toFun s
          (Term.relabel (extIncl X (fun r => Fin (ctx.n r))) P) =
        ctx.fHom.toFun s P :=
  @Term.rec _ _ _
    (motive_1 := fun s P =>
      ctx.hHom.toFun s
          (Term.relabel (extIncl X (fun r => Fin (ctx.n r))) P) =
        ctx.fHom.toFun s P)
    (motive_2 := fun _ Ps =>
      TermVec.evalArgs ctx.NAlg ctx.hAssign
          (TermVec.relabel (extIncl X (fun r => Fin (ctx.n r))) Ps) =
        TermVec.evalArgs ctx.NAlg ctx.fgen Ps)
    (fun _ => rfl)
    (fun σ Ps hPs => congrArg (ctx.Nop σ) hPs)
    rfl
    (fun _ _ hP hPs => congrArg₂ Prod.mk hP hPs)

private theorem mem_aux_full_iff {S : Type} {sig : Signature S}
    {X : SSet S} (ctx : KleeneCtx sig X) {u : S}
    (l : Fin (ctx.n u)) (Q : Term sig ctx.Z u) :
    Q ∈ ctx.auxLang u (fun _ => ∅) ctx.n l ↔
      ∃ P : Term sig X u,
        Term.relabel (extIncl X (fun r => Fin (ctx.n r))) P = Q ∧
        ctx.fHom.toFun u P = l := by
  constructor
  · rintro ⟨hvars, _, hval⟩
    rcases preimage_relabel_of_vars_empty ctx Q hvars with ⟨P, hPQ⟩
    refine ⟨P, hPQ, ?_⟩
    rw [← hHom_relabel ctx P, hPQ]
    exact hval
  · rintro ⟨P, rfl, hval⟩
    refine ⟨relabel_vars_empty ctx P, ?_, ?_⟩
    · intro A _ _ _
      exact (ctx.hHom.toFun A.1 A.2).isLt
    · exact (hHom_relabel ctx P).trans hval

theorem rec_subset_reg_proof {S : Type} [Finite S] (sig : Signature S)
    (X : SSet S) (hsig : SigFinite sig) (hX : SFinite X) (s : S) :
    RecS (freeAlgebra sig X) s ⊆ RegS sig X s := by
  classical
  intro L hL
  rcases hL with ⟨B, hB, f, M, hrecognizes⟩
  letI finiteB (r : S) : Finite (B.carrier r) :=
    finite_fiber_of_sfinite hB r
  letI fintypeB (r : S) : Fintype (B.carrier r) := Fintype.ofFinite _
  let n : S → ℕ := fun r => Fintype.card (B.carrier r)
  let e : (r : S) → B.carrier r ≃ Fin (n r) :=
    fun r => Fintype.equivFin (B.carrier r)
  let ctx : KleeneCtx sig X :=
    { n := n
      Nop := fun σ qs =>
        e _ (B.op σ (Args.map (fun r => (e r).symm) qs))
      fgen := fun r x => e r (f.toFun r (Term.var x)) }
  let eHom : Hom B ctx.NAlg :=
    { toFun := fun r => e r
      map_op := by
        intro w r σ args
        change e r (B.op σ args) =
          e r (B.op σ
            (Args.map (fun r => (e r).symm)
              (Args.map (fun r => e r) args)))
        exact congrArg (fun qs => e r (B.op σ qs))
          (Args.map_equiv_symm e args).symm }
  have hfEq : ctx.fHom = Hom.comp eHom f := by
    rcases free_universal sig X ctx.NAlg ctx.fgen with ⟨g, _, huniq⟩
    have hctx : ctx.fHom = g := by
      apply huniq
      intro r x
      rfl
    have hcomp : Hom.comp eHom f = g := by
      apply huniq
      intro r x
      rfl
    exact hctx.trans hcomp.symm
  have hmain : ∀ l : Fin (ctx.n s),
      ∃ R : RegExpr sig ctx.Z s,
        interpExpr sig ctx.Z s R =
          ctx.auxLang s (fun _ => ∅) ctx.n l := by
    intro l
    exact main_claim sig X hsig hX ctx s (fun _ => ∅) ctx.n
      (fun _ => Nat.le_refl _) l
  choose R hR using hmain
  let good : List (Fin (ctx.n s)) :=
    (Finset.univ.filter (fun l => (e s).symm l ∈ M)).toList
  let Rall : RegExpr sig ctx.Z s := RegExpr.sumR (good.map R)
  refine ⟨fun r => Fin (ctx.n r), ?_, ?_⟩
  · change SFinite ctx.Z
    unfold SFinite KleeneCtx.Z extVars
    letI : Finite (Σ r, X r) := hX
    letI finiteX (r : S) : Finite (X r) := finite_fiber_of_sfinite hX r
    letI finiteState (r : S) : Finite (Fin (ctx.n r)) := inferInstance
    letI finiteFiber (r : S) : Finite (X r ⊕ Fin (ctx.n r)) := inferInstance
    infer_instance
  · change ∃ R' : RegExpr sig ctx.Z s,
        interpExpr sig ctx.Z s R' =
          (fun P : Term sig X s =>
            Term.relabel (extIncl X (fun r => Fin (ctx.n r))) P) '' L
    refine ⟨Rall, ?_⟩
    rw [interp_sumR]
    ext Q
    constructor
    · rintro ⟨RQ, hRQ, hQ⟩
      rw [List.mem_map] at hRQ
      rcases hRQ with ⟨l, hl, rfl⟩
      have hlM : (e s).symm l ∈ M := by
        simpa [good] using hl
      have hQaux : Q ∈ ctx.auxLang s (fun _ => ∅) ctx.n l := by
        rw [← hR l]
        exact hQ
      rcases (mem_aux_full_iff ctx l Q).1 hQaux with ⟨P, hPQ, hstate⟩
      have heval : ctx.fHom.toFun s P = e s (f.toFun s P) := by
        rw [hfEq]
        rfl
      have hback : (e s).symm l = f.toFun s P := by
        rw [← hstate, heval, Equiv.symm_apply_apply]
      have hPM : f.toFun s P ∈ M := by simpa [← hback] using hlM
      have hPL : P ∈ L := by
        rw [← hrecognizes]
        exact hPM
      exact ⟨P, hPL, hPQ⟩
    · rintro ⟨P, hPL, rfl⟩
      have hPM : f.toFun s P ∈ M := by
        exact (Set.ext_iff.mp hrecognizes P).2 hPL
      let l : Fin (ctx.n s) := e s (f.toFun s P)
      have hl : l ∈ good := by
        simp [good, l, hPM]
      refine ⟨R l, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
      rw [hR l]
      apply (mem_aux_full_iff ctx l _).2
      refine ⟨P, rfl, ?_⟩
      rw [hfEq]
      rfl

end MSKleene

theorem solution {S : Type} [Finite S] (sig : MSKleene.Signature S)
    (X : MSKleene.SSet S) (hsig : MSKleene.SigFinite sig)
    (hX : MSKleene.SFinite X) (s : S) :
    MSKleene.RecS (MSKleene.freeAlgebra sig X) s ⊆
      MSKleene.RegS sig X s :=
  MSKleene.rec_subset_reg_proof sig X hsig hX s
