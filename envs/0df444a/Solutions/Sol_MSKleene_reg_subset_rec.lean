-- Prove2me | solution 1 for MSKleene.reg_subset_rec
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T07:58:13.910157+00:00
-- url     : https://prove2.me/submissions/2bdaca6a-6fb2-4ee1-a4b9-2588cde618ba

import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_Regular
import Theorems.Thm_MSKleene_rec_basic
import Theorems.Thm_MSKleene_rec_closed_reg

open MSKleene

namespace MSKleene

private theorem interp_recognizable {S : Type} [Finite S]
    (sig : Signature S) (Z : SSet S) (hZ : SFinite Z) :
    ∀ {s : S} (R : RegExpr sig Z s),
      sRecognizable (freeAlgebra sig Z) s (interpExpr sig Z s R) :=
  @Term.rec _ _ _
    (motive_1 := fun s R =>
      sRecognizable (freeAlgebra sig Z) s (interpExpr sig Z s R))
    (motive_2 := fun w Rs =>
      Args.All
        (fun s L => sRecognizable (freeAlgebra sig Z) s L)
        (TermVec.evalArgs (regPowerAlgebra sig Z) (regGenAssign sig Z) Rs))
    (fun z => by
      change sRecognizable (freeAlgebra sig Z) _ {Term.var z}
      exact (rec_basic sig Z _).1 z)
    (fun sym Rs hRs => by
      change sRecognizable (freeAlgebra sig Z) _
        ((regPowerAlgebra sig Z).op sym
          (TermVec.evalArgs (regPowerAlgebra sig Z) (regGenAssign sig Z) Rs))
      exact rec_closed_reg sig Z hZ sym _ hRs)
    trivial
    (fun _ _ hR hRs => ⟨hR, hRs⟩)

private theorem eval_extIncl {S : Type} (sig : Signature S)
    (X E : SSet S) :
    ∀ {s : S} (P : Term sig X s),
      Term.eval (freeAlgebra sig (extVars X E))
          (fun r x => Term.var (extIncl X E r x)) P =
        Term.relabel (extIncl X E) P :=
  @Term.rec _ _ _
    (motive_1 := fun s P =>
      Term.eval (freeAlgebra sig (extVars X E))
          (fun r x => Term.var (extIncl X E r x)) P =
        Term.relabel (extIncl X E) P)
    (motive_2 := fun w Ps =>
      TermVec.ofArgs
          (TermVec.evalArgs (freeAlgebra sig (extVars X E))
            (fun r x => Term.var (extIncl X E r x)) Ps) =
        TermVec.relabel (extIncl X E) Ps)
    (fun _ => rfl)
    (fun σ _ hPs => congrArg (Term.app σ) hPs)
    rfl
    (fun _ _ hP hPs => congrArg₂ TermVec.cons hP hPs)

private def sequenceArgs {S : Type} {A : SSet S} :
    {w : List S} → Args (fun r => Option (A r)) w → Option (Args A w)
  | [], _ => some PUnit.unit
  | _ :: _, (none, _) => none
  | _ :: _, (some a, qs) => Option.map (Prod.mk a) (sequenceArgs qs)

private noncomputable def decodeAlgebra {S : Type} (sig : Signature S)
    (X : SSet S) : Algebra sig where
  carrier := fun r => Option (Term sig X r)
  op := fun σ qs => Option.map
    (fun args => Term.app σ (TermVec.ofArgs args)) (sequenceArgs qs)

private def decodeAssign {S : Type} {sig : Signature S} (X E : SSet S) :
    SMap (extVars X E) (decodeAlgebra sig X).carrier
  | _, Sum.inl x => some (Term.var x)
  | _, Sum.inr _ => none

private theorem ofArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (Ps : TermVec sig X w),
      TermVec.ofArgs (TermVec.toArgs Ps) = Ps
  | [], .nil => rfl
  | _ :: _, .cons P Ps => congrArg (TermVec.cons P) (ofArgs_toArgs Ps)

private theorem decode_relabel {S : Type} (sig : Signature S)
    (X E : SSet S) :
    ∀ {s : S} (P : Term sig X s),
      Term.eval (decodeAlgebra sig X) (decodeAssign X E)
          (Term.relabel (extIncl X E) P) = some P :=
  @Term.rec _ _ _
    (motive_1 := fun _ P =>
      Term.eval (decodeAlgebra sig X) (decodeAssign X E)
          (Term.relabel (extIncl X E) P) = some P)
    (motive_2 := fun _ Ps =>
      sequenceArgs
          (TermVec.evalArgs (decodeAlgebra sig X) (decodeAssign X E)
            (TermVec.relabel (extIncl X E) Ps)) =
        some (TermVec.toArgs Ps))
    (fun _ => rfl)
    (fun σ Ps hPs => by
      change Option.map (fun args => Term.app σ (TermVec.ofArgs args))
          (sequenceArgs
            (TermVec.evalArgs (decodeAlgebra sig X) (decodeAssign X E)
              (TermVec.relabel (extIncl X E) Ps))) =
        some (Term.app σ Ps)
      rw [hPs]
      change some (Term.app σ (TermVec.ofArgs (TermVec.toArgs Ps))) =
        some (Term.app σ Ps)
      rw [ofArgs_toArgs])
    rfl
    (fun {s} {w} P Ps hP hPs => by
      change @sequenceArgs S (Term sig X) (s :: w)
          (Term.eval (decodeAlgebra sig X) (decodeAssign X E)
              (Term.relabel (extIncl X E) P),
            TermVec.evalArgs (decodeAlgebra sig X) (decodeAssign X E)
              (TermVec.relabel (extIncl X E) Ps)) =
        some ((P, TermVec.toArgs Ps) : Args (Term sig X) (s :: w))
      rw [hP]
      simp only [sequenceArgs]
      rw [hPs]
      rfl)

private theorem relabel_extIncl_injective {S : Type} {sig : Signature S}
    (X E : SSet S) {s : S} :
    Function.Injective
      (fun P : Term sig X s => Term.relabel (extIncl X E) P) := by
  intro P Q hPQ
  have hdecode := congrArg
    (fun R => Term.eval (decodeAlgebra sig X) (decodeAssign X E) R) hPQ
  rw [decode_relabel sig X E P, decode_relabel sig X E Q] at hdecode
  exact Option.some.inj hdecode

end MSKleene

theorem solution {S : Type} [Finite S] (sig : MSKleene.Signature S)
    (X : MSKleene.SSet S) (hsig : MSKleene.SigFinite sig)
    (hX : MSKleene.SFinite X) (s : S) :
    MSKleene.RegS sig X s ⊆ MSKleene.RecS (MSKleene.freeAlgebra sig X) s := by
  intro L hL
  rcases hL with ⟨E, hXE, R, hR⟩
  have hInterp := MSKleene.interp_recognizable sig (MSKleene.extVars X E) hXE R
  rcases hInterp with ⟨B, hB, f, M, hf⟩
  let inclusion : MSKleene.Hom (MSKleene.freeAlgebra sig X)
      (MSKleene.freeAlgebra sig (MSKleene.extVars X E)) :=
    MSKleene.evalHom (MSKleene.freeAlgebra sig (MSKleene.extVars X E))
      (fun r x => MSKleene.Term.var (MSKleene.extIncl X E r x))
  refine ⟨B, hB, MSKleene.Hom.comp f inclusion, M, ?_⟩
  ext P
  change f.toFun s (inclusion.toFun s P) ∈ M ↔ P ∈ L
  have hinclusion : inclusion.toFun s P =
      MSKleene.Term.relabel (MSKleene.extIncl X E) P :=
    MSKleene.eval_extIncl sig X E P
  rw [hinclusion]
  have hpre : f.toFun s (MSKleene.Term.relabel (MSKleene.extIncl X E) P) ∈ M ↔
      MSKleene.Term.relabel (MSKleene.extIncl X E) P ∈
        MSKleene.interpExpr sig (MSKleene.extVars X E) s R := by
    change MSKleene.Term.relabel (MSKleene.extIncl X E) P ∈
        f.toFun s ⁻¹' M ↔ _
    exact Set.ext_iff.mp hf _
  refine hpre.trans ?_
  have himage : MSKleene.Term.relabel (MSKleene.extIncl X E) P ∈
      MSKleene.interpExpr sig (MSKleene.extVars X E) s R ↔
      MSKleene.Term.relabel (MSKleene.extIncl X E) P ∈
        (fun Q => MSKleene.Term.relabel (MSKleene.extIncl X E) Q) '' L :=
    Set.ext_iff.mp hR _
  refine himage.trans ?_
  constructor
  · rintro ⟨Q, hQL, hQP⟩
    have hQP' : Q = P := MSKleene.relabel_extIncl_injective X E hQP
    cases hQP'
    exact hQL
  · intro hPL
    exact ⟨P, hPL, rfl⟩
