-- Prove2me | solution 1 for MSKleene.rec_op
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T06:55:19.2203+00:00
-- url     : https://prove2.me/submissions/74ea1eed-2775-4cea-8ce1-ddea9cabc6fd

import Definitions.Def_MSKleene_Term
import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_Power
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Pi

open MSKleene
open Classical

namespace MSKleene

private def Args.get {S : Type} {A : SSet S} :
    {w : List S} → Args A w → (i : Fin w.length) → A (w.get i)
  | [], _, i => Fin.elim0 i
  | _ :: _, (a, as), i => Fin.cases a (fun j => Args.get as j) i

private theorem Args.get_map {S : Type} {A B : SSet S} (f : SMap A B) :
    ∀ {w : List S} (xs : Args A w) (i : Fin w.length),
      Args.get (Args.map f xs) i = f (w.get i) (Args.get xs i)
  | [], _, i => Fin.elim0 i
  | _ :: _, (x, xs), i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact Args.get_map f xs j

private theorem Args.pmem_iff_get {S : Type} {A : SSet S} :
    ∀ {w : List S} (xs : Args A w) (Ls : Args (fun r => Set (A r)) w),
      Args.pmem xs Ls ↔ ∀ i : Fin w.length, Args.get xs i ∈ Args.get Ls i
  | [], _, _ => ⟨fun _ i => Fin.elim0 i, fun _ => trivial⟩
  | _ :: _, (x, xs), (L, Ls) => by
      constructor
      · rintro ⟨hx, hxs⟩ i
        refine Fin.cases hx (fun j => (Args.pmem_iff_get xs Ls).mp hxs j) i
      · intro h
        constructor
        · exact h ⟨0, by simp⟩
        · apply (Args.pmem_iff_get xs Ls).mpr
          intro j
          exact h j.succ

private theorem Args.all_iff_get {S : Type} {A : SSet S}
    (P : (r : S) → A r → Prop) :
    ∀ {w : List S} (xs : Args A w),
      Args.All P xs ↔ ∀ i : Fin w.length, P (w.get i) (Args.get xs i)
  | [], _ => ⟨fun _ i => Fin.elim0 i, fun _ => trivial⟩
  | _ :: _, (x, xs) => by
      constructor
      · rintro ⟨hx, hxs⟩ i
        refine Fin.cases hx (fun j => (Args.all_iff_get P xs).mp hxs j) i
      · intro h
        constructor
        · exact h ⟨0, by simp⟩
        · apply (Args.all_iff_get P xs).mpr
          intro j
          exact h j.succ

private theorem toArgs_ofArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (xs : Args (Term sig X) w),
      TermVec.toArgs (TermVec.ofArgs xs) = xs
  | [], _ => rfl
  | _ :: _, (x, xs) => congrArg (Prod.mk x) (toArgs_ofArgs xs)

private theorem ofArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (ts : TermVec sig X w), TermVec.ofArgs ts.toArgs = ts
  | [], .nil => rfl
  | _ :: _, .cons t ts => congrArg (TermVec.cons t) (ofArgs_toArgs ts)

private theorem evalArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S}
    (B : Algebra sig) (ρ : SMap X B.carrier) :
    ∀ {w : List S} (ts : TermVec sig X w),
      TermVec.evalArgs B ρ ts = Args.map (fun r P => Term.eval B ρ P) ts.toArgs
  | [], .nil => rfl
  | _ :: _, .cons t ts => congrArg (Prod.mk (Term.eval B ρ t))
      (evalArgs_toArgs B ρ ts)

private theorem hom_app {S : Type} {sig : Signature S} {X : SSet S}
    {B : Algebra sig} (g : Hom (freeAlgebra sig X) B) {w : List S} {r : S}
    (σ : sig w r) (ts : TermVec sig X w) :
    g.toFun r (Term.app σ ts) = B.op σ (Args.map g.toFun ts.toArgs) := by
  calc
    g.toFun r (Term.app σ ts) =
        g.toFun r ((freeAlgebra sig X).op σ ts.toArgs) := by
          change g.toFun r (Term.app σ ts) =
            g.toFun r (Term.app σ (TermVec.ofArgs ts.toArgs))
          rw [ofArgs_toArgs]
    _ = B.op σ (Args.map g.toFun ts.toArgs) := g.map_op _ _

private def opTag {S : Type} {sig : Signature S} {w : List S} {r : S}
    (σ : sig w r) : (w : List S) × (r : S) × sig w r := ⟨w, r, σ⟩

private abbrev OpState {S : Type} {sig : Signature S} {w : List S}
    (Bs : (i : Fin w.length) → Algebra sig) (r : S) :=
  Bool × ((i : Fin w.length) → (Bs i).carrier r)

private noncomputable def coordPart {S : Type} {sig : Signature S}
    {w v : List S} {r : S} (Bs : (i : Fin w.length) → Algebra sig)
    (τ : sig v r) (qs : Args (OpState Bs) v) :
    (i : Fin w.length) → (Bs i).carrier r :=
  fun i => (Bs i).op τ (Args.map (fun _ q => q.2 i) qs)

private noncomputable def rootFlag {S : Type} {sig : Signature S}
    {w v : List S} {s r : S} (σ : sig w s)
    (Bs : (i : Fin w.length) → Algebra sig)
    (Ms : (i : Fin w.length) → Set ((Bs i).carrier (w.get i)))
    (τ : sig v r) (qs : Args (OpState Bs) v) : Bool :=
  decide (∃ target : Args (OpState Bs) w,
    opTag τ = opTag σ ∧ HEq qs target ∧
      ∀ i : Fin w.length, (Args.get target i).2 i ∈ Ms i)

private noncomputable def opRecognizerAlg {S : Type} {sig : Signature S}
    {w : List S} {s : S} (σ : sig w s)
    (Bs : (i : Fin w.length) → Algebra sig)
    (Ms : (i : Fin w.length) → Set ((Bs i).carrier (w.get i))) : Algebra sig where
  carrier := OpState Bs
  op := fun τ qs => (rootFlag σ Bs Ms τ qs, coordPart Bs τ qs)

private noncomputable def opRecognizerAssign {S : Type} {sig : Signature S}
    {X : SSet S} {w : List S} {s : S} (σ : sig w s)
    (Bs : (i : Fin w.length) → Algebra sig)
    (gs : (i : Fin w.length) → Hom (freeAlgebra sig X) (Bs i))
    (Ms : (i : Fin w.length) → Set ((Bs i).carrier (w.get i))) :
    SMap X (opRecognizerAlg σ Bs Ms).carrier :=
  fun r x => (false, fun i => (gs i).toFun r (Term.var x))

mutual
private theorem coord_term {S : Type} {sig : Signature S} {X : SSet S}
    {w : List S} {s : S} (σ : sig w s)
    (Bs : (i : Fin w.length) → Algebra sig)
    (gs : (i : Fin w.length) → Hom (freeAlgebra sig X) (Bs i))
    (Ms : (i : Fin w.length) → Set ((Bs i).carrier (w.get i)))
    {r : S} (R : Term sig X r) (i : Fin w.length) :
    (Term.eval (opRecognizerAlg σ Bs Ms) (opRecognizerAssign σ Bs gs Ms) R).2 i =
      (gs i).toFun r R := by
  cases R with
  | var x => rfl
  | app τ rs =>
      change (Bs i).op τ (Args.map (fun _ q => q.2 i)
        (TermVec.evalArgs (opRecognizerAlg σ Bs Ms)
          (opRecognizerAssign σ Bs gs Ms) rs)) = (gs i).toFun _ (Term.app τ rs)
      rw [hom_app]
      exact congrArg ((Bs i).op τ) (coord_vec σ Bs gs Ms rs i)

private theorem coord_vec {S : Type} {sig : Signature S} {X : SSet S}
    {w : List S} {s : S} (σ : sig w s)
    (Bs : (i : Fin w.length) → Algebra sig)
    (gs : (i : Fin w.length) → Hom (freeAlgebra sig X) (Bs i))
    (Ms : (i : Fin w.length) → Set ((Bs i).carrier (w.get i)))
    {v : List S} (rs : TermVec sig X v) (i : Fin w.length) :
    Args.map (fun _ q => q.2 i)
        (TermVec.evalArgs (opRecognizerAlg σ Bs Ms)
          (opRecognizerAssign σ Bs gs Ms) rs) =
      Args.map (gs i).toFun rs.toArgs := by
  cases rs with
  | nil => rfl
  | cons R rs =>
      apply Prod.ext
      · exact coord_term σ Bs gs Ms R i
      · exact coord_vec σ Bs gs Ms rs i
end

private theorem finite_fiber {S : Type} {Y : SSet S} (hY : SFinite Y) (r : S) :
    Finite (Y r) := by
  letI : Finite (Sigma Y) := hY
  apply Finite.of_injective (fun y : Y r => Sigma.mk r y)
  intro a b hab
  exact eq_of_heq (Sigma.mk.inj hab).2

end MSKleene

theorem solution {S : Type} [Finite S] (sig : Signature S) (X : SSet S)
    (hX : SFinite X) {w : List S} {s : S} (σ : sig w s)
    (Ls : Args (fun s => Set (Term sig X s)) w)
    (hLs : Args.All (fun s L => sRecognizable (freeAlgebra sig X) s L) Ls) :
    sRecognizable (freeAlgebra sig X) s (powerOp (freeAlgebra sig X) σ Ls) := by
  have hi : ∀ i : Fin w.length,
      ∃ B : Algebra sig, B.Finite ∧
        ∃ (g : Hom (freeAlgebra sig X) B)
          (M : Set (B.carrier (w.get i))),
          g.toFun (w.get i) ⁻¹' M = Args.get Ls i := by
    exact (Args.all_iff_get
      (fun r L => sRecognizable (freeAlgebra sig X) r L) Ls).mp hLs
  choose Bs hBs hrest using hi
  choose gs Ms hMs using hrest
  let C := opRecognizerAlg σ Bs Ms
  let assign := opRecognizerAssign σ Bs gs Ms
  refine ⟨C, ?_, evalHom C assign, {q | q.1 = true}, ?_⟩
  · show Finite (Σ r, OpState Bs r)
    letI finB (i : Fin w.length) (r : S) : Finite ((Bs i).carrier r) :=
      finite_fiber (hBs i) r
    infer_instance
  · ext R
    change (Term.eval (opRecognizerAlg σ Bs Ms)
      (opRecognizerAssign σ Bs gs Ms) R).1 = true ↔
      R ∈ powerOp (freeAlgebra sig X) σ Ls
    cases R with
    | var x =>
        constructor
        · intro h
          contradiction
        · rintro ⟨ys, _, hbad⟩
          contradiction
    | app τ rs =>
        by_cases htag : opTag τ = opTag σ
        · cases htag
          have hdiag :
              (∀ i : Fin w.length,
                (Args.get (TermVec.evalArgs (opRecognizerAlg σ Bs Ms)
                  (opRecognizerAssign σ Bs gs Ms) rs) i).2 i ∈ Ms i) ↔
                Args.pmem rs.toArgs Ls := by
            rw [Args.pmem_iff_get]
            constructor
            · intro h i
              have hget :
                  (Args.get (TermVec.evalArgs (opRecognizerAlg σ Bs Ms)
                    (opRecognizerAssign σ Bs gs Ms) rs) i).2 i =
                    (gs i).toFun (w.get i) (Args.get rs.toArgs i) := by
                let ev : SMap (Term sig X) (opRecognizerAlg σ Bs Ms).carrier :=
                  fun r P => Term.eval (opRecognizerAlg σ Bs Ms)
                    (opRecognizerAssign σ Bs gs Ms) P
                calc
                  _ = (Args.get (Args.map ev rs.toArgs) i).2 i := by
                    exact congrArg (fun qs => (Args.get qs i).2 i)
                      (evalArgs_toArgs (opRecognizerAlg σ Bs Ms)
                        (opRecognizerAssign σ Bs gs Ms) rs)
                  _ = (ev (w.get i) (Args.get rs.toArgs i)).2 i := by
                    exact congrArg (fun q => q.2 i) (Args.get_map ev rs.toArgs i)
                  _ = _ := coord_term σ Bs gs Ms (Args.get rs.toArgs i) i
              have hm := Set.ext_iff.mp (hMs i) (Args.get rs.toArgs i)
              have hi := h i
              rw [hget] at hi
              exact hm.mp hi
            · intro h i
              have hget :
                  (Args.get (TermVec.evalArgs (opRecognizerAlg σ Bs Ms)
                    (opRecognizerAssign σ Bs gs Ms) rs) i).2 i =
                    (gs i).toFun (w.get i) (Args.get rs.toArgs i) := by
                let ev : SMap (Term sig X) (opRecognizerAlg σ Bs Ms).carrier :=
                  fun r P => Term.eval (opRecognizerAlg σ Bs Ms)
                    (opRecognizerAssign σ Bs gs Ms) P
                calc
                  _ = (Args.get (Args.map ev rs.toArgs) i).2 i := by
                    exact congrArg (fun qs => (Args.get qs i).2 i)
                      (evalArgs_toArgs (opRecognizerAlg σ Bs Ms)
                        (opRecognizerAssign σ Bs gs Ms) rs)
                  _ = (ev (w.get i) (Args.get rs.toArgs i)).2 i := by
                    exact congrArg (fun q => q.2 i) (Args.get_map ev rs.toArgs i)
                  _ = _ := coord_term σ Bs gs Ms (Args.get rs.toArgs i) i
              have hm := Set.ext_iff.mp (hMs i) (Args.get rs.toArgs i)
              rw [hget]
              exact hm.mpr (h i)
          have hpow :
              Term.app σ rs ∈ powerOp (freeAlgebra sig X) σ Ls ↔
                Args.pmem rs.toArgs Ls := by
            constructor
            · rintro ⟨ys, hys, heq⟩
              change Term.app σ rs = Term.app σ (TermVec.ofArgs ys) at heq
              cases heq
              change Args.pmem
                (TermVec.toArgs (TermVec.ofArgs
                  (show Args (Term sig X) _ from ys))) Ls
              rw [toArgs_ofArgs]
              exact hys
            · intro hrs
              refine ⟨rs.toArgs, hrs, ?_⟩
              change Term.app σ rs = Term.app σ (TermVec.ofArgs rs.toArgs)
              rw [ofArgs_toArgs]
          change rootFlag σ Bs Ms σ
            (TermVec.evalArgs (opRecognizerAlg σ Bs Ms)
              (opRecognizerAssign σ Bs gs Ms) rs) = true ↔ _
          have hroot :
              (∃ target : Args (OpState Bs) w,
                opTag σ = opTag σ ∧
                HEq (TermVec.evalArgs (opRecognizerAlg σ Bs Ms)
                  (opRecognizerAssign σ Bs gs Ms) rs) target ∧
                ∀ i : Fin w.length, (Args.get target i).2 i ∈ Ms i) ↔
              ∀ i : Fin w.length,
                (Args.get (TermVec.evalArgs (opRecognizerAlg σ Bs Ms)
                  (opRecognizerAssign σ Bs gs Ms) rs) i).2 i ∈ Ms i := by
            constructor
            · rintro ⟨target, _, heq, ht⟩
              have heq' := eq_of_heq heq
              subst target
              exact ht
            · intro ht
              exact ⟨_, rfl, HEq.rfl, ht⟩
          constructor
          · intro h
            have hp := of_decide_eq_true h
            exact hpow.mpr (hdiag.mp (hroot.mp hp))
          · intro h
            exact decide_eq_true (hroot.mpr (hdiag.mpr (hpow.mp h)))
        · constructor
          · intro h
            change rootFlag σ Bs Ms τ
              (TermVec.evalArgs (opRecognizerAlg σ Bs Ms)
                (opRecognizerAssign σ Bs gs Ms) rs) = true at h
            have hp := of_decide_eq_true h
            rcases hp with ⟨_, hbad, _⟩
            exact False.elim (htag hbad)
          · rintro ⟨ys, _, heq⟩
            change Term.app τ rs = Term.app σ (TermVec.ofArgs ys) at heq
            cases heq
            exact False.elim (htag rfl)
