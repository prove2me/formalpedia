-- Prove2me | solution 1 for MSKleene.rec_subst
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T06:28:51.97772+00:00
-- url     : https://prove2.me/submissions/0bbc6a09-caf9-428f-88e4-1e076b99eddb

import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_SubstGlobal
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Powerset

open MSKleene
open Classical

namespace MSKleene

private abbrev VX {S : Type} (X : SSet S) := Sigma X

private abbrev SubstState {S : Type} {sig : Signature S} {X : SSet S}
    (A : Algebra sig) (Bs : VX X → Algebra sig) (r : S) :=
  Set (A.carrier r) × ((v : VX X) → (Bs v).carrier r)

private noncomputable def varPart {S : Type} {sig : Signature S} {X : SSet S}
    (Bs : VX X → Algebra sig)
    (gs : (v : VX X) → Hom (freeAlgebra sig X) (Bs v))
    (r : S) (y : X r) : (v : VX X) → (Bs v).carrier r :=
  fun v => (gs v).toFun r (Term.var y)

private noncomputable def prodPart {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (Bs : VX X → Algebra sig) {w : List S} {r : S} (τ : sig w r)
    (qs : Args (SubstState A Bs) w) : (v : VX X) → (Bs v).carrier r :=
  fun v => (Bs v).op τ (Args.map (fun _ q => q.2 v) qs)

private noncomputable def addVars {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} {Bs : VX X → Algebra sig}
    (f : Hom (freeAlgebra sig X) A)
    (Ms : (v : VX X) → Set ((Bs v).carrier v.1)) (r : S)
    (p : (v : VX X) → (Bs v).carrier r) (Q : Set (A.carrier r)) :
    Set (A.carrier r) :=
  Q ∪ {a | ∃ x : X r, p ⟨r, x⟩ ∈ Ms ⟨r, x⟩ ∧ a = f.toFun r (Term.var x)}

private noncomputable def substRecognizerAlg {S : Type} {sig : Signature S}
    {X : SSet S} (A : Algebra sig) (f : Hom (freeAlgebra sig X) A)
    (Bs : VX X → Algebra sig)
    (gs : (v : VX X) → Hom (freeAlgebra sig X) (Bs v))
    (Ms : (v : VX X) → Set ((Bs v).carrier v.1)) : Algebra sig where
  carrier := SubstState A Bs
  op := fun {w} {r} τ qs =>
    let p := prodPart Bs τ qs
    (addVars f Ms r p (powerOp A τ (Args.map (fun _ q => q.1) qs)), p)

private noncomputable def substRecognizerAssign {S : Type} {sig : Signature S}
    {X : SSet S} {A : Algebra sig} (f : Hom (freeAlgebra sig X) A)
    (Bs : VX X → Algebra sig)
    (gs : (v : VX X) → Hom (freeAlgebra sig X) (Bs v))
    (Ms : (v : VX X) → Set ((Bs v).carrier v.1)) :
    SMap X (substRecognizerAlg A f Bs gs Ms).carrier :=
  fun r y =>
    let p := varPart Bs gs r y
    (addVars f Ms r p ∅, p)

private theorem ofArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (ts : TermVec sig X w), TermVec.ofArgs (TermVec.toArgs ts) = ts
  | [], .nil => rfl
  | _ :: _, .cons t ts => congrArg (TermVec.cons t) (ofArgs_toArgs ts)

private theorem toArgs_ofArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (xs : Args (Term sig X) w),
      TermVec.toArgs (TermVec.ofArgs xs) = xs
  | [], _ => rfl
  | _ :: _, (x, xs) => congrArg (Prod.mk x) (toArgs_ofArgs xs)

private theorem evalArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S}
    (B : Algebra sig) (ρ : SMap X B.carrier) :
    ∀ {w : List S} (ts : TermVec sig X w),
      TermVec.evalArgs B ρ ts =
        Args.map (fun r P => Term.eval B ρ P) (TermVec.toArgs ts)
  | [], .nil => rfl
  | _ :: _, .cons t ts => congrArg (Prod.mk (Term.eval B ρ t))
      (evalArgs_toArgs B ρ ts)

private theorem hom_app {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {w : List S} {s : S}
    (σ : sig w s) (ts : TermVec sig X w) :
    g.toFun s (Term.app σ ts) = A.op σ (Args.map g.toFun (TermVec.toArgs ts)) := by
  calc
    g.toFun s (Term.app σ ts) =
        g.toFun s ((freeAlgebra sig X).op σ (TermVec.toArgs ts)) := by
          change g.toFun s (Term.app σ ts) =
            g.toFun s (Term.app σ (TermVec.ofArgs (TermVec.toArgs ts)))
          rw [ofArgs_toArgs]
    _ = A.op σ (Args.map g.toFun (TermVec.toArgs ts)) := g.map_op _ _

mutual
private theorem subst_snd_term {S : Type} {sig : Signature S} {X : SSet S}
    (A : Algebra sig) (f : Hom (freeAlgebra sig X) A)
    (Bs : VX X → Algebra sig)
    (gs : (v : VX X) → Hom (freeAlgebra sig X) (Bs v))
    (Ms : (v : VX X) → Set ((Bs v).carrier v.1))
    {r : S} (R : Term sig X r) (v : VX X) :
    (Term.eval (substRecognizerAlg A f Bs gs Ms)
      (substRecognizerAssign f Bs gs Ms) R).2 v = (gs v).toFun r R := by
  cases R with
  | var y => rfl
  | app τ rs =>
      change (Bs v).op τ
          (Args.map (fun _ q => q.2 v)
            (TermVec.evalArgs (substRecognizerAlg A f Bs gs Ms)
              (substRecognizerAssign f Bs gs Ms) rs)) =
        (gs v).toFun _ (Term.app τ rs)
      rw [hom_app]
      exact congrArg ((Bs v).op τ) (subst_snd_vec A f Bs gs Ms rs v)

private theorem subst_snd_vec {S : Type} {sig : Signature S} {X : SSet S}
    (A : Algebra sig) (f : Hom (freeAlgebra sig X) A)
    (Bs : VX X → Algebra sig)
    (gs : (v : VX X) → Hom (freeAlgebra sig X) (Bs v))
    (Ms : (v : VX X) → Set ((Bs v).carrier v.1))
    {w : List S} (rs : TermVec sig X w) (v : VX X) :
    Args.map (fun _ q => q.2 v)
        (TermVec.evalArgs (substRecognizerAlg A f Bs gs Ms)
          (substRecognizerAssign f Bs gs Ms) rs) =
      Args.map (gs v).toFun (TermVec.toArgs rs) := by
  cases rs with
  | nil => rfl
  | cons R rs =>
      change ((Term.eval (substRecognizerAlg A f Bs gs Ms)
          (substRecognizerAssign f Bs gs Ms) R).2 v,
        Args.map (fun _ q => q.2 v)
          (TermVec.evalArgs (substRecognizerAlg A f Bs gs Ms)
            (substRecognizerAssign f Bs gs Ms) rs)) =
        ((gs v).toFun _ R, Args.map (gs v).toFun (TermVec.toArgs rs))
      apply Prod.ext
      · exact subst_snd_term A f Bs gs Ms R v
      · exact subst_snd_vec A f Bs gs Ms rs v
end

private theorem rec_mem_iff {S : Type} {sig : Signature S} {X : SSet S}
    {B : Algebra sig} (g : Hom (freeAlgebra sig X) B) {r : S}
    (M : Set (B.carrier r)) (L : Set (Term sig X r))
    (h : g.toFun r ⁻¹' M = L) (R : Term sig X r) :
    g.toFun r R ∈ M ↔ R ∈ L := by
  change R ∈ g.toFun r ⁻¹' M ↔ R ∈ L
  exact Set.ext_iff.mp h R

mutual
private theorem subst_fst_term {S : Type} {sig : Signature S} {X : SSet S}
    (A : Algebra sig) (f : Hom (freeAlgebra sig X) A)
    (ρ : SMap X (powerAlgebra (freeAlgebra sig X)).carrier)
    (Bs : VX X → Algebra sig)
    (gs : (v : VX X) → Hom (freeAlgebra sig X) (Bs v))
    (Ms : (v : VX X) → Set ((Bs v).carrier v.1))
    (hMs : ∀ v : VX X, (gs v).toFun v.1 ⁻¹' Ms v = ρ v.1 v.2)
    {r : S} (R : Term sig X r) (a : A.carrier r) :
    a ∈ (Term.eval (substRecognizerAlg A f Bs gs Ms)
      (substRecognizerAssign f Bs gs Ms) R).1 ↔
      ∃ P : Term sig X r,
        R ∈ (show Set (Term sig X r) from (substGlobalHom ρ).toFun r P) ∧
        a = f.toFun r P := by
  cases R with
  | var y =>
      constructor
      · intro ha
        change a ∈ addVars f Ms r (varPart Bs gs r y) ∅ at ha
        rcases ha with ha | ha
        · exact False.elim ha
        · rcases ha with ⟨x, hx, rfl⟩
          refine ⟨Term.var x, ?_, rfl⟩
          change Term.var y ∈ (show Set (Term sig X r) from ρ r x)
          exact (rec_mem_iff (gs ⟨r, x⟩) (Ms ⟨r, x⟩) (ρ r x)
            (hMs ⟨r, x⟩) (Term.var y)).mp hx
      · rintro ⟨P, hRP, rfl⟩
        cases P with
        | var x =>
            change Term.var y ∈ (show Set (Term sig X r) from ρ r x) at hRP
            change f.toFun r (Term.var x) ∈
              addVars f Ms r (varPart Bs gs r y) ∅
            right
            refine ⟨x, ?_, rfl⟩
            change (gs ⟨r, x⟩).toFun r (Term.var y) ∈ Ms ⟨r, x⟩
            exact (rec_mem_iff (gs ⟨r, x⟩) (Ms ⟨r, x⟩) (ρ r x)
              (hMs ⟨r, x⟩) (Term.var y)).mpr hRP
        | app τ ps =>
            change Term.var y ∈ powerOp (freeAlgebra sig X) τ
              (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X)) ρ ps) at hRP
            rcases hRP with ⟨ys, _, hbad⟩
            contradiction
  | app τ rs =>
      have ihVec := subst_fst_vec A f ρ Bs gs Ms hMs rs
      constructor
      · intro ha
        change a ∈ addVars f Ms r
          (prodPart Bs τ (TermVec.evalArgs (substRecognizerAlg A f Bs gs Ms)
            (substRecognizerAssign f Bs gs Ms) rs))
          (powerOp A τ (Args.map (fun _ q => q.1)
            (TermVec.evalArgs (substRecognizerAlg A f Bs gs Ms)
              (substRecognizerAssign f Bs gs Ms) rs))) at ha
        rcases ha with ha | ha
        · rcases ha with ⟨as, has, rfl⟩
          rcases (ihVec as).mp has with
            ⟨ps, hrs, hasf⟩
          refine ⟨Term.app τ (TermVec.ofArgs ps), ?_, ?_⟩
          · change Term.app τ rs ∈ powerOp (freeAlgebra sig X) τ
              (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X)) ρ
                (TermVec.ofArgs ps))
            refine ⟨TermVec.toArgs rs, ?_, ?_⟩
            · rw [TermVec.evalArgs_ofArgs]
              exact hrs
            · change Term.app τ rs = Term.app τ
                (TermVec.ofArgs (TermVec.toArgs rs))
              rw [ofArgs_toArgs]
          · rw [hom_app, hasf, toArgs_ofArgs]
        · rcases ha with ⟨x, hx, rfl⟩
          refine ⟨Term.var x, ?_, rfl⟩
          change Term.app τ rs ∈ (show Set (Term sig X r) from ρ r x)
          apply (rec_mem_iff (gs ⟨r, x⟩) (Ms ⟨r, x⟩) (ρ r x)
            (hMs ⟨r, x⟩) (Term.app τ rs)).mp
          rw [← subst_snd_term A f Bs gs Ms (Term.app τ rs) ⟨r, x⟩]
          exact hx
      · rintro ⟨P, hRP, rfl⟩
        cases P with
        | var x =>
            change Term.app τ rs ∈ (show Set (Term sig X r) from ρ r x) at hRP
            change f.toFun r (Term.var x) ∈ addVars f Ms r
              (prodPart Bs τ (TermVec.evalArgs (substRecognizerAlg A f Bs gs Ms)
                (substRecognizerAssign f Bs gs Ms) rs))
              (powerOp A τ (Args.map (fun _ q => q.1)
                (TermVec.evalArgs (substRecognizerAlg A f Bs gs Ms)
                  (substRecognizerAssign f Bs gs Ms) rs)))
            right
            refine ⟨x, ?_, rfl⟩
            change (Term.eval (substRecognizerAlg A f Bs gs Ms)
              (substRecognizerAssign f Bs gs Ms) (Term.app τ rs)).2 ⟨r, x⟩ ∈
                Ms ⟨r, x⟩
            rw [subst_snd_term A f Bs gs Ms (Term.app τ rs) ⟨r, x⟩]
            exact (rec_mem_iff (gs ⟨r, x⟩) (Ms ⟨r, x⟩) (ρ r x)
              (hMs ⟨r, x⟩) (Term.app τ rs)).mpr hRP
        | app σ ps =>
            change Term.app τ rs ∈ powerOp (freeAlgebra sig X) σ
              (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X)) ρ ps) at hRP
            rcases hRP with ⟨ys, hys, heq⟩
            cases heq
            change f.toFun r (Term.app τ ps) ∈ addVars f Ms r
              (prodPart Bs τ (TermVec.evalArgs (substRecognizerAlg A f Bs gs Ms)
                (substRecognizerAssign f Bs gs Ms) (TermVec.ofArgs ys)))
              (powerOp A τ (Args.map (fun _ q => q.1)
                (TermVec.evalArgs (substRecognizerAlg A f Bs gs Ms)
                  (substRecognizerAssign f Bs gs Ms) (TermVec.ofArgs ys))))
            left
            rw [hom_app]
            refine ⟨Args.map f.toFun (TermVec.toArgs ps), ?_, rfl⟩
            apply (ihVec (Args.map f.toFun (TermVec.toArgs ps))).mpr
            refine ⟨TermVec.toArgs ps, ?_, rfl⟩
            change Args.pmem
              (TermVec.toArgs (TermVec.ofArgs
                (show Args (Term sig X) _ from ys)))
              (Args.map (fun r P =>
                (show Set (Term sig X r) from (substGlobalHom ρ).toFun r P))
                (TermVec.toArgs ps))
            rw [toArgs_ofArgs]
            change Args.pmem ys
              (Args.map (fun r P => Term.eval
                (powerAlgebra (freeAlgebra sig X)) ρ P) (TermVec.toArgs ps))
            rw [← evalArgs_toArgs]
            exact hys

private theorem subst_fst_vec {S : Type} {sig : Signature S} {X : SSet S}
    (A : Algebra sig) (f : Hom (freeAlgebra sig X) A)
    (ρ : SMap X (powerAlgebra (freeAlgebra sig X)).carrier)
    (Bs : VX X → Algebra sig)
    (gs : (v : VX X) → Hom (freeAlgebra sig X) (Bs v))
    (Ms : (v : VX X) → Set ((Bs v).carrier v.1))
    (hMs : ∀ v : VX X, (gs v).toFun v.1 ⁻¹' Ms v = ρ v.1 v.2)
    {w : List S} (rs : TermVec sig X w) (as : Args A.carrier w) :
    Args.pmem as (Args.map (fun _ q => q.1)
      (TermVec.evalArgs (substRecognizerAlg A f Bs gs Ms)
        (substRecognizerAssign f Bs gs Ms) rs)) ↔
      ∃ ps : Args (Term sig X) w,
        Args.pmem (TermVec.toArgs rs)
          (Args.map (fun r P =>
            (show Set (Term sig X r) from (substGlobalHom ρ).toFun r P)) ps) ∧
        as = Args.map f.toFun ps := by
  cases rs with
  | nil =>
      refine ⟨fun _ => ⟨PUnit.unit, trivial, rfl⟩, fun _ => trivial⟩
  | cons R rs =>
      rcases as with ⟨a, as⟩
      change (a ∈ (Term.eval (substRecognizerAlg A f Bs gs Ms)
          (substRecognizerAssign f Bs gs Ms) R).1 ∧
        Args.pmem as (Args.map (fun _ q => q.1)
          (TermVec.evalArgs (substRecognizerAlg A f Bs gs Ms)
            (substRecognizerAssign f Bs gs Ms) rs))) ↔ _
      constructor
      · rintro ⟨ha, has⟩
        rcases (subst_fst_term A f ρ Bs gs Ms hMs R a).mp ha with
          ⟨P, hP, haP⟩
        rcases (subst_fst_vec A f ρ Bs gs Ms hMs rs as).mp has with
          ⟨ps, hps, hasps⟩
        refine ⟨(P, ps), ⟨hP, hps⟩, ?_⟩
        rw [haP, hasps]
        rfl
      · rintro ⟨ps, hps, heq⟩
        rcases ps with ⟨P, ps⟩
        rcases hps with ⟨hP, hps⟩
        constructor
        · apply (subst_fst_term A f ρ Bs gs Ms hMs R a).mpr
          exact ⟨P, hP, congrArg Prod.fst heq⟩
        · apply (subst_fst_vec A f ρ Bs gs Ms hMs rs as).mpr
          exact ⟨ps, hps, congrArg Prod.snd heq⟩
end

private theorem finite_fiber_of_sfinite {S : Type} {Y : SSet S}
    (hY : SFinite Y) (r : S) : Finite (Y r) := by
  letI : Finite (Sigma Y) := hY
  apply Finite.of_injective (fun y : Y r => Sigma.mk r y)
  intro a b hab
  exact eq_of_heq (Sigma.mk.inj hab).2

theorem rec_subst_proof {S : Type} [Finite S] (sig : Signature S) (X : SSet S)
    (hX : SFinite X) {s : S} (K : Set (Term sig X s))
    (hK : sRecognizable (freeAlgebra sig X) s K)
    (ρ : SMap X (powerAlgebra (freeAlgebra sig X)).carrier)
    (hρ : ∀ (t : S) (x : X t), sRecognizable (freeAlgebra sig X) t (ρ t x)) :
    sRecognizable (freeAlgebra sig X) s (substGlobalP ρ s K) := by
  rcases hK with ⟨A, hA, f, M, hf⟩
  have hρ' : ∀ v : VX X,
      ∃ B : Algebra sig, B.Finite ∧
        ∃ (g : Hom (freeAlgebra sig X) B) (N : Set (B.carrier v.1)),
          g.toFun v.1 ⁻¹' N = ρ v.1 v.2 := fun v => hρ v.1 v.2
  choose Bs hBs hrest using hρ'
  choose gs Ms hMs using hrest
  let C := substRecognizerAlg A f Bs gs Ms
  let assign := substRecognizerAssign f Bs gs Ms
  let accept : Set (C.carrier s) :=
    {q | ∃ a : A.carrier s, a ∈ q.1 ∧ a ∈ M}
  refine ⟨C, ?_, evalHom C assign, accept, ?_⟩
  · show Finite (Σ r, SubstState A Bs r)
    letI : Finite (VX X) := hX
    letI finA (r : S) : Finite (A.carrier r) := finite_fiber_of_sfinite hA r
    letI finB (v : VX X) (r : S) : Finite ((Bs v).carrier r) :=
      finite_fiber_of_sfinite (hBs v) r
    letI finSet (r : S) : Finite (Set (A.carrier r)) := inferInstance
    letI finPi (r : S) : Finite ((v : VX X) → (Bs v).carrier r) := inferInstance
    letI finState (r : S) : Finite (SubstState A Bs r) := inferInstance
    infer_instance
  · ext R
    change (∃ a : A.carrier s,
      a ∈ (Term.eval (substRecognizerAlg A f Bs gs Ms)
        (substRecognizerAssign f Bs gs Ms) R).1 ∧ a ∈ M) ↔
      R ∈ substGlobalP ρ s K
    constructor
    · rintro ⟨a, ha, haM⟩
      rcases (subst_fst_term A f ρ Bs gs Ms hMs R a).mp ha with
        ⟨P, hRP, rfl⟩
      have hPK : P ∈ K := (rec_mem_iff f M K hf P).mp haM
      unfold substGlobalP
      apply Set.mem_iUnion.mpr
      refine ⟨P, ?_⟩
      apply Set.mem_iUnion.mpr
      exact ⟨hPK, hRP⟩
    · intro hR
      unfold substGlobalP at hR
      rcases Set.mem_iUnion.mp hR with ⟨P, hP⟩
      rcases Set.mem_iUnion.mp hP with ⟨hPK, hRP⟩
      refine ⟨f.toFun s P, ?_, (rec_mem_iff f M K hf P).mpr hPK⟩
      apply (subst_fst_term A f ρ Bs gs Ms hMs R (f.toFun s P)).mpr
      exact ⟨P, hRP, rfl⟩

end MSKleene

theorem solution {S : Type} [Finite S] (sig : MSKleene.Signature S)
    (X : MSKleene.SSet S) (hX : MSKleene.SFinite X) {s : S}
    (K : Set (MSKleene.Term sig X s))
    (hK : MSKleene.sRecognizable (MSKleene.freeAlgebra sig X) s K)
    (ρ : MSKleene.SMap X
      (MSKleene.powerAlgebra (MSKleene.freeAlgebra sig X)).carrier)
    (hρ : ∀ (t : S) (x : X t),
      MSKleene.sRecognizable (MSKleene.freeAlgebra sig X) t (ρ t x)) :
    MSKleene.sRecognizable (MSKleene.freeAlgebra sig X) s
      (MSKleene.substGlobalP ρ s K) := by
  exact MSKleene.rec_subst_proof sig X hX K hK ρ hρ
