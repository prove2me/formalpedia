-- Prove2me | solution 1 for MSKleene.rec_iter
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T07:26:04.704775+00:00
-- url     : https://prove2.me/submissions/64c9d3da-ce4c-424c-9267-07278a6ddf79

import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_Iteration
import Theorems.Thm_MSKleene_iter_absorb
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Powerset

open MSKleene
open Classical

namespace MSKleene

private abbrev IterState {S : Type} {sig : Signature S}
    (A : Algebra sig) (r : S) := Set (A.carrier r) × Bool

private def castZ {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (f : Hom (freeAlgebra sig X) A) {s r : S}
    (z : X s) (h : r = s) : A.carrier r := by
  subst r
  exact f.toFun s (Term.var z)

private def iterHit {S : Type} {sig : Signature S} {A : Algebra sig}
    {s r : S} (M : Set (A.carrier s)) (Q : Set (A.carrier r)) : Prop :=
  ∃ h : r = s, ∃ a : A.carrier r, a ∈ Q ∧ h ▸ a ∈ M

private noncomputable def iterFlag {S : Type} {sig : Signature S}
    {A : Algebra sig} {s r : S} (M : Set (A.carrier s))
    (Q : Set (A.carrier r)) : Bool :=
  decide (iterHit M Q)

private def isIterVar {S : Type} {X : SSet S} {s r : S}
    (z : X s) (y : X r) : Prop :=
  ∃ h : r = s, h ▸ y = z

private noncomputable def addZ {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (f : Hom (freeAlgebra sig X) A) {s r : S}
    (z : X s) (b : Bool) (Q : Set (A.carrier r)) : Set (A.carrier r) :=
  Q ∪ {a | ∃ h : r = s, b = true ∧ a = castZ f z h}

private noncomputable def iterRecognizerAlg {S : Type} {sig : Signature S}
    {X : SSet S} (A : Algebra sig) (f : Hom (freeAlgebra sig X) A)
    {s : S} (z : X s) (M : Set (A.carrier s)) : Algebra sig where
  carrier := IterState A
  op := fun {w} {r} τ qs =>
    let Q := powerOp A τ (Args.map (fun _ q => q.1) qs)
    let b := iterFlag M Q
    (addZ f z b Q, b)

private noncomputable def iterRecognizerAssign {S : Type} {sig : Signature S}
    {X : SSet S} {A : Algebra sig} (f : Hom (freeAlgebra sig X) A)
    {s : S} (z : X s) (M : Set (A.carrier s)) :
    SMap X (iterRecognizerAlg A f z M).carrier :=
  fun r y =>
    let Q : Set (A.carrier r) := {f.toFun r (Term.var y)}
    let b : Bool := decide (isIterVar z y ∨ iterHit M Q)
    (addZ f z b Q, b)

private theorem ofArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (ts : TermVec sig X w), TermVec.ofArgs ts.toArgs = ts
  | [], .nil => rfl
  | _ :: _, .cons t ts => congrArg (TermVec.cons t) (ofArgs_toArgs ts)

private theorem toArgs_ofArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (xs : Args (Term sig X) w),
      (TermVec.ofArgs xs).toArgs = xs
  | [], _ => rfl
  | _ :: _, (x, xs) => congrArg (Prod.mk x) (toArgs_ofArgs xs)

private theorem evalArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S}
    (B : Algebra sig) (ρ : SMap X B.carrier) :
    ∀ {w : List S} (ts : TermVec sig X w),
      TermVec.evalArgs B ρ ts = Args.map (fun r P => Term.eval B ρ P) ts.toArgs
  | [], .nil => rfl
  | _ :: _, .cons t ts => congrArg (Prod.mk (Term.eval B ρ t))
      (evalArgs_toArgs B ρ ts)

private theorem hom_app {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (g : Hom (freeAlgebra sig X) A) {w : List S} {r : S}
    (σ : sig w r) (ts : TermVec sig X w) :
    g.toFun r (Term.app σ ts) = A.op σ (Args.map g.toFun ts.toArgs) := by
  calc
    g.toFun r (Term.app σ ts) =
        g.toFun r ((freeAlgebra sig X).op σ ts.toArgs) := by
          change g.toFun r (Term.app σ ts) =
            g.toFun r (Term.app σ (TermVec.ofArgs ts.toArgs))
          rw [ofArgs_toArgs]
    _ = A.op σ (Args.map g.toFun ts.toArgs) := g.map_op _ _

mutual
private theorem subst_refl_term {S : Type} {sig : Signature S} {X : SSet S}
    {s : S} (z : X s) (K : Set (Term sig X s))
    (hz : Term.var z ∈ K) {r : S} (P : Term sig X r) :
    P ∈ (show Set (Term sig X r) from (substHom z K).toFun r P) := by
  cases P with
  | var y =>
      simp only [substHom, evalHom, Term.eval]
      by_cases hr : r = s
      · subst r
        by_cases hy : y = z
        · subst y
          simpa [substAssign] using hz
        · simp [substAssign, hy]
      · simp [substAssign, hr]
  | app τ ps =>
      change Term.app τ ps ∈ powerOp (freeAlgebra sig X) τ
        (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
          (substAssign z K) ps)
      refine ⟨ps.toArgs, subst_refl_vec z K hz ps, ?_⟩
      change Term.app τ ps = Term.app τ (TermVec.ofArgs ps.toArgs)
      rw [ofArgs_toArgs]

private theorem subst_refl_vec {S : Type} {sig : Signature S} {X : SSet S}
    {s : S} (z : X s) (K : Set (Term sig X s))
    (hz : Term.var z ∈ K) {w : List S} (ps : TermVec sig X w) :
    Args.pmem ps.toArgs
      (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
        (substAssign z K) ps) := by
  cases ps with
  | nil => trivial
  | cons P ps =>
      exact ⟨subst_refl_term z K hz P, subst_refl_vec z K hz ps⟩
end

private theorem rec_mem_iff {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (f : Hom (freeAlgebra sig X) A) {r : S}
    (M : Set (A.carrier r)) (L : Set (Term sig X r))
    (h : f.toFun r ⁻¹' M = L) (R : Term sig X r) :
    f.toFun r R ∈ M ↔ R ∈ L := by
  change R ∈ f.toFun r ⁻¹' M ↔ R ∈ L
  exact Set.ext_iff.mp h R

private theorem z_mem_iterate {S : Type} {sig : Signature S} {X : SSet S}
    {s : S} (z : X s) (L : Set (Term sig X s)) :
    Term.var z ∈ iterate z L := by
  unfold iterate
  exact Set.mem_iUnion.mpr ⟨0, Set.mem_singleton _⟩

private theorem subst_z_iff {S : Type} {sig : Signature S} {X : SSet S}
    {s : S} (z : X s) (K : Set (Term sig X s)) (R : Term sig X s) :
    R ∈ (show Set (Term sig X s) from (substHom z K).toFun s (Term.var z)) ↔
      R ∈ K := by
  simp [substHom, evalHom, Term.eval, substAssign]

private theorem iterFlag_true_iff {S : Type} {sig : Signature S}
    {A : Algebra sig} {s r : S} (M : Set (A.carrier s))
    (Q : Set (A.carrier r)) :
    iterFlag M Q = true ↔ iterHit M Q := by
  simp [iterFlag]

mutual
private theorem iter_sound_term {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (f : Hom (freeAlgebra sig X) A) {s : S}
    (z : X s) (L : Set (Term sig X s)) (M : Set (A.carrier s))
    (hf : f.toFun s ⁻¹' M = L) {r : S} (R : Term sig X r) :
    ((Term.eval (iterRecognizerAlg A f z M)
        (iterRecognizerAssign f z M) R).2 = true →
      ∃ h : r = s, h ▸ R ∈ iterate z L) ∧
    (∀ a : A.carrier r,
      a ∈ (Term.eval (iterRecognizerAlg A f z M)
        (iterRecognizerAssign f z M) R).1 →
      ∃ P : Term sig X r,
        R ∈ (show Set (Term sig X r) from
          (substHom z (iterate z L)).toFun r P) ∧
        a = f.toFun r P) := by
  cases R with
  | var y =>
      let Q : Set (A.carrier r) := {f.toFun r (Term.var y)}
      let b : Bool := decide (isIterVar z y ∨ iterHit M Q)
      have hb : b = true ↔ isIterVar z y ∨ iterHit M Q := by
        simp [b]
      have hflag : b = true → ∃ h : r = s, h ▸ Term.var y ∈ iterate z L := by
        intro hbt
        rcases hb.mp hbt with hyv | hhit
        · rcases hyv with ⟨h, hy⟩
          subst r
          have hy' : y = z := by simpa using hy
          subst y
          exact ⟨rfl, z_mem_iterate z L⟩
        · rcases hhit with ⟨h, a, haQ, haM⟩
          subst r
          have ha : a = f.toFun s (Term.var y) := by
            simpa [Q] using haQ
          subst a
          have hyL : Term.var y ∈ L := (rec_mem_iff f M L hf _).mp haM
          have hsub : Term.var y ∈ substP z (iterate z L) s L := by
            unfold substP
            apply Set.mem_iUnion.mpr
            refine ⟨Term.var y, ?_⟩
            apply Set.mem_iUnion.mpr
            exact ⟨hyL, subst_refl_term z (iterate z L) (z_mem_iterate z L) _⟩
          exact ⟨rfl, iter_absorb sig X z L hsub⟩
      constructor
      · exact hflag
      · intro a ha
        change a ∈ addZ f z b Q at ha
        rcases ha with haQ | haZ
        · have ha : a = f.toFun r (Term.var y) := by simpa [Q] using haQ
          refine ⟨Term.var y,
            subst_refl_term z (iterate z L) (z_mem_iterate z L) _, ha⟩
        · rcases haZ with ⟨h, hbt, rfl⟩
          rcases hflag hbt with ⟨h', hR⟩
          subst r
          refine ⟨Term.var z, ?_, ?_⟩
          · exact (subst_z_iff z (iterate z L) _).mpr hR
          · rfl
  | app τ rs =>
      let qs := TermVec.evalArgs (iterRecognizerAlg A f z M)
        (iterRecognizerAssign f z M) rs
      let Q := powerOp A τ (Args.map (fun _ q => q.1) qs)
      let b := iterFlag M Q
      have ih := iter_sound_vec f z L M hf rs
      have hraw : ∀ a : A.carrier r, a ∈ Q →
          ∃ P : Term sig X r,
            Term.app τ rs ∈ (show Set (Term sig X r) from
              (substHom z (iterate z L)).toFun r P) ∧
            a = f.toFun r P := by
        intro a ha
        rcases ha with ⟨as, has, rfl⟩
        rcases ih as has with ⟨ps, hrs, hasf⟩
        refine ⟨Term.app τ (TermVec.ofArgs ps), ?_, ?_⟩
        · change Term.app τ rs ∈ powerOp (freeAlgebra sig X) τ
            (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
              (substAssign z (iterate z L)) (TermVec.ofArgs ps))
          refine ⟨rs.toArgs, ?_, ?_⟩
          · rw [TermVec.evalArgs_ofArgs]
            exact hrs
          · change Term.app τ rs = Term.app τ (TermVec.ofArgs rs.toArgs)
            rw [ofArgs_toArgs]
        · rw [hom_app, hasf, toArgs_ofArgs]
      have hflag : b = true →
          ∃ h : r = s, h ▸ Term.app τ rs ∈ iterate z L := by
        intro hbt
        rcases (iterFlag_true_iff M Q).mp hbt with ⟨h, a, haQ, haM⟩
        rcases hraw a haQ with ⟨P, hRP, rfl⟩
        subst r
        have hPL : P ∈ L := (rec_mem_iff f M L hf P).mp haM
        have hsub : Term.app τ rs ∈ substP z (iterate z L) s L := by
          unfold substP
          apply Set.mem_iUnion.mpr
          refine ⟨P, ?_⟩
          apply Set.mem_iUnion.mpr
          exact ⟨hPL, hRP⟩
        exact ⟨rfl, iter_absorb sig X z L hsub⟩
      constructor
      · exact hflag
      · intro a ha
        change a ∈ addZ f z b Q at ha
        rcases ha with haQ | haZ
        · exact hraw a haQ
        · rcases haZ with ⟨h, hbt, rfl⟩
          rcases hflag hbt with ⟨h', hR⟩
          subst r
          refine ⟨Term.var z, ?_, rfl⟩
          exact (subst_z_iff z (iterate z L) _).mpr hR

private theorem iter_sound_vec {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (f : Hom (freeAlgebra sig X) A) {s : S}
    (z : X s) (L : Set (Term sig X s)) (M : Set (A.carrier s))
    (hf : f.toFun s ⁻¹' M = L) {w : List S} (rs : TermVec sig X w)
    (as : Args A.carrier w)
    (has : Args.pmem as
      (Args.map (fun _ q => q.1)
        (TermVec.evalArgs (iterRecognizerAlg A f z M)
          (iterRecognizerAssign f z M) rs))) :
    ∃ ps : Args (Term sig X) w,
      Args.pmem rs.toArgs
        (Args.map (fun r P => (show Set (Term sig X r) from
          (substHom z (iterate z L)).toFun r P)) ps) ∧
      as = Args.map f.toFun ps := by
  cases rs with
  | nil => exact ⟨PUnit.unit, trivial, rfl⟩
  | cons R rs =>
      rcases as with ⟨a, as⟩
      rcases has with ⟨ha, has⟩
      rcases (iter_sound_term f z L M hf R).2 a ha with ⟨P, hP, haP⟩
      rcases iter_sound_vec f z L M hf rs as has with ⟨ps, hps, hasps⟩
      refine ⟨(P, ps), ⟨hP, hps⟩, ?_⟩
      subst a
      subst as
      rfl
end

private theorem finite_fiber_of_sfinite {S : Type} {Y : SSet S}
    (hY : SFinite Y) (r : S) : Finite (Y r) := by
  letI : Finite (Sigma Y) := hY
  apply Finite.of_injective (fun y : Y r => Sigma.mk r y)
  intro a b hab
  exact eq_of_heq (Sigma.mk.inj hab).2

private theorem flag_adds_z {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (f : Hom (freeAlgebra sig X) A) {s : S}
    (z : X s) (M : Set (A.carrier s)) (R : Term sig X s)
    (hflag : (Term.eval (iterRecognizerAlg A f z M)
      (iterRecognizerAssign f z M) R).2 = true) :
    f.toFun s (Term.var z) ∈
      (Term.eval (iterRecognizerAlg A f z M)
        (iterRecognizerAssign f z M) R).1 := by
  cases R with
  | var y =>
      let Q : Set (A.carrier s) := {f.toFun s (Term.var y)}
      let b : Bool := decide (isIterVar z y ∨ iterHit M Q)
      change f.toFun s (Term.var z) ∈ addZ f z b Q
      right
      exact ⟨rfl, hflag, rfl⟩
  | app τ rs =>
      let qs := TermVec.evalArgs (iterRecognizerAlg A f z M)
        (iterRecognizerAssign f z M) rs
      let Q := powerOp A τ (Args.map (fun _ q => q.1) qs)
      let b := iterFlag M Q
      change f.toFun s (Term.var z) ∈ addZ f z b Q
      right
      exact ⟨rfl, hflag, rfl⟩

mutual
private theorem subst_complete_term {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (f : Hom (freeAlgebra sig X) A) {s : S}
    (z : X s) (M : Set (A.carrier s)) (K : Set (Term sig X s))
    (hK : ∀ R : Term sig X s, R ∈ K →
      (Term.eval (iterRecognizerAlg A f z M)
        (iterRecognizerAssign f z M) R).2 = true)
    {r : S} (P : Term sig X r) (R : Term sig X r)
    (hR : R ∈ (show Set (Term sig X r) from (substHom z K).toFun r P)) :
    f.toFun r P ∈ (Term.eval (iterRecognizerAlg A f z M)
      (iterRecognizerAssign f z M) R).1 := by
  cases P with
  | var x =>
      simp only [substHom, evalHom, Term.eval] at hR
      by_cases hr : r = s
      · subst r
        by_cases hx : x = z
        · subst x
          have hRK : R ∈ K := by simpa [substAssign] using hR
          exact flag_adds_z f z M R (hK R hRK)
        · have hEq : R = Term.var x := by
            simpa [substAssign, hx] using hR
          subst R
          let Q : Set (A.carrier s) := {f.toFun s (Term.var x)}
          let b : Bool := decide (isIterVar z x ∨ iterHit M Q)
          change f.toFun s (Term.var x) ∈ addZ f z b Q
          left
          exact Set.mem_singleton _
      · have hEq : R = Term.var x := by
          simpa [substAssign, hr] using hR
        subst R
        let Q : Set (A.carrier r) := {f.toFun r (Term.var x)}
        let b : Bool := decide (isIterVar z x ∨ iterHit M Q)
        change f.toFun r (Term.var x) ∈ addZ f z b Q
        left
        exact Set.mem_singleton _
  | app τ ps =>
      change R ∈ powerOp (freeAlgebra sig X) τ
        (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
          (substAssign z K) ps) at hR
      rcases hR with ⟨ys, hys, hEq⟩
      subst R
      let qs := TermVec.evalArgs (iterRecognizerAlg A f z M)
        (iterRecognizerAssign f z M) (TermVec.ofArgs ys)
      let Q := powerOp A τ (Args.map (fun _ q => q.1) qs)
      let b := iterFlag M Q
      change f.toFun r (Term.app τ ps) ∈ addZ f z b Q
      left
      rw [hom_app]
      refine ⟨Args.map f.toFun ps.toArgs, ?_, rfl⟩
      exact subst_complete_vec f z M K hK ps ys hys

private theorem subst_complete_vec {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (f : Hom (freeAlgebra sig X) A) {s : S}
    (z : X s) (M : Set (A.carrier s)) (K : Set (Term sig X s))
    (hK : ∀ R : Term sig X s, R ∈ K →
      (Term.eval (iterRecognizerAlg A f z M)
        (iterRecognizerAssign f z M) R).2 = true)
    {w : List S} (ps : TermVec sig X w) (ys : Args (Term sig X) w)
    (hys : Args.pmem ys
      (TermVec.evalArgs (powerAlgebra (freeAlgebra sig X))
        (substAssign z K) ps)) :
    Args.pmem (Args.map f.toFun ps.toArgs)
      (Args.map (fun _ q => q.1)
        (TermVec.evalArgs (iterRecognizerAlg A f z M)
          (iterRecognizerAssign f z M) (TermVec.ofArgs ys))) := by
  cases ps with
  | nil => trivial
  | cons P ps =>
      rcases ys with ⟨R, ys⟩
      rcases hys with ⟨hR, hys⟩
      exact ⟨subst_complete_term f z M K hK P R hR,
        subst_complete_vec f z M K hK ps ys hys⟩
end

private theorem accepted_of_first {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (f : Hom (freeAlgebra sig X) A) {s : S}
    (z : X s) (M : Set (A.carrier s)) (R : Term sig X s)
    (a : A.carrier s)
    (ha : a ∈ (Term.eval (iterRecognizerAlg A f z M)
      (iterRecognizerAssign f z M) R).1) (haM : a ∈ M) :
    (Term.eval (iterRecognizerAlg A f z M)
      (iterRecognizerAssign f z M) R).2 = true := by
  cases R with
  | var y =>
      let Q : Set (A.carrier s) := {f.toFun s (Term.var y)}
      let b : Bool := decide (isIterVar z y ∨ iterHit M Q)
      change a ∈ addZ f z b Q at ha
      change b = true
      rcases ha with haQ | haZ
      · have hhit : iterHit M Q := ⟨rfl, a, haQ, haM⟩
        simp [b, hhit]
      · exact haZ.choose_spec.1
  | app τ rs =>
      let qs := TermVec.evalArgs (iterRecognizerAlg A f z M)
        (iterRecognizerAssign f z M) rs
      let Q := powerOp A τ (Args.map (fun _ q => q.1) qs)
      let b := iterFlag M Q
      change a ∈ addZ f z b Q at ha
      change b = true
      rcases ha with haQ | haZ
      · exact (iterFlag_true_iff M Q).mpr ⟨rfl, a, haQ, haM⟩
      · exact haZ.choose_spec.1

private theorem iterStage_complete {S : Type} {sig : Signature S} {X : SSet S}
    {A : Algebra sig} (f : Hom (freeAlgebra sig X) A) {s : S}
    (z : X s) (L : Set (Term sig X s)) (M : Set (A.carrier s))
    (hf : f.toFun s ⁻¹' M = L) :
    ∀ (i : ℕ) (R : Term sig X s), R ∈ iterStage z L i →
      (Term.eval (iterRecognizerAlg A f z M)
        (iterRecognizerAssign f z M) R).2 = true := by
  intro i
  induction i with
  | zero =>
      intro R hR
      have hEq : R = Term.var z := by simpa using hR
      subst R
      change (decide (isIterVar z z ∨
        iterHit M ({f.toFun s (Term.var z)} : Set (A.carrier s)))) = true
      simp [isIterVar]
  | succ i ih =>
      intro R hR
      rw [iterStage_succ] at hR
      rcases hR with hR | hR
      · exact ih R hR
      · unfold substP at hR
        rcases Set.mem_iUnion.mp hR with ⟨P, hP⟩
        rcases Set.mem_iUnion.mp hP with ⟨hPL, hRP⟩
        have hfirst := subst_complete_term f z M (iterStage z L i)
          (fun Q hQ => ih Q hQ) P R hRP
        have hPM : f.toFun s P ∈ M := (rec_mem_iff f M L hf P).mpr hPL
        exact accepted_of_first f z M R (f.toFun s P) hfirst hPM

end MSKleene

theorem solution {S : Type} [Finite S] (sig : Signature S) (X : SSet S) {s : S}
    (z : X s) (L : Set (Term sig X s))
    (hL : sRecognizable (freeAlgebra sig X) s L) :
    sRecognizable (freeAlgebra sig X) s (iterate z L) := by
  rcases hL with ⟨A, hA, f, M, hf⟩
  let C := MSKleene.iterRecognizerAlg A f z M
  let assign := MSKleene.iterRecognizerAssign f z M
  refine ⟨C, ?_, evalHom C assign, {q | q.2 = true}, ?_⟩
  · show Finite (Σ r, MSKleene.IterState A r)
    letI finA (r : S) : Finite (A.carrier r) :=
      MSKleene.finite_fiber_of_sfinite hA r
    letI finSet (r : S) : Finite (Set (A.carrier r)) := inferInstance
    letI finState (r : S) : Finite (MSKleene.IterState A r) := inferInstance
    infer_instance
  · ext R
    change (Term.eval (MSKleene.iterRecognizerAlg A f z M)
      (MSKleene.iterRecognizerAssign f z M) R).2 = true ↔ R ∈ iterate z L
    constructor
    · intro hR
      exact (MSKleene.iter_sound_term f z L M hf R).1 hR |>.choose_spec
    · intro hR
      unfold iterate at hR
      rcases Set.mem_iUnion.mp hR with ⟨i, hi⟩
      exact MSKleene.iterStage_complete f z L M hf i R hi
