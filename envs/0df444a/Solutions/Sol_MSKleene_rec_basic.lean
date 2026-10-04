-- Prove2me | solution 1 for MSKleene.rec_basic
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-08T16:44:31.365785+00:00
-- url     : https://prove2.me/submissions/f1ed0652-d7b5-4e2a-b300-3e154d9d2211

import Definitions.Def_MSKleene_Term
import Definitions.Def_MSKleene_Recognizable
import Definitions.Def_MSKleene_Power
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Fintype.Option

namespace MSKleene

open Classical

private def Args.pack {S : Type} {X : SSet S} :
    {w : List S} → Args X w → List (Sigma X)
  | [], _ => []
  | _ :: _, (x, xs) => ⟨_, x⟩ :: Args.pack xs

private noncomputable def varCode {S : Type} {X : SSet S}
    (targets : List (Sigma X)) (r : S) (y : X r) : Fin targets.length → Bool :=
  fun i => decide (targets.get i = ⟨r, y⟩)

private theorem varCode_ne_zero_of_mem {S : Type} {X : SSet S}
    (targets : List (Sigma X)) {r : S} {x : X r}
    (hx : Sigma.mk r x ∈ targets) :
    varCode targets r x ≠ fun _ => false := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  intro h
  have h' := congrFun h i
  simp [varCode] at h'
  exact h' hi

private theorem varCode_inj_of_mem {S : Type} {X : SSet S}
    (targets : List (Sigma X)) {r : S} {x y : X r}
    (hx : Sigma.mk r x ∈ targets)
    (hcode : varCode targets r y = varCode targets r x) : y = x := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  have h' := congrFun hcode i
  simp [varCode] at h'
  have hxy : Sigma.mk r y = Sigma.mk r x := (h'.mpr hi).symm.trans hi
  exact eq_of_heq (Sigma.mk.inj hxy).2

private abbrev RecState {S : Type} {X : SSet S}
    (targets : List (Sigma X)) := Option (Fin targets.length → Bool)

private noncomputable def appRho {S : Type} {X : SSet S}
    (targets : List (Sigma X)) : SMap X (fun _ => RecState targets) :=
  fun r y => some (varCode targets r y)

private def opTag {S : Type} {sig : Signature S} {w : List S} {s : S}
    (σ : sig w s) : (w : List S) × (s : S) × sig w s := ⟨w, s, σ⟩

private noncomputable def appAlg {S : Type} (sig : Signature S)
    {X : SSet S} (targets : List (Sigma X)) {w : List S} {s : S}
    (σ : sig w s) (expected : Args (fun _ => RecState targets) w) : Algebra sig where
  carrier := fun _ => RecState targets
  op := fun τ ys =>
    if opTag τ = opTag σ ∧ HEq ys expected then none else some (fun _ => false)

private theorem eval_eq_target_var {S : Type} (sig : Signature S) {X : SSet S}
    (targets : List (Sigma X)) {w : List S} {s : S} (σ : sig w s)
    (expected : Args (fun _ => RecState targets) w)
    {r : S} {x : X r} (hx : Sigma.mk r x ∈ targets) (P : Term sig X r)
    (hP : Term.eval (appAlg sig targets σ expected) (appRho targets) P =
      appRho targets r x) : P = Term.var x := by
  cases P with
  | var y =>
      change some (varCode targets r y) = some (varCode targets r x) at hP
      exact congrArg Term.var
        (varCode_inj_of_mem targets hx (Option.some.inj hP))
  | app τ ts =>
      change (if opTag τ = opTag σ ∧ HEq (TermVec.evalArgs (appAlg sig targets σ expected)
        (appRho targets) ts) expected then none else some (fun _ => false)) =
          some (varCode targets r x) at hP
      split at hP
      · contradiction
      · have hz : (fun _ => false) = varCode targets r x := Option.some.inj hP
        exact False.elim ((varCode_ne_zero_of_mem targets hx) hz.symm)

private theorem evalArgs_eq_vars {S : Type} (sig : Signature S) {X : SSet S}
    (targets : List (Sigma X)) {s : S} {w : List S}
    (σ : sig w s) (expected : Args (fun _ => RecState targets) w) :
    ∀ (v : List S) (xs : Args X v) (ts : TermVec sig X v),
      Args.All (fun r x => Sigma.mk r x ∈ targets) xs →
      TermVec.evalArgs (appAlg sig targets σ expected) (appRho targets) ts =
        Args.map (appRho targets) xs →
      ts = TermVec.ofArgs (Args.map (fun _ x => Term.var x) xs)
  | [], PUnit.unit, .nil, _, _ => rfl
  | _ :: v, (x, xs), .cons t ts, hall, heval => by
      have hhead : Term.eval (appAlg sig targets σ expected) (appRho targets) t =
          appRho targets _ x := congrArg Prod.fst heval
      have htail : TermVec.evalArgs (appAlg sig targets σ expected) (appRho targets) ts =
          Args.map (appRho targets) xs := congrArg Prod.snd heval
      have ht : t = Term.var x :=
        eval_eq_target_var sig targets σ expected hall.1 t hhead
      have hts : ts = TermVec.ofArgs (Args.map (fun _ x => Term.var x) xs) :=
        evalArgs_eq_vars sig targets σ expected v xs ts hall.2 htail
      rw [ht, hts]
      rfl

private theorem evalArgs_vars {S : Type} (sig : Signature S) {X : SSet S}
    (targets : List (Sigma X)) {s : S} {w : List S}
    (σ : sig w s) (expected : Args (fun _ => RecState targets) w) :
    ∀ (v : List S) (xs : Args X v),
      TermVec.evalArgs (appAlg sig targets σ expected) (appRho targets)
        (TermVec.ofArgs (Args.map (fun _ x => Term.var x) xs)) =
      Args.map (appRho targets) xs
  | [], PUnit.unit => rfl
  | _ :: v, (x, xs) => congrArg (Prod.mk (appRho targets _ x))
      (evalArgs_vars sig targets σ expected v xs)

private theorem pack_all_mem_aux {S : Type} {X : SSet S}
    (targets : List (Sigma X)) : ∀ {w : List S} (xs : Args X w),
      (∀ q, q ∈ Args.pack xs → q ∈ targets) →
      Args.All (fun r x => Sigma.mk r x ∈ targets) xs
  | [], PUnit.unit, _ => trivial
  | _ :: _, (x, xs), hsub => by
      constructor
      · exact hsub _ (by simp [Args.pack])
      · exact pack_all_mem_aux targets xs fun q hq =>
          hsub q (by simp [Args.pack, hq])

private theorem pack_all_mem {S : Type} {X : SSet S} {w : List S} (xs : Args X w) :
    Args.All (fun r x => Sigma.mk r x ∈ Args.pack xs) xs :=
  pack_all_mem_aux (Args.pack xs) xs fun _ h => h

private theorem rec_app {S : Type} [Finite S] (sig : Signature S)
    (X : SSet S) (s : S) (w : List S) (σ : sig w s) (xs : Args X w) :
    sRecognizable (freeAlgebra sig X) s
      {Term.app σ (TermVec.ofArgs (Args.map (fun _ x => Term.var x) xs))} := by
  let targets := Args.pack xs
  let rho := appRho targets
  let expected := Args.map rho xs
  let B := appAlg sig targets σ expected
  refine ⟨B, ?_, evalHom B rho, {none}, ?_⟩
  · show Finite (Σ _ : S, RecState targets)
    infer_instance
  · ext P
    change Term.eval B rho P = none ↔
      P = Term.app σ (TermVec.ofArgs (Args.map (fun _ x => Term.var x) xs))
    constructor
    · intro hP
      cases P with
      | var y =>
          change some (varCode targets s y) = none at hP
          contradiction
      | app τ ts =>
          change (if opTag τ = opTag σ ∧ HEq (TermVec.evalArgs B rho ts) expected
            then none else some (fun _ => false)) = none at hP
          have hc : opTag τ = opTag σ ∧ HEq (TermVec.evalArgs B rho ts) expected := by
            by_contra hn
            simp [hn] at hP
          rcases hc with ⟨hτ, hargs⟩
          cases hτ
          have hargs' : TermVec.evalArgs B rho ts = expected := eq_of_heq hargs
          have hts := evalArgs_eq_vars sig targets σ expected w xs ts
            (pack_all_mem xs) hargs'
          rw [hts]
    · intro hP
      subst P
      change (if opTag σ = opTag σ ∧ HEq
        (TermVec.evalArgs B rho
          (TermVec.ofArgs (Args.map (fun _ x => Term.var x) xs))) expected
        then none else some (fun _ => false)) = none
      have heval : TermVec.evalArgs (appAlg sig targets σ expected) (appRho targets)
          (TermVec.ofArgs (Args.map (fun _ x => Term.var x) xs)) = expected := by
        change TermVec.evalArgs (appAlg sig targets σ expected) (appRho targets)
          (TermVec.ofArgs (Args.map (fun _ x => Term.var x) xs)) =
            Args.map (appRho targets) xs
        exact evalArgs_vars sig targets σ expected w xs
      rw [if_pos]
      exact ⟨rfl, heq_of_eq heval⟩

private theorem rec_var {S : Type} [Finite S] (sig : Signature S)
    (X : SSet S) (s : S) (x : X s) :
    sRecognizable (freeAlgebra sig X) s {Term.var x} := by
  let B : Algebra sig :=
    { carrier := fun _ => Bool
      op := fun _ _ => false }
  let rho : SMap X B.carrier :=
    fun r y => decide (Sigma.mk r y = Sigma.mk s x)
  refine ⟨B, ?_, evalHom B rho, {true}, ?_⟩
  · show Finite (Σ _ : S, Bool)
    infer_instance
  · ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    cases t with
    | var y =>
      change decide (Sigma.mk s y = Sigma.mk s x) = true ↔
        Term.var y = Term.var x
      simp
    | app τ ts =>
      change false = true ↔ Term.app τ ts = Term.var x
      simp

theorem test_rec_basic_var {S : Type} [Finite S] (sig : Signature S)
    (X : SSet S) (s : S) :
    ∀ x : X s, sRecognizable (freeAlgebra sig X) s {Term.var x} := by
  exact fun x => rec_var sig X s x

end MSKleene

theorem solution {S : Type} [Finite S] (sig : MSKleene.Signature S)
    (X : MSKleene.SSet S) (s : S) :
    (∀ x : X s, MSKleene.sRecognizable (MSKleene.freeAlgebra sig X) s
      {MSKleene.Term.var x})
  ∧ (∀ (w : List S) (σ : sig w s) (xs : MSKleene.Args X w),
      MSKleene.sRecognizable (MSKleene.freeAlgebra sig X) s
        {MSKleene.Term.app σ (MSKleene.TermVec.ofArgs
          (MSKleene.Args.map (fun _ x => MSKleene.Term.var x) xs))}) := by
  constructor
  · exact fun x => MSKleene.rec_var sig X s x
  · exact fun w σ xs => MSKleene.rec_app sig X s w σ xs
