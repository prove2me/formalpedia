-- Prove2me | solution 1 for MSKleene.singleton_term_regular
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-08T13:38:38.248271+00:00
-- url     : https://prove2.me/submissions/a98e0ff6-aa18-4d06-b403-8aa33119e0b8

import Definitions.Def_MSKleene_Regular
import Mathlib.Data.Fintype.EquivFin

open MSKleene

private theorem ofArgs_toArgs {S : Type} {sig : Signature S} {X : SSet S} :
    ∀ {w : List S} (ts : TermVec sig X w), TermVec.ofArgs (TermVec.toArgs ts) = ts
  | [], .nil => rfl
  | _ :: _, .cons t ts => congrArg (TermVec.cons t) (ofArgs_toArgs ts)

private theorem pmem_singletons {S : Type} {A : SSet S} :
    ∀ {w : List S} (xs ys : Args A w),
      Args.pmem xs
          (Args.map (fun s (y : A s) => ({y} : Set (A s))) ys) ↔ xs = ys
  | [], xs, ys => by
      constructor
      · intro _
        cases xs
        cases ys
        rfl
      · intro _
        trivial
  | _ :: _, (x, xs), (y, ys) => by
      simp only [Args.pmem, Args.map, Set.mem_singleton_iff, pmem_singletons]
      constructor
      · rintro ⟨hxy, hrest⟩
        exact congrArg₂ Prod.mk hxy hrest
      · intro h
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

private theorem powerOp_singletons {S : Type} {sig : Signature S}
    (A : Algebra sig) {w : List S} {s : S} (σ : sig w s)
    (xs : Args A.carrier w) :
    powerOp A σ
        (Args.map (fun s (x : A.carrier s) => ({x} : Set (A.carrier s))) xs) =
      {A.op σ xs} := by
  ext y
  constructor
  · rintro ⟨ys, hys, rfl⟩
    have : ys = xs := (pmem_singletons ys xs).mp hys
    subst ys
    rfl
  · intro hy
    have : y = A.op σ xs := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨xs, (pmem_singletons xs xs).mpr rfl, rfl⟩

private theorem interp_toReg_singleton {S : Type} (sig : Signature S) (Z : SSet S) :
    ∀ {s : S} (P : Term sig Z s), interpExpr sig Z s (Term.toReg P) = {P} :=
  @Term.rec _ _ _
    (motive_1 := fun s P => interpExpr sig Z s (Term.toReg P) = {P})
    (motive_2 := fun w ts =>
      TermVec.evalArgs (regPowerAlgebra sig Z) (regGenAssign sig Z)
          (TermVec.toReg ts) =
        Args.map (fun s (t : Term sig Z s) => ({t} : Set (Term sig Z s)))
          (TermVec.toArgs ts))
    (fun _ => rfl)
    (fun σ ts ih => by
      change powerOp (freeAlgebra sig Z) σ
          (TermVec.evalArgs (regPowerAlgebra sig Z) (regGenAssign sig Z)
            (TermVec.toReg ts)) = {Term.app σ ts}
      rw [ih]
      calc
        powerOp (freeAlgebra sig Z) σ
            (Args.map (fun s (t : Term sig Z s) => ({t} : Set (Term sig Z s)))
              (TermVec.toArgs ts)) =
            {(freeAlgebra sig Z).op σ (TermVec.toArgs ts)} :=
          powerOp_singletons (freeAlgebra sig Z) σ (TermVec.toArgs ts)
        _ = {Term.app σ ts} := by
          simp only [freeAlgebra]
          rw [ofArgs_toArgs])
    rfl
    (fun _ _ iht ihv => congrArg₂ Prod.mk iht ihv)

/-- A base term, viewed as a regular expression, denotes its singleton and is
therefore regular. -/
theorem solution {S : Type} [Finite S]
    (sig : Signature S) (X : SSet S) (_hsig : SigFinite sig) (hX : SFinite X)
    {s : S} (P : Term sig X s) :
    interpExpr sig X s (Term.toReg P) = {P}
  ∧ {P} ∈ RegS sig X s := by
  refine ⟨interp_toReg_singleton sig X P, ?_⟩
  let E : SSet S := fun _ => Empty
  have hE : SFinite (extVars X E) := by
    unfold SFinite
    letI : Finite (Σ s, X s) := hX
    let f : (Σ s, extVars X E s) → (Σ s, X s) := fun p =>
      match p with
      | ⟨s, .inl x⟩ => ⟨s, x⟩
      | ⟨_, .inr e⟩ => nomatch e
    apply Finite.of_injective f
    intro a b hab
    rcases a with ⟨sa, xa⟩
    rcases xa with xa | ea
    · rcases b with ⟨sb, xb⟩
      rcases xb with xb | eb
      · simp only [f] at hab
        cases hab
        rfl
      · exact nomatch eb
    · exact nomatch ea
  change sRegular sig X s {P}
  refine ⟨E, hE, Term.toReg (Term.relabel (extIncl X E) P), ?_⟩
  rw [interp_toReg_singleton]
  simp
