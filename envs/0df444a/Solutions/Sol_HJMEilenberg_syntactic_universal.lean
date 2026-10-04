-- Prove2me | solution 1 for HJMEilenberg.syntactic_universal
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-09T10:54:09.099034+00:00
-- url     : https://prove2.me/submissions/956c1ec1-bba6-4261-aa7b-95c40af90f6b

import Definitions.Def_HJMEilenberg_Formations

open MSKleene

namespace HJMEilenberg

/-- A generating step for the join of all congruences saturating `L`. -/
private def SatStep {S : Type} {sig : Signature S} {A : Algebra sig}
    (L : Language A) (s : S) (x y : A.carrier s) : Prop :=
  ∃ Phi : Congruence A, Saturated Phi L ∧ Phi.Rel s x y

private theorem argsRel_refl {S : Type} {sig : Signature S}
    {A : Algebra sig} (Phi : Congruence A) :
    ∀ {w : List S} (xs : Args A.carrier w),
      Args.Rel (fun s => Phi.Rel s) xs xs
  | [], _ => trivial
  | _ :: _, (x, xs) => ⟨(Phi.setoid _).refl x, argsRel_refl Phi xs⟩

/-- Equivalence closure commutes with every operation-compatible map on a
finite argument tuple.  The proof changes one coordinate at a time. -/
private theorem eqvGen_args_apply {S : Type} {sig : Signature S}
    {A : Algebra sig} (L : Language A) {t : S} :
    ∀ {w : List S} (F : Args A.carrier w → A.carrier t),
      (∀ (Phi : Congruence A) (xs ys : Args A.carrier w),
        Args.Rel (fun s => Phi.Rel s) xs ys → Phi.Rel t (F xs) (F ys)) →
      ∀ {xs ys : Args A.carrier w},
        Args.Rel (fun s => Relation.EqvGen (SatStep L s)) xs ys →
          Relation.EqvGen (SatStep L t) (F xs) (F ys) := by
  intro w
  induction w with
  | nil =>
      intro F hF xs ys hxy
      cases xs
      cases ys
      exact Relation.EqvGen.refl _
  | cons r w ih =>
      intro F hF xs ys hxy
      rcases xs with ⟨x, xs⟩
      rcases ys with ⟨y, ys⟩
      have mapHead : ∀ {a b : A.carrier r},
          Relation.EqvGen (SatStep L r) a b →
            Relation.EqvGen (SatStep L t) (F (a, xs)) (F (b, xs)) := by
        intro a b hab
        induction hab with
        | rel a b hab =>
            rcases hab with ⟨Phi, hPhi, hab⟩
            exact Relation.EqvGen.rel _ _
              ⟨Phi, hPhi, hF Phi (a, xs) (b, xs)
                ⟨hab, argsRel_refl Phi xs⟩⟩
        | refl a => exact Relation.EqvGen.refl _
        | symm a b _ ihab => exact Relation.EqvGen.symm _ _ ihab
        | trans a b c _ _ ihab ihbc =>
            exact Relation.EqvGen.trans _ _ _ ihab ihbc
      have hHead : Relation.EqvGen (SatStep L t)
          (F (x, xs)) (F (y, xs)) := mapHead hxy.1
      have hTail : Relation.EqvGen (SatStep L t)
          (F (y, xs)) (F (y, ys)) := by
        apply ih (fun zs => F (y, zs))
        · intro Phi as bs hab
          exact hF Phi (y, as) (y, bs)
            ⟨(Phi.setoid r).refl y, hab⟩
        · exact hxy.2
      exact Relation.EqvGen.trans _ _ _ hHead hTail

/-- The equivalence closure of the union of all congruences saturating `L` is
again a congruence. -/
private def saturatedJoin {S : Type} {sig : Signature S}
    {A : Algebra sig} (L : Language A) : Congruence A where
  setoid s := Relation.EqvGen.setoid (SatStep L s)
  compatible σ xs ys hxy :=
    eqvGen_args_apply L (fun zs => A.op σ zs)
      (fun Phi as bs hab => Phi.compatible σ as bs hab) hxy

private theorem saturatedJoin_saturates {S : Type} {sig : Signature S}
    {A : Algebra sig} (L : Language A) : Saturated (saturatedJoin L) L := by
  intro s x y hxy
  change Relation.EqvGen (SatStep L s) x y at hxy
  induction hxy with
  | rel x y hxy =>
      rcases hxy with ⟨Phi, hPhi, hxy⟩
      exact hPhi s x y hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

private theorem le_saturatedJoin {S : Type} {sig : Signature S}
    {A : Algebra sig} {L : Language A} (Phi : Congruence A)
    (hPhi : Saturated Phi L) : Phi ≤ saturatedJoin L := by
  intro s x y hxy
  exact Relation.EqvGen.rel _ _ ⟨Phi, hPhi, hxy⟩

end HJMEilenberg

theorem solution {S : Type} {sig : Signature S}
    (A : Algebra sig) (L : HJMEilenberg.Language A) :
    HJMEilenberg.Saturated (HJMEilenberg.syntacticCongruence A L) L ∧
      ∀ Phi : HJMEilenberg.Congruence A,
        HJMEilenberg.Saturated Phi L ↔
          Phi ≤ HJMEilenberg.syntacticCongruence A L := by
  open HJMEilenberg in
    have hSyn : Saturated (syntacticCongruence A L) L := by
      intro s x y hxy
      apply saturatedJoin_saturates L s x y
      exact hxy (saturatedJoin L)
        (fun Phi hPhi => le_saturatedJoin Phi hPhi)
    refine ⟨hSyn, ?_⟩
    intro Phi
    constructor
    · intro hPhi s x y hxy Psi hPsi
      exact hPsi Phi hPhi s x y hxy
    · intro hle s x y hxy
      exact hSyn s x y (hle s x y hxy)
