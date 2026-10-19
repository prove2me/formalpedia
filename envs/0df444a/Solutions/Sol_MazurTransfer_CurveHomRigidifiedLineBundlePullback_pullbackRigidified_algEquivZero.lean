-- Prove2me | solution 1 for MazurTransfer.CurveHomRigidifiedLineBundlePullback.pullbackRigidified_algEquivZero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T07:40:39.988209+00:00
-- url     : https://prove2.me/submissions/7cff862d-58bc-430d-a634-321dd5ffdc23

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pointed curve pullback preserves the original fibrewise
algebraic-equivalence-zero predicate for rigidified line bundles.
Named downstream consumer: literal-fibre Picard representation transport.
Original line-bundle APIs: official Anthropic FLT, exact pin
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Mathlib
import Definitions.Def_MazurTransfer_PointedCurveRigidifiedLineBundlePullback
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
open MazurTransfer.CurveHomRigidifiedLineBundlePullback

theorem solution {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.val ≫ f = ε.val)
    {T : Scheme.{u}} {t : T ⟶ Spec (.of R)}
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M) :
    FibrewiseAlgEquivZero (pullbackRigidified f hf hε M) := by
  intro k _ _ s
  let ft := curvePullback f hf t
  let fs : pullback (pullback.snd c' t) s ⟶ pullback (pullback.snd c t) s :=
    pullback.map _ _ _ _ ft (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]; exact (curvePullback_snd f hf t).symm) (by simp)
  have hs : fs ≫ fibreAt c t s = fibreAt c' t s := by
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hfst : fs ≫ pullback.fst (pullback.snd c t) s =
      pullback.fst (pullback.snd c' t) s ≫ ft := pullback.lift_fst _ _ _
  refine IsAlgEquivZero.of_iso ?_ ((hM k s).pullback fs hs)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm
#print axioms solution
