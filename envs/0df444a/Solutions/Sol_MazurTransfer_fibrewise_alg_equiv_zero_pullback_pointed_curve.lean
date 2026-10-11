-- Prove2me | solution 1 for MazurTransfer.fibrewise_alg_equiv_zero_pullback_pointed_curve
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T11:45:35.62685+00:00
-- url     : https://prove2.me/submissions/711ed98b-0830-480c-bedb-5b2f63f7799a

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Owned pullback argument using complete official Anthropic FLT interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2. Design boundary: fibrewise algebraic
equivalence under pointed curve pullback. Named consumer: integral Picard fibre transport. -/
import Mathlib
import Definitions.Def_MazurTransfer_PointCurveRigidifiedPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
open PointCurveRigidifiedPullbackLibrary.MazurTransfer.CurveHomRigidifiedLineBundlePullback
universe u

noncomputable section

theorem solution (R : Type u) [CommRing R] {C C' : Scheme.{u}}
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
