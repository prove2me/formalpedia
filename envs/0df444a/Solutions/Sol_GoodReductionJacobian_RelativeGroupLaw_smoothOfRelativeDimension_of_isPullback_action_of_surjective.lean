-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_isPullback_action_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/03416db6-2202-56c9-839e-23f5565baa0f

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_comp_of_surjective_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_isPullback_action_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} [Nonempty N] (i : N ⟶ G) [IsClosedImmersion i] (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q) (hq : q ≫ fQ = f)
    [Flat q] [LocallyOfFinitePresentation q] [Surjective q] [QuasiCompact q]
    (hR : IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) q q) :
    SmoothOfRelativeDimension h q ∧ SmoothOfRelativeDimension (g - h) fQ ∧ h ≤ g := by

  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension h) :=
    smoothOfRelativeDimension_isStableUnderBaseChange h
  haveI h1 : SmoothOfRelativeDimension h (pullback.snd (i ≫ f) f) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension h) _ _ inferInstance

  have hq' : SmoothOfRelativeDimension h q :=
    AlgebraicGeometry.SmoothOfRelativeDimension.of_isPullback_of_flat_of_surjective h hR

  haveI : Nonempty G := Nonempty.map i.base inferInstance
  haveI : SmoothOfRelativeDimension g (q ≫ fQ) := by rw [hq]; infer_instance
  haveI := hq'
  obtain ⟨hQ, hle⟩ := AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_surjective_of_field fQ q g h
  exact ⟨hq', hQ, hle⟩

#print axioms solution

end S_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_isPullback_action_of_surjective
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_isPullback_action_of_surjective (solution)
