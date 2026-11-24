-- Prove2me | solution 1 for GroundTheory.Arith.Etale.exists_modules_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:39.517658+00:00
-- url     : https://prove2.me/submissions/2521f343-cf07-454b-8049-65c6536b42f0

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
namespace GroundTheory.Arith.Etale
theorem _root_.solution (R : CommRingCat.{u}) (Q : Type u) [AddCommGroup Q]
    [Module Γ(Spec R, ⊤) Q] :
    ∃ P : (Spec R).Modules, Nonempty (Γ(P, ⊤) ≃ₗ[Γ(Spec R, ⊤)] Q) := by
  let : Module R Q := Module.compHom Q (Scheme.ΓSpecIso R).inv.hom
  let e := (tilde.isoTop (ModuleCat.of R Q)).toLinearEquiv
  refine ⟨tilde (ModuleCat.of R Q), ⟨
    { toFun := e.symm
      invFun := e
      map_add' := map_add e.symm
      map_smul' := fun t x => ?_
      left_inv := fun x => e.apply_symm_apply x
      right_inv := fun x => e.symm_apply_apply x }⟩⟩
  obtain ⟨r, rfl⟩ : ∃ r : R, (Scheme.ΓSpecIso R).inv r = t :=
    ⟨(Scheme.ΓSpecIso R).hom t, by simp⟩
  exact e.symm.map_smul r x
end GroundTheory.Arith.Etale
