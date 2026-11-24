-- Prove2me | solution 1 for GroundTheory.Arith.Etale.pullbackComp_inv_pullbackSection
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:44.92383+00:00
-- url     : https://prove2.me/submissions/9f07b99f-9131-4e56-893d-28d9cb9e3bed

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback

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
variable {T U W : Scheme.{u}}
namespace GroundTheory.Arith.Etale
theorem _root_.solution (f : W ⟶ T) (g : T ⟶ U) (N : U.Modules) (n : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app N).app ⊤ (pullbackSection (f ≫ g) N n) =
      pullbackSection f _ (pullbackSection g N n) := by
  have h := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv N
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ ⊤).hom n) h
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply, Scheme.Modules.pushforwardComp_hom_app_app] at h'
  exact h'.symm
end GroundTheory.Arith.Etale
