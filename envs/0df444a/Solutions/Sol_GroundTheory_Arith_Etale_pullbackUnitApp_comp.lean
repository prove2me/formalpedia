-- Prove2me | solution 1 for GroundTheory.Arith.Etale.pullbackUnitApp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:15.652437+00:00
-- url     : https://prove2.me/submissions/6f176783-9577-40de-874b-7b9acf5e64dc

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohPresheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski

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
variable {V T U : Scheme.{u}}
namespace GroundTheory.Arith.Etale
theorem _root_.solution (f : V ⟶ T) (g : T ⟶ U) (N : U.Modules) (O : U.Opens) (n : Γ(N, O)) :
    ((Scheme.Modules.pullbackComp f g).inv.app N).app ((f ≫ g) ⁻¹ᵁ O)
      (pullbackUnitApp (f ≫ g) N O n) =
        pullbackUnitApp f _ (g ⁻¹ᵁ O) (pullbackUnitApp g N O n) := by
  have h := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv N
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ O).hom n) h
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply, Scheme.Modules.pushforwardComp_hom_app_app] at h'
  exact h'.symm
end GroundTheory.Arith.Etale
