-- Prove2me | solution 1 for GroundTheory.Arith.Etale.pullbackSection_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:40.23488+00:00
-- url     : https://prove2.me/submissions/abfacf95-3ae9-454f-9195-e0e333e60176

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
theorem _root_.solution (g : T ⟶ U) {N N' : U.Modules} (φ : N ⟶ N') (n : Γ(N, ⊤)) :
    ((Scheme.Modules.pullback g).map φ).app ⊤ (pullbackSection g N n) =
      pullbackSection g N' (φ.app ⊤ n) := by
  have := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality φ
  have h := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ ⊤).hom n) this
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  exact h.symm
end GroundTheory.Arith.Etale
