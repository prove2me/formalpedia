-- Prove2me | solution 1 for GroundTheory.Arith.Etale.existsUnique_hom_app_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:36.286679+00:00
-- url     : https://prove2.me/submissions/581371ca-4100-48d2-a039-291adbb63953

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Theorems.Thm_GroundTheory_Arith_Etale_bijective_map_of_isIso_counit

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
set_option backward.isDefEq.respectTransparency false
namespace GroundTheory.Arith.Etale
theorem _root_.solution {A : CommRingCat.{u}} (P P' : (Spec A).Modules)
    [IsIso P.fromTildeΓ] (f : Γ(P, ⊤) →ₗ[Γ(Spec A, ⊤)] Γ(P', ⊤)) :
    ∃! θ : P ⟶ P', ∀ x, θ.app ⊤ x = f x := by
  have : IsIso ((tilde.adjunction (R := A)).counit.app P) :=
    inferInstanceAs (IsIso P.fromTildeΓ)
  have hb := bijective_map_of_isIso_counit (tilde.adjunction (R := A)) P P'
  let fA : (moduleSpecΓFunctor (R := A)).obj P ⟶ (moduleSpecΓFunctor (R := A)).obj P' :=
    ModuleCat.ofHom (X := (moduleSpecΓFunctor (R := A)).obj P)
      (Y := (moduleSpecΓFunctor (R := A)).obj P')
      { toFun := f
        map_add' := map_add f
        map_smul' := fun a x => f.map_smul ((Scheme.ΓSpecIso A).inv a) x }
  obtain ⟨θ, hθ⟩ := hb.2 fA
  refine ⟨θ, fun x => ?_, fun θ' hθ' => hb.1 ?_⟩
  · exact congrArg (fun l => l.hom x) hθ
  · refine hθ.symm ▸ ?_
    ext x
    exact hθ' x
end GroundTheory.Arith.Etale
