-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsBasisOn.tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:29:14.321977+00:00
-- url     : https://prove2.me/submissions/3f2f79e9-5754-43b1-945d-c39498be17cd

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
namespace IsBasisOn
theorem _root_.solution {P Q : PMod X} {U : X.Opens} {s : P.obj (op U)} {t : Q.obj (op U)}
    (hs : IsBasisOn P U s) (ht : IsBasisOn Q U t) :
    IsBasisOn (P ⊗ Q) U (s ⊗ₜ t : (P ⊗ Q).obj (op U)) := by
  intro V h
  have e : resM (P ⊗ Q) h (s ⊗ₜ t : (P ⊗ Q).obj (op U)) =
      (resM P h s ⊗ₜ resM Q h t : (P ⊗ Q).obj (op V)) := rfl
  rw [e]
  let eP := LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ringOn X V) _ (resM P h s)) (hs V h)
  let eQ := LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ringOn X V) _ (resM Q h t)) (ht V h)
  let E := (TensorProduct.lid (ringOn X V) (ringOn X V)).symm ≪≫ₗ TensorProduct.congr eP eQ
  have hE : ∀ r : ringOn X V, E r = r • (resM P h s ⊗ₜ resM Q h t) := by
    intro r
    change eP 1 ⊗ₜ eQ r = _
    change ((1 : ringOn X V) • resM P h s) ⊗ₜ (r • resM Q h t) = _
    rw [one_smul, TensorProduct.tmul_smul]
  have : (fun r : ringOn X V => r • (resM P h s ⊗ₜ resM Q h t : (P ⊗ Q).obj (op V))) = E := by
    funext r
    exact (hE r).symm
  have hb := E.bijective
  rw [← this] at hb
  exact hb
end IsBasisOn
end GroundTheory.Arith.SchemeCoh
