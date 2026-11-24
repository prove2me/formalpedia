-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.tensor_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:28:15.964336+00:00
-- url     : https://prove2.me/submissions/61b355cc-cb95-48fd-8eff-8c0366121c87

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R V V' W W' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [AddCommGroup W]
  [AddCommGroup W'] [Module R V] [Module R V'] [Module R W] [Module R W']
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (p q m : V →ₗ[R] V') (p' q' m' : W →ₗ[R] W') (P : V' →ₗ[R] V) (Q : W' →ₗ[R] W)
    (hPp : ∀ v, P (p v) = v) (hPq : ∀ v, P (q v) = 0) (hQp : ∀ w, Q (p' w) = 0)
    (hQq : ∀ w, Q (q' w) = w) (hm : ∀ v, m v = p v + q v) (hm' : ∀ w, m' w = p' w + q' w)
    (t : V ⊗[R] W)
    (ht : TensorProduct.map m m' t = TensorProduct.map p p' t + TensorProduct.map q q' t) : t = 0 := by
  have h1 : ∀ t : V ⊗[R] W, TensorProduct.map P Q (TensorProduct.map m m' t) = t := fun t ↦ by
    induction t with
    | zero => simp
    | tmul v w => simp [hm, hm', hPp, hPq, hQp, hQq]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h2 : ∀ t : V ⊗[R] W, TensorProduct.map P Q (TensorProduct.map p p' t) = 0 := fun t ↦ by
    induction t with
    | zero => simp
    | tmul v w => simp [hQp]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  have h3 : ∀ t : V ⊗[R] W, TensorProduct.map P Q (TensorProduct.map q q' t) = 0 := fun t ↦ by
    induction t with
    | zero => simp
    | tmul v w => simp [hPq]
    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  have := congrArg (TensorProduct.map P Q) ht
  rwa [h1, map_add, h2, h3, add_zero] at this
end GlobalTheory.CompanionTheory.HodgeAlt
