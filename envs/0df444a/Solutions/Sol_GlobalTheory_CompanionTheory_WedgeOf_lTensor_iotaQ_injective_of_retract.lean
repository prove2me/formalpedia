-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.lTensor_iotaQ_injective_of_retract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:23.564862+00:00
-- url     : https://prove2.me/submissions/ca1675d2-8809-4dcf-8fd6-0bb774eb16e2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyInclusionTensorInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_evaluation_coboundary_zero_tensor
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_exists_cocycle
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_iotaQ_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_iotaQ_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  (R' : Type) [CommRing R'] [Algebra R R']
variable {R'} {M : Type} [AddCommGroup M] [Module R M] (j : M →ₗ[R] R')
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution (h : H1CommutesBaseChange F) (p : R' →ₗ[R] M) (hp : p ∘ₗ j = LinearMap.id) :
    Function.Injective ((iotaQ F).lTensor M) := by
  obtain ⟨e, he⟩ := h R' (bcF F R') (bcM F R')
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective M (H1.mk_surjective F) x
  have hcomp : iotaQ F ∘ₗ H1.mk F = (LinearMap.range (d0 F)).mkQ ∘ₗ (Z1 F).subtype :=
    LinearMap.ext fun f => iotaQ_mk F f
  have hx' : ((LinearMap.range (d0 F)).mkQ).lTensor M ((Z1 F).subtype.lTensor M t) = 0 := by
    rw [← LinearMap.lTensor_comp_apply, ← hcomp, LinearMap.lTensor_comp_apply]
    exact hx
  obtain ⟨y, hy⟩ := (lTensor_exact M (LinearMap.exact_map_mkQ_range (d0 F))
    (Submodule.mkQ_surjective _) ((Z1 F).subtype.lTensor M t)).1 hx'
  obtain ⟨z, hz1, hz2⟩ := exists_cocycle F j e he t
  have hz0 : H1.mk (bcF F R') z = 0 := by
    apply iotaQ_injective (bcF F R')
    rw [iotaQ_mk, map_zero, Submodule.Quotient.mk_eq_zero, hz1, ← hy, evaluation_coboundary_zero_tensor]
    exact LinearMap.mem_range_self _ _
  have hx0 : j.rTensor (H1 F) ((H1.mk F).lTensor M t) = 0 := by
    rw [← e.map_eq_zero_iff, ← hz2, hz0]
  calc (H1.mk F).lTensor M t = (p ∘ₗ j).rTensor (H1 F) ((H1.mk F).lTensor M t) := by
        rw [hp, LinearMap.rTensor_id_apply]
    _ = p.rTensor (H1 F) (j.rTensor (H1 F) ((H1.mk F).lTensor M t)) := LinearMap.rTensor_comp_apply _ _ _ _
    _ = 0 := by rw [hx0, map_zero]
end GlobalTheory.CompanionTheory.WedgeOf
