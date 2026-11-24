-- Prove2me | solution 1 for GlobalTheory.nonempty_equiv_prod_of_exact_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:03.511852+00:00
-- url     : https://prove2.me/submissions/41a7348f-944c-457c-b997-ec2e4d3d9216

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsPrincipalMapAwayOfHasProjectiveDimensionLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open scoped TensorProduct
namespace GlobalTheory
theorem _root_.solution {A : Type*} [CommRing A] {K F M : Type*}
    [AddCommGroup K] [Module A K] [AddCommGroup F] [Module A F] [AddCommGroup M] [Module A M]
    [Module.Projective A M] (g : K →ₗ[A] F) (f : F →ₗ[A] M) (hg : Function.Injective g)
    (hf : Function.Surjective f) (h : Function.Exact g f) : Nonempty (F ≃ₗ[A] K × M) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact ⟨(h.splitSurjectiveEquiv hg ⟨s, hs⟩).1⟩
end GlobalTheory
