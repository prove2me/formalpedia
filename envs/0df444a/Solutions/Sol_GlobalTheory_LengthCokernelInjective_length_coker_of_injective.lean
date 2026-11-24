-- Prove2me | solution 1 for GlobalTheory.LengthCokernelInjective.length_coker_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:42:42.188276+00:00
-- url     : https://prove2.me/submissions/0abd0dea-f0c5-4c55-bb3d-3d4a2de1682f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCokerOfNotInjective
import Theorems.Thm_GlobalTheory_LengthCokernelInjective_addVal_finset_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthCokernelInjective
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
namespace GlobalTheory.LengthCokernelInjective
theorem _root_.solution (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) =
      IsDiscreteValuationRing.addVal R (LinearMap.det f) := by
  classical
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hf
  let a := Submodule.smithNormalFormCoeffs b h
  let t := Submodule.smithNormalFormTopBasis b h
  let s := Submodule.smithNormalFormBotBasis b h
  have hs : ∀ i, (s i : M) = a i • t i := Submodule.smithNormalFormBotBasis_def b h
  have h1 : Associated
      (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap))
      (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (t.equiv s (Equiv.refl _)).toLinearMap)) :=
    LinearMap.associated_det_comp_equiv _ _ _
  have h2 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap = f := by
    ext x
    simp
  have h3 : (LinearMap.range f).subtype ∘ₗ (t.equiv s (Equiv.refl _)).toLinearMap =
      Matrix.toLin t t (Matrix.diagonal a) := by
    refine t.ext fun i => ?_
    simp [hs, Matrix.diagonal_apply, Finset.sum_ite_eq']
  rw [h2, h3, LinearMap.det_toLin, Matrix.det_diagonal] at h1
  rw [(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr h1, addVal_finset_prod,
    (Submodule.quotientEquivPiSpan (LinearMap.range f) b h).length_eq,
    Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (a i)
end GlobalTheory.LengthCokernelInjective
