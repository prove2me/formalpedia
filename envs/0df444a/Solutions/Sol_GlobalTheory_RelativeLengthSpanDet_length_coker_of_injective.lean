-- Prove2me | solution 1 for GlobalTheory.RelativeLengthSpanDet.length_coker_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:57:46.424224+00:00
-- url     : https://prove2.me/submissions/2b02a516-97bb-4588-bce4-87fe769d342e

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RelLengthSpanEqAddValDet
import Theorems.Thm_GlobalTheory_RelativeLengthSpanDet_addVal_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RelativeLengthSpanDet
open IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RelativeLengthSpanDet
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  have hr : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hf
  set c := Submodule.smithNormalFormCoeffs b hr with hc
  set bt := Submodule.smithNormalFormTopBasis b hr with hbt
  set bb := Submodule.smithNormalFormBotBasis b hr with hbb
  have hdef : ∀ i, (bb i : M) = c i • bt i := Submodule.smithNormalFormBotBasis_def b hr
  have h1 : Module.length R (M ⧸ LinearMap.range f) = ∑ i, addVal R (c i) := by
    rw [(Submodule.quotientEquivPiSpan _ b hr).length_eq, Module.length_pi_of_fintype]
    exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (c i)
  have h2 := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
    (LinearEquiv.ofInjective f hf) (bt.equiv bb (Equiv.refl ι))
  have h3 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf : M →ₗ[R] _) = f := by
    ext x
    rfl
  have h4 : LinearMap.det ((LinearMap.range f).subtype ∘ₗ
      (bt.equiv bb (Equiv.refl ι) : M →ₗ[R] LinearMap.range f)) = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix bt, ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.refl_apply, Submodule.subtype_apply, hdef, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  rw [h3, h4] at h2
  rw [h1, (addVal_eq_iff_associated _ _).mpr h2, addVal_prod]
end GlobalTheory.RelativeLengthSpanDet
