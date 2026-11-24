-- Prove2me | solution 1 for GlobalTheory.NormVal.addVal_det_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:29:31.524449+00:00
-- url     : https://prove2.me/submissions/76ee555f-adbd-4234-9ec7-746c9e32e3b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
import Theorems.Thm_GlobalTheory_NormVal_length_quot_span_singleton
import Theorems.Thm_GlobalTheory_NormVal_addVal_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open GlobalTheory.NormVal
variable {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
namespace GlobalTheory.NormVal
theorem _root_.solution (f : M →ₗ[R] M) (hf : Function.Injective f) :
    addVal R (LinearMap.det f) = Module.length R (M ⧸ LinearMap.range f) := by
  classical
  let N := LinearMap.range f
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let g : M →ₗ[R] M := N.subtype.comp (e' : M →ₗ[R] N)
  have hfe : f = N.subtype.comp (e : M →ₗ[R] N) := by ext x; rfl
  have hass : Associated (LinearMap.det f) (LinearMap.det g) := by
    rw [hfe]; exact LinearMap.associated_det_comp_equiv _ _ _
  have ha : ∀ i, g (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _) (b' i) : N) : M) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hg : LinearMap.toMatrix b' b' g = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases h : i = j
    · rw [h, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ h, Finsupp.single_eq_of_ne h]
  rw [(addVal_eq_iff_associated _ _).2 hass, ← LinearMap.det_toMatrix b', hg, Matrix.det_diagonal,
    addVal_prod, (N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ => (length_quot_span_singleton _).symm
end GlobalTheory.NormVal
