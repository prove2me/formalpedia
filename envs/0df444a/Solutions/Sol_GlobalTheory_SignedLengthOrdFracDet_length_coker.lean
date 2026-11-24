-- Prove2me | solution 1 for GlobalTheory.SignedLengthOrdFracDet.length_coker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:01:30.600224+00:00
-- url     : https://prove2.me/submissions/71408241-90f1-4548-9f69-9dcb1fbdba15

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthSpanEqOrdFracDet
import Theorems.Thm_GlobalTheory_SignedLengthOrdFracDet_ord_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SignedLengthOrdFracDet
open Module Submodule
namespace GlobalTheory.SignedLengthOrdFracDet
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e₀ : Basis ι R M) (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = Ring.ord R (LinearMap.det f) := by
  have : Module.Finite R M := Module.Finite.of_basis e₀
  have : Module.Free R M := Module.Free.of_basis e₀
  let N := LinearMap.range f
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let c := smithNormalFormCoeffs e₀ h
  let t := smithNormalFormTopBasis e₀ h
  let u := smithNormalFormBotBasis e₀ h
  let e' : M ≃ₗ[R] N := t.equiv u (Equiv.refl _)
  have h1 : Associated (LinearMap.det f) (LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N))) :=
    LinearMap.associated_det_comp_equiv N.subtype e e'
  have h2 : LinearMap.toMatrix t t (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = Matrix.diagonal c := by
    ext i j
    have hj : (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (t j) = c j • t j := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e', Basis.equiv_apply,
        Equiv.refl_apply]
      exact smithNormalFormBotBasis_def e₀ h j
    rw [LinearMap.toMatrix_apply, hj, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [Ring.ord_eq_of_associated h1, ← LinearMap.det_toMatrix t, h2, Matrix.det_diagonal,
    ord_prod _ _ (smithNormalFormCoeffs_ne_zero e₀ h),
    (quotientEquivPiSpan N e₀ h).length_eq, Module.length_pi_of_fintype]
  rfl
end GlobalTheory.SignedLengthOrdFracDet
