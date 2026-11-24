-- Prove2me | solution 1 for GlobalTheory.SignedLengthMapLogDet.length_coker_eq_ord_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:01:33.77283+00:00
-- url     : https://prove2.me/submissions/e2e820fe-9e60-43bc-9af8-974ea4e16f30

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet
import Theorems.Thm_GlobalTheory_SignedLengthMapLogDet_ord_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.SignedLengthMapLogDet
open Module
variable {R : Type*} [CommRing R] [IsDomain R]
namespace GlobalTheory.SignedLengthMapLogDet
theorem _root_.solution [IsPrincipalIdealRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = Ring.ord R (LinearMap.det f) := by
  classical
  set N := LinearMap.range f with hN
  let b := Module.Free.chooseBasis R M
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  have h : finrank R N = finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let top := Submodule.smithNormalFormTopBasis b h
  let bot := Submodule.smithNormalFormBotBasis b h
  let e' : M ≃ₗ[R] N := top.equiv bot (Equiv.refl _)
  have hdiag : LinearMap.toMatrix top top (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = Matrix.diagonal a := by
    ext i j
    have : ((e' (top j) : N) : M) = a j • top j := by
      rw [Basis.equiv_apply, Equiv.refl_apply]
      exact Submodule.smithNormalFormBotBasis_def b h j
    rw [LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.subtype_apply, this, map_smul, Basis.repr_self, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij; simp
    · simp [Finsupp.single_eq_of_ne hij]
  have hassoc : Associated (LinearMap.det f) (∏ i, a i) := by
    rw [← Matrix.det_diagonal, ← hdiag, LinearMap.det_toMatrix]
    exact LinearMap.associated_det_comp_equiv N.subtype e e'
  rw [Ring.ord_eq_of_associated hassoc,
    ord_prod _ _ (Submodule.smithNormalFormCoeffs_ne_zero b h),
    (Submodule.quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype]
  rfl
end GlobalTheory.SignedLengthMapLogDet
