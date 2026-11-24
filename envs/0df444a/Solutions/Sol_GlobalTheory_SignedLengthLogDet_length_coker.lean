-- Prove2me | solution 1 for GlobalTheory.SignedLengthLogDet.length_coker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:02:45.609675+00:00
-- url     : https://prove2.me/submissions/971c67c6-8eb9-4dd9-a861-d541dc28ab02

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthEqLogOrdFracDet
import Theorems.Thm_GlobalTheory_SignedLengthLogDet_ord_finprod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthLogDet
open Module
namespace GlobalTheory.SignedLengthLogDet
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] (b : Basis ι R M)
    (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    Module.length R (M ⧸ LinearMap.range φ) = Ring.ord R (LinearMap.det φ) := by
  classical
  set N := LinearMap.range φ with hN
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective φ hφ
  have hrk : finrank R N = finrank R M := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b hrk
  let t := Submodule.smithNormalFormTopBasis b hrk
  let s := Submodule.smithNormalFormBotBasis b hrk
  have hs : ∀ i, (s i : M) = c i • t i := Submodule.smithNormalFormBotBasis_def b hrk
  have hc : ∀ i, c i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrk
  let e' : M ≃ₗ[R] N := t.equiv s (Equiv.refl _)
  have h1 : Associated (LinearMap.det φ) (LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N))) := by
    have : φ = N.subtype ∘ₗ (e : M →ₗ[R] N) := by ext x; rfl
    conv_lhs => rw [this]
    exact LinearMap.associated_det_comp_equiv _ _ _
  have h2 : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix t, ← Matrix.det_diagonal]
    congr 1
    ext i j
    have : (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (t j) = c j • t j := by
      simp [e', hs]
    rw [LinearMap.toMatrix_apply, this, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h]
  rw [Ring.ord_eq_of_associated h1, h2, ord_finprod _ _ hc,
    (Submodule.quotientEquivPiSpan N b hrk).length_eq, Module.length_pi_of_fintype]
  rfl
end GlobalTheory.SignedLengthLogDet
