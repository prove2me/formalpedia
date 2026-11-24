-- Prove2me | solution 1 for GlobalTheory.LengthQuotientValuationDet.length_quotient_eq_addVal_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:58:22.015897+00:00
-- url     : https://prove2.me/submissions/ded7f2c4-3c5e-4291-b01e-6435d4cb7490

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthQuotientSpanSingleton
import Theorems.Thm_GlobalTheory_LengthQuotientValuationDet_addVal_prod
import Theorems.Thm_GlobalTheory_LengthQuotientValuationDet_length_quotient_span_singleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthQuotientValuationDet
open Module IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace GlobalTheory.LengthQuotientValuationDet
theorem _root_.solution {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type u_2} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (N : Submodule R M) (e : M ≃ₗ[R] N) :
    Module.length R (M ⧸ N) =
      (addVal R : R → ℕ∞) (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) := by
  classical
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
  have hassoc : Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N))) (LinearMap.det f) :=
    LinearMap.associated_det_comp_equiv _ _ _
  rw [(addVal_eq_iff_associated _ _).mpr hassoc]
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _)) (b' i) : M) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  rw [hdet, addVal_prod, (N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ =>
    length_quotient_span_singleton (Submodule.smithNormalFormCoeffs_ne_zero b h i)
end GlobalTheory.LengthQuotientValuationDet
