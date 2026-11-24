-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.exists_basis_trace_conj_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:41:33.001679+00:00
-- url     : https://prove2.me/submissions/6c05f990-95d6-498e-93e5-9fad1e3b9cb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniformizerCompatibleUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitTraceFormDiscrUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitDetConjugationMatrixIntegralBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisTraceInvolutionDetUnitUnramified
import Theorems.Thm_GlobalTheory_T_exists_integral_basis_unramifiedInvolutionExt
import Theorems.Thm_GlobalTheory_T_exists_uniformizer_compatible_unramifiedExt
import Theorems.Thm_GlobalTheory_T_isUnit_det_conjugationMatrix_integralBasis
import Theorems.Thm_GlobalTheory_T_isUnit_traceForm_discr_unramifiedExt
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_val_unit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → letI : Algebra K.E K'.E := φ.toAlgebra; ∃ w : Module.Basis (Fin d) K.E K'.E, (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det ≠ 0 ∧ val K.O (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = 0 := by
  intro K K' d φ h hd
  letI : Algebra K.E K'.E := φ.toAlgebra
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt K K' d φ h hd
  refine ⟨w, ?_⟩
  obtain ⟨π, π', hππ, hm, hm'⟩ := GlobalTheory.T.exists_uniformizer_compatible_unramifiedExt K K' d φ h
  obtain ⟨u, hu, hue⟩ := GlobalTheory.T.isUnit_traceForm_discr_unramifiedExt K K' d φ h π π' hππ hm hm' w hw
  obtain ⟨v, hv, hve⟩ := GlobalTheory.T.isUnit_det_conjugationMatrix_integralBasis K K' d φ h.2.1 w hw
  have key : (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))) =
      (Matrix.of fun k m => Algebra.trace K.E K'.E (w k * w m)) * (Matrix.of fun m l => w.repr (K'.c (w l)) m) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.of_apply]
    conv_lhs => rw [← w.sum_repr (K'.c (w l))]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hdet : (Matrix.of fun k l => Algebra.trace K.E K'.E (w k * K'.c (w l))).det = algebraMap K.O K.E (u * v) := by
    rw [key, Matrix.det_mul, ← hue, ← hve, map_mul]
  rw [hdet]
  refine ⟨?_, GlobalTheory.UnitLemma.Orbit.val_unit _ (hu.mul hv)⟩
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]
  exact (hu.mul hv).ne_zero
end GlobalTheory.UnitLemma.Unr
