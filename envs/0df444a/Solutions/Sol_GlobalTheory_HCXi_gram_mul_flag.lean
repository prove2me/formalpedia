-- Prove2me | solution 1 for GlobalTheory.HCXi.gram_mul_flag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:00:34.198954+00:00
-- url     : https://prove2.me/submissions/2311ba64-8a3c-4a4d-8ab9-5b3e0c97afeb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramMinorDetTriangularMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariant
import Theorems.Thm_GlobalTheory_T_frame_isotropic_orthonormal
import Theorems.Thm_GlobalTheory_T_gram_minor_det_triangular_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi
namespace GlobalTheory.HCXi
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) (g p : Mat k r) (hp : p ∈ Pset k r)
    (a : Fin (r + 1)) : gram k r (g * p) a = gram k r g a * gram k r p a := by
  obtain ⟨-, u, hu, hpu⟩ := hp
  have hF := (GlobalTheory.T.frame_isotropic_orthonormal k r hk).1
  have h1 := GlobalTheory.T.gram_minor_det_triangular_mul _ _ (g * frame k r) u _ (Nat.succ_le_of_lt a.isLt) hu
  have h2 := GlobalTheory.T.gram_minor_det_triangular_mul _ _ (frame k r) u _ (Nat.succ_le_of_lt a.isLt) hu
  have e1 : g * p * frame k r = g * frame k r * u := by
    rw [Matrix.mul_assoc, hpu, Matrix.mul_assoc]
  rw [hF, Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one, mul_one] at h2
  unfold gram
  rw [e1, hpu, h1, h2, Complex.re_ofReal_mul, Complex.ofReal_re, mul_comm]
end GlobalTheory.HCXi
