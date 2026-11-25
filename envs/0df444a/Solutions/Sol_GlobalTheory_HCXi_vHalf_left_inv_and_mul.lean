-- Prove2me | solution 1 for GlobalTheory.HCXi.vHalf_left_inv_and_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:26:09.814147+00:00
-- url     : https://prove2.me/submissions/604f5a91-cfdb-4da4-a08b-a64802dcc1d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramMinorDetTriangularMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariant
import Theorems.Thm_GlobalTheory_HCXi_gram_nonneg_vmul
import Theorems.Thm_GlobalTheory_HCXi_gram_unitary_mul
import Theorems.Thm_GlobalTheory_HCXi_gram_mul_flag

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
theorem _root_.solution : ∀ k r : ℕ, 1 ≤ k →
    (∀ κ ∈ Kset k r, ∀ g : Mat k r, vHalf k r (κ * g) = vHalf k r g) ∧
    ∀ g ∈ GV k r, ∀ p ∈ Pset k r, vHalf k r (g * p) = vHalf k r g * vHalf k r p := by
  intro k r hk
  refine ⟨fun κ hκ g => ?_, fun g _ p hp => ?_⟩
  · unfold vHalf
    simp only [gram_unitary_mul k r κ g hκ.2]
  · unfold vHalf
    simp only [gram_mul_flag k r hk g p hp, mul_inv, Finset.prod_mul_distrib]
    rw [Real.mul_rpow (gram_nonneg_vmul k r g _) (gram_nonneg_vmul k r p _)]
    ring
end GlobalTheory.HCXi
