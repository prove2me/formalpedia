-- Prove2me | solution 1 for GlobalTheory.ThetaSpan.laws_of_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:15:57.314106+00:00
-- url     : https://prove2.me/submissions/89c8e707-e138-4df9-b434-8acc245dc592

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanThetaOfLevel
import Theorems.Thm_GlobalTheory_ThetaSpan_ofIntVec_single
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaSpan
namespace GlobalTheory.ThetaSpan
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (f : (Fin g → ℂ) → ℂ)
    (h : ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) :
    (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) ∧
      ∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) =
        eC (-(τ j j) / 2) ^ N * cexp (-(2 * Real.pi * I) * N * z j) * f z := by
  refine ⟨fun i z => ?_, fun j z => ?_⟩
  · have := h 0 (Pi.single i 1) z
    rw [ofIntVec_zero, ofIntVec_single] at this
    simpa [eC] using this
  · have := h (Pi.single j 1) 0 z
    rw [ofIntVec_zero, ofIntVec_single, add_zero] at this
    rw [this]
    congr 1
    simp only [eC, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [single_one_dotProduct, mulVec_single_one, Matrix.col_apply, transpose_apply]
    ring
end GlobalTheory.ThetaSpan
