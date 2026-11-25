-- Prove2me | solution 1 for GlobalTheory.HCXi.VLev.vHalf_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:56:01.967056+00:00
-- url     : https://prove2.me/submissions/71a48420-f3ac-4e95-a0b3-847b8c2d39ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
import Theorems.Thm_GlobalTheory_HCXi_VLev_gram_K
import Theorems.Thm_GlobalTheory_HCXi_VLev_star_e0_dotProduct_self
import Theorems.Thm_GlobalTheory_HCXi_VLev_vHalf_block
import Theorems.Thm_GlobalTheory_HCXi_VLev_sqLen_eq
import Theorems.Thm_GlobalTheory_HCXi_VLev_levi_embedding_mulVec_e0
import Theorems.Thm_GlobalTheory_HCXi_VLev_parabolic_mulVec_e0_smul
import Theorems.Thm_GlobalTheory_T_exists_mem_Kset_mul_mem_Pset_eq
import Theorems.Thm_GlobalTheory_T_parabolic_line_stabilizer_levi
import Theorems.Thm_PI_QnLevBasicsW_mulVec_lift


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
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.VLev
namespace GlobalTheory.HCXi.VLev
theorem _root_.solution : ∀ k r' : ℕ, 1 ≤ k → ∀ x ∈ GV k (1 + r'), ∃ g₁ ∈ GV k r', ∀ y ∈ GV k r', vHalf k (1 + r') (x * ιLev k 1 r' y) = sqLen (x *ᵥ e0 k r') ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) * vHalf k r' (g₁ * y) := by
  intro k r' hk x hx
  obtain ⟨κ, hκ, p, hp, rfl⟩ := GlobalTheory.T.exists_mem_Kset_mul_mem_Pset_eq k (1 + r') hk x hx
  obtain ⟨a, ha⟩ := parabolic_mulVec_e0_smul hp
  obtain ⟨ha0, g₁, hg₁, hw⟩ := GlobalTheory.T.parabolic_line_stabilizer_levi k r' a p hp.1 ha
  refine ⟨g₁, hg₁, fun y _ => ?_⟩
  have h1 : vHalf k (1 + r') (κ * p * ιLev k 1 r' y) = vHalf k (1 + r') (p * ιLev k 1 r' y) := by
    simp only [vHalf, Matrix.mul_assoc κ, gram_K _ _ _ _ hκ.2]
  have h2 : sqLen ((κ * p) *ᵥ e0 k r') = Complex.normSq a := by
    rw [sqLen_eq, ← Matrix.mulVec_mulVec, ha, star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hκ.2,
      Matrix.one_mulVec, star_smul, smul_dotProduct, dotProduct_smul, star_e0_dotProduct_self]
    simp [Complex.normSq_apply]
  rw [h1, h2]
  refine vHalf_block _ _ a ?_ (fun w => ?_) ha0
  · rw [← Matrix.mulVec_mulVec, levi_embedding_mulVec_e0, ha]
  · rw [← Matrix.mulVec_mulVec, PI.QnLevBasicsW.mulVec_lift, ← Matrix.mulVec_mulVec]
    exact hw _
end GlobalTheory.HCXi.VLev
