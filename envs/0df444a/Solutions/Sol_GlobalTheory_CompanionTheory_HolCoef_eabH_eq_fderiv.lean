-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolCoef.eabH_eq_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:37:49.099799+00:00
-- url     : https://prove2.me/submissions/b49f07c1-de06-4370-8fe9-3a614fa2c8e0

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_ExpEntry
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_HasDerivAtExpReal
import Theorems.Thm_GlobalTheory_CompanionTheory_HolCoef_rdV_eq_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolCoef
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.CompanionTheory.HolCoef
theorem _root_.solution (H g : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : DifferentiableAt ℂ f g) : EabH H a b f g = fderiv ℂ f g (g * Matrix.single a b 1) := by
  unfold EabH
  rw [rdV_eq_fderiv _ _ _ hf, rdV_eq_fderiv _ _ _ hf, ← map_smul, ← map_add, ← Matrix.mul_smul, ← Matrix.mul_add]
  congr 2
  unfold hpart1 hpart2
  rw [smul_smul]
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  rw [this, ← smul_add]
  rw [sub_add_add_cancel, ← two_smul ℂ, smul_smul]
  norm_num
end GlobalTheory.CompanionTheory.HolCoef
