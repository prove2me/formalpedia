-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuExpMem.ex_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:38:06.748166+00:00
-- url     : https://prove2.me/submissions/1a7f1d31-fbc8-498f-9d99-2caea03af3e0

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExponentialMembership
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuExpMem_lin_exp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuExpMem
namespace GlobalTheory.CompanionTheory.BmuExpMem
theorem _root_.solution {n : ℕ} (X : Mat n) (t : ℝ) (v : Fin n → ℂ) (hv : X *ᵥ v = 0) : ex X t *ᵥ v = v := by
  funext i
  have hsm : ∀ (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ), (c • M) *ᵥ v = c • (M *ᵥ v) := by
    intro c M
    funext l
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => (M *ᵥ v) i
      map_add' := fun M N => by simp [Matrix.add_mulVec]
      map_smul' := fun c M => by simp [hsm] }
  have hA : ∀ m : ℕ, L (((t : ℂ) • X) ^ (m + 1)) = 0 := by
    intro m
    show ((((t : ℂ) • X) ^ (m + 1)) *ᵥ v) i = 0
    rw [pow_succ, ← Matrix.mulVec_mulVec, hsm, hv, smul_zero, Matrix.mulVec_zero]
    rfl
  have e := lin_exp_eq ((t : ℂ) • X) L hA
  have e' : ((NormedSpace.exp ((t : ℂ) • X)) *ᵥ v) i = ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i := e
  show ((NormedSpace.exp ((t : ℂ) • X)) *ᵥ v) i = v i
  rw [e', Matrix.one_mulVec]
end GlobalTheory.CompanionTheory.BmuExpMem
