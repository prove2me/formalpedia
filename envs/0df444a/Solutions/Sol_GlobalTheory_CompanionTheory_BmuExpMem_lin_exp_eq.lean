-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuExpMem.lin_exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:02:15.216648+00:00
-- url     : https://prove2.me/submissions/a386e61f-2965-496d-8d7a-4f2975053a0b

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExponentialMembership
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero


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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ m : ℕ, L (A ^ (m + 1)) = 0) : L (NormedSpace.exp A) = L 1 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hs : HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹) • A ^ m) (NormedSpace.exp A) :=
    NormedSpace.exp_series_hasSum_exp' A
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have h1 := hs.map L hL
  have h2 : HasSum (fun m : ℕ => L (((m.factorial : ℂ)⁻¹) • A ^ m)) (L 1) := by
    have e : (fun m : ℕ => L (((m.factorial : ℂ)⁻¹) • A ^ m)) = fun m => if m = 0 then L 1 else 0 := by
      funext m
      cases m with
      | zero => simp
      | succ m => rw [map_smul, h m, smul_zero]; simp
    rw [e]
    exact hasSum_ite_eq 0 (L 1)
  exact h1.unique h2
end GlobalTheory.CompanionTheory.BmuExpMem
