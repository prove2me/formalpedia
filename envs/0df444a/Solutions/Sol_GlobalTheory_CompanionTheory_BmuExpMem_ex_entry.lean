-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuExpMem.ex_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:39:10.106748+00:00
-- url     : https://prove2.me/submissions/89a35045-ce9b-45f6-9083-23420e42b1c0

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExponentialMembership
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuExpMem_lin_exp_eq
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
theorem _root_.solution {n : ℕ} (X : Mat n) (t : ℝ) (a : ℕ) (j : Fin n)
    (h1 : ∀ i l : Fin n, a ≤ i.val → l.val < a → X i l = 0) (h2 : ∀ i : Fin n, a ≤ i.val → X i j = 0)
    (i : Fin n) (hi : a ≤ i.val) : ex X t i j = if i = j then 1 else 0 := by
  have hpow : ∀ m : ℕ, ∀ i' : Fin n, a ≤ i'.val → (X ^ (m + 1)) i' j = 0 := by
    intro m
    induction m with
    | zero => intro i' hi'; simpa using h2 i' hi'
    | succ m ih =>
      intro i' hi'
      rw [pow_succ', Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun l _ => ?_)
      by_cases hl : l.val < a
      · rw [h1 i' l hi' hl, zero_mul]
      · rw [ih l (not_lt.1 hl), mul_zero]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun M N => rfl
      map_smul' := fun c M => rfl }
  have hA : ∀ m : ℕ, L (((t : ℂ) • X) ^ (m + 1)) = 0 := by
    intro m
    show (((t : ℂ) • X) ^ (m + 1)) i j = 0
    rw [smul_pow, Matrix.smul_apply, hpow m i hi, smul_zero]
  have e := lin_exp_eq ((t : ℂ) • X) L hA
  have e' : (NormedSpace.exp ((t : ℂ) • X)) i j = (1 : Matrix (Fin n) (Fin n) ℂ) i j := e
  show (NormedSpace.exp ((t : ℂ) • X)) i j = _
  rw [e', Matrix.one_apply]
end GlobalTheory.CompanionTheory.BmuExpMem
