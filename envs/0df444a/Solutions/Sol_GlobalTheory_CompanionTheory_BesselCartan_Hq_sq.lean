-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.Hq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:25.370341+00:00
-- url     : https://prove2.me/submissions/5bc3fef5-0d52-4e06-91d8-78bd0f831ce2

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_Hq_outer
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_Hq_inner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselCartan
open scoped ComplexOrder
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BesselCartan
theorem _root_.solution (k r : ℕ) : Hq k r * Hq k r = 1 := by
  have hHq : ∀ i j : Fin (2 * r + k + 1), Hq k r i j =
      if outer k r i then (if (i : ℕ) + (j : ℕ) = 2 * r + k then 1 else 0) else if i = j then 1 else 0 :=
    fun _ _ => rfl
  have hout : ∀ i : Fin (2 * r + k + 1), outer k r i ↔ ((i : ℕ) ≤ r ∨ r + k ≤ (i : ℕ)) := fun _ => Iff.rfl
  have hbv : ∀ {m : ℕ} (i : Fin m), bvec i = Pi.single i (1 : ℂ) := fun _ => rfl
  have hcol : ∀ j, (Hq k r * Hq k r) *ᵥ bvec j = bvec j := by
    intro j
    have hjl := j.isLt
    rw [← Matrix.mulVec_mulVec]
    by_cases hj : outer k r j
    · have hlt : 2 * r + k - j.val < 2 * r + k + 1 := by omega
      have hj' : outer k r ⟨2 * r + k - j.val, hlt⟩ := by
        rw [hout] at hj ⊢
        simp only [Fin.val_mk]
        omega
      rw [GlobalTheory.CompanionTheory.BesselCartan.Hq_outer k r ⟨2 * r + k - j.val, hlt⟩ j hj' (by simp only [Fin.val_mk]; omega),
        GlobalTheory.CompanionTheory.BesselCartan.Hq_outer k r j ⟨2 * r + k - j.val, hlt⟩ hj (by simp only [Fin.val_mk]; omega)]
    · rw [GlobalTheory.CompanionTheory.BesselCartan.Hq_inner k r j hj, GlobalTheory.CompanionTheory.BesselCartan.Hq_inner k r j hj]
  ext i j
  have h := congrFun (hcol j) i
  simp only [Matrix.mulVec, dotProduct, hbv, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h, Matrix.one_apply]
end GlobalTheory.CompanionTheory.BesselCartan
