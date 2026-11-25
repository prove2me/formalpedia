-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDecomp.hq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:01:24.01761+00:00
-- url     : https://prove2.me/submissions/d50f330c-a597-407e-b78c-5d0e2326c902

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuDecomp
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.BmuDecomp
theorem _root_.solution : Hq k r * Hq k r = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : outer k r i
  · rw [Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · have h2 : outer k r ⟨2 * r + k - i.val, by omega⟩ := by
        unfold outer at *; have := i.isLt; simp only; omega
      have := i.isLt
      simp only [Hq, hi, h2, if_true, Matrix.one_apply, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · intro b _ hb
      have : ¬ (i.val + b.val = 2 * r + k) := fun h => hb (Fin.ext (by simp only; omega))
      simp [Hq, hi, this]
    · simp
  · rw [Finset.sum_eq_single i]
    · simp [Hq, hi, Matrix.one_apply]
    · intro b _ hb
      simp [Hq, hi, Ne.symm hb]
    · simp
end GlobalTheory.CompanionTheory.BmuDecomp
