-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDecomp.dg_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:53.160974+00:00
-- url     : https://prove2.me/submissions/9c4d72c1-9bce-42a8-911d-d992ae13b62a

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_hq_e
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_hq_es
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_block_of_fix

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
theorem _root_.solution {t : Fin (2 * r + k + 1) → ℝ} (ht : IsTor k r t) (ht0 : t (wI k r 0) = 1)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ Wbq k r) : dg t * h = h * dg t := by
  have b := block_of_fix hh.1 (fun a => ⟨hq_e a, hq_es a⟩) (fun a => ⟨hq_e a, hq_es a⟩) hh.2
  obtain ⟨-, h2, h3, -⟩ := ht
  have mid : ∀ i : Fin (2 * r + k + 1), ¬ (i.val < r ∨ r + k < i.val) → t i = 1 := by
    intro i hi
    by_cases ho : outer k r i
    · by_cases h0 : i.val = r
      · have : i = wI k r 0 := Fin.ext (by simp [wI, h0])
        rw [this, ht0]
      · have := h2 i (wI k r 0) ho (by unfold outer at ho; simp only [wI, Fin.val_zero]; omega)
        rwa [ht0, mul_one] at this
    · exact h3 i ho
  ext i j
  simp only [dg, mul_diagonal, diagonal_mul]
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [(b i hi j).2]
    split_ifs with e
    · subst e; simp
    · simp
  · by_cases hj : j.val < r ∨ r + k < j.val
    · rw [(b j hj i).1]
      split_ifs with e
      · subst e; simp
      · simp
    · rw [mid i hi, mid j hj]; simp
end GlobalTheory.CompanionTheory.BmuDecomp
