-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuTorConj.exists_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:20:53.89524+00:00
-- url     : https://prove2.me/submissions/83a5e7fa-527a-4e97-a240-c8bff8354b7d

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugacy
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuTorConj_cStd_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuTorConj
namespace GlobalTheory.CompanionTheory.BmuTorConj
theorem _root_.solution (r : ℕ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) :
    ∃ T : ℕ → ℂ, (∀ n, T n ≠ 0) ∧ (∀ n, r ≤ n → T n = 1) ∧
      ∀ a : Fin r, c a * T a.val = cStd * T (a.val + 1) := by
  classical
  obtain ⟨c', hc'd⟩ : ∃ f : ℕ → ℂ, f = fun m => if h : m < r then c ⟨m, h⟩ else 1 := ⟨_, rfl⟩
  have hc' : ∀ m, c' m ≠ 0 := fun m => by
    by_cases h : m < r
    · simp only [hc'd, dif_pos h]; exact hc _
    · simp only [hc'd, dif_neg h]; exact one_ne_zero
  refine ⟨fun n => ∏ m ∈ Finset.Ico n r, (cStd / c' m), ?_, ?_, ?_⟩
  · intro n
    exact Finset.prod_ne_zero_iff.mpr fun m _ => div_ne_zero cStd_ne (hc' m)
  · intro n hn
    simp [Finset.Ico_eq_empty_of_le hn]
  · intro a
    simp only
    rw [Finset.prod_eq_prod_Ico_succ_bot a.isLt]
    have hca : c' a.val = c a := by simp only [hc'd, dif_pos a.isLt]
    rw [hca]
    have hcz := hc a
    field_simp
end GlobalTheory.CompanionTheory.BmuTorConj
