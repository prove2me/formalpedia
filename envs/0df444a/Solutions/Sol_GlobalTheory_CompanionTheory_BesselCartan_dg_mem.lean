-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselCartan.dg_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:24:38.939306+00:00
-- url     : https://prove2.me/submissions/1ea68a47-28b9-4606-af27-fae447e9da02

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_tor_pair
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselCartan_tor_inner

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
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) (u : ℝ) (hu : u ≠ 0) : dg (tor k r u) ∈ UH (Hq k r) := by
  have hHq : ∀ i j : Fin (2 * r + k + 1), Hq k r i j =
      if outer k r i then (if (i : ℕ) + (j : ℕ) = 2 * r + k then 1 else 0) else if i = j then 1 else 0 :=
    fun _ _ => rfl
  have hout : ∀ i : Fin (2 * r + k + 1), outer k r i ↔ ((i : ℕ) ≤ r ∨ r + k ≤ (i : ℕ)) := fun _ => Iff.rfl
  have hdg : ∀ {m : ℕ} (d : Fin m → ℝ), dg d = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := fun _ => rfl
  have hUH : ∀ {m : ℕ} (H g : Matrix (Fin m) (Fin m) ℂ), g ∈ UH H ↔ gᴴ * H * g = H := fun _ _ => Iff.rfl
  rw [hUH]
  ext i j
  simp only [hdg, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  by_cases h1 : outer k r i
  · by_cases h2 : i.val + j.val = 2 * r + k
    · have ht := GlobalTheory.CompanionTheory.BesselCartan.tor_pair k r hk u hu i j h2
      have : ((tor k r u i : ℝ) : ℂ) * (tor k r u j : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ht, Complex.ofReal_one]
      calc ((tor k r u i : ℝ) : ℂ) * Hq k r i j * (tor k r u j : ℂ)
          = (((tor k r u i : ℝ) : ℂ) * (tor k r u j : ℂ)) * Hq k r i j := by ring
        _ = Hq k r i j := by rw [this, one_mul]
    · simp [hHq, h1, h2]
  · by_cases h3 : i = j
    · subst h3
      rw [GlobalTheory.CompanionTheory.BesselCartan.tor_inner k r u i h1]
      simp
    · simp [hHq, h1, h3]
end GlobalTheory.CompanionTheory.BesselCartan
