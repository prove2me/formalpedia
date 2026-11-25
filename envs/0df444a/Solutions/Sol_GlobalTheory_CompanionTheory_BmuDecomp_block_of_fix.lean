-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDecomp.block_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:54:43.558619+00:00
-- url     : https://prove2.me/submissions/013129ba-b891-465b-a061-330deb724de4

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_fix_adj
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_col_of_fix
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_row_of_fix

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
theorem _root_.solution {A B P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hP : Pᴴ * A * P = B)
    (hA : ∀ a : Fin r, A *ᵥ bvec (eI k r a) = bvec (esI k r a) ∧ A *ᵥ bvec (esI k r a) = bvec (eI k r a))
    (hB : ∀ a : Fin r, B *ᵥ bvec (eI k r a) = bvec (esI k r a) ∧ B *ᵥ bvec (esI k r a) = bvec (eI k r a))
    (hf : ∀ a : Fin r, P *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ P *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    P j i = (if j = i then 1 else 0) ∧ P i j = (if j = i then 1 else 0) := by
  have := i.isLt
  rcases hi with hi | hi
  · have e : i = eI k r ⟨i.val, hi⟩ := rfl
    rw [e]
    exact ⟨col_of_fix (hf _).1 j, row_of_fix (fix_adj hP (hf _).2 (hA _).2 (hB _).2) j⟩
  · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := Fin.ext (by simp only [esI]; omega)
    rw [e]
    exact ⟨col_of_fix (hf _).2 j, row_of_fix (fix_adj hP (hf _).1 (hA _).1 (hB _).1) j⟩
end GlobalTheory.CompanionTheory.BmuDecomp
