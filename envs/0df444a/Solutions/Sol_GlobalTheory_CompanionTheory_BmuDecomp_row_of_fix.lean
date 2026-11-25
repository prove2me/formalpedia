-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDecomp.row_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:33:13.008625+00:00
-- url     : https://prove2.me/submissions/73cfead6-46a3-4795-85a0-eaf7ce027e19

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuDecomp_col_of_fix

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
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BmuDecomp
theorem _root_.solution {P : Matrix (Fin n) (Fin n) ℂ} {i : Fin n} (h : Pᴴ *ᵥ bvec i = bvec i) (j : Fin n) :
    P i j = if j = i then 1 else 0 := by
  have := congrArg star (col_of_fix h j)
  rw [conjTranspose_apply, star_star] at this
  rw [this]
  split_ifs <;> simp
end GlobalTheory.CompanionTheory.BmuDecomp
