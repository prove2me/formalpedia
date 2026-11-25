-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuSpan.blk_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:35.618849+00:00
-- url     : https://prove2.me/submissions/8ed14a15-005a-4de5-bedb-b78c29be6325

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SpanGenerators
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuSpan_pr_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu GlobalTheory.CompanionTheory.BmuDecomp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuSpan
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.BmuSpan
theorem _root_.solution (i j : Fin (2 * r + k + 1)) : blk k r (pr k r j) i ↔ blk k r (pr k r i) j := by
  have := i.isLt
  have := j.isLt
  simp only [blk, pr_val] at *
  split_ifs at * <;> omega
end GlobalTheory.CompanionTheory.BmuSpan
