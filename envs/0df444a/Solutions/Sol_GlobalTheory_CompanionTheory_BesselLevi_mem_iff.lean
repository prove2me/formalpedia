-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BesselLevi.mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:48:27.046516+00:00
-- url     : https://prove2.me/submissions/270be53e-d3b1-4674-887b-a024304c1134

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LeviDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_Hq_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_BesselLevi_Hq_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BesselLevi
namespace GlobalTheory.CompanionTheory.BesselLevi
theorem _root_.solution (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    g ∈ UH (Hq k r) ↔ ∀ i j, ∑ x, conj (g x i) * g (pr k r x) j = if pr k r i = j then 1 else 0 := by
  unfold UH
  rw [Set.mem_setOf_eq, Matrix.mul_assoc, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.mul_apply, Hq_apply]
  simp only [Hq_mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
end GlobalTheory.CompanionTheory.BesselLevi
