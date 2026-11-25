-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuIwa.pq_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:58:58.767067+00:00
-- url     : https://prove2.me/submissions/f094e39c-d20c-4e25-a81d-81a698cbe620

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwasawaDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuIwa
open Matrix CompanionTheory.Bmu CompanionTheory.D.gk.admitted.CholeskyDecomposition Formalism.QuantumDeterminants
open scoped ComplexOrder MatrixOrder
namespace GlobalTheory.CompanionTheory.BmuIwa
theorem _root_.solution (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (pq k r i).val = if i.val ≤ r ∨ r + k ≤ i.val then 2 * r + k - i.val else i.val := by
  unfold pq
  by_cases h : outer k r i
  · rw [if_pos h, if_pos (show i.val ≤ r ∨ r + k ≤ i.val from h), Fin.val_rev]; omega
  · rw [if_neg h, if_neg (show ¬ (i.val ≤ r ∨ r + k ≤ i.val) from h)]
end GlobalTheory.CompanionTheory.BmuIwa
