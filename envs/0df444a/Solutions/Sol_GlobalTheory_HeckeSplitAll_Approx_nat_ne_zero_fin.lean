-- Prove2me | solution 1 for GlobalTheory.HeckeSplitAll.Approx.nat_ne_zero_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:54.923853+00:00
-- url     : https://prove2.me/submissions/6542514b-e07e-4110-a1b6-fb994a89fd94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFinsetNormOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology Filter
open GlobalTheory GlobalTheory.HeckeSplitAll GlobalTheory.HeckeSplitAll.Approx
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeSplitAll.Approx
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (hm : m ≠ 0) : (m : v.adicCompletion F) ≠ 0 := by
  have h := (algebraMap F (v.adicCompletion F)).injective.ne (Nat.cast_ne_zero.2 hm : (m : F) ≠ 0)
  rwa [map_natCast, map_zero] at h
end GlobalTheory.HeckeSplitAll.Approx
