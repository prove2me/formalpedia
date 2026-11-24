-- Prove2me | solution 1 for GlobalTheory.Mass.SemiBasis.isPID
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:13:23.741672+00:00
-- url     : https://prove2.me/submissions/c8dd2e98-bff4-4b01-b07a-d3932afb4bb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan
import Theorems.Thm_GlobalTheory_Mass_SemiBasis_primes_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SemiBasis
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mass.SemiBasis
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) : IsPrincipalIdealRing (A K hd) := by
  have : IsDedekindDomain (A K hd) :=
    IsLocalization.isDedekindDomain (𝓞 K) (primeTo_le hd) (A K hd)
  exact IsPrincipalIdealRing.of_finite_primes (primes_finite hd)
end GlobalTheory.Mass.SemiBasis
