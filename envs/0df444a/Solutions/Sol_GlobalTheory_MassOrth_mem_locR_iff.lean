-- Prove2me | solution 1 for GlobalTheory.MassOrth.mem_locR_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:10.22464+00:00
-- url     : https://prove2.me/submissions/3e3a4985-28ef-47e9-b8c7-53e9174cb392

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Theorems.Thm_GlobalTheory_MassOrth_mem_loc_span_iff

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
open GlobalTheory GlobalTheory.MassOrth
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.MassOrth
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (k : K) :
    k ∈ locR (K := K) w.asIdeal ↔ k ∈ biInt (w.valuation K) := by
  rw [locR, Submodule.one_eq_span, mem_loc_span_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Subring.smul_def, smul_eq_mul, mul_one]; exact a.2
  · intro hk
    exact ⟨⟨k, hk⟩, by rw [Subring.smul_def, smul_eq_mul, mul_one]⟩
end GlobalTheory.MassOrth
