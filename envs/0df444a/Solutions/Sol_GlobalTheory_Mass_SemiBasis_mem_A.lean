-- Prove2me | solution 1 for GlobalTheory.Mass.SemiBasis.mem_A
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:53.329089+00:00
-- url     : https://prove2.me/submissions/f4625b28-bdde-42c8-9e2d-d6ebd56a4f00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan

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
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) (x : K) :
    x ∈ A K hd ↔ ∃ (a s : 𝓞 K) (_ : s ∈ primeTo (d : 𝓞 K)),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl
end GlobalTheory.Mass.SemiBasis
