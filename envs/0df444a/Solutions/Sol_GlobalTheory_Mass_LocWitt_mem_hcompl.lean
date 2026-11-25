-- Prove2me | solution 1 for GlobalTheory.Mass.LocWitt.mem_hcompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:16:05.466492+00:00
-- url     : https://prove2.me/submissions/de00ebae-8186-4d68-94dc-dcc5011e0f08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LocWitt
namespace GlobalTheory.Mass.LocWitt
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : conjIdeal (K := K) P = P) (s : 𝓞 K) :
    s ∈ hcompl (K := K) P ↔ s ∉ P := by
  constructor
  · intro hs
    have := hP.isPrime
    exact (Submonoid.closure_le (S := P.primeCompl)).2 (fun _ a => a.1) hs
  · intro hs
    refine Submonoid.subset_closure ⟨hs, fun t e ht => hs ?_⟩
    rw [← hc]
    exact Ideal.subset_span ⟨t, ht, by rw [e, star_star]⟩
end GlobalTheory.Mass.LocWitt
