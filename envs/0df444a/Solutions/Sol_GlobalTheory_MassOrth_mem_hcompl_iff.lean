-- Prove2me | solution 1 for GlobalTheory.MassOrth.mem_hcompl_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:22.621115+00:00
-- url     : https://prove2.me/submissions/39a31bd5-a90f-492e-b3de-9f1bc2851ffb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Theorems.Thm_GlobalTheory_MassOrth_coe_starInt

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
omit [NumberField K]
namespace GlobalTheory.MassOrth
theorem _root_.solution (P : Ideal (𝓞 K)) (hP : P.IsPrime) (s : 𝓞 K) :
    s ∈ hcompl (K := K) P ↔ s ∉ P ∧ starInt s ∉ P := by
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact ⟨hx.1, hx.2 _ (coe_starInt x)⟩
    | one =>
      rw [map_one, and_self]
      exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact ⟨fun h => (hP.mem_or_mem h).elim ha.1 hb.1, fun h => (hP.mem_or_mem h).elim ha.2 hb.2⟩
  · rintro ⟨h1, h2⟩
    refine Submonoid.subset_closure ⟨h1, fun t ht => ?_⟩
    have : t = starInt s := RingOfIntegers.coe_injective (ht.trans (coe_starInt s).symm)
    rwa [this]
end GlobalTheory.MassOrth
