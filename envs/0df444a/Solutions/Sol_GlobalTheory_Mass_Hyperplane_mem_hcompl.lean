-- Prove2me | solution 1 for GlobalTheory.Mass.Hyperplane.mem_hcompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:03:08.306374+00:00
-- url     : https://prove2.me/submissions/ae3ebb42-5731-4d91-b4a4-9f11a17c51b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StarMemLocR
import Theorems.Thm_GlobalTheory_Mass_Hyperplane_cj_coe

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Hyperplane
variable {K : Type} [Field K] [StarRing K]
namespace GlobalTheory.Mass.Hyperplane
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsPrime) (s : 𝓞 K) :
    s ∈ hcompl (K := K) P ↔ s ∉ P ∧ cj K s ∉ P := by
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact ⟨hx.1, hx.2 _ (cj_coe x)⟩
    | one => rw [map_one]; exact ⟨hP.one_notMem, hP.one_notMem⟩
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact ⟨fun H => (hP.mem_or_mem H).elim hx.1 hy.1, fun H => (hP.mem_or_mem H).elim hx.2 hy.2⟩
  · rintro ⟨h1, h2⟩
    refine Submonoid.subset_closure ⟨h1, fun t ht => ?_⟩
    rw [← cj_coe] at ht
    rw [RingOfIntegers.coe_injective ht]
    exact h2
end GlobalTheory.Mass.Hyperplane
