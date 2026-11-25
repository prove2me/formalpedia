-- Prove2me | solution 1 for GlobalTheory.Mass.Hyperplane.smul_mem_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:02:08.602262+00:00
-- url     : https://prove2.me/submissions/efa97730-0cba-4aa1-af86-a5501b9041a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StarMemLocR

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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.Mass.Hyperplane
theorem _root_.solution {P : Ideal (𝓞 K)} {M : Submodule (𝓞 K) V} {a : K} {x : V} (ha : a ∈ locR (K := K) P)
    (hx : x ∈ loc (K := K) P M) : a • x ∈ loc (K := K) P M := by
  obtain ⟨s, hs, r, hr⟩ := mem_locR.1 ha
  obtain ⟨t, ht, hq⟩ := hx
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  have : (t * s) • a • x = r • t • x := by
    rw [smul_comm r t x, mul_smul, ← algebraMap_smul K r, hr, mul_smul, algebraMap_smul]
  rw [this]
  exact M.smul_mem _ hq
end GlobalTheory.Mass.Hyperplane
