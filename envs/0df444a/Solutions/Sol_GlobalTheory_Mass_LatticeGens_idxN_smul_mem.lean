-- Prove2me | solution 1 for GlobalTheory.Mass.LatticeGens.idxN_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:30:28.401458+00:00
-- url     : https://prove2.me/submissions/d0bab904-778c-4e68-951e-1bfff92b5be4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LatticeGens
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
namespace GlobalTheory.Mass.LatticeGens
theorem _root_.solution (A B : Submodule R V) {x : V} (hx : x ∈ B) :
    ((idxN B A : ℕ) : R) • x ∈ A := by
  rw [Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup (K := B.toAddSubgroup) hx
end GlobalTheory.Mass.LatticeGens
