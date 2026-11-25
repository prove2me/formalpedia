-- Prove2me | solution 1 for GlobalTheory.SublatCount.finrank_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:33:14.31939+00:00
-- url     : https://prove2.me/submissions/da029a3e-bc19-4fc1-a8ae-664dcd659ea7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSublatticesQuotientProdDegreeOnePrimes

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
open GlobalTheory GlobalTheory.SublatCount
namespace GlobalTheory.SublatCount
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V)
    (hM : Submodule.IsLattice K M) : Module.finrank (𝓞 K) M = Module.finrank K V := by
  have hr : Module.rank (𝓞 K) V = Module.rank K V :=
    (IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl).symm
  have : Module.rank (𝓞 K) M = Module.rank K V := by
    apply le_antisymm
    · rw [← hr]; exact Submodule.rank_le M
    · obtain ⟨s, hsM, hspan, hli⟩ := exists_linearIndependent K (M : Set V)
      rw [hM.span_eq_top] at hspan
      have h1 : Module.rank K V = Cardinal.mk s := by
        rw [← rank_top, ← hspan, rank_span_set hli]
      have h2 : LinearIndependent (𝓞 K) (fun x : s => (⟨x.1, hsM x.2⟩ : M)) := by
        apply LinearIndependent.of_comp M.subtype
        exact (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr hli
      rw [h1]
      exact h2.cardinal_le_rank
  simp only [Module.finrank, this]
end GlobalTheory.SublatCount
