-- Prove2me | solution 1 for GlobalTheory.Mass.finrank_le_of_span_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:41:08.160012+00:00
-- url     : https://prove2.me/submissions/171bbeb1-8d70-48b8-a011-a3b6a2c28b3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardShortVectorsLe
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass
namespace GlobalTheory.Mass
theorem _root_.solution {K V E : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup E] [Module ℝ E] (ι : V →+ E)
    (hs : Submodule.span ℝ (Set.range ι) = ⊤) :
    Module.finrank ℝ E ≤ Module.finrank ℚ K * Module.finrank K V := by
  classical
  let bV := Module.finBasis K V
  let bK := Module.finBasis ℚ K
  let g : Fin (Module.finrank ℚ K) × Fin (Module.finrank K V) → E := fun p => ι (bK p.1 • bV p.2)
  have hsub : Set.range ι ⊆ Submodule.span ℝ (Set.range g) := by
    rintro _ ⟨v, rfl⟩
    rw [← bV.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← bK.sum_repr (bV.repr v j), Finset.sum_smul, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Rat.smul_def, mul_smul, map_ratCast_smul ι K ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hEq : Submodule.span ℝ (Set.range g) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hs]
    exact Submodule.span_le.mpr hsub
  have hc := finrank_range_le_card (R := ℝ) g
  rw [Set.finrank, hEq, finrank_top] at hc
  simpa [Fintype.card_prod] using hc
end GlobalTheory.Mass
