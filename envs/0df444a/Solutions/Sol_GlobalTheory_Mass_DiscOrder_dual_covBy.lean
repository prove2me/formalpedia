-- Prove2me | solution 1 for GlobalTheory.Mass.DiscOrder.dual_covBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:26.380778+00:00
-- url     : https://prove2.me/submissions/12b6ff4f-d974-49d2-b8af-25e7beede628

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_lattice_between
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualLattice


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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn
namespace GlobalTheory.Mass.DiscOrder
theorem _root_.solution {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X)
    (hY : Submodule.IsLattice K Y) (hc : X ⋖ Y) : dual h Y ⋖ dual h X := by
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  have an := (dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).1
  refine ⟨lt_of_le_of_ne (an _ _ hc.le) fun e => hc.ne ?_, fun Z h1 h2 => ?_⟩
  · rw [← (dl X hX).2.1, ← e, (dl Y hY).2.1]
  · have hZ := lattice_between (dl Y hY).1 (dl X hX).1 h1.le h2.le
    have a1 := an _ _ h1.le
    have a2 := an _ _ h2.le
    rw [(dl Y hY).2.1] at a1
    rw [(dl X hX).2.1] at a2
    rcases hc.eq_or_eq a2 a1 with e | e
    · exact h2.ne (by rw [← e, (dl Z hZ).2.1])
    · exact h1.ne (by rw [← e, (dl Z hZ).2.1])
end GlobalTheory.Mass.DiscOrder
