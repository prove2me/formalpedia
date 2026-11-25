-- Prove2me | solution 1 for GlobalTheory.Mass.DiscOrder.exists_covBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:43.135725+00:00
-- url     : https://prove2.me/submissions/c3f82408-57cf-4f7a-aaaa-0f4277c12714

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula

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
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace GlobalTheory.Mass.DiscOrder
theorem _root_.solution {X Y : Submodule R W} (hY : Y.FG) (h : X < Y) : ∃ Z, X ≤ Z ∧ Z ⋖ Y := by
  have := CompleteLattice.Iic_coatomic_of_compact_element ((Submodule.fg_iff_compact Y).1 hY)
  rcases eq_top_or_exists_le_coatom (⟨X, h.le⟩ : Set.Iic Y) with e | ⟨Z, hZ, hle⟩
  · exact absurd (congrArg Subtype.val e) h.ne
  · exact ⟨Z.1, hle, (covBy_iff_coatom_Iic Z.2).2 hZ⟩
end GlobalTheory.Mass.DiscOrder
