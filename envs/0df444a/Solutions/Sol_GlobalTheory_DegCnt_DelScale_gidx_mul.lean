-- Prove2me | solution 1 for GlobalTheory.DegCnt.DelScale.gidx_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:31:52.640962+00:00
-- url     : https://prove2.me/submissions/6706c1c3-40f7-4140-a481-e045fda0aa78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_gidx_of_ge
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.DelScale
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [FiniteDimensional K V]
namespace GlobalTheory.DegCnt.DelScale
theorem _root_.solution {A B C : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B)
    (hC : Submodule.IsLattice K C) : gidx A B * gidx B C = gidx A C := by
  have hL : (A ⊔ B ⊔ C).FG := (hA.fg.sup hB.fg).sup hC.fg
  have a : A ≤ A ⊔ B ⊔ C := le_sup_of_le_left le_sup_left
  have b : B ≤ A ⊔ B ⊔ C := le_sup_of_le_left le_sup_right
  have c : C ≤ A ⊔ B ⊔ C := le_sup_right
  have a0 : idx (A ⊔ B ⊔ C) A ≠ 0 := idxN_ne_zero hA hL
  have b0 : idx (A ⊔ B ⊔ C) B ≠ 0 := idxN_ne_zero hB hL
  rw [gidx_of_ge a b a0 (idxN_ne_zero hA hB.fg), gidx_of_ge b c b0 (idxN_ne_zero hB hC.fg),
    gidx_of_ge a c a0 (idxN_ne_zero hA hC.fg)]
  have : (idx (A ⊔ B ⊔ C) B : ℝ) ≠ 0 := by exact_mod_cast b0
  have : (idx (A ⊔ B ⊔ C) A : ℝ) ≠ 0 := by exact_mod_cast a0
  field_simp
end GlobalTheory.DegCnt.DelScale
