-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitIdx.iso_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:31:43.482801+00:00
-- url     : https://prove2.me/submissions/9aa88134-5ac8-4bf7-ab65-d1c076b6b207

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormTerminalDeterminant

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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.SplitIdx
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder GlobalTheory.DegCnt.DelScale
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.SplitIdx
theorem _root_.solution (F : FlagD H r) {x y : V} (hx : x ∈ F.X) (hy : y ∈ F.X ⊔ Submodule.span K {F.z}) :
    H.B y x = 0 := by
  have h1 : ∀ a : Fin r, ∀ y ∈ F.X ⊔ Submodule.span K {F.z}, H.B y (F.e a.castSucc) = 0 := by
    intro a y hy
    have : F.X ⊔ Submodule.span K {F.z} ≤ LinearMap.ker (H.B.flip (F.e a.castSucc)) := by
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨b, -, rfl⟩
        exact F.iso b a
      · rintro _ rfl
        change H.B F.z _ = 0
        rw [← H.herm, FlagD.z, F.zperp, star_zero]
    exact this hy
  have : F.X ≤ LinearMap.ker (H.B y) := Submodule.span_le.2 (by
    rintro _ ⟨b, -, rfl⟩
    exact h1 b y hy)
  exact this hx
end GlobalTheory.DegCnt.SplitIdx
