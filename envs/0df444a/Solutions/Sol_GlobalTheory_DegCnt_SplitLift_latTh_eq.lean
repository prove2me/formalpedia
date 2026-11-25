-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitLift.latTh_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:30:30.759122+00:00
-- url     : https://prove2.me/submissions/264c4f09-ef1f-4c21-9649-2abe2aa9eed9

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairExistsUnipotentSplitLattice
import Theorems.Thm_GlobalTheory_DegCnt_SplitLift_hermFlagPair_isotropic_sup_le_commonSpace
import Theorems.Thm_GlobalTheory_DegCnt_SplitLift_isotropicMeet_le_jointSpan
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_isotropicMeet_le_jointSpan
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.SplitLift
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.SplitLift
theorem _root_.solution (F F' : FlagD H r) (hI : II F F' ≤ wSp F F') (Λ : Submodule (𝓞 K) V) :
    latTh F F' Λ = (Λ ⊓ rs (𝓞 K) (wSp F F')) ⊔ rs (𝓞 K) (II F F') := by
  have hu : ∀ y ∈ wSp F F', y ∈ uPerp F F' := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (hermFlagPair_isotropic_sup_le_commonSpace F F' hx)
  have hp : ∀ y ∈ wSp F F', y ∈ perp H (II F F') := fun y hy =>
    (mem_perp_iff H _ y).2 fun x hx => (mem_perp_iff H _ y).1 hy x (isotropicMeet_le_jointSpan F F' hx)
  apply le_antisymm
  · rintro y ⟨⟨hy1, -⟩, hy3⟩
    obtain ⟨l, ⟨hl, -⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hy1
    refine Submodule.mem_sup.2 ⟨l, ⟨hl, ?_⟩, x, hx, rfl⟩
    have : l + x - x ∈ wSp F F' := sub_mem hy3 (hI hx)
    simpa using this
  · refine sup_le ?_ ?_
    · rintro l ⟨hl, hw⟩
      exact ⟨⟨Submodule.mem_sup_left ⟨hl, hp l hw⟩, hu l hw⟩, hw⟩
    · intro x hx
      exact ⟨⟨Submodule.mem_sup_right hx, hu x (hI hx)⟩, hI hx⟩
end GlobalTheory.DegCnt.SplitLift
