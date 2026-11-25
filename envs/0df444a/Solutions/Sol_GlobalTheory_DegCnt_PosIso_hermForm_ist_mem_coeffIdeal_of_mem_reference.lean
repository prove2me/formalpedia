-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.hermForm_ist_mem_coeffIdeal_of_mem_reference
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:51.405192+00:00
-- url     : https://prove2.me/submissions/5a0ff975-0156-4118-831f-ff2f40d8ff67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (N : NF H r) (b : Fin r) (hb : N.j ≤ b.val) {y : V} (hy : y ∈ N.P0) :
    H.B y (N.ist b) ∈ N.aa b := by
  have : N.P0 ≤ (N.aa b).comap ((H.B.flip (N.ist b)).restrictScalars (𝓞 K)) := by
    refine sup_le (sup_le (sup_le (iSup_le fun a => ?_) (iSup₂_le fun a ha => ?_)) ?_) (iSup₂_le fun a ha => ?_)
    all_goals
      rintro _ ⟨t, ht, rfl⟩
      show H.B (t • _) (N.ist b) ∈ N.aa b
      rw [map_smul, LinearMap.smul_apply]
    · rw [N.ist_e a b hb]
      split_ifs with h
      · subst h; simpa using ht
      · simp
    · simp [N.ist_e' a b ha hb]
    · simp [N.normalForm_dual_orthogonal_last b hb]
    · simp [N.ist_iso a b ha hb]
  exact this hy
end GlobalTheory.DegCnt.PosIso
