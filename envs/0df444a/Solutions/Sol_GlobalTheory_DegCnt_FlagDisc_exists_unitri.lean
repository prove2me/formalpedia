-- Prove2me | solution 1 for GlobalTheory.DegCnt.FlagDisc.exists_unitri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:26:02.649944+00:00
-- url     : https://prove2.me/submissions/78fbc957-af8a-423f-882a-f1205ac56847

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsSmulMemOfMemSpanLattice
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinor
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_DegCnt_Absorb_exists_coord
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
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FlagDisc
open GlobalTheory.DegCnt.DelScale GlobalTheory.DegCnt.Absorb
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.FlagDisc
theorem _root_.solution (F : FlagD H r) (y : Fin r → V) (he : ∀ a, F.e a.castSucc - y a ∈ F.Xa a.val) {l : ℕ}
    (hr : l ≤ r) (hl : l ≤ r + 1) : ∃ M : Matrix (Fin l) (Fin l) K, M.det = 1 ∧
      ∀ a, y (Fin.castLE hr a) = ∑ b, M a b • F.e (Fin.castLE hl b) := by
  choose m h1 h2 using fun a : Fin l => exists_coord F hl a (he (Fin.castLE hr a))
  refine ⟨1 - Matrix.of m, ?_, fun a => ?_⟩
  · rw [Matrix.det_of_lowerTriangular (1 - Matrix.of m) (fun a b hab => ?_)]
    · simp [fun a => h1 a a le_rfl]
    · have hab : a < b := hab
      simp [h1 a b hab.le, Matrix.one_apply_ne hab.ne]
  · simp only [Matrix.sub_apply, Matrix.of_apply, sub_smul, Finset.sum_sub_distrib, ← h2 a, Matrix.one_apply,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact (sub_sub_cancel _ _).symm
end GlobalTheory.DegCnt.FlagDisc
