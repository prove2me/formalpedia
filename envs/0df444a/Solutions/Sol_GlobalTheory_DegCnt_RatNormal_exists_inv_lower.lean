-- Prove2me | solution 1 for GlobalTheory.DegCnt.RatNormal.exists_inv_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:23.591327+00:00
-- url     : https://prove2.me/submissions/267bad97-2b25-485d-9dbb-e2ae916df937

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsInvLower
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.HermitianLatticeCounting.P
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.RatNormal
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
omit [StarRing K]
namespace GlobalTheory.DegCnt.RatNormal
theorem _root_.solution {j : ℕ} (A : Matrix (Fin j) (Fin j) K) (h0 : ∀ a b, a < b → A a b = 0)
    (h1 : ∀ a, A a a = 1) :
    ∃ M : Matrix (Fin j) (Fin j) K, M * A = 1 ∧ (∀ a b, a < b → M a b = 0) ∧ ∀ a, M a a = 1 := by
  have hT : A.BlockTriangular OrderDual.toDual := fun a b hab => h0 a b hab
  have hd : A.det = 1 := by rw [Matrix.det_of_lowerTriangular A hT]; simp [h1]
  have hu : IsUnit A.det := by rw [hd]; exact isUnit_one
  letI := A.invertibleOfIsUnitDet hu
  have hM := Matrix.blockTriangular_inv_of_blockTriangular hT
  have hM0 : ∀ a b, a < b → A⁻¹ a b = 0 := fun a b hab => hM hab
  have hI := Matrix.nonsing_inv_mul A hu
  refine ⟨A⁻¹, hI, hM0, fun a => ?_⟩
  have h := congrFun (congrFun hI a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, h1, mul_one, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with hb | hb
    · rw [h0 b a hb, mul_zero]
    · rw [hM0 a b hb, zero_mul]
  · simp
end GlobalTheory.DegCnt.RatNormal
