-- Prove2me | solution 1 for GlobalTheory.minor_smul_eq_rowSpace_of_cofVec_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:02:56.411881+00:00
-- url     : https://prove2.me/submissions/2d4f62ce-d095-41e9-8303-aaba4a99498d

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MinorSmulEqRowSpaceOfCofVecOrth
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HermitianLatticeCounting_Final_LatticeSumBounds_kernelRowSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K V : Type) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (r : ℕ)
    (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (b₀ : Fin (r + 1)) (u : Fin (r + 1) → V)
    (hu : ∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec Y b • u b = 0) (b : Fin (r + 1)) :
    (Y.submatrix id b₀.succAbove).det • u b =
      ∑ a, Y a b • ∑ c, (Y.submatrix id b₀.succAbove).adjugate c a • u (b₀.succAbove c) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  have hφ : ∀ (x : 𝓞 K) (v : V), φ (x • v) = algebraMap (𝓞 K) K x * φ v := by
    intro x v
    rw [← algebraMap_smul K x v, map_smul, smul_eq_mul]
  have hsub : ∀ b' : Fin (r + 1), (Y.map (algebraMap (𝓞 K) K)).submatrix id b'.succAbove
      = (algebraMap (𝓞 K) K).mapMatrix (Y.submatrix id b'.succAbove) := by
    intro b'; ext i j; simp
  have h0 : ∑ b, φ (u b) * Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec (Y.map (algebraMap (𝓞 K) K)) b = 0 := by
    have := congrArg φ hu
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [hφ, mul_comm]
    congr 1
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec
    rw [hsub, ← RingHom.map_det, map_mul, map_pow, map_neg, map_one]
  have h := congrFun ((Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.kernelRowSpace K r (Y.map (algebraMap (𝓞 K) K))).2
    (fun b => φ (u b)) h0 b₀) b
  rw [hsub, ← RingHom.map_det, ← RingHom.map_adjugate] at h
  rw [map_sub, sub_eq_zero, hφ, map_sum]
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  simp only [Matrix.vecMul, dotProduct, hφ, map_sum, RingHom.mapMatrix_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]
end GlobalTheory
