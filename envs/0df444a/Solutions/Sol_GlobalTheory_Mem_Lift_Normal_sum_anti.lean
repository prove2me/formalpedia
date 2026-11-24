-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.Normal.sum_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:55.242484+00:00
-- url     : https://prove2.me/submissions/941be5ad-6bf8-45ca-9d17-120f5e089c5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfNormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.Normal
variable {ι : Type}
variable [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.Mem.Lift.Normal
theorem _root_.solution {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (hX : Xᴴ * H + H * X = 0)
    (A : (ι → ℂ) →ₗ⋆[ℂ] ℂ) (v : ι → ℂ) :
    ∑ k, ∑ j, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * A (H⁻¹ *ᵥ Pi.single j 1)) = - A (X *ᵥ v) := by
  have hinv' : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hd)
  set w := X *ᵥ v with hw

  have hexp : w = ∑ j, (H *ᵥ w) j • (H⁻¹ *ᵥ Pi.single j 1) := by
    have h1 : H *ᵥ w = ∑ j, (H *ᵥ w) j • (Pi.single j (1 : ℂ) : ι → ℂ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    calc w = H⁻¹ *ᵥ (H *ᵥ w) := by rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
      _ = H⁻¹ *ᵥ ∑ j, (H *ᵥ w) j • (Pi.single j (1 : ℂ) : ι → ℂ) := by rw [← h1]
      _ = _ := by
        rw [Matrix.mulVec_sum]
        simp only [Matrix.mulVec_smul]
  have hA : A w = ∑ j, (starRingEnd ℂ) ((H *ᵥ w) j) * A (H⁻¹ *ᵥ Pi.single j 1) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smulₛₗ, smul_eq_mul]

  have hcoef : ∀ j, ∑ k, X k j * (star v ⬝ᵥ H *ᵥ Pi.single k 1) = -(starRingEnd ℂ) ((H *ᵥ w) j) := by
    intro j
    have hs : ∀ k, star v ⬝ᵥ H *ᵥ Pi.single k 1 = (star v ᵥ* H) k := by
      intro k
      rw [Matrix.dotProduct_mulVec]
      simp [dotProduct, Pi.single_apply]
    have hXH : (H * X)ᴴ = -(H * X) := by
      rw [Matrix.conjTranspose_mul, hH]
      exact eq_neg_of_add_eq_zero_left hX
    have hstar : (starRingEnd ℂ) ((H *ᵥ w) j) = (star v ᵥ* (H * X)ᴴ) j := by
      rw [hw, Matrix.mulVec_mulVec, ← Matrix.star_mulVec]
      rfl
    simp_rw [hs]
    rw [hstar, hXH, Matrix.vecMul_neg, Pi.neg_apply, neg_neg, ← Matrix.vecMul_vecMul]
    simp [vecMul, dotProduct, mul_comm]
  rw [hA, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ k, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * A (H⁻¹ *ᵥ Pi.single j 1))
      = (∑ k, X k j * (star v ⬝ᵥ H *ᵥ Pi.single k 1)) * A (H⁻¹ *ᵥ Pi.single j 1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
        rw [hcoef j]
        ring
end GlobalTheory.Mem.Lift.Normal
