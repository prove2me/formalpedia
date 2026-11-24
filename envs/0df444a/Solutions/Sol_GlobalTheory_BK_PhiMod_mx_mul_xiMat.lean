-- Prove2me | solution 1 for GlobalTheory.BK.PhiMod.mx_mul_xiMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:01:59.573891+00:00
-- url     : https://prove2.me/submissions/908b92d3-9f9f-4065-945b-f3adccc6a7df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
namespace GlobalTheory.BK.PhiMod
theorem _root_.solution (τ : ZMod a) :
    P.mx τ * (P.xiMat (τ - 1)).map (frob K l) = P.xiMat τ * (P.mx0 τ).map C := by
  have h : P.mx τ * (P.xiMat (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C =
      P.xiMat τ := by
    ext i j n
    have h1 : (X : K⟦X⟧) ^ (n + 2) ∣ (P.mx τ * (P.xiMat (τ - 1)).map (frob K l) *
        ((P.mxInv τ).map constantCoeff).map C) i j - P.xiSeq (n + 1) τ i j := by
      rw [← Matrix.sub_apply, xiSeq_succ, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_apply]
      refine Finset.dvd_sum fun k _ => Dvd.dvd.mul_right ?_ _
      rw [Matrix.mul_apply]
      refine Finset.dvd_sum fun m _ => Dvd.dvd.mul_left ?_ _
      rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub]
      exact X_pow_dvd_frob l (P.xiMat_sub_dvd n (τ - 1) m k)
    have h2 := X_pow_dvd_iff.1 (dvd_sub h1 (P.xiMat_sub_dvd (n + 1) τ i j)) n (by omega)
    rwa [sub_sub_sub_cancel_right, map_sub, sub_eq_zero] at h2
  rw [← h, Matrix.mul_assoc _ _ ((P.mx0 τ).map C), ← Matrix.map_mul, inv_const_mul_matrix_eq_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
end GlobalTheory.BK.PhiMod
