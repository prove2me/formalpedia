-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_mulVec_packetMap_eq_truncatedFormalJet
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:43:32.289182+00:00
-- url     : https://prove2.me/submissions/20f7fc82-86d7-45cc-a2f6-a337d5a94d24

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_coeff_eq_finite_sum
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_subst_logTail_formalJet_eq_truncatedFormalJet

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0)
    (P : WeightedPolynomial w0 w H) :
    (finitePacketShearMatrix K
        (strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) H)
        (fun i => (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
          PowerSeries.log ℂ)).mulVecLin
        (packetMap K w0 v0 theta w H r P) =
      (fun rho : InterpolationMatrix.Row K v0 theta w H =>
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
          (truncatedFormalJet T (fun i => (rho.1.val : ℂ) * r i) P.val)) := by
  classical
  let delta : Fin m → PowerSeries ℂ := fun i =>
    (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) - PowerSeries.log ℂ
  have hdelta : ∀ i (n : ℕ), n < T i → PowerSeries.coeff n (delta i) = 0 := by
    intro i n hn
    dsimp only [delta, InterpolationMatrix.truncatedLog]
    rw [map_sub, PowerSeries.coeff_coe_trunc_of_lt hn, sub_self]
  funext rho
  have hlocal := weightedShear_coeff_eq_finite_sum
    v0 (fun i => w i / theta) H T delta hv0
    (fun i => div_pos (hw i) htheta) hT hdelta
    (formalJet (fun i => (rho.1.val : ℂ) * r i) P.val) rho.2
  have hjet :
      MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
            (fun i : Fin m =>
              MvPowerSeries.X i.succ + liftLogSeries m (delta i)))
          (formalJet (fun i => (rho.1.val : ℂ) * r i) P.val) =
        truncatedFormalJet T (fun i => (rho.1.val : ℂ) * r i) P.val := by
    exact subst_logTail_formalJet_eq_truncatedFormalJet T
      (fun i => (rho.1.val : ℂ) * r i) P.val
  calc
    (finitePacketShearMatrix K
        (strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) H)
        delta).mulVecLin (packetMap K w0 v0 theta w H r P) rho =
        ∑ b : ↥(strictWeightedSimplex
            (InterpolationMatrix.rowWeights v0 theta w) H),
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
              (formalShear delta
                (MvPolynomial.monomial (InterpolationMatrix.exponentVector b.val) 1)) *
            MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
              (formalJet (fun i => (rho.1.val : ℂ) * r i) P.val) := by
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        finitePacketShearMatrix, packetMap, Fintype.sum_prod_type_right, ite_mul]
    _ = MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
        (MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
            (fun i : Fin m =>
              MvPowerSeries.X i.succ + liftLogSeries m (delta i)))
          (formalJet (fun i => (rho.1.val : ℂ) * r i) P.val)) := hlocal.symm
    _ = MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
        (truncatedFormalJet T (fun i => (rho.1.val : ℂ) * r i) P.val) :=
      congrArg (MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)) hjet