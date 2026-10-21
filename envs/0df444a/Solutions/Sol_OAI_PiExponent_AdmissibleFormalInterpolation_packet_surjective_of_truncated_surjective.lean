-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.packet_surjective_of_truncated_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:31:49.977234+00:00
-- url     : https://prove2.me/submissions/f14cd7e9-8c2e-4b30-a359-d1b9f1db1340

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_WeightedSeriesJets
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weighted_series_jet_equiv_of_coeff_agreement
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_matrix_mulVec_weightedSeriesJet

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0) :
    Function.Surjective
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin →
      Function.Surjective (packetMap K w0 v0 theta w H r) := by
  classical
  let G : Fin m → Polynomial ℂ := fun i => InterpolationMatrix.truncatedLog (T i)
  obtain ⟨E, hE⟩ := weighted_series_jet_equiv_of_coeff_agreement
    v0 (fun i => w i / theta) H T (fun _ => PowerSeries.log ℂ)
    (fun i => (G i : PowerSeries ℂ)) hv0
    (fun i => div_pos (hw i) htheta) hT (by
      intro i n hn
      simpa only [G, InterpolationMatrix.truncatedLog] using
        (PowerSeries.coeff_coe_trunc_of_lt
          (f := PowerSeries.log ℂ) hn).symm)
  intro hsurj y
  let z : InterpolationMatrix.Row K v0 theta w H → ℂ :=
    fun rho => E.symm (fun b => y (rho.1, b)) rho.2
  obtain ⟨x, hx⟩ := hsurj z
  have hx' : (InterpolationMatrix.matrix K w0 v0 theta w H r G).mulVecLin x = z := by
    simpa only [InterpolationMatrix.truncatedLogMatrix, G] using hx
  obtain ⟨P, hP⟩ := matrix_mulVec_weightedSeriesJet K w0 v0 theta w H r G x
  refine ⟨P, ?_⟩
  funext rho
  have hslice :
      weightedSeriesJet v0 (fun i => w i / theta) H
        (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ)) P.val =
      E.symm (fun b => y (rho.1, b)) := by
    funext b
    calc
      weightedSeriesJet v0 (fun i => w i / theta) H
          (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ)) P.val b =
          ((InterpolationMatrix.matrix K w0 v0 theta w H r G).mulVecLin x) (rho.1, b) :=
        hP (rho.1, b)
      _ = z (rho.1, b) := congrFun hx' (rho.1, b)
      _ = E.symm (fun a => y (rho.1, a)) b := rfl
  calc
    packetMap K w0 v0 theta w H r P rho =
        weightedSeriesJet v0 (fun i => w i / theta) H
          (fun i => (rho.1.val : ℂ) * r i) (fun _ => PowerSeries.log ℂ) P.val rho.2 := rfl
    _ = E (weightedSeriesJet v0 (fun i => w i / theta) H
          (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ)) P.val) rho.2 :=
      (congrFun (hE (fun i => (rho.1.val : ℂ) * r i) P.val) rho.2).symm
    _ = E (E.symm (fun b => y (rho.1, b))) rho.2 :=
      congrArg (fun f => E f rho.2) hslice
    _ = y rho := by rw [E.apply_symm_apply]