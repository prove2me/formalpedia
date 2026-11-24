-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Tri.aMat_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:35:08.641803+00:00
-- url     : https://prove2.me/submissions/69503f66-7d12-49c7-b0bc-4ec792c42611

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotentStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHermitianDiagonalizationUnitsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroup
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Tri
variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}
namespace GlobalTheory.CompanionTheory.SW.Tri
theorem _root_.solution (ι : R →+* K) (sig : K →+* K) (hs : ∀ r, sig (ι r) = ι r) {U : Subgroup Rˣ}
    (u : Fin n → U) (m : {p : Fin n × Fin n // p.1 < p.2} → K) (d : Fin n → Rˣ) :
    cT sig (aMat ι u m) * Matrix.diagonal (fun i => ι (d i : R)) * aMat ι u m
      = cT sig (nMat m) * Matrix.diagonal (fun i => ι ((((u i : Rˣ) ^ 2 * d i : Rˣ)) : R)) * nMat m := by
  have hd : cT sig (Matrix.diagonal (fun i => ι ((u i : Rˣ) : R))) = Matrix.diagonal (fun i => ι ((u i : Rˣ) : R)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [cT, hs]
    · simp [cT, Matrix.diagonal, h, Ne.symm h]
  have hm : Matrix.diagonal (fun i => ι ((u i : Rˣ) : R)) * Matrix.diagonal (fun i => ι (d i : R)) *
      Matrix.diagonal (fun i => ι ((u i : Rˣ) : R))
      = Matrix.diagonal (fun i => ι ((((u i : Rˣ) ^ 2 * d i : Rˣ)) : R)) := by
    simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    ring
  rw [aMat, cT_mul, hd, ← hm]
  simp only [Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.SW.Tri
