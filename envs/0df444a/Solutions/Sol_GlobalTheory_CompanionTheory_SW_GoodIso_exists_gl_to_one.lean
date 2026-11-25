-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodIso.exists_gl_to_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:25:22.81031+00:00
-- url     : https://prove2.me/submissions/abaa11ca-05b4-4720-afe5-7d6c4954d4e1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlacesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnitStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormsIntegrallyEquivalentAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_T_hermitian_unit_form_diagonalizes
import Theorems.Thm_GlobalTheory_T_hermitian_unit_form_represents_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
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
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodIso
namespace GlobalTheory.CompanionTheory.SW.GoodIso
theorem _root_.solution (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A)
    (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ)
    (hN : ∀ β : A, IsUnit β → σ β = β → ∃ a : A, a * σ a = β)
    (m : ℕ) (J : Matrix (Fin m) (Fin m) A) (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det) :
    ∃ h : GL (Fin m) A,
      cT σ (h : Matrix (Fin m) (Fin m) A) * J * (h : Matrix (Fin m) (Fin m) A) = 1 := by
  obtain ⟨g, d, hg, hdd, hgJ⟩ := GlobalTheory.T.hermitian_unit_form_diagonalizes A σ hσ
    (fun m J hJ hu => GlobalTheory.T.hermitian_unit_form_represents_unit A σ hσ h2 hδ m J hJ hu) m J hJ hd
  choose a ha using fun i => hN (d i) (hdd i).1 (hdd i).2
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_left (y := σ (a i)) (by rw [ha i]; exact (hdd i).1)
  choose c hc using fun i => (hau i).exists_right_inv
  have hcu : ∀ i, IsUnit (c i) := fun i => IsUnit.of_mul_eq_one (a i) (by rw [mul_comm]; exact hc i)
  have hdet : IsUnit (g * Matrix.diagonal c).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact hg.mul (IsUnit.prod_univ_iff.2 hcu)
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, ?_⟩
  rw [IsUnit.unit_spec, cT_mul]
  have hD : cT σ (Matrix.diagonal c) = Matrix.diagonal (fun i => σ (c i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [cT]
    · simp [cT, Matrix.diagonal_apply, hij, Ne.symm hij]
  calc cT σ (Matrix.diagonal c) * cT σ g * J * (g * Matrix.diagonal c)
      = cT σ (Matrix.diagonal c) * (cT σ g * J * g) * Matrix.diagonal c := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hgJ, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        have h1 : σ (c i) * σ (a i) = 1 := by rw [← map_mul, mul_comm, hc i, map_one]
        rw [← ha i]
        calc σ (c i) * (a i * σ (a i)) * c i = (σ (c i) * σ (a i)) * (a i * c i) := by ring
          _ = 1 := by rw [h1, hc i, one_mul]
end GlobalTheory.CompanionTheory.SW.GoodIso
