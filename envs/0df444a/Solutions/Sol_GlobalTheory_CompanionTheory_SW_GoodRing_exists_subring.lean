-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodRing.exists_subring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:28:57.441796+00:00
-- url     : https://prove2.me/submissions/7c0eaa94-5a12-4220-b396-4260244ca84c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_coord_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_coord_two
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_eq_coord
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodRing
variable {K A : Type} [Field K] [CommRing A] [Algebra K A] (R : Subring K)
namespace GlobalTheory.CompanionTheory.SW.GoodRing
theorem _root_.solution {d : ℕ} (B : Module.Basis (Fin 2) K A) (C : Module.Basis (Fin d) K A)
    (D : K) (hB0 : B 0 = 1) (hD : B 1 * B 1 = algebraMap K A D) (hDR : D ∈ R)
    (hBC : ∀ k j, B.repr (C k) j ∈ R) (hCB : ∀ j k, C.repr (B j) k ∈ R) :
    ∃ O : Subring A, (∀ y, y ∈ O ↔ ∀ k, C.repr y k ∈ R) ∧ (∀ y, y ∈ O ↔ ∀ j, B.repr y j ∈ R) := by
  let O : Subring A :=
    { carrier := {y | ∀ j, B.repr y j ∈ R}
      zero_mem' := by intro j; simp [R.zero_mem]
      one_mem' := by
        have h := coord_two B hB0 1 0
        simp only [map_one, map_zero, zero_mul, add_zero] at h
        show ∀ j, B.repr 1 j ∈ R
        refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
        · rw [h.1]; exact R.one_mem
        · rw [h.2]; exact R.zero_mem
      add_mem' := by
        intro a b ha hb j
        rw [map_add, Finsupp.add_apply]
        exact R.add_mem (ha j) (hb j)
      neg_mem' := by
        intro a ha j
        rw [map_neg, Finsupp.neg_apply]
        exact R.neg_mem (ha j)
      mul_mem' := by
        intro a b ha hb j
        have e : a * b = algebraMap K A (B.repr a 0 * B.repr b 0 + B.repr a 1 * B.repr b 1 * D) +
            algebraMap K A (B.repr a 0 * B.repr b 1 + B.repr a 1 * B.repr b 0) * B 1 := by
          conv_lhs => rw [eq_coord B hB0 a, eq_coord B hB0 b]
          simp only [map_add, map_mul]
          linear_combination (algebraMap K A (B.repr a 1) * algebraMap K A (B.repr b 1)) * hD
        have h := coord_two B hB0
          (B.repr a 0 * B.repr b 0 + B.repr a 1 * B.repr b 1 * D)
          (B.repr a 0 * B.repr b 1 + B.repr a 1 * B.repr b 0)
        rw [← e] at h
        fin_cases j
        · show B.repr (a * b) 0 ∈ R
          rw [h.1]
          exact R.add_mem (R.mul_mem (ha 0) (hb 0)) (R.mul_mem (R.mul_mem (ha 1) (hb 1)) hDR)
        · show B.repr (a * b) 1 ∈ R
          rw [h.2]
          exact R.add_mem (R.mul_mem (ha 0) (hb 1)) (R.mul_mem (ha 1) (hb 0)) }
  refine ⟨O, fun y => ⟨fun hy k => coord_mem R B C hCB y hy k,
    fun hy j => coord_mem R C B hBC y hy j⟩, fun y => Iff.rfl⟩
end GlobalTheory.CompanionTheory.SW.GoodRing
