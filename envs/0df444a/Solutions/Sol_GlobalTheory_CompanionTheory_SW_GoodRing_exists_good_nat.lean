-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodRing.exists_good_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:06:48.111657+00:00
-- url     : https://prove2.me/submissions/30033659-aebb-4ced-89c2-9e55643d48ea

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
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
namespace GlobalTheory.CompanionTheory.SW.GoodRing
theorem _root_.solution {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (D A B C : k)
    (hne : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    ∃ a : ℕ, 1 - D * (a : k) ^ 2 ≠ 0 ∧ A + B * (a : k) + C * (a : k) ^ 2 ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hc : ∀ n : ℕ, 0 < n → n < 5 → (n : k) ≠ 0 := by
    intro n h0 h5
    interval_cases n
    · simp
    · simpa using h2
    · simpa using h3
    · have : ((4 : ℕ) : k) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
  have hinj : Function.Injective (fun i : Fin 5 => ((i : ℕ) : k)) := by
    have key : ∀ i j : ℕ, i < j → j < 5 → (i : k) ≠ j := by
      intro i j hij hj h
      apply hc (j - i) (by omega) (by omega)
      rw [Nat.cast_sub hij.le, h, sub_self]
    intro i j h
    simp only at h
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with hl | hl | hl
    · exact absurd h (key _ _ hl j.2)
    · exact Fin.ext hl
    · exact absurd h.symm (key _ _ hl i.2)
  let Q1 : Polynomial k := 1 - Polynomial.C D * Polynomial.X ^ 2
  let Q2 : Polynomial k :=
    Polynomial.C A + Polynomial.C B * Polynomial.X + Polynomial.C C * Polynomial.X ^ 2
  have hQ1 : Q1 ≠ 0 := by
    intro h
    have := congrArg (fun p => Polynomial.coeff p 0) h
    simp [Q1, Polynomial.coeff_one, Polynomial.coeff_X_pow] at this
  have hQ2 : Q2 ≠ 0 := by
    intro h
    have e0 := congrArg (fun p => Polynomial.coeff p 0) h
    have e1 := congrArg (fun p => Polynomial.coeff p 1) h
    have e2 := congrArg (fun p => Polynomial.coeff p 2) h
    simp [Q2, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] at e0 e1 e2
    rcases hne with h' | h' | h'
    · exact h' e0
    · exact h' e1
    · exact h' e2
  have hdeg : (Q1 * Q2).natDegree ≤ 4 := by
    simp only [Q1, Q2]
    compute_degree
  have hz : Q1 * Q2 = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj
    · intro i
      simp only [Polynomial.eval_mul]
      by_cases h : 1 - D * (((i : ℕ) : k)) ^ 2 = 0
      · have : Polynomial.eval (((i : ℕ) : k)) Q1 = 0 := by simpa [Q1] using h
        rw [this, zero_mul]
      · have := hcon i h
        have h' : Polynomial.eval (((i : ℕ) : k)) Q2 = 0 := by simpa [Q2] using this
        rw [h', mul_zero]
    · simpa using Nat.lt_succ_of_le hdeg
  exact (mul_ne_zero hQ1 hQ2) hz
end GlobalTheory.CompanionTheory.SW.GoodRing
