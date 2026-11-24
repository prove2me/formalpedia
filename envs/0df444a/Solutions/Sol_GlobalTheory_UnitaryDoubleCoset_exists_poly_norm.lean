-- Prove2me | solution 1 for GlobalTheory.UnitaryDoubleCoset.exists_poly_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:20.594517+00:00
-- url     : https://prove2.me/submissions/f6228e68-6838-432b-9e02-d42630f1d35c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqXModMonicOfAdicCompleteInvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_add
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
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
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


section
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.UnitaryDoubleCoset
section Abstract
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
open IsDedekindDomain NumberField in
open scoped TensorProduct Matrix in
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n] in
private theorem cT_aeval_eq_aeval_cT_map (c : O →+* O) (B : Matrix n n O) (q : Polynomial O) :
    _root_.Formalism.UG.cT c (Polynomial.aeval B q) = Polynomial.aeval (_root_.Formalism.UG.cT c B) (q.map c) := by
  induction q using Polynomial.induction_on with
  | C a =>
    ext i j
    by_cases hij : i = j
    · subst hij; simp [_root_.Formalism.UG.cT, Polynomial.aeval_C, Matrix.algebraMap_matrix_apply]
    · simp [_root_.Formalism.UG.cT, Polynomial.aeval_C, Matrix.algebraMap_matrix_apply, hij, Ne.symm hij]
  | add p q hp hq =>
    simp only [map_add, Polynomial.map_add, ← hp, ← hq]
    simp [_root_.Formalism.UG.cT, Matrix.map_add, Matrix.transpose_add]
  | monomial m a hm =>
    rw [pow_succ, ← mul_assoc, mul_comm _ Polynomial.X, Polynomial.map_mul,
      map_mul (Polynomial.aeval B) Polynomial.X, map_mul (Polynomial.aeval (_root_.Formalism.UG.cT c B)), ← hm,
      Polynomial.map_X, Polynomial.aeval_X, Polynomial.aeval_X]
    have hcomm : Polynomial.aeval B (Polynomial.C a * Polynomial.X ^ m) * B =
        B * Polynomial.aeval B (Polynomial.C a * Polynomial.X ^ m) := by
      have := congrArg (Polynomial.aeval B) (mul_comm (Polynomial.C a * Polynomial.X ^ m) Polynomial.X)
      simpa only [map_mul, Polynomial.aeval_X] using this
    simp only [_root_.Formalism.UG.cT, ← Matrix.transpose_mul, ← Matrix.map_mul, hcomm]
end Abstract
end GlobalTheory.UnitaryDoubleCoset
end
end

set_option autoImplicit false
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitaryDoubleCoset
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
open IsDedekindDomain NumberField
open scoped TensorProduct Matrix
variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.UnitaryDoubleCoset
namespace _root_.GlobalTheory.UnitaryDoubleCoset
theorem _root_.solution {c : O →+* O} (hc : ∀ x, c (c x) = x)
    (hN : ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) →
      ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X)
    {B : Matrix n n O} (hB : _root_.Formalism.UG.cT c B = B) (hu : IsUnit B) :
    ∃ p : Polynomial O, _root_.Formalism.UG.cT c (Polynomial.aeval B p) * Polynomial.aeval B p = B := by
  have hmap : B.charpoly.map c = B.charpoly := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_transpose]
    conv_rhs => rw [← hB]
    rfl
  have hunit : IsUnit (B.charpoly.coeff 0) := by
    have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hu
    rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  obtain ⟨p, q, hpq⟩ := hN B.charpoly (Matrix.charpoly_monic B) hmap hunit
  refine ⟨p, ?_⟩
  have h1 := congrArg (Polynomial.aeval B) hpq
  rw [map_mul, Matrix.aeval_self_charpoly, zero_mul, map_sub, Polynomial.aeval_X, sub_eq_zero] at h1
  rw [cT_aeval_eq_aeval_cT_map, hB, ← map_mul, mul_comm, h1]
end _root_.GlobalTheory.UnitaryDoubleCoset
end GlobalTheory.UnitaryDoubleCoset
