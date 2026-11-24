-- Prove2me | solution 1 for GlobalTheory.QuadFieldCriterion.isField_iff_no_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:01.147012+00:00
-- url     : https://prove2.me/submissions/47c87f3e-5ca5-487e-a448-b31f4e923b00

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldIffNoResidualRoot
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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.QuadFieldCriterion
open Polynomial IsLocalRing
namespace GlobalTheory.QuadFieldCriterion
theorem _root_.solution {K A : Type*} [Field K] [CommRing A] [Algebra K A] (w : A) (t n : K)
    (hw : w ^ 2 - algebraMap K A t * w + algebraMap K A n = 0)
    (hspan : ∀ z : A, ∃ a b : K, z = algebraMap K A a + algebraMap K A b * w)
    (hind : ∀ a b : K, algebraMap K A a + algebraMap K A b * w = 0 → a = 0 ∧ b = 0) :
    IsField A ↔ ¬ ∃ x : K, x ^ 2 - t * x + n = 0 := by
  constructor
  · rintro hF ⟨x, hx⟩
    letI := hF.toField
    have hx' : algebraMap K A x ^ 2 - algebraMap K A t * algebraMap K A x + algebraMap K A n = 0 := by
      simpa using congrArg (algebraMap K A) hx
    have hprod : (algebraMap K A (-x) + algebraMap K A 1 * w) *
        (algebraMap K A (x - t) + algebraMap K A 1 * w) = 0 := by
      simp only [map_neg, map_sub, map_one]
      linear_combination hw - hx'
    rcases mul_eq_zero.mp hprod with h | h
    · exact one_ne_zero (hind _ _ h).2
    · exact one_ne_zero (hind _ _ h).2
  · intro hno
    refine ⟨⟨1, 0, fun h => one_ne_zero (hind 1 0 (by simpa using h)).1⟩, mul_comm, ?_⟩
    intro z hz
    obtain ⟨a, b, rfl⟩ := hspan z
    have hN : a ^ 2 + t * a * b + n * b ^ 2 ≠ 0 := by
      intro hN
      by_cases hb : b = 0
      · subst hb
        have : a = 0 := by simpa using hN
        subst this
        simp at hz
      · exact hno ⟨-a / b, by field_simp; linear_combination hN⟩
    refine ⟨algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2)⁻¹ *
      (algebraMap K A a + algebraMap K A b * (algebraMap K A t - w)), ?_⟩
    have h1 : algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2)⁻¹ *
        algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hN, map_one]
    rw [← h1]
    simp only [map_add, map_mul, map_pow]
    linear_combination (- algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2)⁻¹ *
      algebraMap K A b ^ 2) * hw
end GlobalTheory.QuadFieldCriterion
