-- Prove2me | solution 1 for GlobalTheory.UnitriJac.deriv_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:53.317915+00:00
-- url     : https://prove2.me/submissions/06e9a333-8949-4360-a297-1b7e7c4e217a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DifferentiableAtAdjugate
import Theorems.Thm_GlobalTheory_UnitriJac_differentiableAt_adjugate
import Theorems.Thm_GlobalTheory_UnitriJac_hasDerivAt_mul
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
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.UnitriJac
open ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
noncomputable section
namespace GlobalTheory.UnitriJac
theorem _root_.solution {r : ℕ} {N M b : ℂ → Matrix (Fin r) (Fin r) ℂ} {g N' M' : Matrix (Fin r) (Fin r) ℂ}
    (hN : ∀ i j, HasDerivAt (fun s => N s i j) (N' i j) 0)
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) 0)
    (hMd : ∀ s, (M s).det = 1) (hNd : (N 0).det = 1) (hbd : (b 0).det ≠ 0)
    (h : ∀ᶠ s in 𝓝 (0 : ℂ), g * N s = M s * b s ∧ ∀ a c : Fin r, c < a → b s a c = 0)
    (a c : Fin r) (hca : c < a) :
    ((M 0)⁻¹ * M') a c = (b 0 * ((N 0)⁻¹ * N') * (b 0)⁻¹) a c := by
  have hgN : ∀ i j, HasDerivAt (fun s => (g * N s) i j) ((g * N') i j) 0 := by
    intro i j
    have := hasDerivAt_mul (A := fun _ => g) (A' := 0) (fun i j => hasDerivAt_const _ _) hN i j
    simpa using this
  have hbe : ∀ i j, (fun s => b s i j) =ᶠ[𝓝 0] fun s => ((M s).adjugate * (g * N s)) i j := by
    intro i j
    filter_upwards [h] with s hs
    rw [hs.1, ← Matrix.mul_assoc, Matrix.adjugate_mul, hMd, one_smul, Matrix.one_mul]
  have hbdiff : ∀ i j, DifferentiableAt ℂ (fun s => b s i j) 0 := by
    intro i j
    refine DifferentiableAt.congr_of_eventuallyEq ?_ (hbe i j)
    exact (hasDerivAt_mul (A := fun s => (M s).adjugate)
      (A' := Matrix.of fun i j => deriv (fun s => (M s).adjugate i j) 0)
      (fun i j => (differentiableAt_adjugate M 0 (fun i j => (hM i j).differentiableAt) i j).hasDerivAt)
      hgN i j).differentiableAt
  set b' : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i j => deriv (fun s => b s i j) 0 with hb'
  have hb : ∀ i j, HasDerivAt (fun s => b s i j) (b' i j) 0 := fun i j => (hbdiff i j).hasDerivAt
  have hup : b'.BlockTriangular id := by
    intro i j hij
    have : (fun s => b s i j) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [h] with s hs using hs.2 i j hij
    show deriv (fun s => b s i j) 0 = 0
    rw [this.deriv_eq]; simp
  have hrel : g * N' = M' * b 0 + M 0 * b' := by
    ext i j
    refine (hgN i j).unique (HasDerivAt.congr_of_eventuallyEq (hasDerivAt_mul hM hb i j) ?_)
    filter_upwards [h] with s hs
    rw [hs.1]
  have h0 := h.self_of_nhds
  have uM : IsUnit (M 0).det := by rw [hMd]; exact isUnit_one
  have uN : IsUnit (N 0).det := by rw [hNd]; exact isUnit_one
  have ub : IsUnit (b 0).det := isUnit_iff_ne_zero.mpr hbd
  have hg : g = M 0 * b 0 * (N 0)⁻¹ := by
    rw [← h0.1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uN, Matrix.mul_one]
  have key : b 0 * ((N 0)⁻¹ * N') * (b 0)⁻¹ = (M 0)⁻¹ * M' + b' * (b 0)⁻¹ := by
    have e1 : b 0 * ((N 0)⁻¹ * N') = (M 0)⁻¹ * (g * N') := by
      rw [hg]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ uM, Matrix.one_mul]
    rw [e1, hrel, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc (M 0)⁻¹ (M 0),
      Matrix.nonsing_inv_mul _ uM, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ub, Matrix.mul_one]
  have hbinv : ((b 0)⁻¹).BlockTriangular id := by
    let _ := Matrix.invertibleOfIsUnitDet _ ub
    exact Matrix.blockTriangular_inv_of_blockTriangular fun i j hij => h0.2 i j hij
  rw [key, Matrix.add_apply, (hup.mul hbinv) hca, add_zero]
end GlobalTheory.UnitriJac
