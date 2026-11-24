-- Prove2me | solution 1 for GlobalTheory.UnitriJac.fderiv_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:41:33.787195+00:00
-- url     : https://prove2.me/submissions/996af681-365a-46b2-8510-12089d1f3059

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DifferentiableAtAdjugate
import Theorems.Thm_GlobalTheory_UnitriJac_leftM_mulVec
import Theorems.Thm_GlobalTheory_UnitriJac_adM_mulVec
import Theorems.Thm_GlobalTheory_UnitriJac_lowMat_leftM
import Theorems.Thm_GlobalTheory_UnitriJac_deriv_rel
import Theorems.Thm_GlobalTheory_UnitriJac_hasDerivAt_nmat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_LowU_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_LUPf_nmat_lowU
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.UnitriJac
theorem _root_.solution {r : ℕ} (X : Data E r) (x0 x1 : Frame X.Ψ r) (γ : GL (Fin r) E) (U : Set (V (nd X)))
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r) (hU : IsOpen U)
    (hΦ : DifferentiableOn ℂ Φ U)
    (h : ∀ z ∈ U, cpt X x0 z ∈ X.dom ∧ bf z ∈ Bor X.Ψ r ∧
      cpt X x0 z = lact γ (rmul (cpt X x1 (Φ z)) (bf z)))
    (z : V (nd X)) (hz : z ∈ U) (v : V (nd X)) (τ : X.Ψ) :
    leftM (mat (nmat X (Φ z)) τ)⁻¹ *ᵥ crd X (fderiv ℂ Φ z v) τ =
      (adM (mat (bf z) τ) * leftM (mat (nmat X z) τ)⁻¹) *ᵥ crd X v τ := by
  set G : Matrix (Fin r) (Fin r) ℂ := (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ with hG
  have hrel : ∀ y ∈ U, mat x0 τ * mat (nmat X y) τ = G * (mat (nmat X (Φ y)) τ * mat (bf y) τ) := by
    intro y hy
    have := congrFun (h y hy).2.2 τ
    rw [hG, Matrix.mul_assoc, ← Matrix.mul_assoc (mat x1 τ)]
    exact this
  have uG : IsUnit G.det := by
    have h1 : (mat x0 τ * mat (nmat X z) τ).det ≠ 0 := ((h z hz).1 τ).1
    rw [hrel z hz, Matrix.det_mul] at h1
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul h1)
  have hl : HasDerivAt (fun s : ℂ => z + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hΦz : HasFDerivAt Φ (fderiv ℂ Φ z) (z + (0 : ℂ) • v) := by
    simpa using (hΦ.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hl2 : HasDerivAt (fun s : ℂ => Φ (z + s • v)) (fderiv ℂ Φ z v) 0 :=
    hΦz.comp_hasDerivAt (0 : ℂ) hl
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), z + s • v ∈ U :=
    hl.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hz))
  funext p
  have := deriv_rel (N := fun s => mat (nmat X (z + s • v)) τ)
    (M := fun s => mat (nmat X (Φ (z + s • v))) τ) (b := fun s => mat (bf (z + s • v)) τ)
    (g := G⁻¹ * mat x0 τ) (hasDerivAt_nmat X hl τ) (hasDerivAt_nmat X hl2 τ)
    (fun s => (nmat_lowU X _ τ).det) (nmat_lowU X _ τ).det
    (by simpa using ((h z hz).2.1 τ).1)
    (by
      filter_upwards [hev] with s hs
      refine ⟨?_, fun a c hca => ((h _ hs).2.1 τ).2 a c hca⟩
      rw [Matrix.mul_assoc, hrel _ hs, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uG, Matrix.one_mul])
    p.1.1 p.1.2 p.2
  simp only [zero_smul, add_zero] at this
  rw [leftM_mulVec, ← Matrix.mulVec_mulVec, adM_mulVec, lowMat_leftM (nmat_lowU X z τ).inv]
  exact this
end GlobalTheory.UnitriJac
