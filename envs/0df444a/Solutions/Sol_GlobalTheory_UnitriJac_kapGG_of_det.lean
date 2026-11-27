-- Prove2me | solution 1 for GlobalTheory.UnitriJac.kapGG_of_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:41.749823+00:00
-- url     : https://prove2.me/submissions/8b169e8c-371d-415a-aebd-38ef1a2907eb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DifferentiableAtAdjugate
import Theorems.Thm_GlobalTheory_UnitriJac_fderiv_rel
import Theorems.Thm_GlobalTheory_UnitriJac_blockDiagonal_mulVec
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
theorem _root_.solution :
    (∀ (r : ℕ) (B : Matrix (Fin r) (Fin r) ℂ), B.det ≠ 0 → (∀ a c : Fin r, c < a → B a c = 0) → (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} => B p.1.1 q.1.1 * B⁻¹ q.1.2 p.1.2).det = ∏ a : Fin r, B a a ^ (2 * (a : ℤ) - ((r : ℤ) - 1))) → (∀ (r : ℕ) (N : Matrix (Fin r) (Fin r) ℂ), (∀ a c : Fin r, a < c → N a c = 0) → (∀ a, N a a = 1) → (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} => if p.1.2 = q.1.2 then N p.1.1 q.1.1 else 0).det = 1) → (KapGGStatement (E := E)) := by
  classical
  intro hAd hL r X x0 x1 γ U Φ bf hU hΦ h z hz
  let e : Low r × X.Ψ ≃ Fin (nd X) := (Equiv.prodComm _ _).trans (Fintype.equivFin (Ent X))
  let β : Module.Basis (Low r × X.Ψ) ℂ (V (nd X)) :=
    (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis.reindex e.symm
  have hβ : ∀ (v : V (nd X)) (τ : X.Ψ), (fun q => β.repr v (q, τ)) = crd X v τ := by
    intro v τ
    funext q
    simp only [β, Module.Basis.repr_reindex_apply, Equiv.symm_symm,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    rfl
  set D : V (nd X) →ₗ[ℂ] V (nd X) := (fderiv ℂ Φ z).toLinearMap with hD
  have hmat : Matrix.blockDiagonal (fun τ => leftM (mat (nmat X (Φ z)) τ)⁻¹) * LinearMap.toMatrix β β D =
      Matrix.blockDiagonal (fun τ => adM (mat (bf z) τ) * leftM (mat (nmat X z) τ)⁻¹) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    obtain ⟨v, rfl⟩ : ∃ v, (β.repr v : Low r × X.Ψ → ℂ) = u := ⟨β.equivFun.symm u, by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]⟩
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix_mulVec_repr]
    funext ⟨p, τ⟩
    rw [blockDiagonal_mulVec, blockDiagonal_mulVec, hβ, hβ]
    exact congrFun (fderiv_rel X x0 x1 γ U Φ bf hU hΦ h z hz v τ) p
  have hdet := congrArg Matrix.det hmat
  have hL' : ∀ (y : V (nd X)) (τ : X.Ψ), (leftM (mat (nmat X y) τ)⁻¹).det = 1 := fun y τ => by
    have := hL r _ (nmat_lowU X y τ).inv.1 (nmat_lowU X y τ).inv.2
    exact this
  have hA' : ∀ τ : X.Ψ, (adM (mat (bf z) τ)).det = ∏ a : Fin r, bf z τ a a ^ kapW X τ a := fun τ => by
    have := hAd r (mat (bf z) τ) ((h z hz).2.1 τ).1 ((h z hz).2.1 τ).2
    exact this
  rw [Matrix.det_mul, Matrix.det_blockDiagonal, Matrix.det_blockDiagonal, LinearMap.det_toMatrix] at hdet
  simp only [Matrix.det_mul, hL', hA', Finset.prod_const_one, one_mul, mul_one] at hdet
  exact hdet
end GlobalTheory.UnitriJac
