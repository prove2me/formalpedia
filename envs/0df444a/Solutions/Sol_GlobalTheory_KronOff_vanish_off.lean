-- Prove2me | solution 1 for GlobalTheory.KronOff.vanish_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:58:30.872875+00:00
-- url     : https://prove2.me/submissions/89a57f87-b81c-4864-b9a0-96fa43bf50d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableIndicatorOfContOn
import Theorems.Thm_GlobalTheory_KronOff_isClosed_satBall
import Theorems.Thm_GlobalTheory_KronOff_rmul_mem_satBall
import Theorems.Thm_GlobalTheory_KronOff_rmul_mem_satBall_iff
import Theorems.Thm_GlobalTheory_KronOff_cpt_mem_satBall
import Theorems.Thm_GlobalTheory_KronOff_eq_of_mem_satBall
import Theorems.Thm_GlobalTheory_KronOff_exp_neg_phla
import Theorems.Thm_GlobalTheory_KronOff_pnorm_eq
import Theorems.Thm_GlobalTheory_KronOff_pnorm_contOn
import Theorems.Thm_GlobalTheory_KronOff_measurable_indicator_of_contOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExF_rhF_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_cont_dmin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_nfac_contOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_cpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_orth_mem_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_cd_cpt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_cd_dmin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_densF_continuousOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_densF_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_OntoB_hol_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowCoefficientBounds_nfac_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_pnorm_eq
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
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app
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
namespace GlobalTheory.KronOff
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
private theorem continuous_mat_frame {r : ℕ} (X : Data E r) (τ : X.Ψ) :
    Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
private theorem mat_rmul_torus_haar_measure {r : ℕ} {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) (τ : Ψ) :
    mat (rmul x b) τ = mat x τ * mat b τ := by
  ext a c
  rfl
private theorem mat_blockTriangular_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (τ : Ψ) :
    (mat b τ).BlockTriangular id := fun i j hij => (hb τ).2 i j hij
private theorem isOpen_dom_torus_haar_measure {r : ℕ} (X : Data E r) : IsOpen X.dom := by
  have h : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x : Frame X.Ψ r | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    rfl
  rw [h]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun (continuous_mat_frame X τ).matrix_det continuous_const
  · exact isOpen_lt continuous_const
      (continuous_const.mul (Complex.continuous_re.comp (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.cont_dmin X τ i)))
private theorem gram_eq_transpose_mul_map_mul_conj {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm
private theorem gram_mul_eq_transpose_mul_gram {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (M * N) = Nᵀ * gram τ G M * N.map (starRingEnd ℂ) := by
  rw [gram_eq_transpose_mul_map_mul_conj, gram_eq_transpose_mul_map_mul_conj, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
private theorem submatrix_congr_mul_of_blockTriangular {r k : ℕ} (h : k ≤ r) (N A : Matrix (Fin r) (Fin r) ℂ)
    (hN : N.BlockTriangular id) :
    (Nᵀ * A * N.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      (N.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ * A.submatrix (Fin.castLE h) (Fin.castLE h) *
        (N.submatrix (Fin.castLE h) (Fin.castLE h)).map (starRingEnd ℂ) := by
  have hz : ∀ (m : Fin r) (c : Fin k), m ∉ Set.range (Fin.castLE h) → N m (Fin.castLE h c) = 0 := by
    intro m c hm
    have hmk : k ≤ (m : ℕ) := by
      by_contra hc
      push_neg at hc
      exact hm ⟨⟨m, hc⟩, Fin.ext rfl⟩
    exact hN (show Fin.castLE h c < m from Fin.lt_iff_val_lt_val.mpr (lt_of_lt_of_le c.isLt hmk))
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun m hm => ?_) (fun m => ?_)
  · rw [hz m c hm, map_zero, mul_zero]
  · congr 1
    exact Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _
      (fun j hj => by rw [hz j a hj, zero_mul]) (fun j => rfl)
private theorem diag_ne_zero_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (τ : Ψ)
    (a : Fin r) : b τ a a ≠ 0 := by
  have h := (hb τ).1
  rw [Matrix.det_of_upperTriangular (mat_blockTriangular_of_mem_bor hb τ)] at h
  exact Finset.prod_ne_zero_iff.mp h a (Finset.mem_univ a)
private theorem exists_dmin_rmul_eq_normSq_mul' {r : ℕ} (X : Data E r) {x b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (i : Fin (r + 1)) :
    ∃ d : ℂ, d ≠ 0 ∧ dmin X.Gm (rmul x b) τ i = (Complex.normSq d : ℂ) * dmin X.Gm x τ i := by
  have hk : (i : ℕ) ≤ r := Nat.le_of_lt_succ i.isLt
  have hNt : ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).BlockTriangular id :=
    fun p q hpq => mat_blockTriangular_of_mem_bor hb τ (show Fin.castLE hk q < Fin.castLE hk p from hpq)
  refine ⟨((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det, ?_, ?_⟩
  · rw [Matrix.det_of_upperTriangular hNt]
    exact Finset.prod_ne_zero_iff.mpr fun p _ => diag_ne_zero_of_mem_bor hb τ (Fin.castLE hk p)
  · simp only [dmin, lminor]
    rw [mat_rmul_torus_haar_measure, gram_mul_eq_transpose_mul_gram, submatrix_congr_mul_of_blockTriangular hk _ _ (mat_blockTriangular_of_mem_bor hb τ), Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose]
    have hc : (((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).map (starRingEnd ℂ)).det =
        starRingEnd ℂ ((mat b τ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det :=
      (RingHom.map_det (starRingEnd ℂ) _).symm
    rw [hc, mul_right_comm, Complex.mul_conj]
private theorem rmul_mem_dom_of_mem_bor {r : ℕ} (X : Data E r) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) : rmul x b ∈ X.dom := by
  show ∀ τ : X.Ψ, (mat (rmul x b) τ).det ≠ 0 ∧
    ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (rmul x b) τ i).re
  refine fun τ => ⟨?_, fun i => ?_⟩
  · rw [mat_rmul_torus_haar_measure, Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · obtain ⟨d, hd, he⟩ := exists_dmin_rmul_eq_normSq_mul' X (x := x) hb τ i
    rw [he, Complex.re_ofReal_mul, mul_left_comm]
    exact mul_pos (Complex.normSq_pos.mpr hd) ((hx τ).2 i)
private theorem lact_one_frame' {r : ℕ} (X : Data E r) (y : Frame X.Ψ r) :
    lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = mat y τ
  rw [Units.val_one, Matrix.map_one τ.1 (map_zero _) (map_one _), Matrix.one_mul]
private theorem bchar_ne_zero_of_mem_bor' {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : bchar la b ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun τ _ =>
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (diag_ne_zero_of_mem_bor hb τ i)
end
end GlobalTheory.KronOff
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.KronOff
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.KronOff
theorem _root_.solution : (MeasInvStatement (E := E)) → (VanishAtSStatement (E := E)) → (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0 x1 : Frame X.Ψ r) (bb δ : ℝ) (χ F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), 0 < nd X → IsOrth X x0 → IsOrth X x1 → X.IsSec L w0 → (∀ k, X.IsSec L (s k)) → ContinuousOn ψ X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → 0 ≤ bb → Metric.closedBall (0 : V (nd X)) δ ⊆ OmF X x0 → (∀ z, δ ≤ ‖z‖ → χ z = 0) → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤ → (∀ z ∈ Metric.closedBall (0 : V (nd X)) δ, ∀ b ∈ Bor X.Ψ r, x1 ≠ rmul (cpt X x0 z) b) → w0 x1 ≠ 0 → (∀ k, s k x1 = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x1) z) / w0 (cpt X (x1) z) : V (nd X))) 0).det ≠ 0 → P x1 = 0) := by
  classical
  intro hMI hVS hNP r X la L w0 s ψ x0 x1 bb δ χ F P hn ho0 ho1 hw0 hs hψc hψi hbb hδ hχ hP hPF hint
    hout hw1 hs1 hdet
  obtain ⟨hNR, -, hPI⟩ := hNP
  have hx1d : x1 ∈ X.dom := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom X x1 ho1
  set U : Set (Frame X.Ψ r) := X.dom ∩ (satBall X x0 δ)ᶜ with hU
  have hUo : IsOpen U := (isOpen_dom_torus_haar_measure X).inter (isClosed_satBall X x0 δ).isOpen_compl
  have hx1U : x1 ∈ U := ⟨hx1d, fun h => by
    obtain ⟨z, hz, b, hb, he⟩ := eq_of_mem_satBall X x0 δ hδ hx1d h
    exact hout z hz b hb he⟩
  have hUinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, (rmul x b ∈ U ↔ x ∈ U) := by
    intro x hx b hb
    exact ⟨fun h => ⟨hx, fun h' => h.2 (rmul_mem_satBall X x0 δ h' hb)⟩,
      fun h => ⟨rmul_mem_dom_of_mem_bor X hx hb, fun h' => h.2 ((rmul_mem_satBall_iff X x0 δ hb).1 h')⟩⟩
  have hPc : ContinuousOn P X.dom := hP.1.continuousOn
  have hg1 : Measurable (U.indicator (X.pnorm la P)) :=
    measurable_indicator_of_contOn hUo ((pnorm_contOn X la hPc).mono fun _ h => h.1)
  have hg2 : Measurable (U.indicator fun y => Real.exp (-ψ y)) :=
    measurable_indicator_of_contOn hUo
      ((Real.continuous_exp.comp_continuousOn hψc.neg).mono fun _ h => h.1)
  have hg3 : ∀ k, Measurable (U.indicator (X.pnorm L (s k))) := fun k =>
    measurable_indicator_of_contOn hUo ((pnorm_contOn X L (hs k).1.continuousOn).mono fun _ h => h.1)
  obtain ⟨φ, hφ⟩ : ∃ φ : Frame X.Ψ r → ℝ≥0∞, φ = fun x => ENNReal.ofReal
      (U.indicator (X.pnorm la P) x ^ 2 * U.indicator (fun y => Real.exp (-ψ y)) x *
        (∑ k, U.indicator (X.pnorm L (s k)) x ^ 2) ^ (-(nd X : ℝ))) := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφ]
    first
    | exact (((hg1.pow_const 2).mul hg2).mul
        ((Finset.measurable_sum (f := fun k x => U.indicator (X.pnorm L (s k)) x ^ 2) Finset.univ
          fun k _ => (hg3 k).pow_const 2).pow_const _)).ennreal_ofReal
    | fun_prop
    | measurability
  have hφinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x := by
    intro x hx b hb
    rw [hφ]
    by_cases hxU : x ∈ U
    · have hxbU : rmul x b ∈ U := (hUinv x hx b hb).2 hxU
      have hc : ‖bchar la b‖ ≠ 0 := norm_ne_zero_iff.mpr (bchar_ne_zero_of_mem_bor' X la hb)
      have p1 : X.pnorm la P (rmul x b) = X.pnorm la P x := by
        rw [pnorm_eq X la P (rmul x b), pnorm_eq X la P x, hP.2 x hx b hb, hNR r X la x hx b hb,
          norm_mul]
        rw [show ‖bchar la b‖ * ‖P x‖ * (‖bchar la b‖⁻¹ * X.nfac la x) =
          (‖bchar la b‖ * ‖bchar la b‖⁻¹) * (‖P x‖ * X.nfac la x) by ring, mul_inv_cancel₀ hc, one_mul]
      have p3 : ∀ k, X.pnorm L (s k) (rmul x b) = X.pnorm L (s k) x := fun k => by
        have h := hPI r X L (s k) (hs k) 1 X.Γ.one_mem x hx b hb
        rwa [lact_one_frame'] at h
      simp only [Set.indicator_of_mem hxU, Set.indicator_of_mem hxbU, p1, p3, hψi x hx b hb]
    · have hxbU : rmul x b ∉ U := fun h => hxU ((hUinv x hx b hb).1 h)
      simp only [Set.indicator_apply, if_neg hxU, if_neg hxbU]
  have hL : ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hint
    rw [hφ]
    by_cases hz : cpt X x0 z ∈ U
    · have hzO : z ∈ OmF X x0 := hz.1
      have hzδ : δ ≤ ‖z‖ := by
        by_contra h
        push_neg at h
        exact hz.2 (cpt_mem_satBall X x0 δ (mem_closedBall_zero_iff.mpr h.le))
      simp only [Set.indicator_of_mem hz]
      rw [hχ z hzδ, ← hPF z hzO, zero_sub, norm_neg, pnorm_eq X la P, mul_pow,
        ← exp_neg_phla X la hz.1, neg_add, Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      have hrh := ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.rhF_nonneg X x0 ho0 hzO
      have hka0 : 0 < kaF X x0 bb z := Real.exp_pos _
      have hka1 : kaF X x0 bb z ≤ 1 := by
        show Real.exp (-bb * rhF X x0 z) ≤ 1
        calc Real.exp (-bb * rhF X x0 z) ≤ Real.exp 0 :=
              Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hbb hrh])
          _ = 1 := Real.exp_zero
      have hS : 0 ≤ (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ)) :=
        Real.rpow_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _) _
      refine mul_le_mul_of_nonneg_right ?_ hS
      rw [mul_assoc]
      first
      | exact le_div_self (by positivity) hka0 hka1
      | (rw [le_div_iff₀ hka0]; nlinarith [mul_nonneg (sq_nonneg ‖P (cpt X x0 z)‖)
          (mul_nonneg (Real.exp_pos (-phla X la (cpt X x0 z))).le (Real.exp_pos (-ψ (cpt X x0 z))).le)])
    · simp only [Set.indicator_apply, if_neg hz]
      simp
  have hR : ∫⁻ z, φ (cpt X x1 z) ∂muF X x1 < ⊤ := by
    rw [← hMI r X x0 x1 ho0 ho1 φ hφm hφinv]
    exact hL
  have hcc : Continuous (cpt X x1) := (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.cd_cpt X x1).continuous
  have hVo : IsOpen {z : V (nd X) | cpt X x1 z ∈ U} := hUo.preimage hcc
  have h0V : (0 : V (nd X)) ∈ {z : V (nd X) | cpt X x1 z ∈ U} := by
    show cpt X x1 0 ∈ U
    rw [ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero X x1]
    exact hx1U
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hVo 0 h0V
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ε / 2 := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; exact half_pos hε
  have hK : Metric.closedBall (0 : V (nd X)) ρ ⊆ {z | cpt X x1 z ∈ U} :=
    (Metric.closedBall_subset_ball (by rw [hρdef]; exact half_lt_self hε)).trans hεV
  have hcK : Set.MapsTo (cpt X x1) (Metric.closedBall (0 : V (nd X)) ρ) X.dom := fun z hz => (hK hz).1
  have hBO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1 := fun z hz => hcK (Metric.ball_subset_closedBall hz)
  have hcont : ContinuousOn (fun z => X.nfac la (cpt X x1 z) ^ 2 * Real.exp (-ψ (cpt X x1 z)) *
      (X.nfac L (cpt X x1 z) ^ 2) ^ (-(nd X : ℝ)) * densF X x1 z) (Metric.closedBall 0 ρ) := by
    have h1 : ContinuousOn (fun z => X.nfac la (cpt X x1 z)) (Metric.closedBall 0 ρ) :=
      (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.nfac_contOn X la).comp hcc.continuousOn hcK
    have h2 : ContinuousOn (fun z => ψ (cpt X x1 z)) (Metric.closedBall 0 ρ) :=
      hψc.comp hcc.continuousOn hcK
    have h3 : ContinuousOn (fun z => X.nfac L (cpt X x1 z)) (Metric.closedBall 0 ρ) :=
      (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.nfac_contOn X L).comp hcc.continuousOn hcK
    have h4 : ContinuousOn (densF X x1) (Metric.closedBall 0 ρ) :=
      (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_continuousOn (X := X) (x0 := x1)).mono fun z hz => hcK hz
    refine (((h1.pow 2).mul (Real.continuous_exp.comp_continuousOn h2.neg)).mul
      ((h3.pow 2).rpow_const fun z hz => Or.inl ?_)).mul h4
    exact (pow_pos (ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X (hcK hz) L) 2).ne'
  have hpos : ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ, 0 < X.nfac la (cpt X x1 z) ^ 2 *
      Real.exp (-ψ (cpt X x1 z)) * (X.nfac L (cpt X x1 z) ^ 2) ^ (-(nd X : ℝ)) * densF X x1 z := by
    intro z hz
    have a1 := ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X (hcK hz) la
    have a2 := ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X (hcK hz) L
    have a3 : 0 < densF X x1 z := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_pos (hcK hz)
    have a4 : 0 < (X.nfac L (cpt X x1 z) ^ 2) ^ (-(nd X : ℝ)) := Real.rpow_pos_of_pos (pow_pos a2 2) _
    exact mul_pos (mul_pos (mul_pos (pow_pos a1 2) (Real.exp_pos _)) a4) a3
  obtain ⟨z0, hz0, hmin⟩ := (isCompact_closedBall (0 : V (nd X)) ρ).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hρ.le⟩ hcont
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = X.nfac la (cpt X x1 z0) ^ 2 * Real.exp (-ψ (cpt X x1 z0)) *
      (X.nfac L (cpt X x1 z0) ^ 2) ^ (-(nd X : ℝ)) * densF X x1 z0 := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hmdef]; exact hpos z0 hz0
  have hle : ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ, m ≤ X.nfac la (cpt X x1 z) ^ 2 *
      Real.exp (-ψ (cpt X x1 z)) * (X.nfac L (cpt X x1 z) ^ 2) ^ (-(nd X : ℝ)) * densF X x1 z := by
    intro z hz
    rw [hmdef]
    exact isMinOn_iff.mp hmin z hz
  have key : ∀ z, z ∈ Metric.ball (0 : V (nd X)) ρ →
      ENNReal.ofReal (‖P (cpt X x1 z)‖ ^ 2 * (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ))) ≤
        ENNReal.ofReal m⁻¹ * (ENNReal.ofReal (densF X x1 z) * φ (cpt X x1 z)) := by
    intro z hz
    have hzK : z ∈ Metric.closedBall (0 : V (nd X)) ρ := Metric.ball_subset_closedBall hz
    have hzU : cpt X x1 z ∈ U := hK hzK
    have hd : 0 < densF X x1 z := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_pos (hcK hzK)
    have hz' := hle z hzK
    have hSn : 0 ≤ ∑ k, ‖s k (cpt X x1 z)‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    have e1 : ∑ k, X.pnorm L (s k) (cpt X x1 z) ^ 2 =
        X.nfac L (cpt X x1 z) ^ 2 * ∑ k, ‖s k (cpt X x1 z)‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [pnorm_eq, mul_pow, mul_comm]
    rw [hφ]
    simp only [Set.indicator_of_mem hzU]
    rw [e1, Real.mul_rpow (sq_nonneg _) hSn, pnorm_eq X la P, mul_pow,
      ← ENNReal.ofReal_mul hd.le, ← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le)]
    apply ENNReal.ofReal_le_ofReal
    have hA : 0 ≤ ‖P (cpt X x1 z)‖ ^ 2 * (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hSn _)
    have hr : 1 ≤ m⁻¹ * (X.nfac la (cpt X x1 z) ^ 2 * Real.exp (-ψ (cpt X x1 z)) *
        (X.nfac L (cpt X x1 z) ^ 2) ^ (-(nd X : ℝ)) * densF X x1 z) := by
      rw [← div_eq_inv_mul, one_le_div hm]
      exact hz'
    calc ‖P (cpt X x1 z)‖ ^ 2 * (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ))
        = ‖P (cpt X x1 z)‖ ^ 2 * (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ)) * 1 := (mul_one _).symm
      _ ≤ ‖P (cpt X x1 z)‖ ^ 2 * (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ)) *
          (m⁻¹ * (X.nfac la (cpt X x1 z) ^ 2 * Real.exp (-ψ (cpt X x1 z)) *
            (X.nfac L (cpt X x1 z) ^ 2) ^ (-(nd X : ℝ)) * densF X x1 z)) :=
          mul_le_mul_of_nonneg_left hr hA
      _ = _ := by ring
  have hdm : Measurable fun z => ENNReal.ofReal (densF X x1 z) := by
    apply Measurable.ennreal_ofReal
    unfold densF
    first
    | exact Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ =>
        ((ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.cd_dmin X x1 τ _).continuous.norm.measurable).pow_const _
    | fun_prop
    | measurability
  have hφcm : Measurable fun z => φ (cpt X x1 z) := hφm.comp hcc.measurable
  have hfin : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ,
      ENNReal.ofReal (‖P (cpt X x1 z)‖ ^ 2 * (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ))) < ⊤ := by
    calc ∫⁻ z in Metric.ball (0 : V (nd X)) ρ,
          ENNReal.ofReal (‖P (cpt X x1 z)‖ ^ 2 * (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ)))
        ≤ ∫⁻ z in Metric.ball (0 : V (nd X)) ρ,
          ENNReal.ofReal m⁻¹ * (ENNReal.ofReal (densF X x1 z) * φ (cpt X x1 z)) :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).mpr (ae_of_all _ key))
      _ = ENNReal.ofReal m⁻¹ * ∫⁻ z in Metric.ball (0 : V (nd X)) ρ,
          ENNReal.ofReal (densF X x1 z) * φ (cpt X x1 z) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal m⁻¹ * ∫⁻ z in OmF X x1, ENNReal.ofReal (densF X x1 z) * φ (cpt X x1 z) :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set hBO) zero_le
      _ = ENNReal.ofReal m⁻¹ * ∫⁻ z, φ (cpt X x1 z) ∂muF X x1 := by
          rw [muF, lintegral_withDensity_eq_lintegral_mul _ hdm hφcm]
          rfl
      _ < ⊤ := by
          first
          | exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hR
          | exact ENNReal.mul_lt_top ENNReal.ofReal_ne_top hR.ne
  exact hVS r X x1 hn ho1 hx1d P w0 s ρ hρ
    ((ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.hol_comp X x1 hP.1).mono hBO)
    (fun k => (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.hol_comp X x1 (hs k).1).mono hBO)
    ((ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.hol_comp X x1 hw0.1).mono hBO) hw1 hs1 hdet hfin
end GlobalTheory.KronOff
