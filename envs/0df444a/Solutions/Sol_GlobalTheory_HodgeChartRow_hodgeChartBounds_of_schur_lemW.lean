-- Prove2me | solution 1 for GlobalTheory.HodgeChartRow.hodgeChartBounds_of_schur_lemW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:20.122473+00:00
-- url     : https://prove2.me/submissions/dce013e8-508f-4dc0-8e34-d3acbebd1cb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydiscStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ChernCurvatureFormSelfEqDualNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeChartBoundsOfSchurLemW
import Theorems.Thm_GlobalTheory_HodgeChartRow_smulMulVec
import Theorems.Thm_GlobalTheory_HodgeChartRow_quad_decomp
import Theorems.Thm_GlobalTheory_HodgeChartRow_isOpen_polydisc
import Theorems.Thm_GlobalTheory_HodgeChartRow_isOpen_punctured
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_one
import Theorems.Thm_GlobalTheory_HermFrame_IsHermFrame_sub
import Theorems.Thm_GlobalTheory_HermFrame_IsPosFrame_sub
import Theorems.Thm_GlobalTheory_HermFrame_OneFormBound_mono
import Theorems.Thm_GlobalTheory_HermFrame_TwoFormBound_mono
import Theorems.Thm_GlobalTheory_HermFrame_form_smul_left
import Theorems.Thm_GlobalTheory_HermFrame_form_smul_right
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_HermFrame_twoFormBound_curv_two_mul
import Theorems.Thm_GlobalTheory_HodgeGramLocal_isOpen_polydisc
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HodgePeriodGram_conn_hodgeGram
import Theorems.Thm_GlobalTheory_IsPshC2On_mono
import Theorems.Thm_GlobalTheory_T_chernCurvature_form_self_eq_dual_norm
import Theorems.Thm_GlobalTheory_T_connectionMatrix_gramOperatorNorm_le
import Theorems.Thm_GlobalTheory_T_hodgeCurvature_dual_metric_pointwise_bound
import Theorems.Thm_GlobalTheory_T_hodgeMetricGramMatrix_local_holomorphic_imPart
import Theorems.Thm_GlobalTheory_T_periodChart_uniform_constants_half_polydisc
import Theorems.Thm_GlobalTheory_T_poincareMetric_punctured_polydisc_bounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeChartRow
namespace GlobalTheory.HodgeChartRow
theorem _root_.solution (hS : ∀ (k l : ℕ) (a bt : Matrix (Fin k) (Fin k) ℝ) (b : Matrix (Fin k) (Fin l) ℝ) (d : Matrix (Fin l) (Fin l) ℝ) (C₀ c₀ b₀ : ℝ), 0 ≤ C₀ → 0 < c₀ → 0 < b₀ → a.IsSymm → d.IsSymm → bt.IsSymm → (∀ x, |x ⬝ᵥ a.mulVec x| ≤ C₀ * (x ⬝ᵥ x)) → (∀ y, (b.mulVec y) ⬝ᵥ (b.mulVec y) ≤ C₀ ^ 2 * (y ⬝ᵥ y)) → (∀ y, c₀ * (y ⬝ᵥ y) ≤ y ⬝ᵥ d.mulVec y) → (∀ x, b₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ bt.mulVec x) → ∀ z : Fin k ⊕ Fin l → ℝ, ((1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀))⁻¹ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Matrix.fromBlocks (a + ((1 + C₀ + C₀ ^ 2 / c₀) / b₀) • bt) b b.transpose d).mulVec z) (hW : ∀ (g a : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (c C : ℝ), 0 < c → (∀ i, (B i).PosSemidef) → ∃ W : ℝ, ∀ (Y' : Matrix (Fin g) (Fin g) ℝ) (t : Fin a → ℝ), Y'.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y'.mulVec x) → (∀ x, x ⬝ᵥ Y'.mulVec x ≤ C * (x ⬝ᵥ x)) → (∀ i, 0 < t i) → ∀ i x, ‖(t i • ((Y' + ∑ l, t l • B l)⁻¹ * B i)).mulVec x‖ ≤ W * ‖x‖) : HodgeChartBounds := by
  intro n a g rk ha τ₀ B hP
  obtain ⟨T₀, c₁, C₁, M, β, hT₀, hc₁, hM, hβ, hBq, hY'⟩ := GlobalTheory.T.periodChart_uniform_constants_half_polydisc n a g rk τ₀ B hS hP
  obtain ⟨W, hW'⟩ := hW g a (fun i => (B i).map (Int.cast : ℤ → ℝ)) c₁ C₁ hc₁ hP.psd
  have hBnn : ∀ i (x : Fin g → ℝ), 0 ≤ x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x := fun i x => by
    simpa using (posSemidef_iff_dotProduct_mulVec.1 (hP.psd i)).2 x
  have hBsymm : ∀ i (j k : Fin g), (B i k j : ℝ) = B i j k := fun i j k => by
    simpa using (hP.psd i).isHermitian.apply j k
  set W' : ℝ := max W 0 with hW'def
  set ρ : ℝ := min (1 / 2) (Real.exp (-(4 * Real.pi * T₀))) with hρ
  have hρ0 : 0 < ρ := lt_min (by norm_num) (Real.exp_pos _)
  have hρ2 : ρ ≤ 1 / 2 := min_le_left _ _
  have hρ1 : ρ ≤ 1 := hρ2.trans (by norm_num)

  have hsymR : ∀ x ∈ polydisc n 1, (imPeriod ha τ₀ B x).IsSymm := fun x hx =>
    IsSymm.ext fun j k => by simp [imPeriod, Matrix.sum_apply, hBsymm, (hP.symm x hx).apply]
  have hsymC : ∀ x ∈ polydisc n 1, (hodgeGram ha τ₀ B x).IsSymm := fun x hx =>
    IsSymm.ext fun j k => by simp [hodgeGram, (hsymR x hx).apply j k]
  have hhermC : ∀ x ∈ polydisc n 1, (hodgeGram ha τ₀ B x).IsHermitian := fun x hx => by
    ext j k; simp [hodgeGram, conjTranspose_apply, (hsymR x hx).apply j k]

  have hz1 : ∀ z ∈ punctured ha ρ, z ∈ punctured ha 1 := fun z hz =>
    ⟨fun k => (hz.1 k).trans_le hρ1, hz.2⟩
  have hzh : ∀ z ∈ punctured ha ρ, z ∈ polydisc n (1 / 2) := fun z hz k => (hz.1 k).trans_le hρ2
  have ht : ∀ z ∈ punctured ha ρ, ∀ i : Fin a, 2 * T₀ < tlog (z (Fin.castLE ha i)) := by
    intro z hz i
    have h0 : 0 < ‖z (Fin.castLE ha i)‖ := norm_pos_iff.2 (hz.2 i)
    have h1 : ‖z (Fin.castLE ha i)‖ < Real.exp (-(4 * Real.pi * T₀)) :=
      (hz.1 _).trans_le (min_le_right _ _)
    have h2 : Real.log ‖z (Fin.castLE ha i)‖ < -(4 * Real.pi * T₀) := by
      rw [← Real.log_exp (-(4 * Real.pi * T₀))]; exact Real.log_lt_log h0 h1
    rw [tlog, lt_div_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  have hdec : ∀ z, imPeriod ha τ₀ B z = ((τ₀ z).map Complex.im + T₀ • ∑ i, (B i).map (Int.cast : ℤ → ℝ))
      + ∑ i, (tlog (z (Fin.castLE ha i)) - T₀) • (B i).map (Int.cast : ℤ → ℝ) := fun z => by
    simp only [imPeriod, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum]; abel

  have hq : ∀ z (x : Fin g → ℝ), x ⬝ᵥ imPeriod ha τ₀ B z *ᵥ x =
      x ⬝ᵥ ((τ₀ z).map Complex.im + T₀ • ∑ i, (B i).map (Int.cast : ℤ → ℝ)) *ᵥ x
      + ∑ i, (tlog (z (Fin.castLE ha i)) - T₀) * (x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x) :=
    fun z x => by rw [hdec z, quad_decomp]
  have hYlow : ∀ z ∈ punctured ha ρ, ∀ x, c₁ * (x ⬝ᵥ x) ≤ x ⬝ᵥ imPeriod ha τ₀ B z *ᵥ x := by
    intro z hz x
    rw [hq]
    have := ((hY' z (hzh z hz)).2.1 x)
    have : 0 ≤ ∑ i, (tlog (z (Fin.castLE ha i)) - T₀) * (x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by linarith [ht z hz i]) (hBnn i x)
    linarith
  have hYBi : ∀ z ∈ punctured ha ρ, ∀ i (x : Fin g → ℝ), (tlog (z (Fin.castLE ha i)) - T₀) *
      (x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x) ≤ x ⬝ᵥ imPeriod ha τ₀ B z *ᵥ x := by
    intro z hz i x
    rw [hq]
    have h1 := ((hY' z (hzh z hz)).2.1 x)
    have h2 : 0 ≤ x ⬝ᵥ x := by simpa [dotProduct] using Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (x j)
    have h3 := Finset.single_le_sum (f := fun i => (tlog (z (Fin.castLE ha i)) - T₀) *
      (x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x))
      (fun i _ => mul_nonneg (by linarith [ht z hz i]) (hBnn i x)) (Finset.mem_univ i)
    nlinarith

  set K₁ : ℝ := 2 * g * M / c₁ + a with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set C : ℝ := max (max C₁ β) (max (g * (2 * g * M / c₁ + W' * a)) (2 * (1 / 4 * K₁ ^ 2))) with hC
  refine ⟨ρ, c₁, C, hρ0, hρ2, hc₁, ?_, ?_, ?_, ?_⟩
  ·
    intro z hz
    have hs : (imPeriod ha τ₀ B z - c₁ • (1 : Matrix (Fin g) (Fin g) ℝ)).IsSymm :=
      (hsymR z (hz1 z hz).1).sub (isSymm_one.smul c₁)
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hs
    · simp only [star_trivial, sub_mulVec, smulMulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      linarith [hYlow z hz x]
  ·
    intro z hz
    set S : ℝ := ∑ i : Fin a, tlog (z (Fin.castLE ha i))
    have hs : ((C * (1 + S)) • (1 : Matrix (Fin g) (Fin g) ℝ) - imPeriod ha τ₀ B z).IsSymm :=
      (isSymm_one.smul _).sub (hsymR z (hz1 z hz).1)
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hs
    · simp only [star_trivial, sub_mulVec, smulMulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul]
      rw [hq]
      have h2 : 0 ≤ x ⬝ᵥ x := by simpa [dotProduct] using Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (x j)
      have h1 := (hY' z (hzh z hz)).2.2.1 x
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by linarith [ht z hz i]
      have h3 : ∑ i, (tlog (z (Fin.castLE ha i)) - T₀) * (x ⬝ᵥ ((B i).map (Int.cast : ℤ → ℝ)) *ᵥ x)
          ≤ S * (β * (x ⬝ᵥ x)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun i _ => ?_
        have := hBq i x
        have := hBnn i x
        have := ht z hz i
        nlinarith
      have hC1 : C₁ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
      have hCβ : β ≤ C := (le_max_right _ _).trans (le_max_left _ _)
      nlinarith [mul_le_mul_of_nonneg_right hC1 h2,
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCβ h2) hS0]
  ·
    intro z hz
    have hzp := hz1 z hz
    obtain ⟨hGpsd, hG⟩ := GlobalTheory.T.poincareMetric_punctured_polydisc_bounds n a ha ρ hρ1 z hz
    refine ⟨PosDef.one, hGpsd, fun ξ => ?_⟩
    have hgn0 : 0 ≤ gnorm (poincareGram a z) ξ := gnorm_nonneg _ _
    obtain ⟨hξk, hξi⟩ := hG ξ
    have hξ : ‖ξ‖ ≤ 2 * gnorm (poincareGram a z) ξ := (pi_norm_le_iff_of_nonneg (by positivity)).2 hξk
    rw [conn_hodgeGram ha hP hzp.1 ξ, (GlobalTheory.T.hodgeMetricGramMatrix_local_holomorphic_imPart n a g rk ha τ₀ B hP z hzp).2.1 ξ]
    have ht'0 : ∀ i, 0 < (fun i => tlog (z (Fin.castLE ha i)) - T₀) i := fun i => by
      simp only; linarith [ht z hz i]
    have hWY : ∀ i x, ‖((fun i => tlog (z (Fin.castLE ha i)) - T₀) i • ((imPeriod ha τ₀ B z)⁻¹ *
        (fun i => (B i).map (Int.cast : ℤ → ℝ)) i)) *ᵥ x‖ ≤ W' * ‖x‖ := by
      intro i x
      have := hW' _ (fun i => tlog (z (Fin.castLE ha i)) - T₀) (hY' z (hzh z hz)).1
        (hY' z (hzh z hz)).2.1 (hY' z (hzh z hz)).2.2.1 ht'0 i x
      beta_reduce at this ⊢
      rw [← hdec z] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have key := GlobalTheory.T.connectionMatrix_gramOperatorNorm_le g a (imPeriod ha τ₀ B z) (fun i => (B i).map (Int.cast : ℤ → ℝ))
      (of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ)
      (fun i => ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i)))
      (fun i => tlog (z (Fin.castLE ha i)) - T₀) c₁ (M * ‖ξ‖) W'
      hc₁ (by positivity) (le_max_right _ _) (hYlow z hz) ht'0 hWY
      (fun j k => by simpa using (hY' z (hzh z hz)).2.2.2 j k ξ)
    refine key.trans ?_
    have hs : ∀ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ /
        (tlog (z (Fin.castLE ha i)) - T₀) ≤ gnorm (poincareGram a z) ξ := by
      intro i
      have hz0 : 0 < ‖z (Fin.castLE ha i)‖ := norm_pos_iff.2 (hz.2 i)
      have htt := ht z hz i
      have hpi := Real.pi_gt_three
      have e : ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ =
          ‖ξ (Fin.castLE ha i)‖ / (2 * Real.pi * ‖z (Fin.castLE ha i)‖) := by
        rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le]; norm_num
      rw [e, div_div, div_le_iff₀ (mul_pos (by positivity) (by linarith))]
      have h1 := hξi i
      have h2 : tlog (z (Fin.castLE ha i)) ≤ Real.pi * (tlog (z (Fin.castLE ha i)) - T₀) := by
        nlinarith
      calc ‖ξ (Fin.castLE ha i)‖ ≤ 2 * (‖z (Fin.castLE ha i)‖ * tlog (z (Fin.castLE ha i))) *
            gnorm (poincareGram a z) ξ := h1
        _ ≤ 2 * (‖z (Fin.castLE ha i)‖ * (Real.pi * (tlog (z (Fin.castLE ha i)) - T₀))) *
            gnorm (poincareGram a z) ξ := by gcongr
        _ = _ := by ring
    have hsum : ∑ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ /
        (tlog (z (Fin.castLE ha i)) - T₀) ≤ a * gnorm (poincareGram a z) ξ := by
      refine (Finset.sum_le_sum fun i _ => hs i).trans ?_
      simp
    have hC3 : g * (2 * g * M / c₁ + W' * a) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
    have hW0 : 0 ≤ W' := le_max_right _ _
    calc (g : ℝ) * (g * (M * ‖ξ‖) / c₁ + W' * ∑ i, ‖ξ (Fin.castLE ha i) /
          (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ / (tlog (z (Fin.castLE ha i)) - T₀))
        ≤ g * (g * (M * (2 * gnorm (poincareGram a z) ξ)) / c₁ + W' * (a * gnorm (poincareGram a z) ξ)) := by
          gcongr
      _ = (g * (2 * g * M / c₁ + W' * a)) * gnorm (poincareGram a z) ξ := by ring
      _ ≤ C * gnorm (poincareGram a z) ξ := by gcongr
  ·
    have hC' : 0 ≤ 1 / 4 * K₁ ^ 2 := by positivity
    have hPD : ∀ z ∈ punctured ha ρ, ((imPeriod ha τ₀ B z).map Complex.ofReal).PosDef := fun z hz =>
      (GlobalTheory.T.hodgeCurvature_dual_metric_pointwise_bound g a (imPeriod ha τ₀ B z) (fun i => (B i).map (Int.cast : ℤ → ℝ)) 0 0
        (fun i => tlog (z (Fin.castLE ha i)) - T₀) c₁ 0 hc₁ le_rfl (hsymR z (hz1 z hz).1) (hYlow z hz)
        hP.psd (fun i => show 0 < tlog _ - T₀ by linarith [ht z hz i]) (hYBi z hz) (fun j k => by simp)).1
    have hPos : IsPosFrame (punctured ha ρ) (hodgeGram ha τ₀ B) := ⟨isOpen_punctured ha ρ,
      fun j k z hz => ((GlobalTheory.T.hodgeMetricGramMatrix_local_holomorphic_imPart n a g rk ha τ₀ B hP z (hz1 z hz)).1 j k).contDiffWithinAt, hPD⟩
    refine (twoFormBound_curv_two_mul hPos (fun z hz => (GlobalTheory.T.poincareMetric_punctured_polydisc_bounds n a ha ρ hρ1 z hz).1) hC' ?_).mono
      ((le_max_right _ _).trans (le_max_right _ _))
    intro z hz ξ v
    have hzp := hz1 z hz
    obtain ⟨hB1, hB2, hB3⟩ := GlobalTheory.T.hodgeMetricGramMatrix_local_holomorphic_imPart n a g rk ha τ₀ B hP z hzp
    obtain ⟨hGpsd, hG⟩ := GlobalTheory.T.poincareMetric_punctured_polydisc_bounds n a ha ρ hρ1 z hz
    have hpd := hPD z hz
    have hgn0 : 0 ≤ gnorm (poincareGram a z) ξ := gnorm_nonneg _ _
    obtain ⟨hξk, hξi⟩ := hG ξ
    have hξ : ‖ξ‖ ≤ 2 * gnorm (poincareGram a z) ξ := (pi_norm_le_iff_of_nonneg (by positivity)).2 hξk
    rw [GlobalTheory.T.chernCurvature_form_self_eq_dual_norm n g (hodgeGram ha τ₀ B) z (hB1.of_le (by norm_cast))
      ((isUnit_iff_isUnit_det _).1 hpd.isUnit)
      (mem_of_superset ((isOpen_polydisc n 1).mem_nhds hzp.1) fun x hx => hsymC x hx)
      (mem_of_superset ((isOpen_polydisc n 1).mem_nhds hzp.1) fun x hx => hhermC x hx) hB3 ξ v,
      hB2 ξ, smulMulVec, form_smul_left, form_smul_right]
    obtain ⟨-, hbd⟩ := GlobalTheory.T.hodgeCurvature_dual_metric_pointwise_bound g a (imPeriod ha τ₀ B z) (fun i => (B i).map (Int.cast : ℤ → ℝ))
      (of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ)
      (fun i => ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i)))
      (fun i => tlog (z (Fin.castLE ha i)) - T₀) c₁ (M * ‖ξ‖) hc₁ (by positivity)
      (hsymR z hzp.1) (hYlow z hz) hP.psd (fun i => show 0 < tlog _ - T₀ by linarith [ht z hz i]) (hYBi z hz)
      (fun j k => by simpa using (hY' z (hzh z hz)).2.2.2 j k ξ)
    have hbd' := hbd v
    beta_reduce at hbd'
    have hs : ∀ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ /
        (tlog (z (Fin.castLE ha i)) - T₀) ≤ gnorm (poincareGram a z) ξ := by
      intro i
      have hz0 : 0 < ‖z (Fin.castLE ha i)‖ := norm_pos_iff.2 (hz.2 i)
      have htt := ht z hz i
      have hpi := Real.pi_gt_three
      have e : ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ =
          ‖ξ (Fin.castLE ha i)‖ / (2 * Real.pi * ‖z (Fin.castLE ha i)‖) := by
        rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le]; norm_num
      rw [e, div_div, div_le_iff₀ (mul_pos (by positivity) (by linarith))]
      have h1 := hξi i
      have h2 : tlog (z (Fin.castLE ha i)) ≤ Real.pi * (tlog (z (Fin.castLE ha i)) - T₀) := by
        nlinarith
      calc ‖ξ (Fin.castLE ha i)‖ ≤ 2 * (‖z (Fin.castLE ha i)‖ * tlog (z (Fin.castLE ha i))) *
            gnorm (poincareGram a z) ξ := h1
        _ ≤ 2 * (‖z (Fin.castLE ha i)‖ * (Real.pi * (tlog (z (Fin.castLE ha i)) - T₀))) *
            gnorm (poincareGram a z) ξ := by gcongr
        _ = _ := by ring
    have hsum : ∑ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ /
        (tlog (z (Fin.castLE ha i)) - T₀) ≤ a * gnorm (poincareGram a z) ξ := by
      refine (Finset.sum_le_sum fun i _ => hs i).trans ?_
      simp
    have hsum0 : 0 ≤ ∑ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))‖ /
        (tlog (z (Fin.castLE ha i)) - T₀) :=
      Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (by linarith [ht z hz i])
    have hK : g * (M * ‖ξ‖) / c₁ + ∑ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I *
        z (Fin.castLE ha i))‖ / (tlog (z (Fin.castLE ha i)) - T₀) ≤ K₁ * gnorm (poincareGram a z) ξ := by
      calc _ ≤ g * (M * (2 * gnorm (poincareGram a z) ξ)) / c₁ + a * gnorm (poincareGram a z) ξ := by
            gcongr
        _ = K₁ * gnorm (poincareGram a z) ξ := by rw [hK₁]; ring
    have hnc : ‖(1 / (2 * Complex.I) : ℂ)‖ = 1 / 2 := by simp
    rw [norm_mul, norm_mul, Complex.norm_conj, hnc]
    simp only [hodgeGram]
    have hX0 : 0 ≤ g * (M * ‖ξ‖) / c₁ + ∑ i, ‖ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I *
        z (Fin.castLE ha i))‖ / (tlog (z (Fin.castLE ha i)) - T₀) := by positivity
    have hsq := pow_le_pow_left₀ hX0 hK 2
    have hv0 : 0 ≤ gnorm (hodgeGram ha τ₀ B z) v ^ 2 := sq_nonneg _
    have hv0' : 0 ≤ gnorm ((imPeriod ha τ₀ B z).map Complex.ofReal) v ^ 2 := sq_nonneg _
    have hstep := mul_le_mul_of_nonneg_right hsq hv0'
    nlinarith [hbd', hstep]
end GlobalTheory.HodgeChartRow
