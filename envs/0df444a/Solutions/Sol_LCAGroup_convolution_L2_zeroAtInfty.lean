-- Prove2me | solution 1 for LCAGroup.convolution_L2_zeroAtInfty
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:37:09.359788+00:00
-- url     : https://prove2.me/submissions/fff56ce1-d30b-4f71-b849-1a811ae4b88d

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution

open MeasureTheory Topology
open scoped ZeroAtInfty

set_option autoImplicit false

namespace Sol_LCAGroup_convolution_L2_zeroAtInfty

set_option linter.unusedSectionVars false

open Bornology Filter MeasureTheory Set Topology RiemannMasullo
open scoped ENNReal NNReal

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

section CompactSupportApproximation

/-- Approximate the indicator of a finite-measure set by a continuous cutoff with compact
support. The error is bounded by a constant on a measurable set of arbitrarily small mass. -/
private theorem exists_continuous_indicator_error_bound
    {X E : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {ν : Measure X} [ν.Regular]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) {s : Set X}
    (hs : MeasurableSet s) (hsfin : ν s < ∞) {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ (v : X → E) (t : Set X), Continuous v ∧ HasCompactSupport v ∧ AEStronglyMeasurable v ν ∧
      MeasurableSet t ∧ ν t ≤ η ∧ ∀ x, ‖(s.indicator (fun _ ↦ c) - v) x‖ ≤
        ‖t.indicator (fun _ ↦ ‖c‖ + ‖c‖) x‖ := by
  have he := (ENNReal.half_pos hη).ne'
  obtain ⟨K, hKs, hK, hsmallK⟩ := hs.exists_isCompact_sdiff_lt hsfin.ne he
  obtain ⟨V, hsV, hV, -, hsmallV⟩ := hs.exists_isOpen_sdiff_lt hsfin.ne he
  obtain ⟨b, hbK, hbV, hbc, hbr⟩ := exists_continuous_one_zero_of_isCompact hK
    hV.isClosed_compl (disjoint_compl_right_iff_subset.mpr (hKs.trans hsV))
  let v (x : X) := b x • c
  refine ⟨v, V \ K, b.continuous.smul continuous_const, hbc.smul_right (f' := fun _ ↦ c),
    b.continuous.aestronglyMeasurable.smul aestronglyMeasurable_const,
    hV.measurableSet.diff hK.isClosed.measurableSet, ?_, ?_⟩
  · calc
      _ ≤ ν ((V \ s) ∪ (s \ K)) := measure_mono (by grind)
      _ ≤ ν (V \ s) + ν (s \ K) := measure_union_le _ _
      _ ≤ η := (add_le_add hsmallV.le hsmallK.le).trans_eq (ENNReal.add_halves _)
  · intro x
    by_cases hx : x ∈ K
    · simp [v, hx, hKs hx, hbK hx]
    by_cases hxV : x ∈ V
    · rw [indicator_of_mem (show x ∈ V \ K from ⟨hxV, hx⟩)]
      refine (norm_sub_le _ _).trans ?_
      rw [Real.norm_of_nonneg (by positivity)]
      exact add_le_add (by simp [indicator]; split <;> simp) (by
        simpa [v, norm_smul, abs_of_nonneg (hbr x).1] using
          mul_le_mul_of_nonneg_right (hbr x).2 (norm_nonneg c))
    · have hxs : x ∉ s := fun h ↦ hxV (hsV h)
      simp [v, hxV, hxs, hbV hxV]

/-- For `p < ∞`, compactly supported continuous functions approximate `Lᵖ` functions on a
locally compact Hausdorff space with a regular measure. -/
theorem exists_hasCompactSupport_eLpNorm_sub_le' {X E : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] {ν : Measure X} [ν.Regular]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} (hp : p ≠ ∞)
    {u : X → E} (hu : MemLp u p ν) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ v : X → E, eLpNorm (u - v) p ν ≤ ε ∧ Continuous v ∧ HasCompactSupport v := by
  classical
  let P (v : X → E) := Continuous v ∧ HasCompactSupport v
  refine hu.induction_dense hp P ?_ ?_ (fun f hf ↦ (hf.1.stronglyMeasurable_of_hasCompactSupport hf.2).aestronglyMeasurable) hε
  · intro c s hs hsfin δ hδ
    obtain ⟨η, hη, hb⟩ := exists_eLpNorm_indicator_le (μ := ν) hp (‖c‖ + ‖c‖) hδ
    obtain ⟨v, t, hv, hvK, hvm, ht, hνt, hbound⟩ :=
      exists_continuous_indicator_error_bound c hs hsfin (ENNReal.coe_ne_zero.mpr hη.ne')
    refine ⟨v, ?_, hv, hvK⟩
    rw [eLpNorm_sub_comm]
    exact (eLpNorm_mono hbound).trans
      (hb t hνt)
  · exact fun f g hf hg ↦ ⟨hf.1.add hg.1, hf.2.add hg.2⟩

end CompactSupportApproximation

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

lemma integrable_lcaConvolution_L2 {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (x : G) :
    Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ ∧
      ‖lcaConvolution μ f g x‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hpres : MeasurePreserving (fun y : G ↦ x / y) μ μ :=
    Measure.measurePreserving_div_left μ x
  have hfun : (fun y ↦ g (y⁻¹ * x)) = g ∘ fun y ↦ x / y := by
    ext y
    simp [div_eq_mul_inv, mul_comm]
  have hg' : MemLp (fun y ↦ g (y⁻¹ * x)) 2 μ := hfun ▸ hg.comp_measurePreserving hpres
  have hnorm : eLpNorm (fun y ↦ g (y⁻¹ * x)) 2 μ = eLpNorm g 2 μ := by
    rw [hfun]
    exact eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hpres
  have hmul : MemLp (fun y ↦ f y * g (y⁻¹ * x)) 1 μ := hg'.mul' hf
  have hint : Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ := memLp_one_iff_integrable.mp hmul
  have hprod : eLpNorm (fun y ↦ f y * g (y⁻¹ * x)) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
    have hsmul := eLpNorm_smul_le_mul_eLpNorm (μ := μ) (p := 2) (q := 2) (r := 1)
      (φ := f) (f := fun y ↦ g (y⁻¹ * x)) hg'.aestronglyMeasurable hf.aestronglyMeasurable
    have hEq : (fun y ↦ f y * g (y⁻¹ * x)) = f • fun y ↦ g (y⁻¹ * x) := by
      ext y
      simp [smul_eq_mul]
    simpa [hEq, hnorm] using hsmul
  refine ⟨hint, ?_⟩
  have hfin : eLpNorm f 2 μ * eLpNorm g 2 μ ≠ ⊤ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top
  have hI : ‖∫ y, f y * g (y⁻¹ * x) ∂μ‖ₑ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
    calc
      ‖∫ y, f y * g (y⁻¹ * x) ∂μ‖ₑ
          ≤ ∫⁻ y, ‖f y * g (y⁻¹ * x)‖ₑ ∂μ :=
            enorm_integral_le_lintegral_enorm (fun y ↦ f y * g (y⁻¹ * x))
      _ = eLpNorm (fun y ↦ f y * g (y⁻¹ * x)) 1 μ := eLpNorm_one_eq_lintegral_enorm.symm
      _ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := hprod
  simpa [lcaConvolution, toReal_enorm', ENNReal.toReal_mul] using ENNReal.toReal_mono hfin hI

/-- Translation in `L²` makes the convolution of two `L²` functions continuous. -/
lemma continuous_lcaConvolution_L2 {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Continuous (lcaConvolution μ f g) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let gInv : G → ℂ := fun y ↦ g y⁻¹
  have hgInv : MemLp gInv 2 μ := hg.comp_measurePreserving (Measure.measurePreserving_inv μ)
  let F : Lp ℂ 2 μ := hf.toLp f
  let H : Lp ℂ 2 μ := hgInv.toLp gInv
  let pairing := (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2
  have hshift : Continuous fun x : G ↦ DomMulAct.mk x⁻¹ • H :=
    (continuous_smul (M := Gᵈᵐᵃ) (X := Lp ℂ 2 μ)).comp
      ((DomMulAct.continuous_mk.comp continuous_inv).prodMk continuous_const)
  have hcont : Continuous (fun x : G ↦ pairing F (DomMulAct.mk x⁻¹ • H)) :=
    (pairing F).continuous.comp hshift
  refine hcont.congr fun x ↦ ?_
  rw [ContinuousLinearMap.lpPairing_eq_integral, lcaConvolution]
  simp only [ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  have hF : (F : G → ℂ) =ᵐ[μ] f := hf.coeFn_toLp
  have hH : (H : G → ℂ) =ᵐ[μ] gInv := hgInv.coeFn_toLp
  have hleft : (fun y ↦ (H : G → ℂ) (x⁻¹ * y)) =ᵐ[μ] fun y ↦ gInv (x⁻¹ * y) :=
    (measurePreserving_mul_left μ x⁻¹).quasiMeasurePreserving.ae_eq_comp hH
  have hAct := DomMulAct.smul_Lp_ae_eq (DomMulAct.mk x⁻¹) H
  simp only [Equiv.symm_apply_apply, smul_eq_mul] at hAct
  have htrans : (DomMulAct.mk x⁻¹ • H : Lp ℂ 2 μ) =ᵐ[μ] fun y ↦ g (y⁻¹ * x) := by
    refine hAct.trans (hleft.trans ?_)
    filter_upwards with y
    simp [gInv, mul_inv_rev, inv_inv]
  filter_upwards [hF, htrans] with y hyF hyT
  simp only [hyF, hyT]

theorem lcaConvolution_L2' {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∀ x, Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ) ∧
      ∃ F : C₀(G, ℂ), (∀ x, F x = lcaConvolution μ f g x) ∧
        ‖F‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hint : ∀ x, Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ :=
    fun x ↦ (integrable_lcaConvolution_L2 μ hf hg x).1
  have hpoint : ∀ x, ‖lcaConvolution μ f g x‖ ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal :=
    fun x ↦ (integrable_lcaConvolution_L2 μ hf hg x).2
  have hcont : Continuous (lcaConvolution μ f g) := continuous_lcaConvolution_L2 μ hf hg
  let A := (eLpNorm f 2 μ).toReal
  let B := (eLpNorm g 2 μ).toReal
  have hzero : Tendsto (lcaConvolution μ f g) (cocompact G) (𝓝 (0 : ℂ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hCpos : 0 < A + B + 1 := by positivity
    let δr : ℝ := min 1 (ε / (2 * (A + B + 1)))
    have hδpos : 0 < δr := by
      have : 0 < ε / (2 * (A + B + 1)) := by positivity
      exact lt_min one_pos this
    have hδle : δr ≤ 1 := min_le_left _ _
    have hδmul : δr * (A + B + 1) ≤ ε / 2 := by
      have hle : δr ≤ ε / (2 * (A + B + 1)) := min_le_right _ _
      calc
        δr * (A + B + 1) ≤ ε / (2 * (A + B + 1)) * (A + B + 1) :=
          mul_le_mul_of_nonneg_right hle hCpos.le
        _ = ε / 2 := by field_simp [hCpos.ne']
    obtain ⟨f', hf'diff, hf'cont, hf'supp⟩ :=
      exists_hasCompactSupport_eLpNorm_sub_le' (p := 2) ENNReal.ofNat_ne_top hf
        (ENNReal.ofReal_pos.mpr hδpos).ne'
    obtain ⟨g', hg'diff, hg'cont, hg'supp⟩ :=
      exists_hasCompactSupport_eLpNorm_sub_le' (p := 2) ENNReal.ofNat_ne_top hg
        (ENNReal.ofReal_pos.mpr hδpos).ne'
    have hf' : MemLp f' 2 μ := hf'cont.memLp_of_hasCompactSupport (p := 2) hf'supp
    have hg' : MemLp g' 2 μ := hg'cont.memLp_of_hasCompactSupport (p := 2) hg'supp
    have hδf : (eLpNorm (f - f') 2 μ).toReal ≤ δr := by
      simpa [ENNReal.toReal_ofReal hδpos.le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hf'diff
    have hδg : (eLpNorm (g - g') 2 μ).toReal ≤ δr := by
      simpa [ENNReal.toReal_ofReal hδpos.le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hg'diff
    have hf'norm : (eLpNorm f' 2 μ).toReal ≤ A + δr := by
      have hle : eLpNorm f' 2 μ ≤ eLpNorm (f - f') 2 μ + eLpNorm f 2 μ := by
        calc
          eLpNorm f' 2 μ = eLpNorm (f + -(f - f')) 2 μ := by
            congr 1
            ext y
            simp [Pi.add_apply, Pi.sub_apply]
          _ ≤ eLpNorm f 2 μ + eLpNorm (-(f - f')) 2 μ :=
            eLpNorm_add_le hf.aestronglyMeasurable (hf.sub hf').neg.aestronglyMeasurable
              (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          _ = eLpNorm (f - f') 2 μ + eLpNorm f 2 μ := by rw [eLpNorm_neg, add_comm]
      have hfin1 : eLpNorm (f - f') 2 μ ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hf'diff
      have hfin : eLpNorm (f - f') 2 μ + eLpNorm f 2 μ ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨hfin1, hf.eLpNorm_ne_top⟩
      calc
        (eLpNorm f' 2 μ).toReal ≤ (eLpNorm (f - f') 2 μ + eLpNorm f 2 μ).toReal :=
          ENNReal.toReal_mono hfin hle
        _ = (eLpNorm (f - f') 2 μ).toReal + A := by
          rw [ENNReal.toReal_add hfin1 hf.eLpNorm_ne_top]
        _ ≤ δr + A := by gcongr
        _ = A + δr := add_comm _ _
    open scoped Pointwise in
    let K := tsupport f' * tsupport g'
    have hK : IsCompact K := hf'supp.isCompact.mul hg'supp.isCompact
    rw [eventually_iff, mem_cocompact']
    refine ⟨K, hK, ?_⟩
    intro x hx
    have hx' : ¬ dist (lcaConvolution μ f g x) 0 < ε := by
      simpa [mem_compl_iff, mem_ofPred] using hx
    by_contra hxK
    have htail : lcaConvolution μ f' g' x = 0 := by
      rw [lcaConvolution]
      rw [show (fun y ↦ f' y * g' (y⁻¹ * x)) = (0 : G → ℂ) by
        ext y
        by_contra hne
        have hy1 : y ∈ tsupport f' :=
          subset_tsupport f' (Function.mem_support.2 (left_ne_zero_of_mul hne))
        have hy2 : y⁻¹ * x ∈ tsupport g' :=
          subset_tsupport g' (Function.mem_support.2 (right_ne_zero_of_mul hne))
        exact hxK ⟨y, hy1, y⁻¹ * x, hy2, mul_inv_cancel_left y x⟩]
      exact integral_zero _ _
    have hsplit : lcaConvolution μ f g x - lcaConvolution μ f' g' x =
        lcaConvolution μ (f - f') g x + lcaConvolution μ f' (g - g') x := by
      have h1 := (integrable_lcaConvolution_L2 μ (hf.sub hf') hg x).1
      have h2 := (integrable_lcaConvolution_L2 μ hf' (hg.sub hg') x).1
      simp only [lcaConvolution]
      have hfg := hint x
      have hfg' := (integrable_lcaConvolution_L2 μ hf' hg' x).1
      rw [← integral_sub hfg hfg', ← integral_add h1 h2]
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp only [Pi.sub_apply]
      ring
    have hdist : ‖lcaConvolution μ f g x‖ ≤
        (eLpNorm (f - f') 2 μ).toReal * B + (eLpNorm f' 2 μ).toReal * (eLpNorm (g - g') 2 μ).toReal := by
      calc
        ‖lcaConvolution μ f g x‖ =
            ‖lcaConvolution μ f g x - lcaConvolution μ f' g' x‖ := by rw [htail, sub_zero]
        _ = ‖lcaConvolution μ (f - f') g x + lcaConvolution μ f' (g - g') x‖ := by rw [hsplit]
        _ ≤ ‖lcaConvolution μ (f - f') g x‖ + ‖lcaConvolution μ f' (g - g') x‖ := norm_add_le _ _
        _ ≤ (eLpNorm (f - f') 2 μ).toReal * (eLpNorm g 2 μ).toReal +
              (eLpNorm f' 2 μ).toReal * (eLpNorm (g - g') 2 μ).toReal :=
            add_le_add (integrable_lcaConvolution_L2 μ (hf.sub hf') hg x).2
              (integrable_lcaConvolution_L2 μ hf' (hg.sub hg') x).2
    have hsmall : ‖lcaConvolution μ f g x‖ < ε := by
      calc
        ‖lcaConvolution μ f g x‖ ≤
            (eLpNorm (f - f') 2 μ).toReal * B +
              (eLpNorm f' 2 μ).toReal * (eLpNorm (g - g') 2 μ).toReal := hdist
        _ ≤ δr * B + (A + δr) * δr := by
            gcongr
        _ ≤ δr * B + (A + 1) * δr := by
            gcongr
        _ = δr * (A + B + 1) := by ring
        _ ≤ ε / 2 := hδmul
        _ < ε := by linarith
    exact hx' <| by simpa [dist_zero_right] using hsmall
  let F : C₀(G, ℂ) :=
    { toFun := lcaConvolution μ f g
      continuous_toFun := hcont
      zero_at_infty' := hzero }
  refine ⟨hint, F, fun _ ↦ rfl, ?_⟩
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le_of_nonempty (f := F.toBCF)).2 fun x ↦ by
    simpa [F, dist_eq_norm] using hpoint x

end Sol_LCAGroup_convolution_L2_zeroAtInfty

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (f g : G → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∀ x : G, Integrable (fun y : G => f y * g (y⁻¹ * x)) μ) ∧
    ∃ F : C₀(G, ℂ), (∀ x : G, F x = RiemannMasullo.lcaConvolution μ f g x) ∧
      ‖F‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal :=
  Sol_LCAGroup_convolution_L2_zeroAtInfty.lcaConvolution_L2' μ hf hg
