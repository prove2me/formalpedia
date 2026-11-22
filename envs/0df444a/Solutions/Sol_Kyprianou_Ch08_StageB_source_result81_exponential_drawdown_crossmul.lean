-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_exponential_drawdown_crossmul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T19:39:12.821297+00:00
-- url     : https://prove2.me/submissions/2d258889-dc12-49f5-a49a-830251ea8678

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_lintegral_all_beta
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_levy_positive_root_strict_gap_below
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

private noncomputable def decay81 (s x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-s*x))
private theorem decay81_meas (s : ℝ) : Measurable (decay81 s) := by unfold decay81; fun_prop
private theorem decay81_add (a b x : ℝ) : decay81 a x * decay81 b x = decay81 (a+b) x := by
  unfold decay81; rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]; congr 2 <;> ring

private theorem core81
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hzero : A.ψ 0 = 0) (hdom : ∀ p : ℝ, 0 ≤ p → IsScaleTransformDomainBridge A.ψ p)
    (q : ℝ) (hq : 0 ≤ q) (d : ℝ) (hd : 0 < d) :
    let f : ℝ → ℝ := fun s => A.ψ (Phi A.ψ q + s) - q
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
          f d * (1 - s / d) := by
  letI : IsProbabilityMeasure P := A.isProbability; intro f
  let φ := Phi A.ψ q; have hφ : 0 ≤ φ := (hdom q hq).1.2.1.1
  have hroot : A.ψ φ = q := (hdom q hq).1.2.1.2
  let α := φ+d; have hα : 0 < α := by dsimp [α]; linarith
  have hφα : φ < α := by dsimp [α]; linarith
  have hαφ : α-φ = d := by dsimp [α]; ring
  let p := A.ψ α; have hqp : q < p := ((hdom q hq).2 α hα.le).mp hφα
  have hp : 0 < p := hq.trans_lt hqp; let r := p-q; have hr : 0 < r := sub_pos.mpr hqp
  have hαroot : Phi A.ψ p = α := by
    have hle : α ≤ Phi A.ψ p := (hdom p hp.le).1.2.2 α ⟨hα.le,rfl⟩; refine le_antisymm ?_ hle; by_contra! hlt
    have hg := avram_ws01e_bt_new_levy_positive_root_strict_gap_below A p (Phi A.ψ p) α hp (hα.trans hlt) (hdom p hp.le).1.2.1.2 hα.le hlt
    exact (lt_irrefl p) hg
  letI : IsProbabilityMeasure (expMeasure p) := ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  let D : Ω × ℝ → ℝ := fun z => runningSup A z.2.toNNReal z.1 - A.X z.2.toNNReal z.1
  have hD : Measurable D := (levy_exponential_real_clock_extrema_drawdown_measurable A).snd; have hDn (z : Ω × ℝ) : 0 ≤ D z := sub_nonneg.mpr ((runningSup_monotone_and_path_le A z.1).2 z.2.toNNReal)
  let M := P.prod (expMeasure p); let μ := M.map D
  let L := fun β => ∫⁻ y, decay81 β y ∂μ
  have hMap (β : ℝ) : L β = ∫⁻ z, decay81 β (D z) ∂M := lintegral_map (decay81_meas β) hD
  have hLle (β : ℝ) (hβ : 0 ≤ β) : L β ≤ 1 := by
    rw [hMap]
    calc
      _ ≤ ∫⁻ _ : Ω × ℝ, (1 : ℝ≥0∞) ∂M := lintegral_mono fun z => by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by linarith [mul_nonneg hβ (hDn z)]))
      _ = 1 := by simp [M]
  rcases avram_ws01e_bt_new_original_clock_descending_lintegral_all_beta A p hp α hα rfl with ⟨m,hm,hm',hAll⟩
  have hcross (β : ℝ) (hβ : 0 ≤ β) : (p-A.ψ β)*α*(L β).toReal = (α-β)*p := by
    rcases hβ.eq_or_lt with hzeroβ | hβp
    · subst β; rw [hMap]; simp [M,hzero,decay81]; ring
    rcases lt_trichotomy β α with hlt | heq | hgt
    · have hg : A.ψ β < p := avram_ws01e_bt_new_levy_positive_root_strict_gap_below A p α β hp hα rfl hβ hlt
      have hv : L β = ENNReal.ofReal ((p/α)*((α-β)/(p-A.ψ β))) := by
        rw [hMap]; simpa only [M,D,decay81,if_neg (ne_of_lt hlt)] using hAll β hβp
      have hnn : 0 ≤ (p/α)*((α-β)/(p-A.ψ β)) := mul_nonneg (div_nonneg hp.le hα.le)
        (div_nonneg (sub_nonneg.mpr hlt.le) (sub_nonneg.mpr hg.le))
      have hden : p-A.ψ β ≠ 0 := by linarith
      rw [hv, ENNReal.toReal_ofReal hnn]; field_simp [hα.ne',hden]
    · subst β; simp [p]
    · have hg : p < A.ψ β := (hdom p hp.le).2 β hβ |>.mp (by simpa [hαroot])
      have hv : L β = ENNReal.ofReal ((p/α)*((α-β)/(p-A.ψ β))) := by
        rw [hMap]; simpa only [M,D,decay81,if_neg (ne_of_gt hgt)] using hAll β (lt_trans hα hgt)
      have hnn : 0 ≤ (p/α)*((α-β)/(p-A.ψ β)) := mul_nonneg (div_nonneg hp.le hα.le)
        (div_nonneg_of_nonpos (sub_nonpos.mpr hgt.le) (sub_nonpos.mpr hg.le))
      have hden : p-A.ψ β ≠ 0 := by linarith
      rw [hv, ENNReal.toReal_ofReal hnn]; field_simp [hα.ne',hden]
  let c := α*r/(p*d); have hc : 0 < c := div_pos (mul_pos hα hr) (mul_pos hp hd)
  let ρ := μ.withDensity (fun y => ENNReal.ofReal c*decay81 φ y)
  have hdm : Measurable (fun y => ENNReal.ofReal c*decay81 φ y) := measurable_const.mul (decay81_meas φ)
  have htr (s : ℝ) : (∫⁻ y, decay81 s y ∂ρ) = ENNReal.ofReal c*L (φ+s) := by
    change (∫⁻ y, decay81 s y ∂(μ.withDensity (fun y => ENNReal.ofReal c*decay81 φ y))) = _; rw [lintegral_withDensity_eq_lintegral_mul μ hdm (decay81_meas s)]
    change (∫⁻ y, (ENNReal.ofReal c*decay81 φ y)*decay81 s y ∂μ) = _
    simp_rw [mul_assoc, decay81_add]; exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hfin : L φ ≠ ⊤ := ((hLle φ hφ).trans_lt ENNReal.one_lt_top).ne
  have hnorm : ENNReal.ofReal c*L φ = 1 := by
    have h := hcross φ hφ; rw [hroot,hαφ] at h
    have hC : c*(L φ).toReal = 1 := by
      dsimp [c,r]; field_simp [hp.ne',hd.ne']; nlinarith only [h]
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hc.le, hC, ENNReal.ofReal_one]
  have hprob : IsProbabilityMeasure ρ := ⟨by have h := (htr 0).trans (by simpa only [add_zero] using hnorm); simpa [decay81] using h⟩
  have hsuppμ : μ (Iio (0 : ℝ)) = 0 := by change (M.map D) (Iio (0 : ℝ)) = 0; rw [Measure.map_apply hD measurableSet_Iio]; have he : D ⁻¹' Iio (0 : ℝ) = ∅ := eq_empty_iff_forall_notMem.mpr (fun z hz => (hDn z).not_gt hz); rw [he, measure_empty]
  have hsupp : ρ (Iio (0 : ℝ)) = 0 := by
    change (μ.withDensity (fun y => ENNReal.ofReal c*decay81 φ y)) (Iio (0 : ℝ)) = 0
    rw [withDensity_apply _ measurableSet_Iio, Measure.restrict_eq_zero.mpr hsuppμ, lintegral_zero_measure]
  refine ⟨ρ,hprob,hsupp,?_⟩; intro s hs
  change (f d-f s)*(∫⁻ y, decay81 s y ∂ρ).toReal = _
  rw [htr, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  have h := hcross (φ+s) (add_nonneg hφ hs.le)
  have hdif : p-A.ψ (φ+s) = f d-f s := by change A.ψ (φ+d)-A.ψ (φ+s) = (A.ψ (φ+d)-q)-(A.ψ (φ+s)-q); ring
  have hshift : α-(φ+s) = d-s := by dsimp [α]; ring
  rw [hdif,hshift] at h
  calc
    _ = (r/(p*d))*((f d-f s)*α*(L (φ+s)).toReal) := by dsimp [c]; ring
    _ = (r/(p*d))*((d-s)*p) := by rw [h]
    _ = f d*(1-s/d) := by
      change (r/(p*d))*((d-s)*p) = r*(1-s/d)
      field_simp [hp.ne',hd.ne'] <;> ring

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hzero : A.ψ 0 = 0) (hdom : ∀ p : ℝ, 0 ≤ p → IsScaleTransformDomainBridge A.ψ p)
    (q : ℝ) (hq : 0 ≤ q) (d : ℝ) (hd : 0 < d) :
    let f : ℝ → ℝ := fun s => A.ψ (Phi A.ψ q + s) - q
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
          f d * (1 - s / d) := by
  exact core81 A hzero hdom q hq d hd
