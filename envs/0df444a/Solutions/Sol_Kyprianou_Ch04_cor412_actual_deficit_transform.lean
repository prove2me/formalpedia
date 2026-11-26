-- Prove2me | solution 1 for Kyprianou.Ch04.cor412_actual_deficit_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:09:23.439642+00:00
-- url     : https://prove2.me/submissions/2cf5be7f-7b97-44e4-84ab-5bf52e017f2a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_bounded
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_contact
import Theorems.Thm_Kyprianou_Ch04_cor412_finite_passage_meas
import Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_no_passage
import Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_total_transform
import Theorems.Thm_Kyprianou_Ch04_cor412_uncapped_renewal_factor
import Theorems.Thm_Kyprianou_Ch04_cor412_renewal_algebra
import Theorems.Thm_Kyprianou_Ch04_cor412_positive_exponent
import Theorems.Thm_Kyprianou_Ch04_downwardPassageFiniteProbabilityBV
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Defective Laplace transform of the actual finite downward-passage position. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) (hm : 0 < derivWithin L.ψ (Ici 0) 0)
    (β : ℝ) (hβ : 0 < β) (finiteTime : Ω → NNReal)
    (hfin : ∀ w, Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤ →
      Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = (finiteTime w : WithTop NNReal)) :
    (∫⁻ w in {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤},
      ENNReal.ofReal (Real.exp (β * L.X (finiteTime w) w)) ∂P) =
      ENNReal.ofReal (1 - L.ψ β / (L.drift * β)) := by
  classical
  letI : IsProbabilityMeasure P := L.isProbability
  let A : Set Ω := {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≠ ⊤}
  let R : Ω → ℝ≥0∞ := fun w => ⨅ q : ℕ × ℕ,
    ENNReal.ofReal (Real.exp (β * L.X ((q.1 : NNReal) / 2 ^ q.2) w))
  let H : Ω → ℝ≥0∞ := fun w => ENNReal.ofReal (Real.exp (β * L.X (finiteTime w) w))
  let W := ∫⁻ w, R w ∂P
  let K := ∫⁻ w in A, H w ∂P
  let m := derivWithin L.ψ (Ici 0) 0
  have hA : MeasurableSet A := Kyprianou.Ch04.cor412_finite_passage_meas L
  obtain ⟨_,hB⟩ := Kyprianou.Ch04.cor412_lower_bounded P F L hm
  have hψ := (Kyprianou.Ch04.cor412_positive_exponent P F L hm).2 β hβ
  have hW : W = ENNReal.ofReal (m * β / L.ψ β) :=
    Kyprianou.Ch04.cor412_dyadic_total_transform L hm β hβ
  have hcap : K ≤ 1 := by
    calc
      K ≤ ∫⁻ _ in A, (1 : ℝ≥0∞) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hA] with w hw
        have ht := Kyprianou.Ch04.cor412_lower_contact P F L w (finiteTime w) (hfin w hw)
        exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hβ.le ht))
      _ ≤ 1 := by
        simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]
        exact (measure_mono (subset_univ A)).trans (by simp)
  have hK : K ≠ ⊤ := ne_top_of_le_ne_top (by simp) hcap
  have hn : (∫⁻ w in Aᶜ, R w ∂P) = P Aᶜ := by
    calc
      _ = ∫⁻ _ in Aᶜ, (1 : ℝ≥0∞) ∂P := by
        apply setLIntegral_congr_fun hA.compl
        intro w hw
        have ht : Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w = ⊤ := by simpa [A] using hw
        exact Kyprianou.Ch04.cor412_dyadic_no_passage L w ht β hβ.le
      _ = _ := by simp
  have hrenew : K * W + P Aᶜ = W := by
    have he := Kyprianou.Ch04.cor412_uncapped_renewal_factor L hB β hβ.le finiteTime hfin
    change (∫⁻ w in A, R w ∂P) = K * W at he
    rw [← he, ← hn]
    exact lintegral_add_compl R hA
  have hwf : W ≠ ⊤ := by rw [hW]; exact ENNReal.ofReal_ne_top
  have hcomp : (P Aᶜ).toReal = m / L.drift := by
    have he := congrArg ENNReal.toReal (measure_add_measure_compl (μ := P) hA)
    rw [ENNReal.toReal_add (measure_ne_top P A) (measure_ne_top P Aᶜ), measure_univ, ENNReal.toReal_one] at he
    have hp := Kyprianou.Ch04.downwardPassageFiniteProbabilityBV P F L hBV hd hm
    change (P A).toReal = (L.drift - m) / L.drift at hp
    rw [hp] at he
    rw [sub_div, div_self hd.ne'] at he
    linarith
  have hr := congrArg ENNReal.toReal hrenew
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hK hwf) (measure_ne_top P Aᶜ),
    ENNReal.toReal_mul, hcomp] at hr
  have hWr : W.toReal = m * β / L.ψ β := by
    rw [hW, ENNReal.toReal_ofReal (div_nonneg (mul_nonneg hm.le hβ.le) hψ.le)]
  have hk := Kyprianou.Ch04.cor412_renewal_algebra m L.drift β (L.ψ β)
    W.toReal K.toReal hm hd hβ hψ hWr (by linarith)
  change K = _
  rw [← hk, ENNReal.ofReal_toReal hK]
