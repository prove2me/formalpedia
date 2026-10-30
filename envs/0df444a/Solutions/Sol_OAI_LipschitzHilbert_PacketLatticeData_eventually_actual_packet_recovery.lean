-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketLatticeData.eventually_actual_packet_recovery
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:14:20.927658+00:00
-- url     : https://prove2.me/submissions/c6a610fb-33fc-4980-b956-ab86950320aa

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_eventually_assigned_parent_central_gain
import Theorems.Thm_OAI_LipschitzHilbert_eventually_polynomial_uniform_selected_reference_good_path

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_CountingDiscard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The cost of discarding the counting exceptional set

This proves §6 `count:discard-cost` from the actual restricted integral,
the ordinary model's L² estimate, and the exceptional-set area budget.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]

/-- Cauchy–Schwarz on a finite-measure set, with the L² energy taken on
the whole space. In particular the restricted norm integral exists. -/
theorem integral_norm_on_set_le_l2 (μ : Measure X) (P : X → V)
    (hP : MemLp P 2 μ) {A : Set X} (hA : μ A ≠ ∞) :
    IntegrableOn (fun x => ‖P x‖) A μ ∧
      (∫ x in A, ‖P x‖ ∂μ) ≤
        Real.sqrt (∫ x, ‖P x‖ ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hA
  have hnorm : MemLp (fun x => ‖P x‖) 2 (μ.restrict A) := (hP.restrict A).norm
  have hone : MemLp (fun _ : X => (1 : ℝ)) 2 (μ.restrict A) := memLp_const 1
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.restrict A)
    Real.HolderConjugate.two_two (Filter.Eventually.of_forall fun x => norm_nonneg (P x))
    (Filter.Eventually.of_forall fun _ => (by norm_num : (0 : ℝ) ≤ 1))
    (by simpa using hnorm) (by simpa using hone)
  have hsq : (∫ x in A, ‖P x‖ ^ 2 ∂μ) ≤ ∫ x, ‖P x‖ ^ 2 ∂μ :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hP.norm.integrable_sq)
  have hh' : (∫ x in A, ‖P x‖ ∂μ) ≤
      Real.sqrt (∫ x in A, ‖P x‖ ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
    simpa only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul,
      mul_one, measureReal_restrict_apply_univ, ← Real.sqrt_eq_rpow] using hh
  exact ⟨hnorm.integrable (by norm_num), hh'.trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _))⟩

theorem sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  congr 1
  ring

/-- The L² model estimate and the area budget give the exponentially
small discarded integral with its exact square-root loss. -/
theorem counting_discard_from_area (μ : Measure X) (P : X → V)
    (hP : MemLp P 2 μ) {A E : Set X} (hA : μ A ≠ ∞)
    {K B J L : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hmodel : (∫ x, ‖P x‖ ^ 2 ∂μ) ≤ K ^ 2 * μ.real E)
    (harea : μ.real A ≤ B * μ.real E * Real.exp (-J * L)) :
    IntegrableOn (fun x => ‖P x‖) A μ ∧
      (∫ x in A, ‖P x‖ ∂μ) ≤ K * Real.sqrt B * μ.real E * Real.exp (-J * L / 2) := by
  obtain ⟨hi, hcs⟩ := integral_norm_on_set_le_l2 μ P hP hA
  refine ⟨hi, hcs.trans ?_⟩
  have he : 0 ≤ μ.real E := measureReal_nonneg
  calc
    Real.sqrt (∫ x, ‖P x‖ ^ 2 ∂μ) * Real.sqrt (μ.real A) ≤
        Real.sqrt (K ^ 2 * μ.real E) *
          Real.sqrt (B * μ.real E * Real.exp (-J * L)) :=
      mul_le_mul (Real.sqrt_le_sqrt hmodel) (Real.sqrt_le_sqrt harea)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = K * Real.sqrt B * μ.real E * Real.exp (-J * L / 2) := by
      rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK,
        Real.sqrt_mul (mul_nonneg hB he), Real.sqrt_mul hB, sqrt_exp_half]
      calc
        _ = K * Real.sqrt B * (Real.sqrt (μ.real E) * Real.sqrt (μ.real E)) *
            Real.exp (-J * L / 2) := by ring
        _ = _ := by rw [Real.mul_self_sqrt he]

/-- Converting `|E|=N²|F|` and `N≤exp(2L)` gives the precise exponent
`(2-J/2)L` in the source discard estimate. -/
theorem counting_discard_cost (μ : Measure X) (P : X → V)
    (hP : MemLp P 2 μ) {A E F : Set X} (hA : μ A ≠ ∞)
    {K B J L N : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hratio : μ.real E = N ^ 2 * μ.real F) (hNlarge : N ≤ Real.exp (2 * L))
    (hmodel : (∫ x, ‖P x‖ ^ 2 ∂μ) ≤ K ^ 2 * μ.real E)
    (harea : μ.real A ≤ B * μ.real E * Real.exp (-J * L)) :
    IntegrableOn (fun x => ‖P x‖) A μ ∧
      (∫ x in A, ‖P x‖ ∂μ) ≤
        (K * Real.sqrt B) * Real.exp ((2 - J / 2) * L) * N * μ.real F := by
  obtain ⟨hi, hdiscard⟩ := counting_discard_from_area μ P hP hA hK hB hmodel harea
  refine ⟨hi, hdiscard.trans ?_⟩
  rw [hratio]
  have hNmul : N ^ 2 ≤ Real.exp (2 * L) * N := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hNlarge hN
  have hweight : 0 ≤ (K * Real.sqrt B) * μ.real F * Real.exp (-J * L / 2) := by positivity
  have h := mul_le_mul_of_nonneg_right hNmul hweight
  have hexp : Real.exp (2 * L) * Real.exp (-J * L / 2) =
      Real.exp ((2 - J / 2) * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    K * Real.sqrt B * (N ^ 2 * μ.real F) * Real.exp (-J * L / 2) ≤
        (Real.exp (2 * L) * N) *
          ((K * Real.sqrt B) * μ.real F * Real.exp (-J * L / 2)) := by
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ = _ := by rw [show (Real.exp (2 * L) * N) *
          ((K * Real.sqrt B) * μ.real F * Real.exp (-J * L / 2)) =
        (K * Real.sqrt B) * (Real.exp (2 * L) * Real.exp (-J * L / 2)) * N * μ.real F by ring,
      hexp]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_EnvelopeSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Cauchy--Schwarz for actual packet synthesis, followed by
polynomially weighted whole-line energy bounds. -/

noncomputable section
open MeasureTheory
open FourierTransform
open scoped BigOperators
open scoped FourierTransform

namespace LipschitzHilbert

theorem packetSynthesis_apply {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (x : ℝ) :
    packetSynthesis c f x = ∑ i, c i * f i x := by
  simp only [packetSynthesis, sum_apply, smul_apply, smul_eq_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SummationByParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation by parts for the weighted vector amplitudes of the hierarchy. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_weighted_sum_le_variation (w : ℕ → ℂ) (f : ℕ → E) (N : ℕ) (B : ℝ)
    (hB : ∀ k ≤ N, ‖∑ i ∈ Finset.range (k + 1), f i‖ ≤ B) :
    ‖∑ i ∈ Finset.range (N + 1), w i • f i‖ ≤
      (‖w N‖ + ∑ i ∈ Finset.range N, ‖w (i + 1) - w i‖) * B := by
  rw [Finset.sum_range_by_parts]
  simp only [Nat.add_sub_cancel]
  calc
    _ ≤ ‖w N • ∑ i ∈ Finset.range (N + 1), f i‖ +
        ‖∑ i ∈ Finset.range N, (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), f j‖ :=
      norm_sub_le _ _
    _ ≤ ‖w N‖ * B + ∑ i ∈ Finset.range N, ‖w (i + 1) - w i‖ * B := by
      apply add_le_add
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hB N le_rfl) (norm_nonneg _)
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hB i (by have := Finset.mem_range.mp hi; omega))
          (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MonotoneCoefficientSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing nonnegative coefficient deficits are controlled by raw
prefix sums, independently of the number of stopping levels. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_monotone_coefficient_sum (w : ℕ → ℝ) (f : ℕ → E) (N : ℕ) (B : ℝ)
    (hB0 : 0 ≤ B) (hw : ∀ i ≤ N, 0 ≤ w i)
    (hmono : ∀ i ≤ N, ∀ j ≤ N, i ≤ j → w i ≤ w j)
    (hB : ∀ k ≤ N, ‖∑ i ∈ Finset.range (k+1), f i‖ ≤ B) :
    ‖∑ i ∈ Finset.range (N+1), (w i : ℂ) • f i‖ ≤ 2*w N*B := by
  have hnorm : ‖(w N : ℂ)‖ = w N := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw N le_rfl)]
  have hdiff (i : ℕ) (hi : i ∈ Finset.range N) :
      ‖(w (i+1) : ℂ)-(w i : ℂ)‖ = w (i+1)-w i := by
    have hiN := Finset.mem_range.mp hi
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (hmono i (by omega) (i+1) (by omega) (by omega)))]
  have hvariation : ‖(w N : ℂ)‖ +
      ∑ i ∈ Finset.range N, ‖(w (i+1) : ℂ)-(w i : ℂ)‖ ≤ 2*w N := by
    rw [hnorm,Finset.sum_congr rfl hdiff,Finset.sum_range_sub]
    linarith [hw 0 (Nat.zero_le N)]
  exact (norm_weighted_sum_le_variation (fun i => (w i : ℂ)) f N B hB).trans
    (mul_le_mul_of_nonneg_right hvariation hB0)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_OriginalRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original adjoint sum is estimated on every discarded set.
The central sum enters only on the moving good set; its boundary error
is averaged over the fixed common good set. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
variable {X E : Type*} [NormedAddCommGroup E]

private theorem three_term_norm (p q w : E) :
    ‖p‖ ≤ ‖p-q‖+‖q-w‖+‖w‖ := by
  calc
    ‖p‖ = ‖(p-q)+(q-w)+w‖ := by congr 1; abel
    _ ≤ ‖(p-q)+(q-w)‖+‖w‖ := norm_add_le _ _
    _ ≤ (‖p-q‖+‖q-w‖)+‖w‖ := by
      linarith [norm_add_le (p-q) (q-w)]

theorem original_recovery_pointwise
    (F Z0 Z : Set X) (hZ0 : Z0 ⊆ F) (hZ : Z ⊆ Z0) (P Q W : X → E) (x : X) :
    F.indicator (fun x => ‖P x‖) x ≤
      (F\Z0).indicator (fun x => ‖P x‖) x +
      (Z0\Z).indicator (fun x => ‖P x‖) x +
      Z0.indicator (fun x => ‖P x-Q x‖) x +
      Z0.indicator (fun x => ‖Q x-W x‖) x + Z.indicator (fun x => ‖W x‖) x := by
  classical
  by_cases hx : x ∈ F
  · by_cases hz0 : x ∈ Z0
    · by_cases hz : x ∈ Z
      · simpa only [indicator_of_mem hx,indicator_of_mem hz0,indicator_of_mem hz,
          indicator_of_notMem (show x ∉ F\Z0 from fun h => h.2 hz0),
          indicator_of_notMem (show x ∉ Z0\Z from fun h => h.2 hz),zero_add]
          using three_term_norm (P x) (Q x) (W x)
      · simp only [indicator_of_mem hx,indicator_of_mem hz0,indicator_of_notMem hz,
          indicator_of_notMem (show x ∉ F\Z0 from fun h => h.2 hz0),
          indicator_of_mem (show x ∈ Z0\Z from ⟨hz0,hz⟩),zero_add,add_zero]
        linarith [norm_nonneg (P x-Q x),norm_nonneg (Q x-W x)]
    · have hz : x ∉ Z := fun h => hz0 (hZ h)
      simp only [indicator_of_mem hx,indicator_of_notMem hz0,indicator_of_notMem hz,
        indicator_of_mem (show x ∈ F\Z0 from ⟨hx,hz0⟩),
        indicator_of_notMem (show x ∉ Z0\Z from fun h => hz0 h.1),add_zero,le_refl]
  · have hz0 : x ∉ Z0 := fun h => hx (hZ0 h)
    have hz : x ∉ Z := fun h => hz0 (hZ h)
    simp only [indicator_of_notMem hx,indicator_of_notMem hz0,indicator_of_notMem hz,
      indicator_of_notMem (show x ∉ F\Z0 from fun h => hx h.1),
      indicator_of_notMem (show x ∉ Z0\Z from fun h => hz0 h.1),add_zero,le_refl]

variable [MeasurableSpace X]

theorem original_recovery_integral
    (μ : Measure X) (F Z0 Z : Set X) (hFm : MeasurableSet F) (hZ0m : MeasurableSet Z0) (hZm : MeasurableSet Z)
    (hZ0 : Z0 ⊆ F) (hZ : Z ⊆ Z0) (P Q W : X → E)
    (hP : IntegrableOn (fun x => ‖P x‖) F μ)
    (hPQ : IntegrableOn (fun x => ‖P x-Q x‖) Z0 μ)
    (hQW : IntegrableOn (fun x => ‖Q x-W x‖) Z0 μ)
    (hW : IntegrableOn (fun x => ‖W x‖) Z μ) :
    (∫ x in F, ‖P x‖ ∂μ) ≤ (∫ x in F\Z0, ‖P x‖ ∂μ) +
      (∫ x in Z0\Z, ‖P x‖ ∂μ) + (∫ x in Z0, ‖P x-Q x‖ ∂μ) +
      (∫ x in Z0, ‖Q x-W x‖ ∂μ) + (∫ x in Z, ‖W x‖ ∂μ) := by
  have h0 : Integrable (F.indicator (fun x => ‖P x‖)) μ :=
    (integrable_indicator_iff hFm).mpr hP
  have h1 : Integrable ((F\Z0).indicator (fun x => ‖P x‖)) μ :=
    (integrable_indicator_iff (hFm.diff hZ0m)).mpr (hP.mono_set sdiff_subset)
  have h2 : Integrable ((Z0\Z).indicator (fun x => ‖P x‖)) μ :=
    (integrable_indicator_iff (hZ0m.diff hZm)).mpr
      (hP.mono_set (fun _ hx => hZ0 hx.1))
  have h3 : Integrable (Z0.indicator (fun x => ‖P x-Q x‖)) μ :=
    (integrable_indicator_iff hZ0m).mpr hPQ
  have h4 : Integrable (Z0.indicator (fun x => ‖Q x-W x‖)) μ :=
    (integrable_indicator_iff hZ0m).mpr hQW
  have h5 : Integrable (Z.indicator (fun x => ‖W x‖)) μ :=
    (integrable_indicator_iff hZm).mpr hW
  have h := integral_mono h0 ((((h1.add h2).add h3).add h4).add h5)
    (original_recovery_pointwise F Z0 Z hZ0 hZ P Q W)
  simp only [Pi.add_apply] at h
  have he5 := integral_add (((h1.add h2).add h3).add h4) h5
  have he4 := integral_add ((h1.add h2).add h3) h4
  have he3 := integral_add (h1.add h2) h3
  have he2 := integral_add h1 h2
  simp only [Pi.add_apply] at he5 he4 he3 he2
  rw [he5,he4,he3,he2] at h
  simpa only [integral_indicator hFm,integral_indicator (hFm.diff hZ0m),
    integral_indicator (hZ0m.diff hZm),integral_indicator hZ0m,integral_indicator hZm] using h

/-- Averaging a pointwise recovery inequality does not require the
moving exceptional sets themselves to be jointly measurable. -/
theorem recover_constant_from_translation_average (R P C : ℝ) (hR : 0 < R)
    (error : ℝ → ℝ) (herror : IntervalIntegrable error volume 0 R)
    (hbound : ∀ origin ∈ Icc 0 R, P ≤ C+error origin) :
    P ≤ C+(∫ origin in (0:ℝ)..R, error origin)/R := by
  have hi := intervalIntegral.integral_mono_on hR.le
    (intervalIntegrable_const (c := P)) ((intervalIntegrable_const (c := C)).add herror) hbound
  rw [intervalIntegral.integral_add (intervalIntegrable_const (c := C)) herror,
    intervalIntegral.integral_const,intervalIntegral.integral_const] at hi
  simp only [sub_zero,smul_eq_mul] at hi
  have hdiv : ((∫ origin in (0:ℝ)..R, error origin)/R)*R =
      (∫ origin in (0:ℝ)..R, error origin) := div_mul_cancel₀ _ hR.ne'
  nlinarith [hi,hdiv]

/-- Fixed exceptions, each moving exception, the mask error, the
averaged boundary error, and the central estimate bound the original sum. -/
theorem recover_original_from_moving_good
    (μ : Measure X) (F Z0 : Set X) (Z : ℝ → Set X)
    (hFm : MeasurableSet F) (hZ0m : MeasurableSet Z0)
    (hZm : ∀ origin, MeasurableSet (Z origin))
    (hZ0 : Z0 ⊆ F) (hZ : ∀ origin, Z origin ⊆ Z0)
    (P Q : X → E) (W : ℝ → X → E)
    (hP : IntegrableOn (fun x => ‖P x‖) F μ)
    (hPQ : IntegrableOn (fun x => ‖P x-Q x‖) Z0 μ)
    (hQW : ∀ origin, IntegrableOn (fun x => ‖Q x-W origin x‖) Z0 μ)
    (hW : ∀ origin, IntegrableOn (fun x => ‖W origin x‖) (Z origin) μ)
    (R Cfixed Cbad Cmask Cboundary Ccentral : ℝ) (hR : 0 < R)
    (hfixed : (∫ x in F\Z0, ‖P x‖ ∂μ) ≤ Cfixed)
    (hbad : ∀ origin, (∫ x in Z0\Z origin, ‖P x‖ ∂μ) ≤ Cbad)
    (hmask : (∫ x in Z0, ‖P x-Q x‖ ∂μ) ≤ Cmask)
    (hcentral : ∀ origin, (∫ x in Z origin, ‖W origin x‖ ∂μ) ≤ Ccentral)
    (herror : IntervalIntegrable (fun origin => ∫ x in Z0, ‖Q x-W origin x‖ ∂μ) volume 0 R)
    (hboundary : (∫ origin in (0:ℝ)..R, ∫ x in Z0, ‖Q x-W origin x‖ ∂μ)/R ≤ Cboundary) :
    (∫ x in F, ‖P x‖ ∂μ) ≤ Cfixed+Cbad+Cmask+Cboundary+Ccentral := by
  have hpoint (origin : ℝ) (_ho : origin ∈ Icc 0 R) :
      (∫ x in F, ‖P x‖ ∂μ) ≤ Cfixed+Cbad+Cmask+Ccentral+
        (∫ x in Z0, ‖Q x-W origin x‖ ∂μ) := by
    have h := original_recovery_integral μ F Z0 (Z origin) hFm hZ0m (hZm origin)
      hZ0 (hZ origin) P Q (W origin) hP hPQ (hQW origin) (hW origin)
    linarith [hbad origin,hcentral origin]
  have h := recover_constant_from_translation_average R (∫ x in F, ‖P x‖ ∂μ)
    (Cfixed+Cbad+Cmask+Ccentral) hR _ herror hpoint
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SequenceExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional exponent comparison used in the Fourier gain. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem phaseConstant_pos : 0 < phaseConstant := by norm_num [phaseConstant]

omit [Fintype ι] in
theorem phaseParameter_range {D : ℝ} (hD : 1 ≤ D) :
    0 < phaseConstant / Real.log (2 * D) ∧
      phaseConstant / Real.log (2 * D) ≤ 1 / 3 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 * D) := by
    have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    exact htwo.trans (Real.log_le_log (by norm_num) (by linarith))
  have hpos : 0 < Real.log (2 * D) := by linarith
  refine ⟨div_pos phaseConstant_pos hpos, (div_le_iff₀ hpos).2 ?_⟩
  have hc : phaseConstant ≤ (1 / 6 : ℝ) := by norm_num [phaseConstant]
  linarith

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationContinuous
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the actual finite variation function. This permits
pointwise interval John--Nirenberg bounds, without exceptional lines. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem continuous_finiteCubicVariation {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : ℕ → X → E) (hF : ∀ n, Continuous (F n)) (N : ℕ) :
    Continuous (fun x => finiteCubicVariation (fun n => F n x) N) := by
  classical
  let g := fun (p : Fin (N + 1) → Fin (N + 1)) (x : X) =>
    if Monotone p then ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0
  have hg (p : Fin (N + 1) → Fin (N + 1)) : Continuous (g p) := by
    by_cases hp : Monotone p
    · simp only [g, ite_eq_left hp]
      exact continuous_finsetSum _ (fun i _ => ((hF _).sub (hF _)).norm.pow 3)
    · simp only [g, ite_eq_right hp]
      exact continuous_const
  have hs := Continuous.finset_sup' Finset.univ_nonempty (fun p _ => hg p)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [finiteCubicVariation, g, Finset.sup'_apply]

theorem continuous_cubicVariation {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : ℕ → X → E) (hF : ∀ n, Continuous (F n)) (N : ℕ) :
    Continuous (fun x => cubicVariation (fun n => F n x) N) := by
  apply (continuous_finiteCubicVariation F hF N).rpow_const
  intro x
  exact Or.inr (by norm_num)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem radius_nonnegative (T : SlopeBox) (z : ℝ × ℝ) : 0 ≤ T.radius z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem weight_pos (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) (z : ℝ × ℝ) :
    0 < T.weight K D z := by
  unfold weight
  have hr := T.radius_nonnegative z
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) D)
    (Real.rpow_pos_of_pos (by positivity) _)

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketDifferentiation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact vertical derivatives of packet syntheses. Coefficients stay
fixed during differentiation, including when they are analyzing integrals. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketInterval_smul (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (s : ℝ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval coeff (fun j i k t z => (s:ℂ)*wave j i k t z) a b x y =
      s • planarPacketInterval coeff wave a b x y := by
  have hs (j : Fin N) (k : κ) :
      planarPacketBand coeff (fun j i k t z => (s:ℂ)*wave j i k t z) j k x y =
        (s:ℂ)*planarPacketBand coeff wave j k x y := by
    simp only [planarPacketBand, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hp (n : ℕ) (k : κ) :
      scalarBandPartial (fun j => planarPacketBand coeff
        (fun j i k t z => (s:ℂ)*wave j i k t z) j k x) n y =
      (s:ℂ)*scalarBandPartial (fun j => planarPacketBand coeff wave j k x) n y := by
    simp only [scalarBandPartial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [hs, mul_zero]
  ext k
  change _ = (s:ℂ)*(_-_)
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp, hp, mul_sub]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the coefficient normalization after the packet concentration
estimate, preserving the original integral-defined analyzing coefficients. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketInterval_coeff_smul (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (s : ℝ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval (fun j i => s • coeff j i) wave a b x y =
      s • planarPacketInterval coeff wave a b x y := by
  rw [← planarPacketInterval_smul coeff wave s a b x y]
  have hb (j : Fin N) (k : κ) (y : ℝ) :
      planarPacketBand (fun j i => s • coeff j i) wave j k x y =
        planarPacketBand coeff (fun j i k t z => (s:ℂ)*wave j i k t z) j k x y := by
    apply Finset.sum_congr rfl
    intro i _
    change ((s:ℂ)*coeff j i k)*wave j i k y x = coeff j i k*((s:ℂ)*wave j i k y x)
    ring
  ext k
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp, scalarBandPartial, hb]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SelectedTopInterval
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of the finite band interval with the selected
scale sum, preserving the actual analyzing coefficients. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem planarPacketInterval_eq_selected
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (f : ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
    (a b : ℕ) (hab : a ≤ b) (x y : ℝ) :
    planarPacketInterval c (fun j u k t s => f j u k t s) a b x y =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => a ≤ j.val ∧ j.val < b),
        vectorPacketSynthesis (c j) (fun u k => f j u k y) x := by
  ext k
  simp only [planarPacketInterval,bandIntervalSignal,WithLp.ofLp_toLp,scalarBandPartial,
    WithLp.ofLp_sum,Finset.sum_apply,vectorPacketSynthesis,packetSynthesis_apply,
    planarPacketBand,Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hja : j.val < a
  · have hjb : j.val < b := hja.trans_le hab
    simp only [hja,hjb,ite_true, if_true,sub_self,not_le.mpr hja,false_and,ite_false, if_false,WithLp.ofLp_zero,Pi.zero_apply]
  · by_cases hjb : j.val < b
    · simp only [hja,hjb,ite_true, if_true,ite_false, if_false,sub_zero,not_lt.mp hja,true_and]
    · simp only [hja,hjb,ite_false, if_false,sub_self,and_false,WithLp.ofLp_zero,Pi.zero_apply]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopMaskApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript mask at its actual scale. Inside the prescribed
near region its error is at most a fixed constant times L^(1-A). -/

noncomputable section

namespace LipschitzHilbert

theorem topSincMask_nonneg (L A x y : ℝ) : 0 ≤ topSincMask L A x y :=
  sincProductMask_nonneg _ _ _

theorem topSincMask_le_one (L A x y : ℝ) : topSincMask L A x y ≤ 1 :=
  sincProductMask_le_one _ _ _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeightIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrability and exact area scaling for the actual decaying top weights. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

theorem planeDivide_apply (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (z : ℝ × ℝ) :
    planeDivide a b ha hb z = (z.1 / a, z.2 / b) := by
  rfl

theorem map_planeDivide (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Measure.map (planeDivide a b ha hb) (volume.prod volume) =
      (ENNReal.ofReal |a| * ENNReal.ofReal |b|) • (volume.prod volume) := by
  have hmap (c : ℝ) (hc : c ≠ 0) :
      Measure.map (fun x : ℝ => x * c⁻¹) volume = ENNReal.ofReal |c| • volume := by
    simpa only [smul_eq_mul, Module.finrank_self, pow_one, inv_inv, mul_comm] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (inv_ne_zero hc))
  change Measure.map (Prod.map (fun x => x * a⁻¹) (fun y => y * b⁻¹)) _ = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) (by fun_prop), hmap a ha, hmap b hb,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]

theorem integrable_planeDivide (f : ℝ × ℝ → ℝ)
    (hf : Integrable f (volume.prod volume)) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun z => f (planeDivide a b ha hb z)) (volume.prod volume) := by
  apply (integrable_map_equiv (planeDivide a b ha hb) f).mp
  rw [map_planeDivide]
  exact hf.smul_measure (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

theorem topProfile_nonnegative (D : ℝ) (z : ℝ × ℝ) : 0 ≤ topProfile D z :=
  Real.rpow_nonneg (by positivity) _

theorem topProfile_continuous (D : ℝ) : Continuous (topProfile D) := by
  unfold topProfile
  apply Continuous.rpow_const (by fun_prop)
  intro z
  left
  positivity

/-- The fixed normalized profile is integrable once its decay exponent exceeds
its two-dimensional domain. -/
theorem topProfile_integrable {D : ℝ} (hD : 2 < D) :
    Integrable (topProfile D) (volume.prod volume) := by
  have hd : (Module.finrank ℝ (ℝ × ℝ) : ℝ) < D := by simpa using hD
  have h := integrable_one_add_norm (μ := (volume.prod volume)) hd
  apply h.mono' (topProfile_continuous D).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (topProfile_nonnegative D z)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  simp only [Prod.norm_def, Real.norm_eq_abs]
  have hmax : max |z.1| |z.2| ≤ |z.1| + |z.2| :=
    max_le (by linarith [abs_nonneg z.2]) (by linarith [abs_nonneg z.1])
  linarith

namespace SlopeBox

theorem normalizedCoordinates_eq (T : SlopeBox) (K : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.normalizedCoordinates K hK z = (T.horizontal z / K, T.transverse z / K) := by
  ext <;> simp [normalizedCoordinates, planeDivide_apply, slopeShear, horizontal, transverse]
  <;> ring

theorem weight_eq_topProfile (T : SlopeBox) (K D : ℝ) (hK : 0 < K) (z : ℝ × ℝ) :
    T.weight K D z = 2 ^ D * topProfile D (T.normalizedCoordinates K hK z) := by
  rw [normalizedCoordinates_eq]
  simp only [weight, topProfile, radius, abs_div, abs_of_pos hK, add_div]

/-- The actual top weight is integrable, uniformly over positions and slopes. -/
theorem weight_integrable (T : SlopeBox) {K D : ℝ} (hK : 0 < K) (hD : 2 < D) :
    Integrable (T.weight K D) (volume.prod volume) := by
  have hf := integrable_planeDivide (topProfile D) (topProfile_integrable hD)
    (K * T.length) (K * T.width)
    (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne')
  have hs := (slopeShear_measurePreserving (-T.slope)).integrable_comp_of_integrable hf
  have ht := hs.comp_sub_right (T.x, T.y)
  have heq : T.weight K D = fun z => 2 ^ D *
      ((fun z => topProfile D (planeDivide (K * T.length) (K * T.width)
        (mul_ne_zero hK.ne' T.length_pos.ne') (mul_ne_zero hK.ne' T.width_pos.ne') z)) ∘
        slopeShear (-T.slope)) (z - (T.x, T.y)) := by
    funext z
    exact T.weight_eq_topProfile K D hK z
  rw [heq]
  exact ht.const_mul _

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SlopeBoxMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sinc mask in the manuscript's actual slope coordinates, with
parameters fixed uniformly before choosing the finite top family. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
namespace SlopeBox

theorem mask_continuous (T : SlopeBox) (L A : ℝ) : Continuous (T.mask L A) := by
  unfold mask topSincMask sincProductMask horizontal transverse
  apply Continuous.pow
  apply Continuous.mul
  · apply Real.continuous_sinc.comp
    fun_prop
  · apply Real.continuous_sinc.comp
    fun_prop

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translated nested angular grids and their actual eligible-top masses. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace AngularGrid

theorem index_parent (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    g.index (level + 1) slope / (g.branching : ℤ) = g.index level slope := by
  have hG : g.branching ≠ 0 := by have h := g.branching_ge_two; omega
  simpa only [index, pow_succ, mul_assoc] using
    (Int.mul_natCast_floor_div_cancel hG
      (((slope - g.origin) / g.rootWidth) * (g.branching : ℝ) ^ level))

variable {ι X : Type*}

theorem cellTops_subset_parent (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (level : ℕ) (child : ℤ) :
    g.cellTops tops slope precision cutoff (level + 1) child ⊆
      g.cellTops tops slope precision cutoff level (child / (g.branching : ℤ)) := by
  intro i hi
  obtain ⟨hit, hindex, heligible⟩ := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  apply (g.mem_cellTops _ _ _ _ _ _ _).2
  refine ⟨hit, ?_, g.eligible_parent (hp i hit) level heligible⟩
  rw [← g.index_parent level (slope i), hindex]

theorem mass_pos_of_member (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 < weight i x)
    (level : ℕ) (cell : ℤ) (x : X) {i : ι}
    (hi : i ∈ g.cellTops tops slope precision cutoff level cell) :
    0 < g.mass tops slope precision cutoff weight level cell x := by
  classical
  exact (hw i x).trans_le (Finset.single_le_sum (fun j _ => (hw j x).le) hi)

/-- An eligible top supplies a strictly positive summand on its own path. -/
theorem path_mass_pos (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 < weight i x)
    (level : ℕ) (top : ι) (htop : top ∈ tops) (heligible : g.eligible cutoff (precision top) level)
    (x : X) : 0 < g.mass tops slope precision cutoff weight level (g.index level (slope top)) x :=
  g.mass_pos_of_member tops slope precision cutoff weight hw level _ x
    ((g.mem_cellTops _ _ _ _ _ _ _).2 ⟨htop, rfl, heligible⟩)

/-- Every angular mass is a submass of the fixed total top weight. -/
theorem mass_le_total (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 ≤ weight i x)
    (level : ℕ) (cell : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight level cell x ≤ ∑ i ∈ tops, weight i x := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro i _ _
    exact hw i x

/-- Child mass is at most parent mass, with the eligibility restriction
already built into both finite sums. -/
theorem mass_le_parent (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (hw : ∀ i x, 0 ≤ weight i x) (level : ℕ) (child : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight (level + 1) child x ≤
      g.mass tops slope precision cutoff weight level (child / (g.branching : ℤ)) x := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (g.cellTops_subset_parent tops slope precision cutoff hp level child) (fun i _ _ => hw i x)

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric separation in the actual translated angular grid. -/

noncomputable section

namespace LipschitzHilbert.AngularGrid

/-- The floor assignment is exactly the half-open translated interval. -/
theorem slope_mem_cell (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    g.left level (g.index level slope) ≤ slope ∧
      slope < g.left level (g.index level slope) + g.width level := by
  let a := ((slope - g.origin) / g.rootWidth) * (g.branching : ℝ) ^ level
  have hlow := Int.floor_le a
  have hhigh := Int.lt_floor_add_one a
  have heq : g.width level * a = slope - g.origin := by
    unfold width a
    have hG : (g.branching : ℝ) ≠ 0 := by
      exact_mod_cast (show g.branching ≠ 0 by have h := g.branching_ge_two; omega)
    field_simp [g.rootWidth_pos.ne', pow_ne_zero level hG]
  have hlow' := mul_le_mul_of_nonneg_left hlow (g.width_pos level).le
  have hhigh' := mul_lt_mul_of_pos_left hhigh (g.width_pos level)
  rw [heq] at hlow' hhigh'
  change g.origin + g.width level * (⌊a⌋ : ℝ) ≤ slope ∧
    slope < g.origin + g.width level * (⌊a⌋ : ℝ) + g.width level
  constructor <;> nlinarith

theorem slope_dist_center_le (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    |slope - g.center level (g.index level slope)| ≤ g.width level / 2 := by
  obtain ⟨hl, hr⟩ := g.slope_mem_cell level slope
  unfold center
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary masses formed from actual top sets in a common angular ancestor. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem index_eq_of_add (g : AngularGrid) (base steps : ℕ) {s t : ℝ}
    (h : g.index (base + steps) s = g.index (base + steps) t) :
    g.index base s = g.index base t := by
  induction steps with
  | zero => simpa using h
  | succ steps ih =>
    apply ih
    rw [← g.index_parent (base + steps) s, ← g.index_parent (base + steps) t]
    simpa only [Nat.add_succ] using congrArg (fun a : ℤ => a / g.branching) h

theorem index_eq_of_le (g : AngularGrid) {base level : ℕ} (hle : base ≤ level)
    {s t : ℝ} (h : g.index level s = g.index level t) :
    g.index base s = g.index base t := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact g.index_eq_of_add base steps h

/-- Tops in a descendant cell remain eligible and lie in its actual ancestor. -/
theorem cellTops_subset_ancestor (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (s : ℝ) :
    g.cellTops tops slope precision cutoff level (g.index level s) ⊆
      g.cellTops tops slope precision cutoff base (g.index base s) := by
  intro i hi
  obtain ⟨hit, hindex, he⟩ := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  exact (g.mem_cellTops _ _ _ _ _ _ _).2
    ⟨hit, g.index_eq_of_le hle hindex, g.eligible_of_le (hp i hit) hle he⟩

theorem parent_subset_boundary (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (base level : ℕ) (gap s : ℝ) :
    g.cellTops tops slope precision cutoff level (g.index level s) ⊆
      g.boundaryTops tops slope precision cutoff base level gap s := by
  classical
  exact Finset.subset_union_left

theorem boundary_subset_ancestor (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (gap s : ℝ) :
    g.boundaryTops tops slope precision cutoff base level gap s ⊆
      g.cellTops tops slope precision cutoff base (g.index base s) := by
  classical
  apply Finset.union_subset
  · exact g.cellTops_subset_ancestor tops slope precision cutoff hp hle s
  · exact Finset.filter_subset _ _

/-- The union defining the boundary has no double counting. -/
theorem boundary_mass_eq (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (base level : ℕ) (gap s : ℝ) (x : X) :
    g.boundaryMass tops slope precision cutoff weight base level gap s x =
      g.mass tops slope precision cutoff weight level (g.index level s) x +
      ∑ i ∈ g.outsideNearTops tops slope precision cutoff base level gap s, weight i x := by
  classical
  apply Finset.sum_union
  apply Finset.disjoint_left.mpr
  intro i hi hnear
  have hparent := ((g.mem_cellTops _ _ _ _ _ _ _).1 hi).2.1
  exact (Finset.mem_filter.mp hnear).2.2.2 hparent

/-- The immediate child, parent, boundary and block ancestor have ordered masses. -/
theorem boundary_mass_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {base level : ℕ} (hle : base ≤ level) (gap s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (level + 1) (g.index (level + 1) s) x ≤
        g.mass tops slope precision cutoff weight level (g.index level s) x ∧
    g.mass tops slope precision cutoff weight level (g.index level s) x ≤
        g.boundaryMass tops slope precision cutoff weight base level gap s x ∧
    g.boundaryMass tops slope precision cutoff weight base level gap s x ≤
        g.mass tops slope precision cutoff weight base (g.index base s) x := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have h := g.mass_le_parent tops slope precision cutoff weight hp hw level
      (g.index (level + 1) s) x
    simpa only [g.index_parent] using h
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (g.parent_subset_boundary tops slope precision cutoff base level gap s)
      (fun i _ _ => hw i x)
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (g.boundary_subset_ancestor tops slope precision cutoff hp hle gap s)
      (fun i _ _ => hw i x)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual last eligible angular level exists for every positive
precision. Packet stopping precedes the stopping of its assigned top. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem eligible_iff_le_lastEligible (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hstart : g.eligible cutoff precision 0) (n : ℕ) :
    g.eligible cutoff precision n ↔ n ≤ g.lastEligible cutoff precision hp := by
  let h := g.exists_ineligible cutoff precision hp
  have hfirst : 0 < Nat.find h := by
    by_contra hn
    have hz : Nat.find h = 0 := by omega
    apply Nat.find_spec h
    simpa only [hz] using hstart
  constructor
  · intro hn
    by_contra hle
    have hfind : Nat.find h ≤ n := by
      change ¬n ≤ Nat.find h - 1 at hle
      omega
    exact Nat.find_spec h (g.eligible_of_le hp.le hfind hn)
  · intro hn
    have hlt : n < Nat.find h := by
      change n ≤ Nat.find h - 1 at hn
      omega
    exact Classical.not_not.mp (Nat.find_min h hlt)

theorem eligible_lastEligible (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hstart : g.eligible cutoff precision 0) :
    g.eligible cutoff precision (g.lastEligible cutoff precision hp) :=
  (g.eligible_iff_le_lastEligible cutoff precision hp hstart _).mpr le_rfl

theorem lastEligible_antitone_precision (g : AngularGrid) (cutoff p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q)
    (hstartp : g.eligible cutoff p 0) (hstartq : g.eligible cutoff q 0) :
    g.lastEligible cutoff q hq ≤ g.lastEligible cutoff p hp := by
  apply (g.eligible_iff_le_lastEligible cutoff p hp hstartp _).mp
  have hqelig := g.eligible_lastEligible cutoff q hq hstartq
  exact (mul_le_mul_of_nonneg_right hpq (by positivity)).trans hqelig

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppingScaleIntervals
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopping-level bands are intervals of the original source length
index. This is the bridge from interval concentration to summation by
parts over angular stopping levels. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem antitone_stopping_band_interval {N : ℕ} (stop : Fin N → ℕ)
    (hstop : Antitone stop) (a b : ℕ) :
    ∃ lower upper : ℕ, lower ≤ upper ∧ upper ≤ N ∧
      ∀ j : Fin N, (a ≤ stop j ∧ stop j < b) ↔ lower ≤ j.val ∧ j.val < upper := by
  let s := Finset.univ.filter (fun j : Fin N => a ≤ stop j ∧ stop j < b)
  by_cases hs : s.Nonempty
  · let lo := s.min' hs
    let hi := s.max' hs
    have hlo : lo ∈ s := s.min'_mem hs
    have hhi : hi ∈ s := s.max'_mem hs
    have hlh : lo ≤ hi := s.min'_le hi hhi
    refine ⟨lo.val, hi.val+1, by omega, by omega, ?_⟩
    intro j
    constructor
    · intro hj
      have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      have hl := s.min'_le j hjs
      have hr := s.le_max' j hjs
      exact ⟨hl, by change j.val ≤ hi.val at hr; omega⟩
    · intro hj
      have hlj : lo ≤ j := hj.1
      have hjh : j ≤ hi := by change j.val ≤ hi.val; omega
      have hstoplo := (Finset.mem_filter.mp hlo).2.2
      have hstophi := (Finset.mem_filter.mp hhi).2.1
      exact ⟨hstophi.trans (hstop hjh), (hstop hlj).trans_lt hstoplo⟩
  · refine ⟨0,0,le_rfl,Nat.zero_le _,?_⟩
    intro j
    constructor
    · intro hj
      exact False.elim (hs ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩)
    · intro hj
      omega

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem rawInterval_eq_band_sum (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    P.rawInterval coeff i lower upper x y =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper),
        P.rawBand coeff i j x y := by
  have h := planarPacketInterval_eq_selected
    (ι := fun j => Σ l : P.labels j, Item j l)
    (fun j p => coeff j p.1 p.2)
    (fun j p k t => P.raw i j p.1 p.2 k t) lower upper hlu x y
  exact h

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopLogAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic endpoint factor is absorbed by the spare decay of
an actual top weight, without any positive lower cutoff on that weight. -/

noncomputable section
namespace LipschitzHilbert

theorem bounded_weight_rpow_le_linear {h C q : ℝ} {d : ℕ}
    (hh : 0 < h) (hC : 1 ≤ C) (hhC : h ≤ C)
    (hq : 1 ≤ q) (hqd : q ≤ (d : ℝ)+1) :
    h^q ≤ C^d*h := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hbase : h^(q-1) ≤ C^d := by
    apply (Real.rpow_le_rpow hh.le hhC (by linarith : 0 ≤ q-1)).trans
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  calc
    h^q = h^((q-1)+1) := by congr 1; ring
    _ = h^(q-1)*h := by rw [Real.rpow_add hh, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hbase hh.le

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineWeightAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested line averaging against the manuscript's actual top weight. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem continuous_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) :
    Continuous (T.weight K D) := by
  have hr : Continuous (fun z => 1 + T.radius z / K) := by
    unfold radius horizontal transverse
    fun_prop
  unfold weight
  apply continuous_const.mul
  exact hr.rpow_const fun z => Or.inl (ne_of_gt (by
    have h := T.radius_nonnegative z
    positivity))

end SlopeBox

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_TileEnvelopeKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-point lattice overlap after normalization by tile area. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem tileEnvelope_measurable (a b l W : ℝ) (n : ℕ) :
    Measurable (tileEnvelope a b l W n) := by
  unfold tileEnvelope lineEnvelope
  fun_prop

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketLatticeData
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite packet family before choosing a reference direction.
There is no small-shear condition on its slopes. That condition is proved
only for the labels retained in a short reference cone. -/
noncomputable section
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F / w)

local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_actualZ (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).actualZ j l u = P.actualZ j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u +
      (oldSlope - newSlope) * P.actualX j
        (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  dsimp [SourceLabeledLattice.actualZ, actualZ, actualX, referenceFamily,
    SourceLabeledLattice.length, length]
  ring

theorem referenceFamily_physicalPacket (j : Fin N) (l : (Q).labels j)
    (u : Item j l) (k : κ) :
    (Q).physicalPacket newSlope j l u k = P.physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k := by
  let l₀ := P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l
  have hx := P.referenceFamily_actualX oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  have hz := P.referenceFamily_actualZ oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  unfold SourceLabeledLattice.physicalPacket physicalPacket
  rw [hx, hz]
  have hc : P.actualZ j l₀ u + (oldSlope - newSlope) * P.actualX j l₀ u +
      newSlope * P.actualX j l₀ u = P.actualZ j l₀ u + oldSlope * P.actualX j l₀ u := by ring
  have hs : newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope)) =
      oldSlope + P.rowSlope j l₀ := by ring
  change physicalPlanarPacket (P.profile j l₀ u k) _ _ (P.length j) P.width
    (newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope))) (P.frequency k) _ _ = _
  rw [hc, hs]

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rounded dyadic parameters in the manuscript. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem log_step_bounds {L : ℝ} (hL : 0 ≤ L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) ∧
      Real.log (step L) ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 ≤ L ^ (7 / 10 : ℝ) / (2 * Real.log 2) := by positivity
  have hlo := Nat.le_ceil (L ^ (7 / 10 : ℝ) / (2 * Real.log 2))
  have hhi := (Nat.ceil_lt_add_one hr).le
  rw [step, Real.log_pow, stepExponent, Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · have h := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : L ^ (7 / 10 : ℝ) / (2 * Real.log 2) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) := div_mul_cancel₀ _ (by positivity)
    rw [heq] at h
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : (L ^ (7 / 10 : ℝ) / (2 * Real.log 2) + 1) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
      rw [add_mul, div_mul_cancel₀ _ (by positivity), one_mul]
    rw [heq] at h
    nlinarith

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledRawEnvelope
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier-free raw bounds for the original labeled lattices, before
any bound on the total number of labels is imposed. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem raw_eq_physical_slice (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y t : ℝ) :
    P.raw i j l u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j l u k) (P.frequency k) P.scale i) y t := by
  have h := physicalPlanarPacket_jet_slice (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u+t*P.actualX j l u) (P.length j) P.width
    (t+P.rowSlope j l) (P.frequency k) P.scale y t (P.length_pos j).ne' P.width_pos.ne' i
  have hc : P.actualZ j l u+t*P.actualX j l u-t*P.actualX j l u = P.actualZ j l u := by ring
  have hd : t-(t+P.rowSlope j l) = -P.rowSlope j l := by ring
  simpa only [hc,hd,raw,physicalPacket] using h.symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceLabeledAngularErrorData
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The labeled dyadic error family formed from the original physical
packets and selectors, with an exact measure-preserving coefficient identity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item) (horder : 6 ≤ P.order)
  (t a c Cwide M Lip radius : ℝ) (E J K H : ℕ)
  (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1)
  (hC : Cwide ≤ c*(2:ℝ)^J) (hwide : 1 ≤ Cwide*((2:ℝ)^E)^4)
  (hM : 0 ≤ M) (hLip : 0 ≤ Lip) (hradius : radius ≤ K)
  (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
    (fun l => t+P.rowSlope j l) (a*(2:ℝ)^j.val) H)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (hb : ∀ j l k, Measurable (b j l k))
  (hbM : ∀ j l k s, ‖b j l k s‖ ≤ M)
  (hsupport : ∀ j l k s, b j l k s ≠ 0 → |s-(t+P.rowSlope j l)| ≤ radius*(a*(2:ℝ)^j.val))
  (hnear : ∀ j l k s, |s-t| ≤ c*(a*(2:ℝ)^j.val) →
    ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(a*(2:ℝ)^j.val)))
  (hfar : ∀ j l k s, (Cwide*((2:ℝ)^E)^4)*(a*(2:ℝ)^j.val) < |s-t| → b j l k s = 0)
  (v : ℝ×ℝ → ℝ) (hv : Measurable v)
  (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)

theorem physicalAngularError_measurable (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    Measurable (P.physicalAngularError t a b v g) := by
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro l _
  apply Finset.measurable_sum
  intro u _
  apply measurable_const.mul
  exact (tileEnvelope_measurable _ _ _ _ _).comp
    (measurable_fst.prodMk (measurable_snd.sub (measurable_fst.const_mul t)))

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analyzing coefficients for unrestricted packet lattices and their
exact transport to the local reference lattice. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_multiplier_coefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope
      (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g j l u =
    P.physicalMultiplierCoefficient oldSlope b v g j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  ext k
  simp only [SourceLabeledLattice.physicalMultiplierCoefficient,physicalMultiplierCoefficient,
    analyzingCoefficient,WithLp.ofLp_toLp]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hp := congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => f z)
    (P.referenceFamily_physicalPacket oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency j l u k)
  dsimp only [referenceSelector]
  rw [hp]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceConditions
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen main coefficients vanish outside the fixed selector cone.
Restricting the main reference family to that cone is an exact identity;
its carrier bound therefore does not inherit the wide error cone. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

/-- A finite source sum supported on the reference labels equals the
sum in the literal restricted family. -/
theorem sum_referenceLabels_of_zero {E : Type*} [AddCommMonoid E]
    (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E)
    (hzero : ∀ l, ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l →
      ∀ u, f l u = 0) :
    (∑ l : P.referenceLabels oldSlope newSlope referenceLength cone w j,
      ∑ u : Item j l, f (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have hrestrict := Equiv.sum_comp (P.referenceLabelsEquiv oldSlope newSlope referenceLength cone w j)
    (fun l => ∑ u : Item j l.val, f l.val u)
  have hz : (∑ l : {l : P.labels j //
      ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l},
      ∑ u : Item j l.val, f l.val u) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact Finset.sum_eq_zero (fun u _ => hzero l.val l.property u)
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (P.referenceCondition oldSlope newSlope referenceLength cone w j)
    (fun l : P.labels j => ∑ u : Item j l, f l u)
  rw [hz,add_zero] at hsum
  exact hrestrict.trans hsum

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceProperties
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical selector centers are invariant under recentering.
Restricting to the reference cone can only decrease their local count. -/

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physical_center (j : Fin N) (l : (Q).labels j) :
    newSlope+(Q).rowSlope j l = oldSlope+P.rowSlope j (orig j l) := by
  change newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) = _
  ring

theorem referenceFamily_localMultiplicity (j : Fin N) (d : ℝ) (M : ℕ)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) d M) :
    SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : (Q).labels j => newSlope+(Q).rowSlope j l) d M := by
  intro a
  apply (Finset.card_le_card_of_injOn (orig j) ?_ ?_).trans (hlocal a)
  · intro l hl
    obtain ⟨_,hlo,hhi⟩ := Finset.mem_filter.mp hl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · change a ≤ newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) at hlo
      change a ≤ oldSlope+P.rowSlope j (orig j l)
      linarith
    · change newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) < a+d at hhi
      change oldSlope+P.rowSlope j (orig j l) < a+d
      linarith
  · intro l _ m _ heq
    apply Subtype.ext
    exact congrArg (fun u : P.labels j => u.val) heq

theorem referenceFamily_selector_support
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (radius d : Fin N → ℝ)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ radius j*d j) :
    ∀ j (l : (Q).labels j) k s, b j (orig j l) k s ≠ 0 →
      |s-(newSlope+(Q).rowSlope j l)| ≤ radius j*d j := by
  intro j l k s hb
  rw [P.referenceFamily_physical_center oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l]
  exact hsupport j (orig j l) k s hb

theorem referenceFamily_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l)) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u :=
  P.referenceFamily_multiplier_coefficient oldSlope newSlope R cone w F hw hcone hF hwide hfrequency b v f j l u

theorem referenceFamily_alternate_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) (k : κ) :
    ((Q).withProfile (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))).physicalPacket
      newSlope j l u k = (P.withProfile alt hAlt).physicalPacket oldSlope j (orig j l) u k :=
  (P.withProfile alt hAlt).referenceFamily_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l u k

theorem referenceFamily_spectrum (cStar cEta CEta : ℝ)
    (hspectrum : ∀ j (l : P.labels j) (u : Item j l) k ξ η,
      planarAngularFourier (P.physicalPacket oldSlope j l u k) (ξ,η) ≠ 0 →
        |ξ+(oldSlope+P.rowSlope j l)*η| ≤ cStar/P.length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta) :
    ∀ j (l : (Q).labels j) (u : Item j l) k ξ η,
      planarAngularFourier ((Q).physicalPacket newSlope j l u k) (ξ,η) ≠ 0 →
        |ξ+(newSlope+(Q).rowSlope j l)*η| ≤ cStar/(Q).length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta := by
  intro j l u k ξ η hξ
  rw [P.referenceFamily_physicalPacket oldSlope newSlope R cone w F hw hcone hF hwide hfrequency j l u k] at hξ
  have h := hspectrum j (P.referenceOriginalLabel oldSlope newSlope R cone w j l) u k ξ η hξ
  have hs : newSlope+(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope R cone w j l)+
      (oldSlope-newSlope)) = oldSlope+P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope R cone w j l) := by ring
  change |ξ+(newSlope+(P.rowSlope j
    (P.referenceOriginalLabel oldSlope newSlope R cone w j l)+(oldSlope-newSlope)))*η| ≤
      cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta
  rw [hs]
  exact h

/-- A selected set supported in the reference cone has the identical
sum after the literal label restriction, including empty item fibers. -/
theorem sum_referenceFamily_selected {E : Type*} [AddCommMonoid E]
    (S : Finset P.PacketIndex) (f : P.PacketIndex → E)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1) :
    (∑ u ∈ (Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S),
      f ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) = ∑ u ∈ S, f u := by
  have hs : (Finset.univ.filter fun u : P.PacketIndex => u ∈ S) = S := by
    ext u
    simp
  conv_rhs => rw [← hs,Finset.sum_filter]
  simp only [Finset.sum_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact P.sum_referenceLabels_of_zero oldSlope newSlope R cone w j
    (fun l u => if (⟨j,⟨l,u⟩⟩ : P.PacketIndex) ∈ S then f ⟨j,⟨l,u⟩⟩ else 0)
    (by
      intro l hl u
      rw [ite_eq_right]
      exact fun hu => hl (hS ⟨j,⟨l,u⟩⟩ hu))

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledGoodQuantities
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint measurability of the actual reference quantities is needed
before weighted bad-path sets are integrated over the physical plane. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem lineEnvelope_continuous (a l : ℝ) (n : ℕ) : Continuous (lineEnvelope a l n) := by
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalMainScale_joint_continuous (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) :
    Continuous (fun z : ℝ×ℝ => P.physicalMainScale t a b v g j z.2 z.1) := by
  apply continuous_finsetSum
  intro l _
  apply continuous_finsetSum
  intro u _
  apply Continuous.mul continuous_const
  exact ((lineEnvelope_continuous _ _ _).comp continuous_fst).mul
    ((lineEnvelope_continuous _ _ _).comp continuous_snd)

theorem physicalMainSquare_joint_continuous (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    Continuous (fun z : ℝ×ℝ => P.physicalMainSquare t a b v g z.2 z.1) := by
  apply Continuous.sqrt
  exact continuous_finsetSum _ (fun j _ =>
    (P.physicalMainScale_joint_continuous t a b v g j).pow 2)

theorem physicalMainSquareOnPlane_continuous (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    Continuous (P.physicalMainSquareOnPlane t a b v g) := by
  let shear : ℝ×ℝ → ℝ×ℝ := fun z => (z.1,z.2-t*z.1)
  have hs : Continuous shear :=
    continuous_fst.prodMk (continuous_snd.sub (continuous_const.mul continuous_fst))
  have h := (P.physicalMainSquare_joint_continuous t a b v g).comp hs
  change Continuous ((fun z : ℝ×ℝ =>
    P.physicalMainSquare t a b v g z.2 z.1) ∘ shear)
  exact h

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledVariationSplit
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed masked variation uses the full original analyzing
coefficients. Its centered main part has the narrow-slot variation
bound; its angular error is bounded by the positive physical error
sum, using the carrier-free synthesis envelope. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

theorem physicalMaskedBand_physical_continuous (j : Fin N) :
    Continuous (fun z : ℝ×ℝ => P.physicalMaskedBand
      alt hAlt t b v g T L A (z.2-t*z.1) j z.1) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro l _
  apply continuous_finsetSum
  intro u _
  have hpoint : Continuous (fun z : ℝ×ℝ => (z.1,(z.2-t*z.1)+t*z.1)) := by fun_prop
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (((T j l u).mask_continuous L A).comp hpoint))).mul
    (((P.withProfile alt hAlt).physicalPacket t j l u k).continuous.comp hpoint)

theorem physicalMaskedVariation_physical_continuous :
    Continuous (fun z : ℝ×ℝ => P.physicalMaskedVariation
      alt hAlt t b v g T L A (z.2-t*z.1) z.1) := by
  apply continuous_cubicVariation _ _ N
  intro n
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using
      P.physicalMaskedBand_physical_continuous alt hAlt t b v g T L A j
  · simp only [ite_eq_right hj]
    exact continuous_const

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledGoodEvents
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable reference events for the original error, positive main
square and full masked variation. All three thresholds are fixed before
the angular path or mass cutoff is selected. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A e s r : ℝ)

theorem physicalReferenceEvent_measurable (i : Fin 3) :
    MeasurableSet (P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i) := by
  unfold physicalReferenceEvent
  split_ifs
  · exact measurableSet_le measurable_const (P.physicalAngularError_measurable t a b v g)
  · exact measurableSet_le measurable_const (P.physicalMainSquareOnPlane_continuous t a b v g).measurable
  · exact measurableSet_le measurable_const
      (P.physicalMaskedVariation_physical_continuous alt hAlt t b v g T L A).measurable

theorem physicalReferenceBad_measurable :
    MeasurableSet (P.physicalReferenceBad alt hAlt t a b v g T L A e s r) :=
  MeasurableSet.iUnion (P.physicalReferenceEvent_measurable alt hAlt t a b v g T L A e s r)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCountParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dyadic source parameters meet the counting hypotheses. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem blockCount_pos {L : ℝ} (hL : 1 < L) : 0 < blockCount L := by
  apply Nat.one_le_ceil_iff.mpr
  exact sq_pos_of_pos (Real.log_pos hL)

theorem one_lt_step {L : ℝ} (hL : 0 < L) : 1 < step L := by
  apply (Real.log_pos_iff (step_pos L).le).mp
  exact (Real.rpow_pos_of_pos hL _).trans_le (log_step_bounds hL.le).1

theorem log_branching_lower {L : ℝ} (hL : 1 < L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (branching L) := by
  have hstep := one_lt_step (zero_lt_one.trans hL)
  have hK : (1 : ℝ) ≤ blockCount L := by exact_mod_cast blockCount_pos hL
  calc
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) := (log_step_bounds (zero_lt_one.trans hL).le).1
    _ ≤ (blockCount L : ℝ) * Real.log (step L) :=
      le_mul_of_one_le_left (Real.log_nonneg hstep.le) hK
    _ = Real.log (branching L) := (Real.log_pow _ _).symm

theorem eventually_branching_ge (c : ℝ) : ∀ᶠ L : ℝ in atTop, c ≤ branching L := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).eventually_ge_atTop
      (Real.log (max c 1))] with L hL hpow
  have hmax : 0 < max c 1 := zero_lt_one.trans_le (le_max_right _ _)
  apply (le_max_left c 1).trans
  exact (Real.log_le_log_iff hmax (branching_pos L)).mp
    (hpow.trans (log_branching_lower (by linarith)))

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_ResidualBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Final source-parameter budgets for the marked and unary residual costs. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert

/-- Any fixed polynomial times the source step's negative power tends to
zero. This pays for the cumulative marked prediction losses. -/
theorem source_polynomial_step_decay (a c : ℝ) (hc : 0 < c) :
    Tendsto (fun L : ℝ => L ^ a * SourceParameters.step L ^ (-c)) atTop (𝓝 0) := by
  have hmodel : Tendsto (fun L : ℝ => L ^ a * Real.exp (-c * L ^ (7 / 10 : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / (7 / 10)) c hc).comp
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10))
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    simp only [Function.comp_apply, ← Real.rpow_mul hL]
    congr 2
    ring
  apply squeeze_zero' ?_ ?_ hmodel
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact mul_nonneg (Real.rpow_nonneg hL _)
      (Real.rpow_nonneg (SourceParameters.step_pos L).le _)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hL _)
  rw [Real.rpow_def_of_pos (SourceParameters.step_pos L)]
  apply Real.exp_le_exp.mpr
  have hlog := (SourceParameters.log_step_bounds hL).1
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSourceWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary masses and logarithmic variation along actual eligible top
paths. Every boundary uses the start of the block whose last transition
is the current level, in the shared family of all shifted groupings. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem index_center (g : AngularGrid) (level : ℕ) (cell : ℤ) :
    g.index level (g.center level cell) = cell := by
  have hG : (g.branching : ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  have heq : ((g.center level cell - g.origin) / g.rootWidth) *
      (g.branching : ℝ)^level = (cell : ℝ) + 1/2 := by
    unfold center left width
    field_simp [g.rootWidth_pos.ne', pow_ne_zero level hG]
    ring
  unfold index
  rw [heq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num

theorem boundaryTops_eq_of_cell (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) {base level : ℕ} (hle : base ≤ level)
    (gap : ℝ) {s t : ℝ} (hc : g.index (level+1) s = g.index (level+1) t) :
    g.boundaryTops tops slope precision cutoff base level gap s =
      g.boundaryTops tops slope precision cutoff base level gap t := by
  have hp := g.index_eq_of_le (Nat.le_succ level) hc
  have ha := g.index_eq_of_le (hle.trans (Nat.le_succ level)) hc
  simp only [boundaryTops, outsideNearTops, hp, ha, hc]

theorem boundaryMass_eq_of_cell (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    {base level : ℕ} (hle : base ≤ level) (gap : ℝ) {s t : ℝ}
    (hc : g.index (level+1) s = g.index (level+1) t) (x : X) :
    g.boundaryMass tops slope precision cutoff weight base level gap s x =
      g.boundaryMass tops slope precision cutoff weight base level gap t x := by
  unfold boundaryMass
  rw [g.boundaryTops_eq_of_cell tops slope precision cutoff hle gap hc]

theorem sourceBoundaryMass_path (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.sourceBoundaryMass tops slope precision cutoff weight K gap level
        (g.index (level+1) s) x =
      g.boundaryMass tops slope precision cutoff weight (level+1-K) level (gap level) s x := by
  apply g.boundaryMass_eq_of_cell tops slope precision cutoff weight (by omega)
  exact g.index_center (level+1) _

theorem sourceBoundaryMass_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (level+1) (g.index (level+1) s) x ≤
      g.sourceBoundaryMass tops slope precision cutoff weight K gap level (g.index (level+1) s) x ∧
    g.sourceBoundaryMass tops slope precision cutoff weight K gap level (g.index (level+1) s) x ≤
      g.mass tops slope precision cutoff weight (level+1-K) (g.index (level+1-K) s) x := by
  rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hK gap]
  have h := g.boundary_mass_bounds tops slope precision cutoff weight hp hw
    (by omega : level+1-K ≤ level) (gap level) s x
  exact ⟨h.1.trans h.2.1, h.2.2⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSourceAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shared source amplitude uses the packet's stopping mass and the
actual boundary mass at each transition. The assigned top supplies the
positive mass required by every logarithm along the packet's path. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] Classical.propDecidable

theorem sourceBoundaryMass_parent_le (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight level (g.index level s) x ≤
      g.sourceBoundaryMass tops slope precision cutoff weight K gap level
        (g.index (level+1) s) x := by
  rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hK gap]
  exact (g.boundary_mass_bounds tops slope precision cutoff weight hp hw
    (by omega : level+1-K ≤ level) (gap level) s x).2.1

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBoundaryLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locality of every top entering a boundary mass, including boundaries
whose block ancestor starts before the current path cell. The estimate uses
the immediate child-neighbor relation and therefore does not depend on that
ancestor's width. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

/-- Neighboring children control all slopes in those children. -/
theorem slopes_close_of_neighbors (g : AngularGrid) (level : ℕ) (gap s t : ℝ)
    (hnear : g.neighbors level gap (g.index level s) (g.index level t)) :
    |s-t| ≤ gap + 2*g.width level := by
  have hs := g.slope_dist_center_le level s
  have ht := g.slope_dist_center_le level t
  have hc : |g.center level (g.index level s)-g.center level (g.index level t)| <
      gap+g.width level := hnear
  have htriangle : |s-t| ≤ |s-g.center level (g.index level s)| +
      |g.center level (g.index level s)-g.center level (g.index level t)| +
      |g.center level (g.index level t)-t| := by
    calc
      _ = |(s-g.center level (g.index level s)) +
          (g.center level (g.index level s)-g.center level (g.index level t)) +
          (g.center level (g.index level t)-t)| := by congr 1; ring
      _ ≤ |(s-g.center level (g.index level s)) +
          (g.center level (g.index level s)-g.center level (g.index level t))| +
          |g.center level (g.index level t)-t| := abs_add_le _ _
      _ ≤ _ := add_le_add
        (abs_add_le (s-g.center level (g.index level s))
          (g.center level (g.index level s)-g.center level (g.index level t))) le_rfl
  rw [abs_sub_comm (g.center level (g.index level t)) t] at htriangle
  linarith

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMaskMotion
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual top mask preserves interval motion.  Only absolute mask
differences occur, so no nonvanishing hypothesis is imposed on the mask. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert
open PhaseCombinatorics

variable {κ : Type} [Fintype κ]

namespace SourceLabeledLattice

variable {N : ℕ} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [∀ j l, Fintype (Item j l)]

theorem rawInterval_coeff_smul (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q : ℝ) (jet : Fin 3) (lower upper : ℕ) (x y : ℝ) :
    P.rawInterval (fun j l u => q • coeff j l u) jet lower upper x y =
      q • P.rawInterval coeff jet lower upper x y := by
  exact planarPacketInterval_coeff_smul (ι := fun j => Σ l : P.labels j, Item j l)
    (fun j p => coeff j p.1 p.2) (fun j p k t s => P.raw jet j p.1 p.2 k t s)
    q lower upper x y

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePhaseParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform phase and amplitude estimates at the actual source parameters. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert

open PhaseCombinatorics

theorem phaseMu_positive_le {D p : ℝ} (hD : 1 ≤ D) (hp : 0 < p) :
    0 < phaseMu D p ∧ phaseMu D p ≤ (4 / 3 : ℝ) / p := by
  have hθ := phaseParameter_range hD
  change 0 < phaseParameter D ∧ phaseParameter D ≤ 1 / 3 at hθ
  constructor
  · exact div_pos (by linarith [hθ.1]) hp
  · exact div_le_div_of_nonneg_right (by linarith [hθ.2]) hp.le

theorem source_phaseMu_small {D L : ℝ} (hD : 1 ≤ D) (hL : 256 ≤ L) :
    0 < phaseMu D (Real.sqrt L) ∧ phaseMu D (Real.sqrt L) ≤ 1 / 12 := by
  have hroot : (16 : ℝ) ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    exact hL
  have hp : 0 < Real.sqrt L := by linarith
  have hμ := phaseMu_positive_le hD hp
  refine ⟨hμ.1, hμ.2.trans ?_⟩
  exact (div_le_iff₀ hp).mpr (by linarith)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSnapshotSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Snapshot sizes for the source prediction. The node bound retains
the original coefficient family; normalization costs only the parent mass
raised to the small phase exponent. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem SlopeBox.weight_le_two_pow (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 0 ≤ D) (z : ℝ × ℝ) : T.weight K D z ≤ (2:ℝ)^D := by
  unfold SlopeBox.weight
  have hb : 1 ≤ 1+T.radius z/K :=
    le_add_of_nonneg_right (div_nonneg (T.radius_nonnegative z) hK.le)
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr hD)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) D)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_BoundaryTelescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cancellation of boundary losses along an eligible path in §11. -/

open scoped BigOperators

namespace LipschitzHilbert

/-- Shifting a finite difference sum leaves only its two boundary blocks. -/
theorem sum_range_shift_difference (a : ℕ → ℝ) (k r : ℕ) :
    (∑ i ∈ Finset.range k, (a i - a (i + r))) =
      (∑ i ∈ Finset.range r, a i) - ∑ i ∈ Finset.range r, a (i + k) := by
  have hkr := Finset.sum_range_add a k r
  have hrk := Finset.sum_range_add a r k
  have hlen : (∑ i ∈ Finset.range (k + r), a i) =
      ∑ i ∈ Finset.range (r + k), a i := by rw [Nat.add_comm k r]
  have hs1 : (∑ i ∈ Finset.range k, a (i + r)) =
      ∑ i ∈ Finset.range k, a (r + i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm i r]
  have hs2 : (∑ i ∈ Finset.range r, a (i + k)) =
      ∑ i ∈ Finset.range r, a (k + i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm i k]
  rw [Finset.sum_sub_distrib, hs1, hs2]
  linarith

/-- The number of path levels does not enter the boundary-loss estimate.
Here `r` is the shift coming from the ratio of two angular radii. -/
theorem boundary_loss_sum_le (a loss : ℕ → ℝ) (k r : ℕ) {B : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hbound : ∀ i < r, a i ≤ B)
    (hloss : ∀ i < k, loss i ≤ a i - a (i + r)) :
    (∑ i ∈ Finset.range k, loss i) ≤ (r : ℝ) * B := by
  calc
    _ ≤ ∑ i ∈ Finset.range k, (a i - a (i + r)) :=
      Finset.sum_le_sum fun i hi => hloss i (Finset.mem_range.mp hi)
    _ = (∑ i ∈ Finset.range r, a i) - ∑ i ∈ Finset.range r, a (i + k) :=
      sum_range_shift_difference a k r
    _ ≤ ∑ i ∈ Finset.range r, a i :=
      sub_le_self _ (Finset.sum_nonneg fun i _ => ha (i + k))
    _ ≤ ∑ _i ∈ Finset.range r, B :=
      Finset.sum_le_sum fun i hi => hbound i (Finset.mem_range.mp hi)
    _ = (r : ℝ) * B := by simp

end LipschitzHilbert

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed residual collection is grouped by stopping level in the
unary recurrence and by packet length in the reference-line variation.
Antitone stopping transports every disjoint collection of level bands
to disjoint length bands. Empty bands contribute zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

/-- Exact regrouping by stopping levels for any fixed packet subset. -/
theorem sum_packet_stopping_fibers {σ E : Type*} [AddCommMonoid E]
    (Q : Finset σ) (stop : σ → ℕ) (value : σ → E) (a b : ℕ) :
    (∑ k ∈ Finset.Ico a b, ∑ q ∈ Q.filter (fun q => stop q = k), value q) =
      ∑ q ∈ Q.filter (fun q => a ≤ stop q ∧ stop q < b), value q := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : stop q ∈ Finset.Ico a b
  · rw [Finset.sum_eq_single_of_mem (stop q) hq]
    · simp only [ite_true, if_true,ite_eq_left (Finset.mem_Ico.mp hq)]
    · intro k _ hk
      exact ite_eq_right (Ne.symm hk)
  · rw [Finset.sum_eq_zero]
    · exact (ite_eq_right (fun h => hq (Finset.mem_Ico.mpr h))).symm
    · intro k hk
      exact ite_eq_right (fun heq => hq (by simpa only [heq] using hk))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledStoppingVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original masked physical packets, grouped by their actual stopping
levels, have the same fixed length-variation bound used in the reference
event. This includes clamped prefixes and every disjoint unary run. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

theorem physicalMaskedValue_length_sum (y x : ℝ) (j : Fin N) :
    (∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => q.1 = j),
      P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x) q) =
        P.physicalMaskedBand alt hAlt t b v g T L A y j x := by
  classical
  rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [ite_true, if_true]
    ext k
    simp only [Fintype.sum_sigma,physicalMaskedValue,physicalMaskedBand,
      WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]
  · intro k _ hkj
    simp only [hkj,ite_false, if_false,Finset.sum_const_zero]
  · simp

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalGoodPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted good-path construction for actual physical reference
packets. A reference bundle only packages the original formulas; it has
no probabilistic or path estimate as a field. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert

namespace PhysicalReferenceData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PhysicalReferenceData N κ Label Item)

theorem bad_measurable (L A e s r : ℝ) : MeasurableSet (P.bad L A e s r) :=
  P.family.physicalReferenceBad_measurable P.alternate P.alternate_bound P.slope P.angle
    P.selector P.direction P.test P.packetTop L A e s r

end PhysicalReferenceData

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParentReferenceEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference events at the path-top slope keep the original packets and
selectors. The angular mesh is w/topLength, independently of the exponent
used in the path weights. One parent event and all continuing-shift events
form a single finite, phase-independent union. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

section Union
variable {ι : Type*} {N K : ℕ} {κ : Type} {Label : Fin N → Type}
  {Item : ∀ j, Label j → Type} [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem parentShiftReference_card_le (L : ℝ) (hL : 2 ≤ L) (hK : (K:ℝ) ≤ L^2) :
    ((Finset.univ : Finset (Option (Fin K))).card:ℝ) ≤ L^3 := by
  simp only [Finset.card_univ,Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  nlinarith [sq_nonneg L]

end Union
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataParentReference
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual data at a selected reference uses only its local cone. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (packetTop : ∀ j (l : P.labels j), Item j l → SlopeBox)

theorem recenteredReferenceData_short (j : Fin N)
    (l : (P.recenteredReferenceData alt hAlt oldSlope newSlope R cone w F hw hcone hF hwide
      hfrequency b v f packetTop).family.labels j) :
    (P.recenteredReferenceData alt hAlt oldSlope newSlope R cone w F hw hcone hF hwide
      hfrequency b v f packetTop).family.length j ≤ R :=
  (P.referenceLabel_bounds oldSlope newSlope R cone w j l).1

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataRecenteredSelector
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selector mesh and physical centers survive exact recentering.
Only selected items enter the packet-top and mask-cone conclusions. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem reference_angular_mesh (w : ℝ) (j : Fin N) :
    (w/P.topLength)*(2:ℝ)^j.val = w/P.length j := by
  unfold length
  field_simp

theorem reference_normalized_localMultiplicity
    (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w) (M : ℕ)
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) M) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : Q.labels j => newSlope+Q.rowSlope j l)
      ((w/P.topLength)*(2:ℝ)^j.val) M := by
  intro Q j
  rw [P.reference_angular_mesh w j]
  exact P.referenceFamily_localMultiplicity oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j (w/P.length j) M (hlocal j)

theorem reference_normalized_selector_support
    (oldSlope newSlope R cone w F radius : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ radius*(w/P.length j)) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    ∀ j (l : Q.labels j) k s, b j (orig j l) k s ≠ 0 →
      |s-(newSlope+Q.rowSlope j l)| ≤ radius*((w/P.topLength)*(2:ℝ)^j.val) := by
  intro Q orig j l k s hs
  rw [P.reference_angular_mesh w j]
  exact P.referenceFamily_selector_support oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency b (fun _ => radius) (fun j => w/P.length j)
    hsupport j l k s hs

theorem reference_normalized_selector_motion
    (oldSlope newSlope R cone w F Lip : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hmotion : ∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    ∀ j (l : Q.labels j) k s, ‖b j (orig j l) k s-b j (orig j l) k newSlope‖ ≤
      Lip*(|s-newSlope|/((w/P.topLength)*(2:ℝ)^j.val)) := by
  intro Q orig j l k s
  rw [P.reference_angular_mesh w j]
  exact hmotion j (orig j l) k s newSlope

theorem reference_alt_spectrum
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (oldSlope newSlope R cone w F cStar cEta CEta : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (hspectrum : ∀ j l u k xi eta,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    ∀ j (l : Q.labels j) u k xi eta,
      planarAngularFourier ((Q.withProfile (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l))).physicalPacket newSlope j l u k) (xi,eta) ≠ 0 →
      |xi+(newSlope+Q.rowSlope j l)*eta| ≤ cStar/Q.length j ∧
        cEta ≤ w*eta ∧ w*eta ≤ CEta := by
  intro Q orig j l u k xi eta hxi
  exact (P.withProfile alt hAlt).referenceFamily_spectrum oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency cStar cEta CEta hspectrum j l u k xi eta hxi

theorem reference_selector_far
    (oldSlope newSlope R cone w F radius cutoff : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ radius*(w/P.length j))
    (hcutoff : radius+cone ≤ cutoff) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    ∀ j (l : Q.labels j) k s, cutoff*((w/P.topLength)*(2:ℝ)^j.val) < |s-newSlope| →
      b j (orig j l) k s = 0 := by
  intro Q orig j l k s hs
  by_contra hn
  have hb := hsupport j (orig j l) k s hn
  have hl := (P.referenceLabel_bounds oldSlope newSlope R cone w j l).2
  have hdist : |(oldSlope+P.rowSlope j (orig j l))-newSlope| ≤ cone*(w/P.length j) := by
    calc
      _ = |P.rowSlope j (orig j l)+(oldSlope-newSlope)| := by congr 1; ring
      _ ≤ cone*w/P.length j := hl
      _ = _ := by ring
  have ht := abs_sub_le s (oldSlope+P.rowSlope j (orig j l)) newSlope
  rw [P.reference_angular_mesh w j] at hs
  have hm := mul_le_mul_of_nonneg_right hcutoff (div_pos hw (P.length_pos j)).le
  have hle : |s-newSlope| ≤ cutoff*(w/P.length j) := by
    calc
      _ ≤ _ := ht
      _ ≤ radius*(w/P.length j)+cone*(w/P.length j) := add_le_add hb hdist
      _ = (radius+cone)*(w/P.length j) := by ring
      _ ≤ _ := hm
  exact (not_lt_of_ge hle) hs

theorem reference_selector_active_separation
    (oldSlope newSlope R cone w F cb Cb : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hactive : ∀ j l k s, b j l k s ≠ 0 →
      cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
        |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    ∀ j (l : Q.labels j), (∃ k, b j (orig j l) k newSlope ≠ 0) →
      cb*w/Q.length j ≤ |Q.rowSlope j l| ∧ |Q.rowSlope j l| ≤ Cb*w/Q.length j := by
  intro Q orig j l hl
  obtain ⟨k,hk⟩ := hl
  have h := hactive j (orig j l) k newSlope hk
  have heq : newSlope-(oldSlope+P.rowSlope j (orig j l)) =
      -(P.rowSlope j (orig j l)+(oldSlope-newSlope)) := by ring
  simpa only [Q,referenceFamily,heq,abs_neg,length,SourceLabeledLattice.length] using h

theorem reference_selected_mask_cone
    {τ : Type*} (T : τ → SlopeBox) (packets : Finset P.PacketIndex)
    (assigned : P.PacketIndex → τ)
    (oldSlope newSlope R cone w F C Cb : ℝ) (hw : 0 < w)
    (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (hangle : ∀ u ∈ packets,
      |oldSlope+P.rowSlope u.1 u.2.1-(T (assigned u)).slope| ≤ C*(w/P.length u.1))
    (hwidth : ∀ u ∈ packets, (Cb+C)*w ≤ (T (assigned u)).width)
    (j : Fin N)
    (l : (P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency).labels j)
    (u : Item j l)
    (hmem : (⟨j,⟨P.referenceOriginalLabel oldSlope newSlope R cone w j l,u⟩⟩ : P.PacketIndex) ∈ packets)
    (hactive : |(P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency).rowSlope j l| ≤
      Cb*w/P.length j) :
    |newSlope-(T (assigned ⟨j,⟨P.referenceOriginalLabel oldSlope newSlope R cone w j l,u⟩⟩)).slope| ≤
      (T (assigned ⟨j,⟨P.referenceOriginalLabel oldSlope newSlope R cone w j l,u⟩⟩)).width/P.length j := by
  let orig := P.referenceOriginalLabel oldSlope newSlope R cone w j l
  have ha := hangle ⟨j,⟨orig,u⟩⟩ hmem
  have hw' := hwidth ⟨j,⟨orig,u⟩⟩ hmem
  have heq : newSlope-(oldSlope+P.rowSlope j orig) =
      -(P.rowSlope j orig+(oldSlope-newSlope)) := by ring
  have hb : |newSlope-(oldSlope+P.rowSlope j orig)| ≤ Cb*w/P.length j := by
    simpa only [heq,abs_neg,referenceFamily] using hactive
  have ht := abs_sub_le newSlope (oldSlope+P.rowSlope j orig)
    (T (assigned ⟨j,⟨orig,u⟩⟩)).slope
  have hm := div_le_div_of_nonneg_right hw' (P.length_pos j).le
  change |newSlope-(T (assigned ⟨j,⟨orig,u⟩⟩)).slope| ≤ _
  calc
    _ ≤ _ := ht
    _ ≤ Cb*w/P.length j+C*(w/P.length j) := add_le_add hb ha
    _ = (Cb+C)*w/P.length j := by ring
    _ ≤ _ := hm

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictableDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial bounds for the source predictable-motion
coefficient, before its dyadic gain is absorbed. -/

noncomputable section
namespace LipschitzHilbert

theorem source_blockCount_le_square {L : ℝ} (hL : 5 ≤ L) :
    (SourceParameters.blockCount L : ℝ) ≤ L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlog : Real.log L ≤ 2*Real.sqrt L := by
    have hb := Real.log_le_rpow_div hL0 (by norm_num : (0:ℝ)<1/2)
    rw [← Real.sqrt_eq_rpow] at hb
    linarith
  have hsq : Real.log L^2 ≤ 4*L := by
    have ht := pow_le_pow_left₀ hlog0 hlog 2
    have hr := Real.sq_sqrt hL0
    nlinarith
  have hceil : (SourceParameters.blockCount L : ℝ) ≤ Real.log L^2+1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log L))).le
  exact hceil.trans (by nlinarith)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mask in §4 is dominated by the actual hierarchy weight with
dilation `L^(A+2)`. Consequently the negative weight power in every
residual coefficient costs at most one, uniformly in the spatial point. -/

noncomputable section
namespace LipschitzHilbert

theorem topSincMask_abs_le_one (L A x y : ℝ) : |topSincMask L A x y| ≤ 1 := by
  simpa only [abs_of_nonneg (topSincMask_nonneg L A x y)] using
    topSincMask_le_one L A x y

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceAngularScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Carrier spread and Fourier separation at the actual source block windows. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

namespace AngularGrid

theorem sourceGap_pos (g : AngularGrid) (L : ℝ) (child : ℕ) :
    0 < g.sourceGap L child :=
  mul_pos (Real.rpow_pos_of_pos (SourceParameters.step_pos L) _) (g.width_pos child)

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftedScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shifted angular blocks meet the source scale conditions.
The first block is included with its original shorter length. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

/-- The ratio of actual angular widths is exactly the iterated step. -/
theorem source_width_ratio (g : AngularGrid) (L : ℝ) {lower upper : ℕ}
    (hle : lower ≤ upper) (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    g.width lower = SourceParameters.step L^(upper-lower)*g.width upper := by
  have hp : SourceParameters.step L^upper =
      SourceParameters.step L^lower*SourceParameters.step L^(upper-lower) := by
    rw [← pow_add,Nat.add_sub_of_le hle]
  unfold width
  rw [hbranch,hp]
  field_simp [(SourceParameters.step_pos L).ne']

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAssignedStoppedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported assigned-top estimates apply to the original individual
physical packets. These identities retain their analyzing coefficients,
alternate profiles, stopping levels, masks and source transitions. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- A constant top mask can be placed in the raw coefficients exactly. -/
theorem physicalMaskedBand_const_eq_rawBand (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (T : SlopeBox) (L A : ℝ)
    (z : ℝ×ℝ) (j : Fin N) :
    P.physicalMaskedBand alt hAlt t b v f (fun _ _ _ => T) L A (z.2-t*z.1) j z.1 =
      (P.withProfile alt hAlt).rawBand
        (fun j l u => T.mask L A z • P.physicalMultiplierCoefficient t b v f j l u)
        0 j z.1 (z.2-t*z.1) := by
  ext k
  have hpoint : (z.1,(z.2-t*z.1)+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  simp only [physicalMaskedBand,rawBand,vectorPacketSynthesis,packetSynthesis_apply,
    WithLp.ofLp_toLp,Fintype.sum_sigma,hpoint]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro u _
  have hp := congrArg (fun f : SchwartzMap ℝ ℂ => f z.1)
    ((P.withProfile alt hAlt).raw_eq_physical_slice 0 j l u k (z.2-t*z.1) t)
  change (P.withProfile alt hAlt).raw 0 j l u k (z.2-t*z.1) z.1 =
    (P.withProfile alt hAlt).physicalPacket t j l u k (z.1,(z.2-t*z.1)+t*z.1) at hp
  rw [hpoint] at hp
  simp only [PiLp.smul_apply,Complex.real_smul,hp]
  ring

variable (P : SourceLabeledLattice N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

local notation "orig" => assignedReferenceOriginalLabel P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

local notation "alts" => assignedReferenceAlternate P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt

include hAlt in
theorem assignedReferenceAlternate_bound (top : τ) (j : Fin N) (l : (Q top).labels j)
    (u : P.AssignedTopItem packets assigned j l) (k : κ) :
    planarProfileConstant (alts top j l u k) (2*(Q top).order) ≤ (Q top).profileBound :=
  hAlt j (orig top j l) u.val k

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's boundary radius is G^(-1/4) times the parent width.
At a last transition this is exactly G^(3/4) times the child width. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

theorem sourceBoundaryGap_pos (g : AngularGrid) (L : ℝ) (level : ℕ) :
    0 < g.sourceBoundaryGap L level :=
  mul_pos (Real.rpow_pos_of_pos (SourceParameters.step_pos L) _) (g.width_pos level)

theorem sourceBoundaryGap_eq_sourceGap (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) (level : ℕ) :
    g.sourceBoundaryGap L level = g.sourceGap L (level+1) := by
  have hw := g.source_width_ratio L (Nat.le_succ level) hbranch
  change g.width level = SourceParameters.step L^((level+1)-level)*g.width (level+1) at hw
  simp only [Nat.add_sub_cancel_left,pow_one] at hw
  have hp : SourceParameters.step L^(-(1/4:ℝ))*SourceParameters.step L =
      SourceParameters.step L^(3/4:ℝ) := by
    calc
      _ = SourceParameters.step L^(-(1/4:ℝ))*SourceParameters.step L^(1:ℝ) := by
        rw [Real.rpow_one]
      _ = SourceParameters.step L^(-(1/4:ℝ)+1) :=
        (Real.rpow_add (SourceParameters.step_pos L) _ _).symm
      _ = _ := by norm_num
  rw [sourceBoundaryGap,hw,← mul_assoc,hp]
  rfl

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataActualReferenceEvents
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual parent-square and continuing-path reference events of the
source packet family. The union is independent of every complex phase. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (L oldSlope C w F : ℝ) (hw : 0 < w) (hC : 0 ≤ C) (hF : 0 ≤ F)
  (hwide : ∀ i : Option (Fin (SourceParameters.blockCount L)),
    (C+(SourceParameters.branching L)^(if i.isNone then 3 else 2))*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (g : AngularGrid) (tops : Finset τ) (T : τ → SlopeBox)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (hKb : 0 < SourceParameters.blockCount L)

theorem actualReferenceBad_measurable (maskExponent q : ℝ) (top : τ) :
    MeasurableSet (P.actualReferenceBad alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
      b v f g tops T packets assigned hKb maskExponent q top) :=
  MeasurableSet.iUnion fun i =>
    ((P.actualReferenceData alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
      b v f T assigned top i).restrictPackets
      (P.actualReferenceSelection alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
        b v f g tops T packets assigned hKb top i)).bad_measurable _ _ _ _ _

theorem actualReferencePacketSet_subset (top : τ)
    (i : Option (Fin (SourceParameters.blockCount L))) :
    P.actualReferencePacketSet L oldSlope C w hw g tops T packets assigned hKb top i ⊆ packets := by
  cases i with
  | none => exact Finset.filter_subset _ _
  | some i => exact Finset.filter_subset _ _

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataSelectedSum
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact synthesis and separated-energy identities for the selected
reference lattice, with its cost expressed only in the original fixed
profile bounds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem referenceEnvelopeConstant_pos :
    0<P.referenceEnvelopeConstant := by
  have hp := P.profileBound_pos
  have hr : 0<P.ratioBound := zero_lt_one.trans_le P.ratioBound_ge_one
  unfold referenceEnvelopeConstant
  positivity

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReferenceWindowBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The large parent reference cone is still inside the B^4 window used
by the angular-error estimate. All constants here precede the packet family. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.SourceParameters

theorem reference_window_budget {B C radius cone : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hradius : 0 ≤ radius) (hcone : cone ≤ C+B^3) :
    radius+cone ≤ (C+radius+1)*B^4 := by
  have hp : B^3 ≤ B^4 := pow_le_pow_right₀ hB (by norm_num)
  have hfour : 1 ≤ B^4 := one_le_pow₀ hB
  have hc := mul_le_mul_of_nonneg_left hfour (add_nonneg hC hradius)
  nlinarith

theorem branching_eq_two_pow_product (L : ℝ) :
    branching L = (2:ℝ)^(stepExponent L*blockCount L) := by
  exact (pow_mul (2:ℝ) (stepExponent L) (blockCount L)).symm

theorem branching_ge_one (L : ℝ) : 1 ≤ branching L :=
  one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))

theorem exists_reference_window_index (C radius : ℝ) :
    ∃ J : ℕ, C+radius+1 ≤ (2:ℝ)^J := by
  obtain ⟨J,hJ⟩ := pow_unbounded_of_one_lt (C+radius+1) (by norm_num : (1:ℝ) < 2)
  exact ⟨J,hJ.le⟩

theorem eventually_reference_mask_width (C Cb : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ w W : ℝ, 0 ≤ w → branching L^2*w ≤ W → (Cb+C)*w ≤ W := by
  filter_upwards [eventually_branching_ge (max 1 (Cb+C))] with L hL
  intro w W hw hW
  have hB : 1 ≤ branching L := (le_max_left _ _).trans hL
  have hsize : Cb+C ≤ branching L^2 :=
    ((le_max_right _ _).trans hL).trans (le_self_pow₀ hB (by norm_num))
  exact (mul_le_mul_of_nonneg_right hsize hw).trans hW

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataRecenteredReferenceConditions
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original spectra, selectors and assigned packet geometry imply every
local hypothesis of the selected-reference tail theorem after recentering.
The selected packet set may have empty fibers and arbitrary finite support. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem recentered_reference_conditions
    (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (L q oldSlope newSlope referenceLength cone w F Cwide radius Lip cStar cEta CEta cb Cb C : ℝ)
    (E Jcut K Hlabels : ℕ)
    (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (horder : 6 ≤ P.order) (hP : P.referenceEnvelopeConstant ≤ L^q)
    (hwindow : Cwide ≤ (2:ℝ)^Jcut) (hwideError : 1 ≤ Cwide*((2:ℝ)^E)^4)
    (hradius : radius ≤ K) (hcutoff : radius+cone ≤ Cwide*((2:ℝ)^E)^4)
    (hE : E = SourceParameters.stepExponent L*SourceParameters.blockCount L)
    (hbandWidth : Cb*w ≤ P.width)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ radius*(w/P.length j))
    (hmotion : ∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j)))
    (hlocal : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hlabels)
    (hactive : ∀ j l k s, b j l k s ≠ 0 →
      cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
        |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (hf : Measurable f) (hf1 : ∀ z, ‖f z‖ ≤ 1)
    (hspectrum : ∀ j l u k xi eta,
      planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (haltSpectrum : ∀ j l u k xi eta,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
          cEta ≤ w*eta ∧ w*eta ≤ CEta)
    (T : τ → SlopeBox) (packets S : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (hS : S ⊆ packets)
    (hlength : ∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length)
    (hangle : ∀ u ∈ packets,
      |oldSlope+P.rowSlope u.1 u.2.1-(T (assigned u)).slope| ≤ C*(w/P.length u.1))
    (hwidth : ∀ u ∈ packets, (Cb+C)*w ≤ (T (assigned u)).width) :
    let R := P.recenteredReferenceData alt hAlt oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency b v f (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩))
    let selected := P.recenteredReferenceSelection oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency S
    6 ≤ R.family.order ∧ R.family.absoluteConstant ≤ L^q ∧ R.slope = newSlope ∧
    ∃ (c Cwide' radius' : ℝ) (E' Jcut' : ℕ) (w' : ℝ),
      0 < R.angle ∧ 0 < c ∧ c ≤ 1 ∧ Cwide' ≤ c*(2:ℝ)^Jcut' ∧
      1 ≤ Cwide'*((2:ℝ)^E')^4 ∧ radius' ≤ K ∧
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : R.family.labels j => R.slope+R.family.rowSlope j l)
        (R.angle*(2:ℝ)^j.val) Hlabels) ∧
      (∀ j l k, Measurable (R.selector j l k)) ∧
      (∀ j l k s, ‖R.selector j l k s‖ ≤ 1) ∧
      (∀ j l k s, R.selector j l k s ≠ 0 →
        |s-(R.slope+R.family.rowSlope j l)| ≤ radius'*(R.angle*(2:ℝ)^j.val)) ∧
      (∀ j l k s, |s-R.slope| ≤ c*(R.angle*(2:ℝ)^j.val) →
        ‖R.selector j l k s-R.selector j l k R.slope‖ ≤
          Lip*(|s-R.slope|/(R.angle*(2:ℝ)^j.val))) ∧
      (∀ j l k s, (Cwide'*((2:ℝ)^E')^4)*(R.angle*(2:ℝ)^j.val) < |s-R.slope| →
        R.selector j l k s = 0) ∧
      Measurable R.direction ∧ Measurable R.test ∧ (∀ z, ‖R.test z‖ ≤ 1) ∧
      Jcut' ≤ Jcut ∧ E' = SourceParameters.stepExponent L*SourceParameters.blockCount L ∧
      0 < w' ∧ Cb*w' ≤ R.family.width ∧ (∀ k, |R.family.frequency k| ≤ F/w') ∧
      (∀ j l u k xi eta,
        planarAngularFourier (R.family.physicalPacket R.slope j l u k) (xi,eta) ≠ 0 →
          |xi+(R.slope+R.family.rowSlope j l)*eta| ≤ cStar/R.family.length j ∧
            cEta ≤ w'*eta ∧ w'*eta ≤ CEta) ∧
      (∀ j l u k xi eta,
        planarAngularFourier ((R.family.withProfile R.alternate R.alternate_bound).physicalPacket
          R.slope j l u k) (xi,eta) ≠ 0 →
          |xi+(R.slope+R.family.rowSlope j l)*eta| ≤ cStar/R.family.length j ∧
            cEta ≤ w'*eta ∧ w'*eta ≤ CEta) ∧
      (∀ j l, (∃ k, R.selector j l k R.slope ≠ 0) →
        cb*w'/R.family.length j ≤ |R.family.rowSlope j l| ∧
          |R.family.rowSlope j l| ≤ Cb*w'/R.family.length j) ∧
      (∀ j l u, (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ selected →
        R.family.length j ≤ (R.packetTop j l u).length) ∧
      (∀ j (_l : R.family.labels j), R.family.length j ≤ referenceLength) ∧
      (∀ j l u, (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ selected →
        R.family.length j ≤ referenceLength →
        |R.family.rowSlope j l| ≤ Cb*w'/R.family.length j →
        |R.slope-(R.packetTop j l u).slope| ≤ 1*(R.packetTop j l u).width/R.family.length j) := by
  intro R selected
  have hmem (j : Fin N) (l : R.family.labels j) (u : Item j l)
      (hu : (⟨j,⟨l,u⟩⟩ : R.family.PacketIndex) ∈ selected) :
      (⟨j,⟨P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l,u⟩⟩ : P.PacketIndex) ∈ packets :=
    hS (Finset.mem_filter.mp hu).2
  refine ⟨horder,hP,rfl,1,Cwide,radius,E,Jcut,w,div_pos hw P.topLength_pos,
    by norm_num,le_rfl,?_,hwideError,hradius,?_,?_,?_,?_,?_,?_,hv,hf,hf1,
    le_rfl,hE,hw,hbandWidth,hfrequency,?_,?_,?_,?_,?_,?_⟩
  · simpa only [one_mul] using hwindow
  · exact P.reference_normalized_localMultiplicity oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency Hlabels hlocal
  · intro j l k
    exact hb j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) k
  · intro j l k s
    exact hb1 j (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) k s
  · exact P.reference_normalized_selector_support oldSlope newSlope referenceLength cone w F radius
      hw hcone hF hwide hfrequency b hsupport
  · intro j l k s _
    exact P.reference_normalized_selector_motion oldSlope newSlope referenceLength cone w F Lip
      hw hcone hF hwide hfrequency b hmotion j l k s
  · exact P.reference_selector_far oldSlope newSlope referenceLength cone w F radius
      (Cwide*((2:ℝ)^E)^4) hw hcone hF hwide hfrequency b hsupport hcutoff
  · exact P.referenceFamily_spectrum oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency cStar cEta CEta hspectrum
  · exact P.reference_alt_spectrum alt hAlt oldSlope newSlope referenceLength cone w F
      cStar cEta CEta hw hcone hF hwide hfrequency haltSpectrum
  · exact P.reference_selector_active_separation oldSlope newSlope referenceLength cone w F
      cb Cb hw hcone hF hwide hfrequency b hactive
  · intro j l u hu
    exact hlength _ (hmem j l u hu)
  · exact P.recenteredReferenceData_short alt hAlt oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency b v f (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩))
  · intro j l u hu _ ha
    rw [one_mul]
    exact P.reference_selected_mask_cone T packets assigned oldSlope newSlope referenceLength
      cone w F C Cb hw hcone hF hwide hfrequency hangle hwidth j l u (hmem j l u hu) ha

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataActualReferenceArea
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal parent-square and continuing-path reference events have
one common weighted bad-mass and area bound. Only original physical packet
spectra, selectors, and assigned-top geometry enter the hypotheses. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_actual_reference_area
    (hVariation : LepingleInput)
    (D weightPower q A F cStar cEta CEta cb Cb C Lip : ℝ) (K Hlabels : ℕ)
    (hD : 2 < D) (hq : 0 ≤ q) (hA : 1 < A) (hF : 0 ≤ F)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hC : 0 ≤ C) (hLip : 0 ≤ Lip)
    (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop, ∀ (Kw : ℝ), 1 ≤ Kw → Kw ≤ L^weightPower →
    ∀ (N : ℕ) (κ τ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item), 6 ≤ P.order → P.referenceEnvelopeConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (oldSlope w : ℝ) (hw : 0 < w)
      (hwide : ∀ i : Option (Fin (SourceParameters.blockCount L)),
        (C+(SourceParameters.branching L)^(if i.isNone then 3 else 2))*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w), Cb*w ≤ P.width →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ (K:ℝ)*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hlabels) →
      (∀ j l k s, b j l k s ≠ 0 →
        cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
          |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
      (∀ j l u k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
            cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
            cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    ∀ (g : AngularGrid) (tops : Finset τ) (T : τ → SlopeBox)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (hKb : 0 < SourceParameters.blockCount L),
      (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
      (∀ u ∈ packets,
        |oldSlope+P.rowSlope u.1 u.2.1-(T (assigned u)).slope| ≤ C*(w/P.length u.1)) →
      (∀ u ∈ packets, (SourceParameters.branching L)^2*w ≤ (T (assigned u)).width) →
    ∀ (base : Set (ℝ×ℝ)), MeasurableSet base →
      let bad := P.actualReferenceBad alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
        b v f g tops T packets assigned hKb A q
      let good := sourceGoodPathSet base tops (fun t => (T t).weight Kw D) bad L
      Integrable (sourceBadPathMass tops (fun t => (T t).weight Kw D) bad) (volume.prod volume) ∧
      (∫ z, sourceBadPathMass tops (fun t => (T t).weight Kw D) bad z ∂volume.prod volume) ≤
        (∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-10*L) ∧
      MeasurableSet good ∧ good ⊆ base ∧
      (volume.prod volume) (base \ good) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L)) ∧
      ∀ t, ∀ z ∉ bad t, ∀ i : Option (Fin (SourceParameters.blockCount L)),
        z ∉ ((P.actualReferenceData alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
          b v f T assigned t i).restrictPackets
          (P.actualReferenceSelection alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
            b v f g tops T packets assigned hKb t i)).bad
              L A (q+8) (2*q+9) (2*q+11) := by
  obtain ⟨J,hJ⟩ := SourceParameters.exists_reference_window_index C (K:ℝ)
  filter_upwards [eventually_polynomial_uniform_selected_reference_good_path
      hVariation D 3 weightPower q A F cStar cEta CEta cb Cb 1 Lip K Hlabels J
      hD hq hA hF hcStar hcEta hCEta hcb hCb (by norm_num) hLip hgap,
    SourceParameters.eventually_reference_mask_width C Cb,
    eventually_ge_atTop (5:ℝ)] with L harea hmask hL
  intro Kw hKw hKwL N κ τ Label Item _ _ P horder hP alt hAlt oldSlope w hw hwide
    hfrequency hband b hb hb1 hsupport hmotion hlocal hactive v hv f hf hf1 hspectrum haltSpectrum
    g tops T packets assigned hKb hlength hangle hwidth base hbase bad good
  let E := SourceParameters.stepExponent L*SourceParameters.blockCount L
  let B := SourceParameters.branching L
  have hB : 1 ≤ B := SourceParameters.branching_ge_one L
  have hBpow : B = (2:ℝ)^E := SourceParameters.branching_eq_two_pow_product L
  have hB4 : 1 ≤ B^4 := one_le_pow₀ hB
  have hCwide : 1 ≤ C+(K:ℝ)+1 := by linarith [show (0:ℝ) ≤ (K:ℝ) from Nat.cast_nonneg K]
  have hwideError : 1 ≤ (C+(K:ℝ)+1)*((2:ℝ)^E)^4 := by
    rw [← hBpow]
    exact one_le_mul_of_one_le_of_one_le hCwide hB4
  have hwidth' (u) (hu : u ∈ packets) : (Cb+C)*w ≤ (T (assigned u)).width :=
    hmask w _ hw.le (hwidth u hu)
  let R := P.actualReferenceData alt hAlt L oldSlope C w F hw hC hF hwide hfrequency b v f T assigned
  let Q := P.actualReferenceSelection alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
    b v f g tops T packets assigned hKb
  have hdata (t : τ) (_ht : t ∈ tops) (i : Option (Fin (SourceParameters.blockCount L))) :=
    P.recentered_reference_conditions alt hAlt L q oldSlope (T t).slope (T t).length
      (C+B^(if i.isNone then 3 else 2)) w F (C+(K:ℝ)+1) K Lip cStar cEta CEta cb Cb C
      E J K Hlabels hw (add_nonneg hC (pow_nonneg (le_trans zero_le_one hB) _)) hF
      (hwide i) hfrequency horder hP hJ hwideError le_rfl
      (by
        rw [← hBpow]
        apply SourceParameters.reference_window_budget hB hC (Nat.cast_nonneg K)
        apply add_le_add le_rfl
        apply pow_le_pow_right₀ hB
        split <;> omega)
      rfl hband b hb hb1 hsupport hmotion hlocal hactive v hv f hf hf1 hspectrum haltSpectrum
      T packets (P.actualReferencePacketSet L oldSlope C w hw g tops T packets assigned hKb t i)
      assigned (P.actualReferencePacketSet_subset L oldSlope C w hw g tops T packets assigned hKb t i)
      hlength hangle hwidth'
  have ha := harea Kw hKw hKwL τ (Option (Fin (SourceParameters.blockCount L)))
    tops T (fun _ => Finset.univ) N κ Label Item R Q base hbase
    (fun _ _ => by
      simpa only [Real.rpow_ofNat] using
        parentShiftReference_card_le L (by linarith) (source_blockCount_le_square hL))
    (fun t ht i _ => hdata t ht i)
  have heq : (fun t => ⋃ i ∈ (Finset.univ : Finset (Option (Fin (SourceParameters.blockCount L)))),
      ((R t i).restrictPackets (Q t i)).bad L A (q+8) (2*q+9) (2*q+11)) = bad := by
    funext t
    simp only [Finset.mem_univ,iUnion_true,R,Q,bad,actualReferenceBad]
  rw [heq] at ha
  exact ⟨ha.1,ha.2.1,ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2.1,
    fun t z hz i => (ha.2.2.2.2.2 t z hz i (Finset.mem_univ i)).1⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCrossValue
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual distinct-profile, masked analyzing packet sum. No auxiliary
jet is needed for the physical bilinear operator. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)

theorem crossPacketValue_memLp (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (p : ℝ≥0∞) (q : P.PacketIndex) :
    MemLp (fun z => P.crossPacketValue alt hAlt t b v g z q) p (volume.prod volume) := by
  apply memLp_piLp_iff.mpr
  intro k
  exact (((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).memLp p
    (volume.prod volume)).const_mul _

theorem crossSum_memLp (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (p : ℝ≥0∞) (S : Finset P.PacketIndex) :
    MemLp (fun z => ∑ q∈S, P.crossPacketValue alt hAlt t b v g z q) p (volume.prod volume) :=
  memLp_finsetSum S (fun q _ => P.crossPacketValue_memLp alt hAlt t b v g p q)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation-independent radial masses and the literal distance to the
nearest angular boundary. Eligibility is retained in every radial set. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem index_eq_of_mem_cell (g : AngularGrid) (level : ℕ) (cell : ℤ) (s : ℝ)
    (hl : g.left level cell ≤ s) (hr : s < g.left level cell+g.width level) :
    g.index level s = cell := by
  have hG : (g.branching:ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  have heq : ((s-g.origin)/g.rootWidth)*(g.branching:ℝ)^level =
      (s-g.origin)/g.width level := by
    unfold width
    field_simp
  rw [index,heq]
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ (g.width_pos level)).mpr
    dsimp only [left] at hl
    nlinarith
  · apply (div_lt_iff₀ (g.width_pos level)).mpr
    dsimp only [left] at hr
    nlinarith

theorem index_eq_of_dist_lt_boundary (g : AngularGrid) (level : ℕ) (s t r : ℝ)
    (hr : r ≤ g.boundaryDistance level s) (hst : |t-s| < r) :
    g.index level t = g.index level s := by
  have hl := hr.trans (min_le_left _ _)
  have hh := hr.trans (min_le_right _ _)
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hst
  exact g.index_eq_of_mem_cell level (g.index level s) t (by linarith) (by linarith)

theorem nearbyEligibleTops_subset_cell (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (level : ℕ) (radius s : ℝ)
    (hr : radius ≤ g.boundaryDistance level s) :
    g.nearbyEligibleTops tops slope precision cutoff level radius s ⊆
      g.cellTops tops slope precision cutoff level (g.index level s) := by
  intro t ht
  obtain ⟨htt,he,hd⟩ := Finset.mem_filter.mp ht
  exact (g.mem_cellTops _ _ _ _ _ _ _).mpr
    ⟨htt,g.index_eq_of_dist_lt_boundary level s (slope t) radius hr hd,he⟩

theorem nearbyEligibleTops_mono (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (level : ℕ) (s : ℝ)
    {r R : ℝ} (hr : r ≤ R) :
    g.nearbyEligibleTops tops slope precision cutoff level r s ⊆
      g.nearbyEligibleTops tops slope precision cutoff level R s := by
  intro t ht
  obtain ⟨htt,he,hd⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨htt,he,hd.trans_le hr⟩

theorem outsideNearTops_subset_radial (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (base level : ℕ) (gap s R : ℝ) (hR : gap+2*g.width (level+1) < R) :
    g.outsideNearTops tops slope precision cutoff base level gap s ⊆
      g.nearbyEligibleTops tops slope precision cutoff level R s := by
  intro t ht
  obtain ⟨hbase,he,hnear,_⟩ := Finset.mem_filter.mp ht
  have htt := ((g.mem_cellTops _ _ _ _ _ _ _).mp hbase).1
  refine Finset.mem_filter.mpr ⟨htt,g.eligible_parent (hp t htt) level he,?_⟩
  rw [abs_sub_comm]
  exact (g.slopes_close_of_neighbors (level+1) gap s (slope t) hnear).trans_lt hR

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBoundaryDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized distance to the nearest boundary is a one-periodic
folded fractional part of the common grid translation. -/

noncomputable section
namespace LipschitzHilbert

theorem unitBoundaryDistance_periodic : Function.Periodic unitBoundaryDistance 1 := by
  intro u
  simp only [unitBoundaryDistance,Int.fract_add_one]

theorem unitBoundaryDistance_on_unit {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    unitBoundaryDistance u = min u (1-u) := by
  by_cases hu : u = 1
  · subst u
    norm_num [unitBoundaryDistance]
  · rw [unitBoundaryDistance,Int.fract_eq_self.mpr ⟨hu0,lt_of_le_of_ne hu1 hu⟩]

theorem unitBoundaryDistance_lower {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1/2) :
    unitBoundaryDistance u = u := by
  rw [unitBoundaryDistance_on_unit hu0 (by linarith),min_eq_left (by linarith)]

theorem unitBoundaryDistance_upper {u : ℝ} (hu : 1/2 ≤ u) (hu1 : u ≤ 1) :
    unitBoundaryDistance u = 1-u := by
  rw [unitBoundaryDistance_on_unit (by linarith) hu1,min_eq_right (by linarith)]

theorem unitBoundaryDistance_measurable : Measurable unitBoundaryDistance :=
  measurable_fract.min (measurable_const.sub measurable_fract)

namespace AngularGrid

theorem boundaryDistance_eq_unit (g : AngularGrid) (i : ℕ) (s : ℝ) :
    g.boundaryDistance i s = g.width i*unitBoundaryDistance ((s-g.origin)/g.width i) := by
  have hG : (g.branching:ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  have hi : g.index i s = ⌊(s-g.origin)/g.width i⌋ := by
    unfold index width
    congr 1
    field_simp
  have hleft : s-g.left i (g.index i s) = g.width i*Int.fract ((s-g.origin)/g.width i) := by
    rw [hi,left,Int.fract]
    field_simp [(g.width_pos i).ne']
    ring
  have hright : g.left i (g.index i s)+g.width i-s =
      g.width i*(1-Int.fract ((s-g.origin)/g.width i)) := by
    calc
      _ = g.width i-(s-g.left i (g.index i s)) := by ring
      _ = g.width i-g.width i*Int.fract ((s-g.origin)/g.width i) := by rw [hleft]
      _ = _ := by ring
  rw [boundaryDistance,hleft,hright,unitBoundaryDistance,mul_min_of_nonneg _ _ (g.width_pos i).le]

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_BoundaryDistanceAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single common translation is uniform at every angular scale.
The folded fractional part has density two on [0,1/2]; no independent
translations at distinct levels are introduced. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem unitBoundaryDistance_integral (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 (1/2:ℝ)) :
    IntervalIntegrable (fun u => f (unitBoundaryDistance u)) volume 0 1 ∧
      (∫ u in (0:ℝ)..1, f (unitBoundaryDistance u)) = 2*(∫ u in (0:ℝ)..(1/2:ℝ), f u) := by
  have hlow : IntervalIntegrable (fun u => f (unitBoundaryDistance u)) volume 0 (1/2:ℝ) := by
    apply hf.congr_uIoo
    intro u hu
    have hu' : 0 < u ∧ u < (1/2:ℝ) := by simpa only [uIoo_of_lt (by norm_num : (0:ℝ)<1/2),mem_Ioo] using hu
    dsimp only
    rw [unitBoundaryDistance_lower hu'.1.le hu'.2.le]
  have href : IntervalIntegrable (fun u => f (1-u)) volume (1/2:ℝ) 1 := by
    convert (hf.comp_sub_left 1).symm using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  have hhigh : IntervalIntegrable (fun u => f (unitBoundaryDistance u)) volume (1/2:ℝ) 1 := by
    apply href.congr_uIoo
    intro u hu
    have hu' : (1/2:ℝ) < u ∧ u < 1 := by simpa only [uIoo_of_lt (by norm_num : (1/2:ℝ)<1),mem_Ioo] using hu
    dsimp only
    rw [unitBoundaryDistance_upper hu'.1.le hu'.2.le]
  refine ⟨hlow.trans hhigh,?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hlow hhigh]
  have hlo : (∫ u in (0:ℝ)..(1/2:ℝ), f (unitBoundaryDistance u)) =
      ∫ u in (0:ℝ)..(1/2:ℝ), f u := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    dsimp only
    rw [unitBoundaryDistance_lower hu.1.le hu.2.le]
  have hhi : (∫ u in (1/2:ℝ)..1, f (unitBoundaryDistance u)) =
      ∫ u in (0:ℝ)..(1/2:ℝ), f u := by
    calc
      _ = ∫ u in (1/2:ℝ)..1, f (1-u) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro u hu
        dsimp only
        rw [unitBoundaryDistance_upper hu.1.le hu.2.le]
      _ = _ := by rw [intervalIntegral.integral_comp_sub_left]; norm_num
  rw [hlo,hhi]
  ring

theorem unitBoundaryDistance_period_integral (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 (1/2:ℝ)) (n : ℕ) (a : ℝ) :
    (∫ u in a..a+(n:ℝ), f (unitBoundaryDistance u)) =
      (n:ℝ)*2*(∫ u in (0:ℝ)..(1/2:ℝ), f u) := by
  have hper : Function.Periodic (fun u => f (unitBoundaryDistance u)) 1 :=
    fun u => congrArg f (unitBoundaryDistance_periodic u)
  have hu := unitBoundaryDistance_integral f hf
  have hall := hper.intervalIntegrable₀ (by norm_num : (1:ℝ) ≠ 0) hu.1
  have h := hper.intervalIntegral_add_zsmul_eq (n:ℤ) a hall
  have hbase := hper.intervalIntegral_add_eq a 0
  simp only [zero_add] at hbase
  rw [hbase,hu.2] at h
  simpa only [zsmul_eq_mul,Int.cast_natCast,mul_one,mul_assoc] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularCommonTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One uniform translation modulo the root width induces the correct
boundary-distance average at every level of the nested angular grid. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.AngularGrid

theorem normalized_boundaryDistance_withOrigin (g : AngularGrid) (i : ℕ) (s origin : ℝ) :
    (g.withOrigin origin).boundaryDistance i s/g.width i =
      unitBoundaryDistance ((s-origin)/g.width i) := by
  rw [boundaryDistance_eq_unit,width_withOrigin]
  change (g.width i*unitBoundaryDistance ((s-origin)/g.width i))/g.width i = _
  field_simp [(g.width_pos i).ne']

theorem common_translation_boundary_integral (g : AngularGrid) (i : ℕ) (s : ℝ)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 (1/2:ℝ)) :
    (∫ origin in (0:ℝ)..g.rootWidth,
      f ((g.withOrigin origin).boundaryDistance i s/g.width i)) =
        2*g.rootWidth*(∫ b in (0:ℝ)..(1/2:ℝ), f b) := by
  simp_rw [g.normalized_boundaryDistance_withOrigin i s,sub_div]
  rw [intervalIntegral.integral_comp_sub_div (fun u => f (unitBoundaryDistance u))
    (g.width_pos i).ne']
  simp only [zero_div,sub_zero,smul_eq_mul]
  have hG : (g.branching:ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  have hcount : g.rootWidth/g.width i = ((g.branching^i:ℕ):ℝ) := by
    push_cast
    unfold width
    field_simp [g.rootWidth_pos.ne',pow_ne_zero i hG]
  rw [hcount]
  have h := unitBoundaryDistance_period_integral f hf (g.branching^i)
    (s/g.width i-((g.branching^i:ℕ):ℝ))
  rw [sub_add_cancel] at h
  rw [h]
  have hw : g.width i*((g.branching^i:ℕ):ℝ) = g.rootWidth := by
    push_cast
    unfold width
    field_simp [g.rootWidth_pos.ne',pow_ne_zero i hG]
  rw [← mul_assoc,← mul_assoc,hw]
  ring

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBoundaryNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary coincidences are a null set of the common translation. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.AngularGrid

theorem ae_boundaryDistance_pos (g : AngularGrid) (i : ℕ) (s : ℝ) :
    ∀ᵐ origin : ℝ, 0 < (g.withOrigin origin).boundaryDistance i s := by
  filter_upwards [(Set.countable_range (fun k : ℤ => s-g.width i*k)).ae_notMem volume] with origin ho
  by_contra h
  have hs := (g.withOrigin origin).slope_mem_cell i s
  have hlow : origin+g.width i*((g.withOrigin origin).index i s) ≤ s := hs.1
  have hhigh : s < origin+g.width i*((g.withOrigin origin).index i s)+g.width i := hs.2
  have hd : min (s-(origin+g.width i*((g.withOrigin origin).index i s)))
      (origin+g.width i*((g.withOrigin origin).index i s)+g.width i-s) ≤ 0 := le_of_not_gt h
  rcases min_le_iff.mp hd with hleft | hright
  · apply ho
    refine ⟨(g.withOrigin origin).index i s,?_⟩
    linarith
  · linarith

theorem ae_normalized_boundaryDistance_pos (g : AngularGrid) (i : ℕ) (s : ℝ) :
    ∀ᵐ origin : ℝ, 0 < (g.withOrigin origin).boundaryDistance i s/g.width i :=
  (g.ae_boundaryDistance_pos i s).mono fun _ h => div_pos h (g.width_pos i)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularTranslationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the actual path and boundary masses as the common
angular-grid origin varies. The top weights are held fixed here. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem measurable_path_mass_withOrigin (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (i : ℕ) (s : ℝ) (x : X) :
    Measurable (fun origin => (g.withOrigin origin).mass tops slope precision cutoff weight
      i ((g.withOrigin origin).index i s) x) := by
  simp only [mass,cellTops,Finset.sum_filter]
  apply Finset.measurable_sum
  intro t _
  have hc : MeasurableSet {origin : ℝ | (g.withOrigin origin).index i (slope t) =
      (g.withOrigin origin).index i s} :=
    measurableSet_eq_fun (g.measurable_index_withOrigin i (slope t)) (g.measurable_index_withOrigin i s)
  by_cases he : g.eligible cutoff (precision t) i
  · simp only [show ∀ origin, (g.withOrigin origin).eligible cutoff (precision t) i from fun _ => he,
      and_true]
    exact measurable_const.piecewise hc measurable_const
  · have he' : ∀ origin, ¬(g.withOrigin origin).eligible cutoff (precision t) i := fun _ => he
    simp only [he',and_false,ite_false, if_false]
    exact measurable_const

theorem measurable_boundary_mass_withOrigin (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (base i : ℕ) (gap s : ℝ) (x : X) :
    Measurable (fun origin => (g.withOrigin origin).boundaryMass tops slope precision cutoff weight
      base i gap s x) := by
  simp_rw [boundary_mass_eq]
  apply (g.measurable_path_mass_withOrigin tops slope precision cutoff weight i s x).add
  simp only [outsideNearTops,cellTops,Finset.filter_filter,Finset.sum_filter]
  apply Finset.measurable_sum
  intro t _
  have hbase : MeasurableSet {origin : ℝ | (g.withOrigin origin).index base (slope t) =
      (g.withOrigin origin).index base s} :=
    measurableSet_eq_fun (g.measurable_index_withOrigin base (slope t)) (g.measurable_index_withOrigin base s)
  have hparent : MeasurableSet {origin : ℝ | (g.withOrigin origin).index i (slope t) ≠
      (g.withOrigin origin).index i s} :=
    (measurableSet_eq_fun (g.measurable_index_withOrigin i (slope t)) (g.measurable_index_withOrigin i s)).compl
  have hnear : MeasurableSet {origin : ℝ | (g.withOrigin origin).neighbors (i+1) gap
      ((g.withOrigin origin).index (i+1) s) ((g.withOrigin origin).index (i+1) (slope t))} := by
    change MeasurableSet {origin : ℝ | |(g.withOrigin origin).center (i+1) ((g.withOrigin origin).index (i+1) s)-
      (g.withOrigin origin).center (i+1) ((g.withOrigin origin).index (i+1) (slope t))| < gap+g.width (i+1)}
    exact measurableSet_lt
      (continuous_abs.measurable.comp ((g.measurable_center_withOrigin (i+1) s).sub (g.measurable_center_withOrigin (i+1) (slope t))))
      measurable_const
  have hel (j : ℕ) : MeasurableSet {origin : ℝ | (g.withOrigin origin).eligible cutoff (precision t) j} := by
    change MeasurableSet {origin : ℝ | g.eligible cutoff (precision t) j}
    by_cases hh : g.eligible cutoff (precision t) j <;> simp only [hh,Set.ofPred_true,Set.ofPred_false] <;> measurability
  exact measurable_const.piecewise ((hbase.inter (hel base)).inter ((hel (i+1)).inter (hnear.inter hparent))) measurable_const

theorem measurable_source_boundary_log_loss_withOrigin (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (i : ℕ) (s : ℝ) (x : X) :
    Measurable (fun origin => Real.log
      ((g.withOrigin origin).sourceBoundaryMass tops slope precision cutoff weight K gap i
        ((g.withOrigin origin).index (i+1) s) x /
       (g.withOrigin origin).mass tops slope precision cutoff weight i ((g.withOrigin origin).index i s) x)) := by
  simp_rw [sourceBoundaryMass_path _ tops slope precision cutoff weight hK gap]
  exact ((g.measurable_boundary_mass_withOrigin tops slope precision cutoff weight (i+1-K) i (gap i) s x).div
    (g.measurable_path_mass_withOrigin tops slope precision cutoff weight i s x)).log

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact central coefficient loses at most the sum of the logarithmic
parent-to-boundary losses. Its deficit grows with the packet stopping level. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ X : Type*}

theorem sourceBoundaryCoefficient_eq_exp (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N) (a : ℝ) (x : X) :
    g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap N top a x =
      Real.exp (-a*g.sourceBoundaryLogLoss tops slope precision cutoff weight K gap N top x) := by
  let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope top)) x
  let b := fun j => g.sourceBoundaryMass tops slope precision cutoff weight K gap j
    (g.index (j+1) (slope top)) x
  have hn (j : ℕ) (hj : j < N) : 0 < n j :=
    g.path_mass_pos tops slope precision cutoff weight hw j top htop
      (g.eligible_of_le (hp top htop) (Nat.le_of_lt hj) he) x
  have hb (j : ℕ) (hj : j < N) : 0 < b j :=
    (hn j hj).trans_le (g.sourceBoundaryMass_parent_le tops slope precision cutoff weight
      hp (fun t x => (hw t x).le) hK gap j (slope top) x)
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      (n j/b j)^a = Real.exp (-a*Real.log (b j/n j)) := by
    have hjN := Finset.mem_range.mp hj
    rw [Real.rpow_def_of_pos (div_pos (hn j hjN) (hb j hjN)),
      Real.log_div (hn j hjN).ne' (hb j hjN).ne',
      Real.log_div (hb j hjN).ne' (hn j hjN).ne']
    congr 1
    ring
  change (∏ j ∈ Finset.range N, (n j/b j)^a) =
    Real.exp (-a*∑ j ∈ Finset.range N, Real.log (b j/n j))
  rw [Finset.prod_congr rfl hterm,← Real.exp_sum,Finset.mul_sum]

theorem sourceBoundaryLogLoss_mono (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) {N M : ℕ} (hNM : N ≤ M) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) M) (x : X) :
    g.sourceBoundaryLogLoss tops slope precision cutoff weight K gap N top x ≤
      g.sourceBoundaryLogLoss tops slope precision cutoff weight K gap M top x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
  intro j hj _
  have hn := g.path_mass_pos tops slope precision cutoff weight hw j top htop
    (g.eligible_of_le (hp top htop) (Nat.le_of_lt (Finset.mem_range.mp hj)) he) x
  apply Real.log_nonneg
  exact (one_le_div hn).mpr (g.sourceBoundaryMass_parent_le tops slope precision cutoff weight
    hp (fun t x => (hw t x).le) hK gap j (slope top) x)

theorem sourceBoundaryCoefficient_deficit_le (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N) (a : ℝ) (x : X) :
    1-g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap N top a x ≤
      a*g.sourceBoundaryLogLoss tops slope precision cutoff weight K gap N top x := by
  rw [g.sourceBoundaryCoefficient_eq_exp tops slope precision cutoff weight hp hw hK gap N top
    htop he a x]
  have h := Real.add_one_le_exp
    (-a*g.sourceBoundaryLogLoss tops slope precision cutoff weight K gap N top x)
  linarith

theorem sourceBoundaryCoefficient_antitone (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) {N M : ℕ} (hNM : N ≤ M) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) M)
    (a : ℝ) (ha : 0 ≤ a) (x : X) :
    g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap M top a x ≤
      g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap N top a x := by
  rw [g.sourceBoundaryCoefficient_eq_exp tops slope precision cutoff weight hp hw hK gap M top
      htop he a x,
    g.sourceBoundaryCoefficient_eq_exp tops slope precision cutoff weight hp hw hK gap N top
      htop (g.eligible_of_le (hp top htop) hNM he) a x]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (g.sourceBoundaryLogLoss_mono tops slope precision cutoff weight hp hw hK gap hNM top htop he x)
    (neg_nonpos.mpr ha)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryLossBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single actual source boundary loss lies between zero and the
fixed total/self logarithm; this supplies integrability in the translation. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ X : Type*}

theorem source_boundary_log_loss_bounds (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (i : ℕ) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) i) (x : X) :
    let loss := Real.log (g.sourceBoundaryMass tops slope precision cutoff weight K gap i
      (g.index (i+1) (slope top)) x / g.mass tops slope precision cutoff weight i (g.index i (slope top)) x)
    0 ≤ loss ∧ loss ≤ Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  intro loss
  have hself : weight top x ≤ g.mass tops slope precision cutoff weight i (g.index i (slope top)) x :=
    Finset.single_le_sum (fun t _ => (hw t x).le)
      ((g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,he⟩)
  have hn := (hw top x).trans_le hself
  have hnb := g.sourceBoundaryMass_parent_le tops slope precision cutoff weight hp
    (fun t x => (hw t x).le) hK gap i (slope top) x
  have hb := (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
    (fun t x => (hw t x).le) hK gap i (slope top) x).2
  have hbt := hb.trans (g.mass_le_total tops slope precision cutoff weight
    (fun t x => (hw t x).le) (i+1-K) (g.index (i+1-K) (slope top)) x)
  have ht0 := (hn.trans_le hnb).trans_le hbt
  exact ⟨Real.log_nonneg ((one_le_div hn).mpr hnb),
    Real.log_le_log (div_pos (hn.trans_le hnb) hn) (div_le_div₀ ht0.le hbt (hw top x) hself)⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One angular boundary loss is controlled by radial eligible masses.
The comparison includes the precision cutoff, including for extra tops. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem boundary_mass_ratio_le_radial (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (base level : ℕ) (gap r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (top : τ) (hrb : r ≤ g.boundaryDistance level (slope top))
    (hR : gap+2*g.width (level+1) < R)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) level) (x : X) :
    g.boundaryMass tops slope precision cutoff weight base level gap (slope top) x /
        g.mass tops slope precision cutoff weight level (g.index level (slope top)) x ≤
      g.nearbyEligibleMass tops slope precision cutoff weight level R (slope top) x /
        g.nearbyEligibleMass tops slope precision cutoff weight level r (slope top) x := by
  let inner := g.nearbyEligibleTops tops slope precision cutoff level r (slope top)
  let outer := g.nearbyEligibleTops tops slope precision cutoff level R (slope top)
  let extra := g.outsideNearTops tops slope precision cutoff base level gap (slope top)
  let n := g.mass tops slope precision cutoff weight level (g.index level (slope top)) x
  let u := ∑ t ∈ inner, weight t x
  let v := ∑ t ∈ outer, weight t x
  let e := ∑ t ∈ extra, weight t x
  have hn : 0 < n := g.path_mass_pos tops slope precision cutoff weight hw level top htop he x
  have htopi : top ∈ inner := Finset.mem_filter.mpr ⟨htop,he,by simpa using hr⟩
  have hu : 0 < u := (hw top x).trans_le (Finset.single_le_sum (fun t _ => (hw t x).le) htopi)
  have hinner := g.nearbyEligibleTops_subset_cell tops slope precision cutoff level r (slope top) hrb
  have hun : u ≤ n := Finset.sum_le_sum_of_subset_of_nonneg hinner (fun t _ _ => (hw t x).le)
  have hextra := g.outsideNearTops_subset_radial tops slope precision cutoff hp base level gap (slope top) R hR
  have hd : Disjoint inner extra := by
    apply Finset.disjoint_left.mpr
    intro t hti hte
    have hsame := ((g.mem_cellTops _ _ _ _ _ _ _).mp (hinner hti)).2.1
    exact (Finset.mem_filter.mp hte).2.2.2 hsame
  have hsum : u+e ≤ v := by
    rw [← Finset.sum_union hd]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.union_subset (g.nearbyEligibleTops_mono tops slope precision cutoff level (slope top) hrR) hextra)
      (fun t _ _ => (hw t x).le)
  have he0 : 0 ≤ e := Finset.sum_nonneg fun t _ => (hw t x).le
  change _/n ≤ v/u
  rw [g.boundary_mass_eq tops slope precision cutoff weight base level gap (slope top) x]
  change (n+e)/n ≤ v/u
  apply (div_le_div_iff₀ hn hu).mpr
  have hm := mul_le_mul_of_nonneg_right hsum hn.le
  have hem := mul_le_mul_of_nonneg_left hun he0
  nlinarith

theorem boundary_log_loss_le_radial (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (base level : ℕ) (gap r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (top : τ) (hrb : r ≤ g.boundaryDistance level (slope top))
    (hR : gap+2*g.width (level+1) < R)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) level) (x : X) :
    Real.log (g.boundaryMass tops slope precision cutoff weight base level gap (slope top) x /
      g.mass tops slope precision cutoff weight level (g.index level (slope top)) x) ≤
    Real.log (g.nearbyEligibleMass tops slope precision cutoff weight level R (slope top) x /
      g.nearbyEligibleMass tops slope precision cutoff weight level r (slope top) x) := by
  have hn := g.path_mass_pos tops slope precision cutoff weight hw level top htop he x
  have hb : 0 < g.boundaryMass tops slope precision cutoff weight base level gap (slope top) x := by
    rw [g.boundary_mass_eq tops slope precision cutoff weight base level gap (slope top) x]
    exact add_pos_of_pos_of_nonneg hn (Finset.sum_nonneg fun t _ => (hw t x).le)
  exact Real.log_le_log (div_pos hb hn)
    (g.boundary_mass_ratio_le_radial tops slope precision cutoff weight hp hw base level gap r R
      hr hrR top hrb hR htop he x)

theorem boundary_mass_eq_parent_of_far (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (base level : ℕ) (gap R s : ℝ)
    (hR : gap+2*g.width (level+1) < R) (hfar : R ≤ g.boundaryDistance level s) (x : X) :
    g.boundaryMass tops slope precision cutoff weight base level gap s x =
      g.mass tops slope precision cutoff weight level (g.index level s) x := by
  have he : g.outsideNearTops tops slope precision cutoff base level gap s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hi := g.outsideNearTops_subset_radial tops slope precision cutoff hp base level gap s R hR ht
    have hs := g.nearbyEligibleTops_subset_cell tops slope precision cutoff level R s hfar hi
    exact (Finset.mem_filter.mp ht).2.2.2 (((g.mem_cellTops _ _ _ _ _ _ _).mp hs).2.1)
  rw [g.boundary_mass_eq tops slope precision cutoff weight base level gap s x,he]
  simp

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source neighborhood fits inside the radius 4 G^(-1/4) d(i).
The one-boundary radial comparison uses exactly this radius. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid
variable {τ X : Type*}

theorem sourceBoundaryGap_ge_child (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) (i : ℕ) :
    g.width (i+1) ≤ g.sourceBoundaryGap L i := by
  rw [g.sourceBoundaryGap_eq_sourceGap L hbranch]
  change g.width (i+1) ≤ SourceParameters.step L^(3/4:ℝ)*g.width (i+1)
  exact le_mul_of_one_le_left (g.width_pos (i+1)).le
    (Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) (by norm_num))

theorem source_boundary_radius (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) (i : ℕ) :
    g.sourceBoundaryGap L i+2*g.width (i+1) <
      (4*SourceParameters.step L^(-(1/4:ℝ)))*g.width i := by
  have hc := g.sourceBoundaryGap_ge_child L hbranch i
  have hg := g.sourceBoundaryGap_pos L i
  have heq : (4*SourceParameters.step L^(-(1/4:ℝ)))*g.width i =
      4*g.sourceBoundaryGap L i := by unfold sourceBoundaryGap; ring
  rw [heq]
  nlinarith

theorem source_boundary_log_loss_le_radial (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (i : ℕ) (b : ℝ) (hb : 0 < b)
    (hbε : b ≤ 4*SourceParameters.step L^(-(1/4:ℝ))) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) i)
    (hbd : b*g.width i ≤ g.boundaryDistance i (slope top)) (x : X) :
    Real.log (g.sourceBoundaryMass tops slope precision cutoff weight K (g.sourceBoundaryGap L)
      i (g.index (i+1) (slope top)) x /
        g.mass tops slope precision cutoff weight i (g.index i (slope top)) x) ≤
    Real.log (g.nearbyEligibleMass tops slope precision cutoff weight i
      ((4*SourceParameters.step L^(-(1/4:ℝ)))*g.width i) (slope top) x /
        g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x) := by
  rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hK]
  exact g.boundary_log_loss_le_radial tops slope precision cutoff weight hp hw
    (i+1-K) i (g.sourceBoundaryGap L i) (b*g.width i)
    ((4*SourceParameters.step L^(-(1/4:ℝ)))*g.width i)
    (mul_pos hb (g.width_pos i)) (mul_le_mul_of_nonneg_right hbε (g.width_pos i).le)
    top hbd (g.source_boundary_radius L hbranch i) htop he x

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_GeometricBoundaryDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact average of the boundary-depth envelope used after telescoping. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert

theorem geometricBoundaryLayer_nonneg (ε q : ℝ) (j : ℕ) (b : ℝ) :
    0 ≤ geometricBoundaryLayer ε q j b := by
  exact indicator_nonneg (fun _ _ => zero_le_one) b

theorem geometricBoundaryLayer_integrable (ε q : ℝ) (j : ℕ) :
    Integrable (geometricBoundaryLayer ε q j) := by
  exact (integrable_indicator_iff measurableSet_Ioo).2
    (integrableOn_const (by simp [Real.volume_Ioo]))

theorem integral_geometricBoundaryLayer {ε q : ℝ} (hε : 0 ≤ ε) (hq : 0 ≤ q) (j : ℕ) :
    (∫ b, geometricBoundaryLayer ε q j b) = ε * q ^ j := by
  change (∫ b, (Ioo 0 (ε * q ^ j)).indicator (1 : ℝ → ℝ) b) = _
  rw [integral_indicator_one measurableSet_Ioo,
    Real.volume_real_Ioo_of_le (by positivity), sub_zero]

theorem integral_norm_geometricBoundaryLayer {ε q : ℝ} (hε : 0 ≤ ε) (hq : 0 ≤ q) (j : ℕ) :
    (∫ b, ‖geometricBoundaryLayer ε q j b‖) = ε * q ^ j := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (geometricBoundaryLayer_nonneg ε q j _)] using
    integral_geometricBoundaryLayer hε hq j

/-- The boundary-depth average is finite and has the exact geometric-series
value. This avoids any loss depending on the number of angular levels. -/
theorem integral_geometricBoundaryDepth {ε q : ℝ}
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hq1 : q < 1) :
    (∫ b, geometricBoundaryDepth ε q b) = ε / (1 - q) := by
  have hs : Summable (fun j : ℕ => ∫ b, ‖geometricBoundaryLayer ε q j b‖) := by
    simp_rw [integral_norm_geometricBoundaryLayer hε hq]
    exact (summable_geometric_of_lt_one hq hq1).mul_left ε
  change (∫ b, ∑' j : ℕ, geometricBoundaryLayer ε q j b) = _
  rw [← integral_tsum_of_summable_integral_norm
    (geometricBoundaryLayer_integrable ε q) hs]
  simp_rw [integral_geometricBoundaryLayer hε hq]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1, div_eq_mul_inv]

theorem geometricBoundaryDepth_integrable {ε q : ℝ}
    (hε : 0 < ε) (hq : 0 ≤ q) (hq1 : q < 1) :
    Integrable (geometricBoundaryDepth ε q) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_geometricBoundaryDepth hε.le hq hq1]
  exact (div_pos hε (sub_pos.mpr hq1)).ne'

/-- With angular branching at least two, the average depth costs at most
`2ε`, independent of the depth of the hierarchy. -/
theorem integral_geometricBoundaryDepth_le {ε G : ℝ} (hε : 0 ≤ ε) (hG : 2 ≤ G) :
    (∫ b, geometricBoundaryDepth ε G⁻¹ b) ≤ 2 * ε := by
  have hG0 : 0 < G := by linarith
  have hi0 : 0 ≤ G⁻¹ := inv_nonneg.mpr hG0.le
  have hi2 : G⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using (inv_le_inv₀ hG0 (by norm_num : (0 : ℝ) < 2)).2 hG
  rw [integral_geometricBoundaryDepth hε hi0 (by linarith)]
  apply (div_le_iff₀ (by linarith : 0 < 1 - G⁻¹)).2
  nlinarith [mul_le_mul_of_nonneg_left hi2 hε]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_BoundaryDepthCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric envelope equals the first angular scale crossing, and hence
controls the shifted differences of the actual boundary argument. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace LipschitzHilbert

theorem geometricBoundaryDepth_eq_crossing {ε q b : ℝ} {r : ℕ}
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hb : 0 < b)
    (hbefore : ∀ j < r, b < ε * q ^ j) (hcross : ε * q ^ r ≤ b) :
    geometricBoundaryDepth ε q b = (r : ℝ) := by
  unfold geometricBoundaryDepth
  rw [tsum_eq_sum (s := Finset.range r)]
  · have heq : ∀ j ∈ Finset.range r, geometricBoundaryLayer ε q j b = 1 := by
      intro j hj
      exact indicator_of_mem
        (show b ∈ Ioo 0 (ε * q ^ j) from ⟨hb, hbefore j (Finset.mem_range.mp hj)⟩)
        (fun _ => (1 : ℝ))
    simp only [Finset.sum_congr rfl heq, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · intro j hj
    have hle : ε * q ^ j ≤ b :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq hq1 (by
        simpa only [Finset.mem_range, not_lt] using hj)) hε).trans hcross
    exact indicator_of_notMem (show b ∉ Ioo 0 (ε * q ^ j) from by
      intro hmem
      exact (not_lt_of_ge hle) hmem.2) _

/-- Every positive boundary distance has a finite first crossing scale. The
geometric depth counts exactly the preceding scales. -/
theorem exists_geometricBoundaryDepth_crossing {ε q b : ℝ}
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hq1 : q < 1) (hb : 0 < b) :
    ∃ r : ℕ, geometricBoundaryDepth ε q b = (r : ℝ) ∧ ε * q ^ r ≤ b ∧
      ∀ j < r, b < ε * q ^ j := by
  have ht : Filter.Tendsto (fun j : ℕ => ε * q ^ j) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).const_mul ε
  have he : ∃ r : ℕ, ε * q ^ r ≤ b := by
    obtain ⟨r, hr⟩ := (ht.eventually (gt_mem_nhds hb)).exists
    exact ⟨r, hr.le⟩
  let r := Nat.find he
  have hcross : ε * q ^ r ≤ b := Nat.find_spec he
  have hbefore : ∀ j < r, b < ε * q ^ j := by
    intro j hj
    exact lt_of_not_ge (Nat.find_min he hj)
  exact ⟨r, geometricBoundaryDepth_eq_crossing hε hq hq1.le hb hbefore hcross,
    hcross, hbefore⟩

/-- The finite-difference estimate can use the first scale crossing directly,
without losing the number of levels in the path. -/
theorem boundary_loss_le_geometricDepth (a loss : ℕ → ℝ) (k : ℕ) {ε q b B : ℝ}
    (hε : 0 ≤ ε) (hq : 0 ≤ q) (hq1 : q < 1) (hb : 0 < b)
    (ha : ∀ i, 0 ≤ a i) (hbound : ∀ i, a i ≤ B)
    (hloss : ∀ r : ℕ, ε * q ^ r ≤ b →
      ∀ i < k, loss i ≤ a i - a (i + r)) :
    (∑ i ∈ Finset.range k, loss i) ≤ geometricBoundaryDepth ε q b * B := by
  obtain ⟨r, hr, hcross, _⟩ := exists_geometricBoundaryDepth_crossing hε hq hq1 hb
  rw [hr]
  exact boundary_loss_sum_le a loss k r ha (fun i _ => hbound i) (hloss r hcross)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceRadialScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial eligible sets shrink in both angular radius and precision.
This is the scale inclusion used in the boundary-loss telescoping argument. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem nearbyEligibleTops_subset_of_scale (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    {i j : ℕ} (hij : i ≤ j) {r R : ℝ} (hr : r ≤ R) (s : ℝ) :
    g.nearbyEligibleTops tops slope precision cutoff j r s ⊆
      g.nearbyEligibleTops tops slope precision cutoff i R s := by
  intro t ht
  obtain ⟨htt,he,hd⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr
    ⟨htt,g.eligible_of_le (hp t htt) hij he,hd.trans_le hr⟩

theorem nearbyEligibleMass_le_of_scale (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    {i j : ℕ} (hij : i ≤ j) {r R : ℝ} (hr : r ≤ R) (s : ℝ) (x : X) :
    g.nearbyEligibleMass tops slope precision cutoff weight j r s x ≤
      g.nearbyEligibleMass tops slope precision cutoff weight i R s x :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (g.nearbyEligibleTops_subset_of_scale tops slope precision cutoff hp hij hr s)
    (fun t _ _ => hw t x)

theorem width_add (g : AngularGrid) (i j : ℕ) :
    g.width (i+j) = g.width i*(g.branching:ℝ)⁻¹^j := by
  have hG : (g.branching:ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  unfold width
  rw [pow_add,inv_pow]
  field_simp

theorem nearbyEligibleMass_scale_crossing (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (i r : ℕ) (epsilon b s : ℝ)
    (hcross : epsilon*(g.branching:ℝ)⁻¹^r ≤ b) (x : X) :
    g.nearbyEligibleMass tops slope precision cutoff weight (i+r)
        (epsilon*g.width (i+r)) s x ≤
      g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) s x := by
  apply g.nearbyEligibleMass_le_of_scale tops slope precision cutoff weight hp hw
    (Nat.le_add_right i r) _ s x
  rw [g.width_add i r]
  nlinarith [mul_le_mul_of_nonneg_right hcross (g.width_pos i).le]

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceRadialMassBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive self mass and the fixed total mass bound every radial eligible
mass along a top's eligible path. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem nearbyEligibleMass_self_le (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 ≤ weight t x) (i : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) i) {r : ℝ} (hr : 0 < r) (x : X) :
    weight top x ≤ g.nearbyEligibleMass tops slope precision cutoff weight i r (slope top) x := by
  apply Finset.single_le_sum (fun t _ => hw t x)
  exact Finset.mem_filter.mpr ⟨htop,he,by simpa using hr⟩

theorem nearbyEligibleMass_le_total (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 ≤ weight t x) (i : ℕ) (r s : ℝ) (x : X) :
    g.nearbyEligibleMass tops slope precision cutoff weight i r s x ≤ ∑ t ∈ tops, weight t x :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun t _ _ => hw t x)

theorem radialPathLogMass_bounds (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 < weight t x) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : ∀ i < N, g.eligible cutoff (precision top) i) (x : X) (i : ℕ) :
    0 ≤ g.radialPathLogMass tops slope precision cutoff weight epsilon N top x i ∧
      g.radialPathLogMass tops slope precision cutoff weight epsilon N top x i ≤
        Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  have htotal : weight top x ≤ ∑ t ∈ tops, weight t x :=
    Finset.single_le_sum (fun t _ => (hw t x).le) htop
  have htotallog : 0 ≤ Real.log ((∑ t ∈ tops, weight t x)/weight top x) :=
    Real.log_nonneg ((one_le_div (hw top x)).mpr htotal)
  by_cases hi : i < N
  · have hself := g.nearbyEligibleMass_self_le tops slope precision cutoff weight
      (fun t x => (hw t x).le) i top htop (he i hi) (mul_pos hepsilon (g.width_pos i)) x
    have hmasspos := (hw top x).trans_le hself
    have hupper := g.nearbyEligibleMass_le_total tops slope precision cutoff weight
      (fun t x => (hw t x).le) i (epsilon*g.width i) (slope top) x
    simp only [radialPathLogMass,ite_eq_left hi]
    exact ⟨Real.log_nonneg ((one_le_div (hw top x)).mpr hself),
      Real.log_le_log (div_pos hmasspos (hw top x))
        (div_le_div_of_nonneg_right hupper (hw top x).le)⟩
  · simpa only [radialPathLogMass,ite_eq_right hi] using And.intro le_rfl htotallog

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceRadialTelescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite sum of literal radial log ratios is bounded by geometric
boundary depth, including the terminal eligibility cutoff. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem radial_log_ratio_sum_le_depth (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (epsilon b : ℝ) (hepsilon : 0 < epsilon) (hb : 0 < b)
    (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : ∀ i < N, g.eligible cutoff (precision top) i) (x : X) :
    (∑ i ∈ Finset.range N, Real.log
      (g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x /
        g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x)) ≤
      geometricBoundaryDepth epsilon (g.branching:ℝ)⁻¹ b *
        Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  have hG : (1:ℝ) < g.branching := by
    exact_mod_cast (show 1 < g.branching by have := g.branching_ge_two; omega)
  have hinv0 : 0 ≤ (g.branching:ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hinv1 : (g.branching:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hG
  apply boundary_loss_le_geometricDepth
    (g.radialPathLogMass tops slope precision cutoff weight epsilon N top x) _ N
    hepsilon.le hinv0 hinv1 hb
    (fun i => (g.radialPathLogMass_bounds tops slope precision cutoff weight hw epsilon hepsilon
      N top htop he x i).1)
    (fun i => (g.radialPathLogMass_bounds tops slope precision cutoff weight hw epsilon hepsilon
      N top htop he x i).2)
  intro r hcross i hi
  let A := g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x
  let B := g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x
  have hw0 := hw top x
  have hA := g.nearbyEligibleMass_self_le tops slope precision cutoff weight
    (fun t x => (hw t x).le) i top htop (he i hi) (mul_pos hepsilon (g.width_pos i)) x
  have hB := g.nearbyEligibleMass_self_le tops slope precision cutoff weight
    (fun t x => (hw t x).le) i top htop (he i hi) (mul_pos hb (g.width_pos i)) x
  have hA0 : 0 < A := hw0.trans_le hA
  have hB0 : 0 < B := hw0.trans_le hB
  change Real.log (A/B) ≤ _
  by_cases hnext : i+r < N
  · let C := g.nearbyEligibleMass tops slope precision cutoff weight (i+r)
      (epsilon*g.width (i+r)) (slope top) x
    have hC := g.nearbyEligibleMass_self_le tops slope precision cutoff weight
      (fun t x => (hw t x).le) (i+r) top htop (he (i+r) hnext)
      (mul_pos hepsilon (g.width_pos (i+r))) x
    have hC0 : 0 < C := hw0.trans_le hC
    have hCB : C ≤ B := g.nearbyEligibleMass_scale_crossing tops slope precision cutoff weight hp
      (fun t x => (hw t x).le) i r epsilon b (slope top) hcross x
    have hlog := Real.log_le_log hC0 hCB
    simp only [radialPathLogMass,ite_eq_left hi,ite_eq_left hnext]
    change Real.log (A/B) ≤ Real.log (A/weight top x)-Real.log (C/weight top x)
    rw [Real.log_div hA0.ne' hB0.ne',Real.log_div hA0.ne' hw0.ne',
      Real.log_div hC0.ne' hw0.ne']
    linarith
  · have hlog := Real.log_le_log hw0 hB
    simp only [radialPathLogMass,ite_eq_left hi,ite_eq_right hnext,sub_zero]
    change Real.log (A/B) ≤ Real.log (A/weight top x)
    rw [Real.log_div hA0.ne' hB0.ne',Real.log_div hA0.ne' hw0.ne']
    linarith

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceRadialIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal radial logarithmic loss has integral O(epsilon), uniformly
in the number of eligible levels. This is the scalar integral used by the
common-translation boundary average. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem nearbyEligibleMass_measurable_radius (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (i : ℕ) (s : ℝ) (x : X) :
    Measurable (fun r : ℝ => g.nearbyEligibleMass tops slope precision cutoff weight i r s x) := by
  simp only [nearbyEligibleMass,nearbyEligibleTops,Finset.sum_filter]
  apply Finset.measurable_sum
  intro t _
  by_cases he : g.eligible cutoff (precision t) i
  · simp only [he,true_and]
    exact measurable_const.piecewise measurableSet_Ioi measurable_const
  · simp only [he,false_and,ite_false, if_false]
    exact measurable_const

theorem radial_log_ratio_integral_le (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : ∀ i < N, g.eligible cutoff (precision top) i) (x : X) :
    let loss := fun b => ∑ i ∈ Finset.range N, Real.log
      (g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x /
        g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x)
    IntegrableOn loss (Ioo 0 epsilon) volume ∧
      (∫ b in Ioo 0 epsilon, loss b) ≤
        2*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  dsimp only
  let loss := fun b => ∑ i ∈ Finset.range N, Real.log
    (g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x /
      g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x)
  let B := Real.log ((∑ t ∈ tops, weight t x)/weight top x)
  let depth := geometricBoundaryDepth epsilon (g.branching:ℝ)⁻¹
  have hB : 0 ≤ B := Real.log_nonneg ((one_le_div (hw top x)).mpr
    (Finset.single_le_sum (fun t _ => (hw t x).le) htop))
  have hG : (2:ℝ) ≤ g.branching := by exact_mod_cast g.branching_ge_two
  have hG0 : 0 < (g.branching:ℝ) := by linarith
  have hinv0 : 0 ≤ (g.branching:ℝ)⁻¹ := inv_nonneg.mpr hG0.le
  have hinv1 : (g.branching:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hid : Integrable depth volume := geometricBoundaryDepth_integrable hepsilon hinv0 hinv1
  have hdepth0 (b : ℝ) : 0 ≤ depth b := tsum_nonneg fun j => geometricBoundaryLayer_nonneg _ _ _ _
  have hlossMeas : Measurable loss := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_const.div ((g.nearbyEligibleMass_measurable_radius tops slope precision cutoff
      weight i (slope top) x).comp (measurable_id.mul_const (g.width i)))).log
  have hloss0 (b : ℝ) (hb : b ∈ Ioo 0 epsilon) : 0 ≤ loss b := by
    apply Finset.sum_nonneg
    intro i hi
    have hbi := g.nearbyEligibleMass_self_le tops slope precision cutoff weight
      (fun t x => (hw t x).le) i top htop (he i (Finset.mem_range.mp hi))
      (mul_pos hb.1 (g.width_pos i)) x
    apply Real.log_nonneg
    apply (one_le_div ((hw top x).trans_le hbi)).mpr
    exact g.nearbyEligibleMass_le_of_scale tops slope precision cutoff weight hp
      (fun t x => (hw t x).le) le_rfl (mul_le_mul_of_nonneg_right hb.2.le (g.width_pos i).le)
      (slope top) x
  have hbound (b : ℝ) (hb : b ∈ Ioo 0 epsilon) : loss b ≤ depth b*B :=
    g.radial_log_ratio_sum_le_depth tops slope precision cutoff weight hp hw epsilon b hepsilon hb.1
      N top htop he x
  have hi : IntegrableOn loss (Ioo 0 epsilon) volume :=
    ((hid.mul_const B).restrict (s := Ioo 0 epsilon)).mono' hlossMeas.aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with b hb
        rw [Real.norm_eq_abs,abs_of_nonneg (hloss0 b hb)]
        exact hbound b hb)
  refine ⟨hi,?_⟩
  apply (integral_mono_ae hi ((hid.mul_const B).restrict (s := Ioo 0 epsilon)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with b hb
    exact hbound b hb)).trans
  have hfull : (∫ b in Ioo 0 epsilon, depth b*B) ≤ ∫ b, depth b*B :=
    integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall fun b => mul_nonneg (hdepth0 b) hB) (hid.mul_const B)
  apply hfull.trans
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (integral_geometricBoundaryDepth_le hepsilon.le hG) hB

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceRadialLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A radial one-level loss is cut off to the near-boundary region.
It is measurable and uniformly bounded by the fixed total/self log ratio. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem radialBoundaryLoss_measurable (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (epsilon : ℝ) (i : ℕ) (top : τ) (x : X) :
    Measurable (g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x) :=
  ((measurable_const.div ((g.nearbyEligibleMass_measurable_radius tops slope precision cutoff
    weight i (slope top) x).comp (measurable_id.mul_const (g.width i)))).log).indicator measurableSet_Ioo

theorem radialBoundaryLoss_bounds (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (epsilon : ℝ) (i : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) i) (x : X) (b : ℝ) :
    0 ≤ g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x b ∧
      g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x b ≤
        Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  have hw0 := hw top x
  have htotal : weight top x ≤ ∑ t ∈ tops, weight t x :=
    Finset.single_le_sum (fun t _ => (hw t x).le) htop
  have hBlog := Real.log_nonneg ((one_le_div hw0).mpr htotal)
  by_cases hb : b ∈ Ioo 0 epsilon
  · rw [radialBoundaryLoss,indicator_of_mem hb]
    have hself := g.nearbyEligibleMass_self_le tops slope precision cutoff weight
      (fun t x => (hw t x).le) i top htop he (mul_pos hb.1 (g.width_pos i)) x
    have hinner : 0 < g.nearbyEligibleMass tops slope precision cutoff weight i
        (b*g.width i) (slope top) x := hw0.trans_le hself
    have houter := g.nearbyEligibleMass_le_total tops slope precision cutoff weight
      (fun t x => (hw t x).le) i (epsilon*g.width i) (slope top) x
    have horder := g.nearbyEligibleMass_le_of_scale (i := i) (j := i) tops slope precision cutoff weight hp
      (fun t x => (hw t x).le) le_rfl (mul_le_mul_of_nonneg_right hb.2.le (g.width_pos i).le)
      (slope top) x
    refine ⟨Real.log_nonneg ((one_le_div hinner).mpr horder),?_⟩
    apply Real.log_le_log (div_pos (hinner.trans_le horder) hinner)
    exact div_le_div₀ (hw0.trans_le htotal).le houter hw0 hself
  · rw [radialBoundaryLoss,indicator_of_notMem hb]
    exact ⟨le_rfl,hBlog⟩

theorem radialBoundaryLoss_intervalIntegrable (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (epsilon : ℝ) (i : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) i) (x : X) (a b : ℝ) :
    IntervalIntegrable (g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x)
      volume a b := by
  have hi (a b : ℝ) : IntegrableOn
      (g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x) (Ioc a b) volume := by
    apply (integrableOn_const (μ := volume) (C := Real.log ((∑ t ∈ tops, weight t x)/weight top x))
      (by simp)).mono' (g.radialBoundaryLoss_measurable tops slope precision cutoff weight epsilon i top x).aestronglyMeasurable
    filter_upwards [] with u
    have hu := g.radialBoundaryLoss_bounds tops slope precision cutoff weight hp hw epsilon i top htop he x u
    rw [Real.norm_eq_abs,abs_of_nonneg hu.1]
    exact hu.2
  exact ⟨hi a b,hi b a⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source boundary log loss is bounded by the radial near-boundary
majorant at its actual normalized distance. Far from boundaries it vanishes. -/

noncomputable section
open Set
namespace LipschitzHilbert.AngularGrid
variable {τ X : Type*}

theorem source_boundary_log_loss_le_majorant (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (i : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) i) (x : X) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let b := g.boundaryDistance i (slope top)/g.width i
    0 < b →
    Real.log (g.sourceBoundaryMass tops slope precision cutoff weight K (g.sourceBoundaryGap L)
      i (g.index (i+1) (slope top)) x /
        g.mass tops slope precision cutoff weight i (g.index i (slope top)) x) ≤
      g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x b := by
  intro epsilon b hb
  by_cases hnear : b < epsilon
  · rw [radialBoundaryLoss,indicator_of_mem (show b ∈ Ioo 0 epsilon from ⟨hb,hnear⟩)]
    apply g.source_boundary_log_loss_le_radial L hbranch tops slope precision cutoff weight hp hw
      hK i b hb hnear.le top htop he _ x
    dsimp only [b]
    rw [div_mul_cancel₀ _ (g.width_pos i).ne']
  · rw [radialBoundaryLoss,indicator_of_notMem (show b ∉ Ioo 0 epsilon from fun h => hnear h.2)]
    have hfar : epsilon*g.width i ≤ g.boundaryDistance i (slope top) :=
      (le_div_iff₀ (g.width_pos i)).mp (le_of_not_gt hnear)
    have heq := g.boundary_mass_eq_parent_of_far tops slope precision cutoff weight hp
      (i+1-K) i (g.sourceBoundaryGap L i) (epsilon*g.width i) (slope top)
      (g.source_boundary_radius L hbranch i) hfar x
    rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hK,heq,
      div_self (g.path_mass_pos tops slope precision cutoff weight hw i top htop he x).ne',Real.log_one]

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceRadialAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Averaging the literal radial majorants over one common translation
costs 4 epsilon times the total/self logarithm, independently of depth. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem radialBoundaryLoss_sum_integral (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1/2)
    (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : ∀ i < N, g.eligible cutoff (precision top) i) (x : X) :
    (∫ b in (0:ℝ)..(1/2:ℝ), ∑ i ∈ Finset.range N,
      g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x b) ≤
        2*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  let loss := fun b => ∑ i ∈ Finset.range N, Real.log
    (g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x /
      g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x)
  have heq : (fun b => ∑ i ∈ Finset.range N,
      g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x b) =
        (Ioo 0 epsilon).indicator loss := by
    funext b
    by_cases hb : b ∈ Ioo 0 epsilon
    · simp only [radialBoundaryLoss,indicator_of_mem hb]
      rfl
    · simp only [radialBoundaryLoss,indicator_of_notMem hb,Finset.sum_const_zero]
  rw [heq,intervalIntegral.integral_of_le (by norm_num),setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.mpr (show Ioo 0 epsilon ⊆ Ioc 0 (1/2:ℝ) from fun b hb =>
      ⟨hb.1,hb.2.le.trans hepsilon1⟩)]
  exact (g.radial_log_ratio_integral_le tops slope precision cutoff weight hp hw epsilon hepsilon
    N top htop he x).2

theorem radialBoundaryLoss_common_average (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1/2)
    (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : ∀ i < N, g.eligible cutoff (precision top) i) (x : X) :
    (∫ origin in (0:ℝ)..g.rootWidth, ∑ i ∈ Finset.range N,
      g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x
        ((g.withOrigin origin).boundaryDistance i (slope top)/g.width i)) / g.rootWidth ≤
      4*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  let B := Real.log ((∑ t ∈ tops, weight t x)/weight top x)
  let f := fun i => g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x
  let dist := fun i origin => (g.withOrigin origin).boundaryDistance i (slope top)/g.width i
  have hm (i : ℕ) : Measurable (dist i) := by
    simp only [dist,g.normalized_boundaryDistance_withOrigin]
    exact unitBoundaryDistance_measurable.comp ((measurable_const.sub measurable_id).div_const _)
  have hint (i : ℕ) (hi : i ∈ Finset.range N) :
      IntervalIntegrable (fun origin => f i (dist i origin)) volume 0 g.rootWidth := by
    have hib (a b : ℝ) : IntegrableOn (fun origin => f i (dist i origin)) (Ioc a b) volume := by
      apply (integrableOn_const (μ := volume) (C := B) (by simp)).mono'
        ((g.radialBoundaryLoss_measurable tops slope precision cutoff weight epsilon i top x).comp (hm i)).aestronglyMeasurable
      filter_upwards [] with origin
      have hb := g.radialBoundaryLoss_bounds tops slope precision cutoff weight hp hw epsilon i top
        htop (he i (Finset.mem_range.mp hi)) x (dist i origin)
      dsimp only [Function.comp_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
      exact hb.2
    exact ⟨hib 0 g.rootWidth,hib g.rootWidth 0⟩
  have hhalf (i : ℕ) (hi : i ∈ Finset.range N) : IntervalIntegrable (f i) volume 0 (1/2:ℝ) :=
    g.radialBoundaryLoss_intervalIntegrable tops slope precision cutoff weight hp hw epsilon i top htop
      (he i (Finset.mem_range.mp hi)) x 0 (1/2)
  change (∫ origin in (0:ℝ)..g.rootWidth, ∑ i ∈ Finset.range N, f i (dist i origin))/g.rootWidth ≤ 4*epsilon*B
  rw [intervalIntegral.integral_finsetSum hint]
  have heq (i : ℕ) (hi : i ∈ Finset.range N) :
      (∫ origin in (0:ℝ)..g.rootWidth, f i (dist i origin)) =
        (2*g.rootWidth)*(∫ b in (0:ℝ)..(1/2:ℝ), f i b) :=
    g.common_translation_boundary_integral i (slope top) (f i) (hhalf i hi)
  rw [Finset.sum_congr rfl heq,← Finset.mul_sum,← intervalIntegral.integral_finsetSum hhalf]
  apply (div_le_iff₀ g.rootWidth_pos).mpr
  have hb := g.radialBoundaryLoss_sum_integral tops slope precision cutoff weight hp hw epsilon
    hepsilon hepsilon1 N top htop he x
  change (∫ b in (0:ℝ)..(1/2:ℝ), ∑ i ∈ Finset.range N, f i b) ≤ 2*epsilon*B at hb
  have hc : 0 ≤ (2:ℝ)*g.rootWidth := mul_nonneg (by norm_num) g.rootWidth_pos.le
  have h := mul_le_mul_of_nonneg_left hb hc
  nlinarith

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryExpectedLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expected logarithmic boundary loss for the literal source coefficients.
Only one common angular translation is averaged; the eligibility cutoff
and the terminal path length are retained. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem source_boundary_expected_log_loss (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : ∀ i < N, g.eligible cutoff (precision top) i) (x : X) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let loss := fun origin => (g.withOrigin origin).sourceBoundaryLogLoss tops slope precision cutoff
      weight K (g.sourceBoundaryGap L) N top x
    IntervalIntegrable loss volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, loss origin)/g.rootWidth ≤
        4*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  intro epsilon loss
  let B := Real.log ((∑ t ∈ tops, weight t x)/weight top x)
  let ell := fun i origin => Real.log
    ((g.withOrigin origin).sourceBoundaryMass tops slope precision cutoff weight K
      (g.sourceBoundaryGap L) i ((g.withOrigin origin).index (i+1) (slope top)) x /
      (g.withOrigin origin).mass tops slope precision cutoff weight i
        ((g.withOrigin origin).index i (slope top)) x)
  let major := fun i origin => g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x
    ((g.withOrigin origin).boundaryDistance i (slope top)/g.width i)
  have hbounded (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ u, 0 ≤ f u ∧ f u ≤ B) :
      IntervalIntegrable f volume 0 g.rootWidth := by
    have hint (a b : ℝ) : IntegrableOn f (Ioc a b) volume := by
      apply (integrableOn_const (μ := volume) (C := B) (by simp)).mono' hf.aestronglyMeasurable
      filter_upwards [] with u
      rw [Real.norm_eq_abs,abs_of_nonneg (hb u).1]
      exact (hb u).2
    exact ⟨hint 0 g.rootWidth,hint g.rootWidth 0⟩
  have hel (i : ℕ) (hi : i ∈ Finset.range N) : IntervalIntegrable (ell i) volume 0 g.rootWidth := by
    apply hbounded
    · exact g.measurable_source_boundary_log_loss_withOrigin tops slope precision cutoff weight hK
        (g.sourceBoundaryGap L) i (slope top) x
    · intro origin
      exact (g.withOrigin origin).source_boundary_log_loss_bounds tops slope precision cutoff weight
        hp hw hK (g.sourceBoundaryGap L) i top htop (he i (Finset.mem_range.mp hi)) x
  have hmajor (i : ℕ) (hi : i ∈ Finset.range N) : IntervalIntegrable (major i) volume 0 g.rootWidth := by
    apply hbounded
    · apply (g.radialBoundaryLoss_measurable tops slope precision cutoff weight epsilon i top x).comp
      simp only [normalized_boundaryDistance_withOrigin]
      exact unitBoundaryDistance_measurable.comp ((measurable_const.sub measurable_id).div_const _)
    · intro origin
      exact g.radialBoundaryLoss_bounds tops slope precision cutoff weight hp hw epsilon i top htop
        (he i (Finset.mem_range.mp hi)) x _
  have hae (i : ℕ) (hi : i ∈ Finset.range N) : ∀ᵐ origin, ell i origin ≤ major i origin := by
    filter_upwards [g.ae_normalized_boundaryDistance_pos i (slope top)] with origin ho
    exact (g.withOrigin origin).source_boundary_log_loss_le_majorant L hbranch tops slope precision cutoff
      weight hp hw hK i top htop (he i (Finset.mem_range.mp hi)) x ho
  have hsum : ∀ᵐ origin, (∑ i ∈ Finset.range N, ell i origin) ≤ ∑ i ∈ Finset.range N, major i origin := by
    have hforall := ae_all_iff.mpr fun i : Fin N => hae i (Finset.mem_range.mpr i.isLt)
    filter_upwards [hforall] with origin ho
    exact Finset.sum_le_sum fun i hi => ho ⟨i,Finset.mem_range.mp hi⟩
  have hi : IntervalIntegrable loss volume 0 g.rootWidth := by
    change IntervalIntegrable (fun origin => ∑ i ∈ Finset.range N, ell i origin) volume 0 g.rootWidth
    convert IntervalIntegrable.sum (Finset.range N) hel using 1
    all_goals try with_reducible_and_instances rfl
    ext origin
    simp only [Finset.sum_apply]
  refine ⟨hi,?_⟩
  have hm : IntervalIntegrable (fun origin => ∑ i ∈ Finset.range N, major i origin) volume 0 g.rootWidth := by
    convert IntervalIntegrable.sum (Finset.range N) hmajor using 1
    all_goals try with_reducible_and_instances rfl
    ext origin
    simp only [Finset.sum_apply]
  have hb := intervalIntegral.integral_mono_ae g.rootWidth_pos.le hi hm hsum
  apply (div_le_div_of_nonneg_right hb g.rootWidth_pos.le).trans
  exact g.radialBoundaryLoss_common_average tops slope precision cutoff weight hp hw epsilon
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (SourceParameters.step_pos L) _)) hsmall N top htop he x

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceBoundaryPacketError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary coefficient deficits acting on the original stopping bands.
The bound uses their raw prefix sums, with no loss in the number of levels. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sourceBoundaryCoefficient_bounds (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N)
    (a : ℝ) (ha : 0 ≤ a) (x : X) :
    0 < g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap N top a x ∧
      g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap N top a x ≤ 1 := by
  constructor
  · rw [g.sourceBoundaryCoefficient_eq_exp tops slope precision cutoff weight hp hw hK gap N top htop he a x]
    exact Real.exp_pos _
  · have h := g.sourceBoundaryCoefficient_antitone tops slope precision cutoff weight hp hw hK gap
      (Nat.zero_le N) top htop he a ha x
    simpa only [sourceBoundaryCoefficient,Finset.range_zero,Finset.prod_empty] using h

theorem measurable_sourceBoundaryLogLoss_withOrigin (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : τ) (x : X) :
    Measurable (fun origin => (g.withOrigin origin).sourceBoundaryLogLoss
      tops slope precision cutoff weight K gap N top x) := by
  unfold sourceBoundaryLogLoss
  apply Finset.measurable_sum
  intro i _
  exact g.measurable_source_boundary_log_loss_withOrigin tops slope precision cutoff weight hK gap i (slope top) x

theorem measurable_sourceBoundaryCoefficient_withOrigin (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N) (a : ℝ) (x : X) :
    Measurable (fun origin => (g.withOrigin origin).sourceBoundaryCoefficient
      tops slope precision cutoff weight K gap N top a x) := by
  have heq : (fun origin => (g.withOrigin origin).sourceBoundaryCoefficient
      tops slope precision cutoff weight K gap N top a x) =
      (fun origin => Real.exp (-a*(g.withOrigin origin).sourceBoundaryLogLoss
        tops slope precision cutoff weight K gap N top x)) := by
    funext origin
    exact (g.withOrigin origin).sourceBoundaryCoefficient_eq_exp tops slope precision cutoff weight
      hp hw hK gap N top htop he a x
  rw [heq]
  exact (measurable_const.mul (g.measurable_sourceBoundaryLogLoss_withOrigin tops slope precision
    cutoff weight hK gap N top x)).exp

theorem source_boundary_deficit_sum_le_log_loss (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (N : ℕ) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) N)
    (a : ℝ) (ha : 0 ≤ a) (x : X) (f : ℕ → E) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ k ≤ N, ‖∑ j ∈ Finset.range (k+1), f j‖ ≤ B) :
    ‖∑ j ∈ Finset.range (N+1),
      ((1-g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap j top a x : ℝ):ℂ) • f j‖ ≤
      2*a*B*g.sourceBoundaryLogLoss tops slope precision cutoff weight K gap N top x := by
  let w := fun j => 1-g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap j top a x
  have hnonneg (j : ℕ) (hj : j ≤ N) : 0 ≤ w j :=
    sub_nonneg.mpr (g.sourceBoundaryCoefficient_bounds tops slope precision cutoff weight hp hw hK gap
      j top htop (g.eligible_of_le (hp top htop) hj he) a ha x).2
  have hmono (i : ℕ) (_hi : i ≤ N) (j : ℕ) (hj : j ≤ N) (hij : i ≤ j) : w i ≤ w j := by
    exact sub_le_sub_left (g.sourceBoundaryCoefficient_antitone tops slope precision cutoff weight
      hp hw hK gap hij top htop (g.eligible_of_le (hp top htop) hj he) a ha x) 1
  have h := norm_monotone_coefficient_sum w f N B hB0 hnonneg hmono hB
  apply h.trans
  have hd := mul_le_mul_of_nonneg_left (g.sourceBoundaryCoefficient_deficit_le tops slope precision
    cutoff weight hp hw hK gap N top htop he a x) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB0)
  dsimp only [w]
  nlinarith only [hd]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem source_boundary_expected_packet_error (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) N) (a : ℝ) (ha : 0 ≤ a)
    (x : X) (f : ℕ → E) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ k ≤ N, ‖∑ j ∈ Finset.range (k+1), f j‖ ≤ B) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let err := fun origin => ‖∑ j ∈ Finset.range (N+1),
      ((1-(g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K
        (g.sourceBoundaryGap L) j top a x : ℝ):ℂ) • f j‖
    IntervalIntegrable err volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, err origin)/g.rootWidth ≤
        8*a*B*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  intro epsilon err
  let loss := fun origin => (g.withOrigin origin).sourceBoundaryLogLoss tops slope precision cutoff
    weight K (g.sourceBoundaryGap L) N top x
  have hl := g.source_boundary_expected_log_loss L hbranch hsmall tops slope precision cutoff weight
    hp hw hK N top htop (fun i hi => g.eligible_of_le (hp top htop) hi.le he) x
  have hbound (origin : ℝ) : err origin ≤ (2*a*B)*loss origin :=
    (g.withOrigin origin).source_boundary_deficit_sum_le_log_loss tops slope precision cutoff weight
      hp hw hK (g.sourceBoundaryGap L) N top htop he a ha x f B hB0 hB
  have hm : Measurable err := by
    apply Measurable.norm
    apply Finset.measurable_sum
    intro j hj
    apply Measurable.smul _ measurable_const
    exact (Complex.continuous_ofReal.measurable.comp
      (measurable_const.sub (g.measurable_sourceBoundaryCoefficient_withOrigin tops slope precision
        cutoff weight hp hw hK (g.sourceBoundaryGap L) j top htop
        (g.eligible_of_le (hp top htop) (by have := Finset.mem_range.mp hj; omega) he) a x)))
  have hc : 0 ≤ 2*a*B := mul_nonneg (mul_nonneg (by norm_num) ha) hB0
  have hi : IntervalIntegrable err volume 0 g.rootWidth := by
    apply (hl.1.const_mul (2*a*B)).mono_fun' hm.aestronglyMeasurable
    filter_upwards [] with origin
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ err origin from norm_nonneg _)] using hbound origin
  refine ⟨hi,?_⟩
  have hh := intervalIntegral.integral_mono g.rootWidth_pos.le hi (hl.1.const_mul (2*a*B)) hbound
  rw [intervalIntegral.integral_const_mul] at hh
  have hh' := div_le_div_of_nonneg_right hh g.rootWidth_pos.le
  have hh'' := mul_le_mul_of_nonneg_left hl.2 hc
  calc
    (∫ origin in (0:ℝ)..g.rootWidth, err origin)/g.rootWidth ≤
        (2*a*B)*((∫ origin in (0:ℝ)..g.rootWidth, loss origin)/g.rootWidth) := by
      convert hh' using 1 <;> first | rfl | ring
    _ ≤ (2*a*B)*(4*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x)) := hh''
    _ = _ := by ring

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceBoundaryPacketRegroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-packet regrouping for the expected boundary error.
The only prefix bound is on the original packet values. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
theorem packet_stopping_prefix_bound {N : ℕ} (packets : Finset σ)
    (lengthIndex : σ → Fin N) (stop : Fin N → ℕ) (hstop : Antitone stop)
    (value : σ → E) (B : ℝ)
    (hinterval : ∀ l u : ℕ, l ≤ u → u ≤ N →
      ‖∑ s ∈ packets.filter (fun s => l ≤ (lengthIndex s).val ∧ (lengthIndex s).val < u), value s‖ ≤ B)
    (k : ℕ) :
    ‖∑ s ∈ packets.filter (fun s => stop (lengthIndex s) ≤ k), value s‖ ≤ B := by
  obtain ⟨l,u,hlu,hu,hband⟩ := antitone_stopping_band_interval stop hstop 0 (k+1)
  have hset : packets.filter (fun s => stop (lengthIndex s) ≤ k) =
      packets.filter (fun s => l ≤ (lengthIndex s).val ∧ (lengthIndex s).val < u) := by
    ext s
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro _
    simpa only [Nat.zero_le,true_and,Nat.lt_add_one_iff] using hband (lengthIndex s)
  rw [hset]
  exact hinterval l u hlu hu

theorem sum_weighted_stopping_fibers (packets : Finset σ) (stop : σ → ℕ)
    (value : σ → E) (w : ℕ → ℂ) (M : ℕ) (hmax : ∀ s ∈ packets, stop s ≤ M) :
    (∑ j ∈ Finset.range (M+1), w j • ∑ s ∈ packets.filter (fun s => stop s = j), value s) =
      ∑ s ∈ packets, w (stop s) • value s := by
  calc
    _ = ∑ j ∈ Finset.range (M+1), ∑ s ∈ packets.filter (fun s => stop s = j),
        w (stop s) • value s := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun s hs => Finset.mem_range.mpr (Nat.lt_succ_of_le (hmax s hs))) _

namespace AngularGrid
variable {τ X : Type*} [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem source_boundary_expected_finite_packet_error (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (M : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) M) (a : ℝ) (ha : 0 ≤ a) (x : X)
    (packets : Finset σ) (stop : σ → ℕ) (value : σ → E)
    (hmax : ∀ s ∈ packets, stop s ≤ M) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ k ≤ M, ‖∑ s ∈ packets.filter (fun s => stop s ≤ k), value s‖ ≤ B) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let err := fun origin => ‖∑ s ∈ packets,
      ((1-(g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K
        (g.sourceBoundaryGap L) (stop s) top a x : ℝ):ℂ) • value s‖
    IntervalIntegrable err volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, err origin)/g.rootWidth ≤
        8*a*B*epsilon*Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  intro epsilon err
  let f := fun j => ∑ s ∈ packets.filter (fun s => stop s = j), value s
  have hprefix (k : ℕ) (hk : k ≤ M) : ‖∑ j ∈ Finset.range (k+1), f j‖ ≤ B := by
    dsimp only [f]
    rw [← Nat.Ico_zero_eq_range, sum_packet_stopping_fibers]
    simpa only [Nat.zero_le,true_and,Nat.lt_add_one_iff] using hB k hk
  have hb := g.source_boundary_expected_packet_error L hbranch hsmall tops slope precision cutoff weight
    hp hw hK M top htop he a ha x f B hB0 hprefix
  have heq : (fun origin => ‖∑ j ∈ Finset.range (M+1),
      ((1-(g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K
        (g.sourceBoundaryGap L) j top a x : ℝ):ℂ) • f j‖) = err := by
    funext origin
    congr 1
    exact sum_weighted_stopping_fibers packets stop value _ M hmax
  simpa only [heq] using hb

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataMaskedValue
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal physical top masks for unrestricted packets. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
variable (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

theorem physicalMaskedValue_eq_cross_at (z : ℝ×ℝ) (q : P.PacketIndex) :
    P.physicalMaskedValue alt hAlt t b v g T L A z q =
      (T q.1 q.2.1 q.2.2).mask L A z • P.crossPacketValue alt hAlt t b v g z q := by
  ext k
  simp only [physicalMaskedValue,crossPacketValue,WithLp.ofLp_toLp,PiLp.smul_apply,
    Complex.real_smul]
  ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataMaskedBand
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact physical length bands of unrestricted masked packets. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

theorem physicalMaskedValue_length_sum (y x : ℝ) (j : Fin N) :
    (∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => q.1 = j),
      P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x) q) =
        P.physicalMaskedBand alt hAlt t b v g T L A y j x := by
  classical
  rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [ite_true, if_true]
    ext k
    simp only [Fintype.sum_sigma,physicalMaskedValue,physicalMaskedBand,
      WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]
  · intro k _ hkj
    simp only [hkj,ite_false, if_false,Finset.sum_const_zero]
  · simp

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedPhysical
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact assignment and length regrouping of the physical packet sum. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)

theorem assignedPhysicalBands_eq (z : ℝ×ℝ) (p : τ×Fin N) :
    P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned z p =
      ∑ q∈packets.filter (fun q => (assigned q,q.1)=p),
        P.physicalMaskedValue alt hAlt t b v f T L A z q := rfl

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned top restrictions with common label and item types. The top
is part of the label, so each top family contains exactly its own packets
and the family-valued concentration and path estimates apply literally. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem sum_assignedTopPackets {E : Type*} [AddCommMonoid E]
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
    (f : P.PacketIndex → E) :
    (∑ q : (P.assignedTopFamily packets assigned top).PacketIndex,
      f ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩) =
      ∑ q ∈ packets.filter (fun q => assigned q = top), f q := by
  have h := Equiv.sum_comp (P.assignedTopPacketEquiv packets assigned top)
    (fun q => f q.val)
  exact h.trans (Finset.sum_subtype _ (p := fun q =>
    q ∈ packets.filter (fun q => assigned q = top)) (by simp) f).symm

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopAlternate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common-type assigned top families have exactly the original
physical bands, including original selector coefficients and top masks. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

theorem sum_assignedTopPackets_filter {E : Type*} [AddCommMonoid E]
    (top : τ) (f : P.PacketIndex → E) (keep : P.PacketIndex → Prop) :
    (∑ q ∈ Finset.univ.filter (fun q : (P.assignedTopFamily packets assigned top).PacketIndex =>
      keep ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩),
      f ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩) =
      ∑ q ∈ (packets.filter (fun q => assigned q = top)).filter keep, f q := by
  simpa only [Finset.sum_filter] using
    P.sum_assignedTopPackets packets assigned top (fun q => if keep q then f q else 0)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopSelector
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The assigned-top constructor preserves the original selectors,
packet spectra, and local label count. Its geometry is supplied by the
actual selected packets; the global longest-scale bound remains explicit. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)


section Reference
variable (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone)
  (hF : 0 ≤ F) (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top) oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top) oldSlope newSlope R cone w

theorem assignedTopReference_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (l : (Q).labels j)
    (u : P.AssignedTopItem packets assigned j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l).val.2) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l).val.2 u.val :=
  (P.assignedTopFamily packets assigned top).referenceFamily_physicalMultiplierCoefficient oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency (P.assignedTopSelector packets assigned top b) v f j l u

end Reference

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assigned top bands retain the actual top mask and physical packet. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

theorem assignedTopFamily_physicalMaskedValue (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (q : (P.assignedTopFamily packets assigned top).PacketIndex) :
    (P.assignedTopFamily packets assigned top).physicalMaskedValue
      (P.assignedTopAlternate packets assigned alt top)
      (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
      (fun j l => b j l.val.2) v f (fun j l u => T j l.val.2 u.val) L A z q =
      P.physicalMaskedValue alt hAlt t b v f T L A z
        ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩ := rfl

theorem assignedTopFamily_physicalMaskedBand (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (P.assignedTopFamily packets assigned top).physicalMaskedBand
      (P.assignedTopAlternate packets assigned alt top)
      (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
      (fun j l => b j l.val.2) v f (fun j l u => T j l.val.2 u.val)
      L A (z.2-t*z.1) j z.1 =
      P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned z (top,j) := by
  let Q := P.assignedTopFamily packets assigned top
  have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hband := Q.physicalMaskedValue_length_sum
    (P.assignedTopAlternate packets assigned alt top)
    (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
    (fun j l => b j l.val.2) v f (fun j l u => T j l.val.2 u.val) L A
    (z.2-t*z.1) z.1 j
  rw [hpoint] at hband
  apply hband.symm.trans
  have hs := P.sum_assignedTopPackets_filter packets assigned top
    (P.physicalMaskedValue alt hAlt t b v f T L A z) (fun q => q.1 = j)
  calc
    _ = ∑ q ∈ Finset.univ.filter (fun q : Q.PacketIndex => q.1 = j),
        P.physicalMaskedValue alt hAlt t b v f T L A z
          ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩ := by
      apply Finset.sum_congr rfl
      intro q _
      exact P.assignedTopFamily_physicalMaskedValue packets assigned alt hAlt top t b v f T L A z q
    _ = ∑ q ∈ (packets.filter (fun q => assigned q = top)).filter (fun q => q.1 = j),
        P.physicalMaskedValue alt hAlt t b v f T L A z q := by
      convert hs using 1 <;> first | (with_reducible_and_instances rfl) | (apply Finset.sum_congr)
      · ext q
        simp
      · intro q _
        rfl
      · ext q
        simp
      · intro q _
        rfl
    _ = _ := by
      rw [P.assignedPhysicalBands_eq alt hAlt t b v f T L A packets assigned z (top,j)]
      apply Finset.sum_congr
      · ext q
        simp only [Finset.mem_filter,Prod.mk.injEq,and_assoc]
      · intro q _
        rfl

/-- The mask on an assigned family is its single assigned top mask. -/
theorem assignedTopFamily_single_mask (top : τ) (T : τ → SlopeBox) :
    (fun j (l : (P.assignedTopFamily packets assigned top).labels j)
      (u : P.AssignedTopItem packets assigned j l) =>
        T (assigned ⟨j,⟨l.val.2,u.val⟩⟩)) = fun _ _ _ => T top := by
  funext j l u
  have ht : l.val.1 = top := Finset.mem_singleton.mp (Finset.mem_product.mp l.property).1
  rw [u.property.2,ht]

theorem assignedTopFamily_topMaskBand (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (T : τ → SlopeBox)
    (L A : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (P.assignedTopFamily packets assigned top).physicalMaskedBand
      (P.assignedTopAlternate packets assigned alt top)
      (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
      (fun j l => b j l.val.2) v f (fun _ _ _ => T top) L A (z.2-t*z.1) j z.1 =
      P.assignedPhysicalBands alt hAlt t b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j) := by
  have h := P.assignedTopFamily_physicalMaskedBand packets assigned alt hAlt top t b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z j
  rw [P.assignedTopFamily_single_mask packets assigned top T] at h
  exact h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original assigned-packet cone condition gives the full-family
condition required to recenter each common-type top family. -/

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem assignedTopFamily_referenceCondition (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
    (oldSlope newSlope R cone w : ℝ)
    (hcondition : ∀ u ∈ packets, assigned u = top →
      P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1) :
    ∀ q : (P.assignedTopFamily packets assigned top).PacketIndex,
      (P.assignedTopFamily packets assigned top).referenceCondition
        oldSlope newSlope R cone w q.1 q.2.1 := by
  intro q
  have hq := (P.assignedTopPacketEquiv packets assigned top q).property
  change P.referenceCondition oldSlope newSlope R cone w q.1 q.2.1.val.2
  exact hcondition _ (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceMasked
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact masked amplitudes and residuals survive the local reference change. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F)
  (hwide : cone*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physicalMaskedValue
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (u : (Q).PacketIndex) :
    (Q).physicalMaskedValue (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
      newSlope (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l)) L A z u =
    P.physicalMaskedValue alt hAlt oldSlope b v f T L A z ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ := by
  ext k
  simp only [physicalMaskedValue,SourceLabeledLattice.physicalMaskedValue,WithLp.ofLp_toLp]
  rw [P.referenceFamily_physicalMultiplierCoefficient oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency]
  rw [P.referenceFamily_alternate_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceBand
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recentring an entire already-selected top family preserves its
physical length bands. Only the literal short-cone membership is needed. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem referenceFamily_physicalMaskedBand_all (P : PacketLatticeData N κ Label Item)
    (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (hcondition : ∀ u : P.PacketIndex,
      P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    Q.physicalMaskedBand (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
      newSlope (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l))
      L A (z.2-newSlope*z.1) j z.1 =
    P.physicalMaskedBand alt hAlt oldSlope b v f T L A (z.2-oldSlope*z.1) j z.1 := by
  intro Q orig
  have hpoint (s : ℝ) : (z.1,z.2-s*z.1+s*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hQ := Q.physicalMaskedValue_length_sum (fun j l => alt j (orig j l))
    (fun j l => hAlt j (orig j l)) newSlope (fun j l => b j (orig j l)) v f
    (fun j l => T j (orig j l)) L A (z.2-newSlope*z.1) z.1 j
  rw [hpoint newSlope] at hQ
  have hP := P.physicalMaskedValue_length_sum alt hAlt oldSlope b v f T L A
    (z.2-oldSlope*z.1) z.1 j
  rw [hpoint oldSlope] at hP
  apply hQ.symm.trans
  apply Eq.trans _ hP
  have h := P.sum_referenceFamily_selected oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency Finset.univ
    (fun u => if u.1 = j then P.physicalMaskedValue alt hAlt oldSlope b v f T L A z u else 0)
    (fun u _ => hcondition u)
  simp only [Finset.sum_filter,Finset.mem_univ,ite_true, if_true] at h
  simp only [Finset.sum_filter]
  calc
    _ = ∑ q : Q.PacketIndex, if q.1 = j then
        P.physicalMaskedValue alt hAlt oldSlope b v f T L A z
          ⟨q.1,⟨orig q.1 q.2.1,q.2.2⟩⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      split_ifs
      · exact P.referenceFamily_physicalMaskedValue oldSlope newSlope R cone w F
          hw hcone hF hwide hfrequency alt hAlt b v f T L A z q
      · rfl
    _ = _ := by convert h using 1

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedTopEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only nonempty assigned scales impose a reference length restriction. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ) (top : τ)
  (oldSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (T : τ → SlopeBox)
local notation "Q" => referenceFamily (P.assignedTopFamily packets assigned top)
  oldSlope (SlopeBox.slope (T top)) R cone w F hw hcone hF hwide hfrequency
local notation "orig" => referenceOriginalLabel (P.assignedTopFamily packets assigned top)
  oldSlope (SlopeBox.slope (T top)) R cone w


/-- The supported assigned/reference bands remain the original physical
synthesis with its original top mask, including empty scales. -/
theorem assignedTopReference_topMaskBand_all
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope R cone w q.1 q.2.1)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (L maskExponent : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (Q).physicalMaskedBand
      (fun j l u k => alt j (orig j l).val.2 u.val k)
      (fun j l u k => hAlt j (orig j l).val.2 u.val k)
      (T top).slope (fun j l => b j (orig j l).val.2) v f
      (fun _ _ _ => T top) L maskExponent (z.2-(T top).slope*z.1) j z.1 =
    P.assignedPhysicalBands alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent packets assigned z (top,j) := by
  have href := (P.assignedTopFamily packets assigned top).referenceFamily_physicalMaskedBand_all
    oldSlope (T top).slope R cone w F hw hcone hF hwide hfrequency
    (P.assignedTopFamily_referenceCondition packets assigned top oldSlope (T top).slope
      R cone w hcondition)
    (P.assignedTopAlternate packets assigned alt top)
    (P.assignedTopAlternate_bound packets assigned alt hAlt top)
    (P.assignedTopSelector packets assigned top b) v f (fun _ _ _ => T top) L maskExponent z j
  exact href.trans (P.assignedTopFamily_topMaskBand packets assigned alt hAlt top oldSlope
    b v f T L maskExponent z j)


end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedStoppedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual masked packet sum agrees with the bounded reference
families used in the supported stopped-path estimates. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

/-- The common-type recentered family used in the actual top envelopes. -/
local notation "Q" => assignedReferenceFamily P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

local notation "alts" => assignedReferenceAlternate P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt

local notation "halt" => assignedReferenceAlternate_bound P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt hAlt

variable (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

local notation "selector" => assignedReferenceSelector P packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency b

theorem assignedReference_rawBand_original (L A : ℝ) (z : ℝ×ℝ) (top : τ) (j : Fin N)
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope (R top) cone w q.1 q.2.1) :
    ((Q top).withProfile (alts top) (halt top)).rawBand
      (fun j l u => (T top).mask L A z •
        (Q top).physicalMultiplierCoefficient (T top).slope (selector top) v f j l u)
      0 j z.1 (z.2-(T top).slope*z.1) =
    P.assignedPhysicalBands alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j) := by
  have hr := (Q top).physicalMaskedBand_const_eq_rawBand (alts top) (halt top)
    (T top).slope (selector top) v f (T top) L A z j
  exact hr.symm.trans (P.assignedTopReference_topMaskBand_all packets assigned top
    oldSlope (R top) cone w F hw hcone hF hwide hfrequency T hcondition alt hAlt b v f L A z j)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataScaleGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem length_antitone (P : PacketLatticeData N κ Label Item) : Antitone P.length := by
  intro i j hij
  unfold length
  exact div_le_div_of_nonneg_left P.topLength_pos.le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij)

theorem precision_monotone (P : PacketLatticeData N κ Label Item) (w : ℝ) (hw : 0 ≤ w) :
    Monotone (fun j => w / P.length j) := by
  intro i j hij
  exact div_le_div_of_nonneg_left hw (P.length_pos j) (P.length_antitone hij)

theorem stopping_antitone (P : PacketLatticeData N κ Label Item) (grid : AngularGrid)
    (cutoff w : ℝ) (hw : 0 < w)
    (hstart : ∀ j, grid.eligible cutoff (w / P.length j) 0) :
    Antitone (fun j => grid.lastEligible cutoff (w / P.length j) (div_pos hw (P.length_pos j))) := by
  intro i j hij
  exact grid.lastEligible_antitone_precision cutoff (w / P.length i) (w / P.length j)
    (div_pos hw (P.length_pos i)) (div_pos hw (P.length_pos j))
    (P.precision_monotone w hw.le hij) (hstart i) (hstart j)


end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataPathRegularity
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original selected coefficients are fixed integrals. Spatial
regularity of the masked packets therefore requires no regularity of
the selecting direction field beyond that used to define them. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem physicalMaskedValue_continuous (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (q : P.PacketIndex) :
    Continuous (fun z => P.physicalMaskedValue alt hAlt t b v f T L A z q) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    ((T q.1 q.2.1 q.2.2).mask_continuous L A))).mul
    ((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).continuous

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataActualReferenceCentral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual parent/continuing reference union supplies every reference
event used in the original-packet central estimate. One good set is chosen
before all phases, and retains both its area and weighted bad-mass bounds. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_actual_reference_central_gain (hVariation : LepingleInput)
    (pProfile qEnv Cmass Cweight F c0 A_M d m decay maskExponent cStar cEta CEta cb Cb Lip cone : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*pProfile+13) (2*pProfile+17)+3/2) ≤ A_M)
    (hDweight : 2 < (Dweight:ℝ)) (hd : 0 ≤ d) (hm : 0 ≤ m)
    (hqm : 2*(qEnv+6)+2 ≤ m) (hCmassM : Cmass ≤ m) (hdecay : 0 ≤ decay)
    (hMask : 1 < maskExponent) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hLip : 0 ≤ Lip)
    (hgap : cStar < cEta*cb) (hcone : 0 ≤ cone) (hconeK : cone ≤ Kcount) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item),
    ∀ (tops : Finset τ) (T : τ → SlopeBox)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope w : ℝ) (hw : 0 < w)
      (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ k, c0/w ≤ |P.frequency k|) →
      (F*cone+2)*P.referenceEnvelopeConstant ≤ L^pProfile →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
    (∀ j l k s, b j l k s ≠ 0 →
      cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
        |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
    (∀ j l u k xi eta,
      planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    (∀ j l u k xi eta,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    let Kw := L^(maskExponent+2)
    let R := fun t => (T t).length
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt
    ∀ (hwideResidual : (cone+(SourceParameters.branching L)^2)*w ≤ P.width)
      (hwideParent : (cone+(SourceParameters.branching L)^3)*w ≤ P.width),
    (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hcount) →
    (∀ t ∈ tops, P.width ≤ Kw*(T t).width) →
    3+2*(8*Dweight+1) ≤ P.order →
    (∀ t ∈ tops, P.scale = 4*(Kw*(T t).width)) →
    (∀ u ∈ packets, |P.actualX u.1 u.2.1 u.2.2-(T (assigned u)).x|+P.length u.1 ≤
      Kw*(T (assigned u)).length) →
    (∀ u ∈ packets,
      |P.actualZ u.1 u.2.1 u.2.2+(oldSlope-(T (assigned u)).slope)*P.actualX u.1 u.2.1 u.2.2-
        ((T (assigned u)).y-(T (assigned u)).slope*(T (assigned u)).x)|+P.width ≤
      Kw*(T (assigned u)).width) →
    (∀ u ∈ packets, assigned u ∈ tops) →
    (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
    (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
      (R (assigned u)) cone w u.1 u.2.1) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (Dphase Nmass A : ℝ), 2 ≤ Dphase → Dphase ≤ L^d → 0 < Nmass → Real.log Nmass ≤ 2*L →
      0 ≤ A → A ≤ L^qEnv →
    let p := Real.sqrt L
    let mu := PhaseCombinatorics.phaseMu Dphase p
    let a := mu/(SourceParameters.blockCount L:ℝ)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let countTop := fun shift => g.sourceTopTerminalCount T cut w hw hKb shift
    let count := fun shift => tops.sup (countTop shift)
    ∀ (Z0 : Set (ℝ×ℝ)), MeasurableSet Z0 →
    let wide : ∀ i : Option (Fin (SourceParameters.blockCount L)),
        (cone+(SourceParameters.branching L)^(if i.isNone then 3 else 2))*w ≤ P.width := by
      intro i
      cases i with
      | none => exact hwideParent
      | some i => exact hwideResidual
    let bad := P.actualReferenceBad alt hAlt L oldSlope cone w F hw hcone hF wide hfrequency
      b v f g tops T packets assigned hKb maskExponent pProfile
    let good := sourceGoodPathSet Z0 tops weight bad L
    (∀ z ∈ Z0, ∀ t ∈ tops, weight t z ≤ Cweight) →
    (∀ z ∈ Z0, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
    (∀ z ∈ Z0, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
    (∀ z ∈ Z0, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N → ∀ yy,
      |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      let V := ((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper
      ‖V z.1 yy‖+(T t).width*
        ‖covariantSignal P.frequency (fun k zz => V z.1 zz k) yy‖ ≤ A*(weight t z)^8) →
    (∀ shift, ∀ j < count shift, ∀ z ∈ Z0, ∀ I : Finset τ, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, w/(T t).length ≤ g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |(T t).slope-(T u).slope| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1))) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u →
        g.sourceGap L (ShiftedBlocks.endpoint shift (j+1)) ≤ |(T t).slope-(T u).slope|) →
      (I.card:ℝ) ≤ Dphase/100) →
    ∀ (start Fmass : ℝ), 0 < Fmass → L/2 ≤ Real.log Nmass →
      (volume.prod volume) Z0 ≠ ∞ → (volume.prod volume).real Z0 ≤ Fmass →
      (∀ t ∈ tops, start ≤ (T t).slope ∧ (T t).slope ≤ start+g.rootWidth) →
      (∑ t ∈ tops, ∫ z, weight t z ∂volume.prod volume) ≤ L^m*Nmass^2*Fmass →
    let W := fun z => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cut weight (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
        (stop s.1) (assigned s) a z : ℝ):ℂ) • original z s
    Integrable (sourceBadPathMass tops weight bad) (volume.prod volume) ∧
      (∫ z, sourceBadPathMass tops weight bad z ∂volume.prod volume) ≤
        (∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-10*L) ∧
      MeasurableSet good ∧ good ⊆ Z0 ∧
      (volume.prod volume) (Z0 \ good) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L)) ∧
      IntegrableOn (fun z => ‖W z‖) good (volume.prod volume) ∧
      (∫ z in good, ‖W z‖ ∂volume.prod volume) ≤ L^(-decay)*Nmass*Fmass := by
  filter_upwards [eventually_assigned_parent_central_gain pProfile qEnv Cmass Cweight F c0
      A_M d m decay Dweight Kcount Hcount hpProfile hqEnv hCmass hCweight hF hc0 hAM hchoice
      hDweight hd hm hqm hCmassM hdecay,
    eventually_actual_reference_area hVariation (Dweight:ℝ) (maskExponent+2) pProfile
      maskExponent F cStar cEta CEta cb Cb cone Lip Kcount Hcount
      hDweight hpProfile hMask hF hcStar hcEta hCEta hcb hCb hcone hLip hgap,
    SourceParameters.eventually_branching_ge (max 1 Cb),
    eventually_ge_atTop (256:ℝ)] with L hcentral harea0 hBlarge hL
  intro τ κ _ N Label Item _ P tops T packets assigned oldSlope w hw hwide hfrequency
    hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 hmotion hactive hspectrum haltSpectrum
    Kw R Q orig alts halt hwideResidual hwideParent hlocal hwidth horder hscale hX hZ
    hassigned hshort hcondition g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A
    hD hDL hNmass hlogN hA hAq p mu a cut weight stop original countTop count
    Z0 hZ0 wide bad good hweight htotal hmass hconc hcount start Fmass hFmass hloglo
    hZ0finite hmeasure hslope hweightTotal W
  have hL1 : 1 ≤ L := by linarith
  have hKw : 1 ≤ Kw := Real.one_le_rpow hL1 (by linarith)
  have hfactor : 1 ≤ F*cone+2 := by nlinarith [mul_nonneg hF hcone]
  have hPabs : P.referenceEnvelopeConstant ≤ L^pProfile :=
    (le_mul_of_one_le_left P.referenceEnvelopeConstant_pos.le hfactor).trans hP
  have hDw : 2 < Dweight := by exact_mod_cast hDweight
  have horder6 : 6 ≤ P.order := by omega
  have hB : 1 ≤ SourceParameters.branching L := (le_max_left _ _).trans hBlarge
  have hCbB : Cb ≤ SourceParameters.branching L := (le_max_right _ _).trans hBlarge
  have hband : Cb*w ≤ P.width := by
    apply (mul_le_mul_of_nonneg_right (show Cb ≤ cone+(SourceParameters.branching L)^3 from ?_) hw.le).trans hwideParent
    exact (hCbB.trans (le_self_pow₀ hB (by norm_num))).trans (le_add_of_nonneg_left hcone)
  have hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ (Kcount:ℝ)*(w/P.length j) := by
    intro j l k s hs
    exact (hsupp j l k s hs).trans
      (mul_le_mul_of_nonneg_right hconeK (div_pos hw (P.length_pos j)).le)
  have hpacketAngle : ∀ u ∈ packets,
      |oldSlope+P.rowSlope u.1 u.2.1-(T (assigned u)).slope| ≤ cone*(w/P.length u.1) := by
    intro u hu
    calc
      _ ≤ cone*w/P.length u.1 := (hcondition u hu).2
      _ = _ := by ring
  have ha := harea0 Kw hKw le_rfl N κ τ Label Item P horder6 hPabs alt hAlt oldSlope w hw
    wide hfrequency hband b hb hb1 hsupport hmotion hlocal hactive v hv f hf hf1 hspectrum haltSpectrum
    g tops T packets assigned hKb hshort hpacketAngle
    (fun u hu => htopWidth (assigned u) (hassigned u hu)) Z0 hZ0
  have hc := hcentral τ κ N Label Item P tops T packets assigned oldSlope cone w hw hcone hwide
    hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 maskExponent (2*pProfile+11)
    (by linarith) hwideResidual hwideParent hconeK hlocal hwidth horder hscale hX hZ hassigned hshort hcondition
    g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A hD hDL hNmass hlogN hA hAq
    Z0 bad hZ0 (fun t _ => P.actualReferenceBad_measurable alt hAlt L oldSlope cone w F hw hcone hF
      wide hfrequency b v f g tops T packets assigned hKb maskExponent pProfile t)
    hweight htotal hmass hconc hcount
    (by
      intro t _ z hz
      exact ha.2.2.2.2.2 t z hz.2 none)
    (by
      intro shift t _ z hz
      exact ha.2.2.2.2.2 t z hz.2 (some shift))
    start Fmass hFmass hloglo hZ0finite hmeasure hslope hweightTotal
  exact ⟨ha.1,ha.2.1,ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2.1,hc.1,hc.2⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedBoundaryPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concentration of a recentered assigned family controls the
original masked packet intervals and stopping prefixes. Empty length
fibers contribute zero; no longest-scale restriction is added. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ) (L A : ℝ) (z : ℝ×ℝ) (top : τ)

local notation "Q" => P.assignedReferenceFamily packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency top
local notation "orig" => P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency top
local notation "alts" => P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt top
local notation "halt" => P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt hAlt top
local notation "original" => P.physicalMaskedValue alt hAlt oldSlope b v f
  (fun j l u => T (assigned (Sigma.mk j (Sigma.mk l u)))) L A z

/-- Regrouping the original packets by length preserves the exact
assigned top subset. -/
theorem assignedPhysicalBands_interval_sum (lower upper : ℕ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper),
      P.assignedPhysicalBands alt hAlt oldSlope b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j)) =
      ∑ q ∈ packets.filter (fun q => assigned q = top ∧ lower ≤ q.1.val ∧ q.1.val < upper),
        original q := by
  let chosen := packets.filter (fun q => assigned q = top)
  let levels := Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper)
  calc
    _ = ∑ j ∈ levels, ∑ q ∈ chosen.filter (fun q => q.1 = j), original q := by
      apply Finset.sum_congr rfl
      intro j _
      rw [P.assignedPhysicalBands_eq alt hAlt oldSlope b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j)]
      apply Finset.sum_congr
      · ext q
        simp only [chosen,Finset.mem_filter,Prod.mk.injEq,and_assoc]
      · intro q _
        rfl
    _ = ∑ q ∈ chosen.filter (fun q => q.1 ∈ levels), original q :=
      Finset.sum_fiberwise_eq_sum_filter chosen levels (fun q => q.1) original
    _ = _ := by
      apply Finset.sum_congr
      · ext q
        simp only [chosen,levels,Finset.mem_filter,Finset.mem_univ,true_and,and_assoc]
      · intro q _
        rfl

/-- Exact original masked interval, expressed by the raw assigned
reference interval whose norm is bounded on the concentration good set. -/
theorem assignedPhysicalInterval_eq_maskedRawInterval
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope (R top) cone w q.1 q.2.1)
    (lower upper : ℕ) (hlu : lower ≤ upper) :
    (∑ q ∈ packets.filter (fun q => assigned q = top ∧ lower ≤ q.1.val ∧ q.1.val < upper),
      original q) =
      (T top).mask L A z • ((Q).withProfile alts halt).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u.val)
        0 lower upper z.1 (z.2-(T top).slope*z.1) := by
  have hcoeff : (Q).physicalMultiplierCoefficient (T top).slope
      (fun j l => b j (orig j l)) v f =
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned top oldSlope
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency b v f j l u
  have hraw := congrArg
    (fun co => ((Q).withProfile alts halt).rawInterval co 0 lower upper
      z.1 (z.2-(T top).slope*z.1)) hcoeff
  calc
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper),
        P.assignedPhysicalBands alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j) :=
      (P.assignedPhysicalBands_interval_sum packets assigned T oldSlope alt hAlt b v f
        L A z top lower upper).symm
    _ = ((Q).withProfile alts halt).rawInterval
        (fun j l u => (T top).mask L A z •
          (Q).physicalMultiplierCoefficient (T top).slope (fun j l => b j (orig j l)) v f j l u)
        0 lower upper z.1 (z.2-(T top).slope*z.1) := by
      rw [((Q).withProfile alts halt).rawInterval_eq_band_sum _ _ _ _ hlu]
      apply Finset.sum_congr rfl
      intro j _
      exact (P.assignedReference_rawBand_original packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency alt hAlt b v f L A z top j hcondition).symm
    _ = _ := by
      rw [((Q).withProfile alts halt).rawInterval_coeff_smul]
      exact congrArg (fun v => (T top).mask L A z • v) hraw

theorem assignedPhysicalInterval_norm_le
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope (R top) cone w q.1 q.2.1)
    (C : ℝ) (hinterval : ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖((Q).withProfile alts halt).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u.val)
        0 lower upper z.1 (z.2-(T top).slope*z.1)‖ ≤ C)
    (lower upper : ℕ) (hlu : lower ≤ upper) (hu : upper ≤ N) :
    ‖∑ q ∈ packets.filter (fun q => assigned q = top ∧ lower ≤ q.1.val ∧ q.1.val < upper),
      original q‖ ≤ C := by
  rw [P.assignedPhysicalInterval_eq_maskedRawInterval packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z top hcondition lower upper hlu,
    norm_smul,Real.norm_eq_abs]
  have hm : |(T top).mask L A z| ≤ 1 :=
    topSincMask_abs_le_one L A ((T top).horizontal z) ((T top).transverse z)
  exact (mul_le_of_le_one_left (norm_nonneg _) hm).trans (hinterval lower upper hlu hu)

theorem assignedPhysicalStoppingPrefix_norm_le
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope (R top) cone w q.1 q.2.1)
    (C : ℝ) (hinterval : ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖((Q).withProfile alts halt).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u.val)
        0 lower upper z.1 (z.2-(T top).slope*z.1)‖ ≤ C)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (k : ℕ) :
    ‖∑ q ∈ (packets.filter (fun q => assigned q = top)).filter (fun q => stop q.1 ≤ k),
      original q‖ ≤ C := by
  apply packet_stopping_prefix_bound (packets.filter (fun q => assigned q = top))
    (fun q => q.1) stop hstop original C _ k
  intro lower upper hlu hu
  have heq : (packets.filter (fun q => assigned q = top)).filter
      (fun q => lower ≤ q.1.val ∧ q.1.val < upper) =
      packets.filter (fun q => assigned q = top ∧ lower ≤ q.1.val ∧ q.1.val < upper) := by
    ext q
    simp only [Finset.mem_filter,and_assoc]
  rw [heq]
  exact P.assignedPhysicalInterval_norm_le packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z top hcondition C hinterval
    lower upper hlu hu

theorem assignedPhysicalSourcePrefix_norm_le
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope (R top) cone w q.1 q.2.1)
    (C : ℝ) (hinterval : ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖((Q).withProfile alts halt).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u.val)
        0 lower upper z.1 (z.2-(T top).slope*z.1)‖ ≤ C)
    (g : AngularGrid) (cutoff : ℝ)
    (hstart : ∀ j, g.eligible cutoff (w/P.length j) 0) (k : ℕ) :
    let stop := fun j : Fin N => g.lastEligible cutoff (w/P.length j) (div_pos hw (P.length_pos j))
    ‖∑ q ∈ (packets.filter (fun q => assigned q = top)).filter (fun q => stop q.1 ≤ k),
      original q‖ ≤ C := by
  intro stop
  exact P.assignedPhysicalStoppingPrefix_norm_le packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z top hcondition C hinterval stop
    (P.stopping_antitone g cutoff w hw hstart) k

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_BoundaryErrorFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the nonnegative boundary error over physical space and
one finite translation interval. Integrability follows from the proved
pointwise average bound, rather than being assumed on the product. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

theorem nonnegative_translation_average_integral_le
    (μ : Measure X) [SFinite μ] (R : ℝ) (hR : 0 < R)
    (f : ℝ×X → ℝ) (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    (hfi : ∀ᵐ x ∂μ, IntervalIntegrable (fun origin => f (origin,x)) volume 0 R)
    (G : X → ℝ) (hG : Integrable G μ)
    (hbound : ∀ᵐ x ∂μ, (∫ origin in (0:ℝ)..R, f (origin,x))/R ≤ G x) :
    Integrable f ((volume.restrict (Ioc 0 R)).prod μ) ∧
      IntervalIntegrable (fun origin => ∫ x, f (origin,x) ∂μ) volume 0 R ∧
      (∫ origin in (0:ℝ)..R, ∫ x, f (origin,x) ∂μ)/R ≤ ∫ x, G x ∂μ := by
  let ν := volume.restrict (Ioc 0 R)
  let H := fun x => ∫ origin, ‖f (origin,x)‖ ∂ν
  have hHeq (x : X) : H x = ∫ origin in (0:ℝ)..R, f (origin,x) := by
    dsimp only [H,ν]
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (hf0 _)]
    rw [intervalIntegral.integral_of_le hR.le]
  have hHm : StronglyMeasurable H := hf.stronglyMeasurable.norm.integral_prod_left'
  have hHi : Integrable H μ := by
    apply (hG.const_mul R).mono' hHm.aestronglyMeasurable
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun origin => norm_nonneg (f (origin,x))))]
    change H x ≤ R*G x
    rw [hHeq]
    exact (div_le_iff₀ hR).mp hx |>.trans_eq (mul_comm _ _)
  have hprod : Integrable f (ν.prod μ) := by
    apply (integrable_prod_iff' hf.aestronglyMeasurable).mpr
    refine ⟨?_,hHi⟩
    filter_upwards [hfi] with x hx
    exact hx.1
  have hint : IntervalIntegrable (fun origin => ∫ x, f (origin,x) ∂μ) volume 0 R := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr
    exact hprod.integral_prod_left
  refine ⟨hprod,hint,?_⟩
  have havg : Integrable (fun x => (∫ origin in (0:ℝ)..R, f (origin,x))/R) μ := by
    simp_rw [intervalIntegral.integral_of_le hR.le]
    exact hprod.integral_prod_right.div_const R
  have hswap := intervalIntegral_integral_swap
    (show Integrable (Function.uncurry (fun origin x => f (origin,x)))
      ((volume.restrict (uIoc 0 R)).prod μ) by
        rw [uIoc_of_le hR.le]
        apply hprod.congr
        filter_upwards [] with z
        rfl)
  rw [hswap,← integral_div]
  exact integral_mono_ae havg hG hbound

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining logarithmic boundary loss is linear in the actual top
weight after its available eight powers are used. Summation has no
factor depending on the number of tops. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

/-- A positive bounded weight absorbs the logarithmic ratio to the
ambient mass, with a constant independent of the small weight. -/
theorem boundary_weight_entropy_le {h n C : ℝ}
    (hh : 0 < h) (hhn : h ≤ n) (hC : 1 ≤ C) (hhC : h ≤ C) :
    h^8*Real.log (n/h) ≤ C^7*h*(1+Real.log (max 1 n)) := by
  have hn : 0 < n := hh.trans_le hhn
  have hlog : Real.log (n/h) ≤ Real.log (max 1 n)+h⁻¹ := by
    have hnlog := Real.log_le_log hn (le_max_right 1 n)
    have hhlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hh)
    rw [Real.log_inv] at hhlog
    rw [Real.log_div hn.ne' hh.ne']
    linarith
  have hlog0 : 0 ≤ Real.log (max 1 n) := Real.log_nonneg (le_max_left 1 n)
  have hp8 : h^8 ≤ C^7*h := by
    simpa only [Real.rpow_ofNat] using
      (bounded_weight_rpow_le_linear (q := (8:ℝ)) (d := 7) hh hC hhC
        (by norm_num) (by norm_num))
  have hp7 : h^7 ≤ C^7*h := by
    simpa only [Real.rpow_ofNat] using
      (bounded_weight_rpow_le_linear (q := (7:ℝ)) (d := 7) hh hC hhC
        (by norm_num) (by norm_num))
  have hinv : h^8*h⁻¹ = h^7 := by
    rw [show h^8 = h^7*h by ring,mul_assoc,mul_inv_cancel₀ hh.ne',mul_one]
  calc
    h^8*Real.log (n/h) ≤ h^8*(Real.log (max 1 n)+h⁻¹) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = h^8*Real.log (max 1 n)+h^7 := by rw [mul_add,hinv]
    _ ≤ (C^7*h)*Real.log (max 1 n)+C^7*h :=
      add_le_add (mul_le_mul_of_nonneg_right hp8 hlog0) hp7
    _ = C^7*h*(1+Real.log (max 1 n)) := by ring

theorem boundary_weight_entropy_sum_le {ι : Type*} (tops : Finset ι) (h : ι → ℝ)
    {C : ℝ} (hC : 1 ≤ C) (hpos : ∀ t ∈ tops, 0 < h t)
    (hbound : ∀ t ∈ tops, h t ≤ C) :
    (∑ t ∈ tops, h t^8*Real.log ((∑ u ∈ tops, h u)/h t)) ≤
      C^7*(1+Real.log (max 1 (∑ u ∈ tops, h u)))*(∑ t ∈ tops, h t) := by
  classical
  calc
    _ ≤ ∑ t ∈ tops, C^7*h t*(1+Real.log (max 1 (∑ u ∈ tops, h u))) := by
      apply Finset.sum_le_sum
      intro t ht
      exact boundary_weight_entropy_le (hpos t ht)
        (Finset.single_le_sum (fun u hu => (hpos u hu).le) ht) hC (hbound t ht)
    _ = _ := by rw [←Finset.sum_mul,←Finset.mul_sum]; ring

theorem top_weight_boundary_entropy_sum_le {ι : Type*}
    (tops : Finset ι) (T : ι → SlopeBox) {Kw D : ℝ}
    (hKw : 0 < Kw) (hD : 0 ≤ D) (z : ℝ×ℝ) :
    (∑ t ∈ tops, ((T t).weight Kw D z)^8*
      Real.log ((∑ u ∈ tops, (T u).weight Kw D z)/(T t).weight Kw D z)) ≤
      ((2:ℝ)^D)^7*(1+Real.log (max 1 (∑ u ∈ tops, (T u).weight Kw D z)))*
        (∑ t ∈ tops, (T t).weight Kw D z) :=
  boundary_weight_entropy_sum_le tops (fun t => (T t).weight Kw D z)
    (Real.one_le_rpow (by norm_num) hD) (fun t _ => (T t).weight_pos hKw D z)
    (fun t _ => (T t).weight_le_two_pow hKw hD z)

/-- The common good-set logarithmic mass bound turns the entropy sum
into the same linear top mass used by the plane estimates. -/
theorem top_weight_boundary_entropy_sum_le_log_bound {ι : Type*}
    (tops : Finset ι) (T : ι → SlopeBox) {Kw D H : ℝ}
    (hKw : 0 < Kw) (hD : 0 ≤ D) (z : ℝ×ℝ)
    (hlog : Real.log (max 1 (∑ u ∈ tops, (T u).weight Kw D z)) ≤ H) :
    (∑ t ∈ tops, ((T t).weight Kw D z)^8*
      Real.log ((∑ u ∈ tops, (T u).weight Kw D z)/(T t).weight Kw D z)) ≤
      ((2:ℝ)^D)^7*(1+H)*(∑ t ∈ tops, (T t).weight Kw D z) := by
  apply (top_weight_boundary_entropy_sum_le tops T hKw hD z).trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · exact Finset.sum_nonneg (fun t _ => ((T t).weight_pos hKw D z).le)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryTotalError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual original-minus-central finite packet sum is controlled
by the sum of the individual top entropy costs. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem source_boundary_expected_total_error (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (M : τ → ℕ)
    (he : ∀ t ∈ tops, g.eligible cutoff (precision t) (M t))
    (a : ℝ) (ha : 0 ≤ a) (x : X) (packets : Finset σ)
    (assigned : σ → τ) (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (stop : σ → ℕ) (value : σ → E)
    (hmax : ∀ s ∈ packets, stop s ≤ M (assigned s))
    (B : τ → ℝ) (hB0 : ∀ t ∈ tops, 0 ≤ B t)
    (hB : ∀ t ∈ tops, ∀ k ≤ M t,
      ‖∑ s ∈ (packets.filter (fun s => assigned s = t)).filter (fun s => stop s ≤ k), value s‖ ≤ B t) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let original := ∑ s ∈ packets, value s
    let central := fun origin => ∑ s ∈ packets,
      (((g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K
        (g.sourceBoundaryGap L) (stop s) (assigned s) a x : ℝ):ℂ) • value s
    let err := fun origin => ‖original-central origin‖
    IntervalIntegrable err volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, err origin)/g.rootWidth ≤
        8*a*epsilon*(∑ t ∈ tops, B t*Real.log ((∑ u ∈ tops, weight u x)/weight t x)) := by
  intro epsilon original central err
  let e := fun t origin => ∑ s ∈ packets.filter (fun s => assigned s = t),
    ((1-(g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K
      (g.sourceBoundaryGap L) (stop s) t a x : ℝ):ℂ) • value s
  have ht (t : τ) (ht : t ∈ tops) :
      IntervalIntegrable (fun origin => ‖e t origin‖) volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, ‖e t origin‖)/g.rootWidth ≤
        8*a*B t*epsilon*Real.log ((∑ u ∈ tops, weight u x)/weight t x) := by
    apply g.source_boundary_expected_finite_packet_error L hbranch hsmall tops slope precision cutoff
      weight hp hw hK (M t) t ht (he t ht) a ha x (packets.filter (fun s => assigned s = t))
      stop value _ (B t) (hB0 t ht) (hB t ht)
    intro s hs
    obtain ⟨hsp,hst⟩ := Finset.mem_filter.mp hs
    simpa only [hst] using hmax s hsp
  have heq (origin : ℝ) : original-central origin = ∑ t ∈ tops, e t origin := by
    calc
      original-central origin = ∑ s ∈ packets,
          ((1-(g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K
            (g.sourceBoundaryGap L) (stop s) (assigned s) a x : ℝ):ℂ) • value s := by
        dsimp only [original,central]
        rw [←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro s _
        rw [Complex.ofReal_sub,Complex.ofReal_one,sub_smul,one_smul]
      _ = ∑ t ∈ tops, e t origin := by
        rw [←Finset.sum_fiberwise_of_maps_to hassigned]
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro s hs
        rw [(Finset.mem_filter.mp hs).2]
  have hm : Measurable err := by
    apply Measurable.norm
    apply measurable_const.sub
    apply Finset.measurable_sum
    intro s hs
    apply Measurable.smul _ measurable_const
    exact Complex.continuous_ofReal.measurable.comp
      (g.measurable_sourceBoundaryCoefficient_withOrigin tops slope precision cutoff weight hp hw hK
        (g.sourceBoundaryGap L) (stop s) (assigned s) (hassigned s hs)
        (g.eligible_of_le (hp (assigned s) (hassigned s hs)) (hmax s hs)
          (he (assigned s) (hassigned s hs))) a x)
  have hle (origin : ℝ) : err origin ≤ ∑ t ∈ tops, ‖e t origin‖ := by
    dsimp only [err]
    rw [heq]
    exact norm_sum_le _ _
  have hsum : IntervalIntegrable (fun origin => ∑ t ∈ tops, ‖e t origin‖) volume 0 g.rootWidth := by
    convert IntervalIntegrable.sum tops (fun t ht' => (ht t ht').1) using 1
    all_goals try with_reducible_and_instances rfl
    ext origin
    simp only [Finset.sum_apply]
  have hi : IntervalIntegrable err volume 0 g.rootWidth := by
    apply hsum.mono_fun' hm.aestronglyMeasurable
    filter_upwards [] with origin
    simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ err origin from norm_nonneg _)] using hle origin
  refine ⟨hi,?_⟩
  have hh := intervalIntegral.integral_mono g.rootWidth_pos.le hi hsum hle
  apply (div_le_div_of_nonneg_right hh g.rootWidth_pos.le).trans
  rw [intervalIntegral.integral_finsetSum (fun t ht' => (ht t ht').1),Finset.sum_div]
  calc
    _ ≤ ∑ t ∈ tops, 8*a*B t*epsilon*Real.log ((∑ u ∈ tops, weight u x)/weight t x) :=
      Finset.sum_le_sum (fun t ht' => (ht t ht').2)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryEntropyError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual top-weight entropy converts the expected packet error
into a multiple of the total top mass. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem source_boundary_expected_error_mass (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (tops : Finset τ) (T : τ → SlopeBox) (w cutoff Kw D : ℝ)
    (hw : 0 < w) (hKw : 0 < Kw) (hD : 0 ≤ D) {K : ℕ} (hK : 0 < K)
    (M : τ → ℕ) (he : ∀ t ∈ tops, g.eligible cutoff (w/(T t).length) (M t))
    (a : ℝ) (ha : 0 ≤ a) (x : ℝ×ℝ) (packets : Finset σ)
    (assigned : σ → τ) (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (stop : σ → ℕ) (value : σ → E) (hmax : ∀ s ∈ packets, stop s ≤ M (assigned s))
    (A H : ℝ) (hA : 0 ≤ A)
    (hlog : Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D x)) ≤ H)
    (hB : ∀ t ∈ tops, ∀ k ≤ M t,
      ‖∑ s ∈ (packets.filter (fun s => assigned s = t)).filter (fun s => stop s ≤ k), value s‖ ≤
        A*((T t).weight Kw D x)^8) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let err := fun origin => ‖(∑ s ∈ packets, value s)-
      ∑ s ∈ packets, (((g.withOrigin origin).sourceBoundaryCoefficient tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cutoff (fun t x => (T t).weight Kw D x) K
        (g.sourceBoundaryGap L) (stop s) (assigned s) a x : ℝ):ℂ) • value s‖
    IntervalIntegrable err volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, err origin)/g.rootWidth ≤
        (8*a*A*epsilon*((2:ℝ)^D)^7*(1+H))*(∑ t ∈ tops, (T t).weight Kw D x) := by
  intro epsilon err
  have hb := g.source_boundary_expected_total_error L hbranch hsmall tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cutoff (fun t x => (T t).weight Kw D x)
    (fun t _ => (div_pos hw (T t).length_pos).le) (fun t x => (T t).weight_pos hKw D x)
    hK M he a ha x packets assigned hassigned stop value hmax
    (fun t => A*((T t).weight Kw D x)^8)
    (fun t _ => mul_nonneg hA (pow_nonneg ((T t).weight_pos hKw D x).le _)) hB
  refine ⟨hb.1,hb.2.trans ?_⟩
  have heq : (∑ t ∈ tops, (A*((T t).weight Kw D x)^8)*
      Real.log ((∑ u ∈ tops, (T u).weight Kw D x)/(T t).weight Kw D x)) =
      A*(∑ t ∈ tops, ((T t).weight Kw D x)^8*
        Real.log ((∑ u ∈ tops, (T u).weight Kw D x)/(T t).weight Kw D x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [heq]
  have hc : 0 ≤ 8*a*epsilon*A := by
    dsimp only [epsilon]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha)
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos (SourceParameters.step_pos L) _)).le) hA
  have h := mul_le_mul_of_nonneg_left (top_weight_boundary_entropy_sum_le_log_bound tops T hKw hD x hlog) hc
  first | (convert h using 1 <;> ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryJointMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint measurability in the common grid translation and physical
point, for the actual finite boundary coefficients and packet error. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*} [MeasurableSpace X]

theorem measurable_path_mass_origin_point (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (i : ℕ) (s : ℝ) :
    Measurable (fun z : ℝ×X => (g.withOrigin z.1).mass tops slope precision cutoff weight
      i ((g.withOrigin z.1).index i s) z.2) := by
  simp only [mass,cellTops,Finset.sum_filter]
  apply Finset.measurable_sum
  intro t _
  have hc : MeasurableSet {z : ℝ×X | (g.withOrigin z.1).index i (slope t) =
      (g.withOrigin z.1).index i s} := measurableSet_eq_fun
        ((g.measurable_index_withOrigin i (slope t)).comp measurable_fst)
        ((g.measurable_index_withOrigin i s).comp measurable_fst)
  by_cases he : g.eligible cutoff (precision t) i
  · simp only [show ∀ z : ℝ×X, (g.withOrigin z.1).eligible cutoff (precision t) i from fun _ => he,
      and_true]
    exact (hw t |>.comp measurable_snd).piecewise hc measurable_const
  · have he' : ∀ z : ℝ×X, ¬(g.withOrigin z.1).eligible cutoff (precision t) i := fun _ => he
    simp only [he',and_false,ite_false, if_false]
    exact measurable_const

theorem measurable_boundary_mass_origin_point (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) (base i : ℕ) (gap s : ℝ) :
    Measurable (fun z : ℝ×X => (g.withOrigin z.1).boundaryMass tops slope precision cutoff weight
      base i gap s z.2) := by
  simp_rw [boundary_mass_eq]
  apply (g.measurable_path_mass_origin_point tops slope precision cutoff weight hw i s).add
  simp only [outsideNearTops,cellTops,Finset.filter_filter,Finset.sum_filter]
  apply Finset.measurable_sum
  intro t _
  have hbase : MeasurableSet {z : ℝ×X | (g.withOrigin z.1).index base (slope t) =
      (g.withOrigin z.1).index base s} := measurableSet_eq_fun
        ((g.measurable_index_withOrigin base (slope t)).comp measurable_fst)
        ((g.measurable_index_withOrigin base s).comp measurable_fst)
  have hparent : MeasurableSet {z : ℝ×X | (g.withOrigin z.1).index i (slope t) ≠
      (g.withOrigin z.1).index i s} :=
    (measurableSet_eq_fun ((g.measurable_index_withOrigin i (slope t)).comp measurable_fst)
      ((g.measurable_index_withOrigin i s).comp measurable_fst)).compl
  have hnear : MeasurableSet {z : ℝ×X | (g.withOrigin z.1).neighbors (i+1) gap
      ((g.withOrigin z.1).index (i+1) s) ((g.withOrigin z.1).index (i+1) (slope t))} := by
    change MeasurableSet {z : ℝ×X | |(g.withOrigin z.1).center (i+1) ((g.withOrigin z.1).index (i+1) s)-
      (g.withOrigin z.1).center (i+1) ((g.withOrigin z.1).index (i+1) (slope t))| < gap+g.width (i+1)}
    exact measurableSet_lt
      (continuous_abs.measurable.comp
        (((g.measurable_center_withOrigin (i+1) s).comp measurable_fst).sub
          ((g.measurable_center_withOrigin (i+1) (slope t)).comp measurable_fst))) measurable_const
  have hel (j : ℕ) : MeasurableSet {z : ℝ×X | (g.withOrigin z.1).eligible cutoff (precision t) j} := by
    change MeasurableSet {z : ℝ×X | g.eligible cutoff (precision t) j}
    by_cases hh : g.eligible cutoff (precision t) j <;>
      simp only [hh,Set.ofPred_true,Set.ofPred_false] <;> measurability
  exact (hw t |>.comp measurable_snd).piecewise
    ((hbase.inter (hel base)).inter ((hel (i+1)).inter (hnear.inter hparent))) measurable_const

theorem measurable_sourceBoundaryLogLoss_origin_point (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K)
    (gap : ℕ → ℝ) (N : ℕ) (top : τ) :
    Measurable (fun z : ℝ×X => (g.withOrigin z.1).sourceBoundaryLogLoss
      tops slope precision cutoff weight K gap N top z.2) := by
  unfold sourceBoundaryLogLoss
  apply Finset.measurable_sum
  intro i _
  simp_rw [sourceBoundaryMass_path _ tops slope precision cutoff weight hK gap]
  exact ((g.measurable_boundary_mass_origin_point tops slope precision cutoff weight hw
    (i+1-K) i (gap i) (slope top)).div
    (g.measurable_path_mass_origin_point tops slope precision cutoff weight hw i (slope top))).log

theorem measurable_sourceBoundaryCoefficient_origin_point (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hwm : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K)
    (gap : ℕ → ℝ) (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) N) (a : ℝ) :
    Measurable (fun z : ℝ×X => (g.withOrigin z.1).sourceBoundaryCoefficient
      tops slope precision cutoff weight K gap N top a z.2) := by
  have heq : (fun z : ℝ×X => (g.withOrigin z.1).sourceBoundaryCoefficient
      tops slope precision cutoff weight K gap N top a z.2) =
      (fun z => Real.exp (-a*(g.withOrigin z.1).sourceBoundaryLogLoss
        tops slope precision cutoff weight K gap N top z.2)) := by
    funext z
    exact (g.withOrigin z.1).sourceBoundaryCoefficient_eq_exp tops slope precision cutoff weight
      hp hw hK gap N top htop he a z.2
  rw [heq]
  exact (measurable_const.mul (g.measurable_sourceBoundaryLogLoss_origin_point tops slope precision
    cutoff weight hwm hK gap N top)).exp

variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem measurable_source_boundary_error_origin_point (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hwm : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K)
    (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (he : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (a : ℝ) (value : X → σ → E) (hv : ∀ s, Measurable (fun x => value x s)) :
    Measurable (fun z : ℝ×X => ‖(∑ s ∈ packets, value z.2 s)-
      ∑ s ∈ packets, (((g.withOrigin z.1).sourceBoundaryCoefficient tops slope precision cutoff
        weight K gap (stop s) (assigned s) a z.2 : ℝ):ℂ) • value z.2 s‖) := by
  apply Measurable.norm
  apply Measurable.sub
  · apply Finset.measurable_sum
    intro s _
    exact (hv s).comp measurable_snd
  · apply Finset.measurable_sum
    intro s hs
    apply Measurable.smul _ ((hv s).comp measurable_snd)
    exact Complex.continuous_ofReal.measurable.comp
      (g.measurable_sourceBoundaryCoefficient_origin_point tops slope precision cutoff weight hp hw hwm
        hK gap (stop s) (assigned s) (hassigned s hs) (he s hs) a)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryIntegratedError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial integration of the expected original-minus-central packet
error. Joint measurability and product integrability are proved for the
literal finite packet sum on the fixed common good set. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem source_boundary_integrated_error (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (tops : Finset τ) (T : τ → SlopeBox) (w cutoff Kw D : ℝ)
    (hw : 0 < w) (hKw : 0 < Kw) (hD : 0 ≤ D) {K : ℕ} (hK : 0 < K)
    (M : τ → ℕ) (he : ∀ t ∈ tops, g.eligible cutoff (w/(T t).length) (M t))
    (a : ℝ) (ha : 0 ≤ a) (packets : Finset σ)
    (assigned : σ → τ) (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (stop : σ → ℕ) (value : (ℝ×ℝ) → σ → E)
    (hv : ∀ s, Measurable (fun x => value x s))
    (hmax : ∀ s ∈ packets, stop s ≤ M (assigned s))
    (A H : ℝ) (hA : 0 ≤ A) (μ : Measure (ℝ×ℝ)) [SFinite μ]
    (good : Set (ℝ×ℝ)) (hgood : MeasurableSet good)
    (hweight : IntegrableOn (fun x => ∑ t ∈ tops, (T t).weight Kw D x) good μ)
    (hlog : ∀ x ∈ good, Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D x)) ≤ H)
    (hB : ∀ x ∈ good, ∀ t ∈ tops, ∀ k ≤ M t,
      ‖∑ s ∈ (packets.filter (fun s => assigned s = t)).filter (fun s => stop s ≤ k), value x s‖ ≤
        A*((T t).weight Kw D x)^8) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let C := 8*a*A*epsilon*((2:ℝ)^D)^7*(1+H)
    let err := fun z : ℝ×(ℝ×ℝ) => ‖(∑ s ∈ packets, value z.2 s)-
      ∑ s ∈ packets, (((g.withOrigin z.1).sourceBoundaryCoefficient tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cutoff (fun t x => (T t).weight Kw D x) K
        (g.sourceBoundaryGap L) (stop s) (assigned s) a z.2 : ℝ):ℂ) • value z.2 s‖
    Integrable err ((volume.restrict (Ioc 0 g.rootWidth)).prod (μ.restrict good)) ∧
      IntervalIntegrable (fun origin => ∫ x in good, err (origin,x) ∂μ) volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, ∫ x in good, err (origin,x) ∂μ)/g.rootWidth ≤
        C*(∫ x in good, ∑ t ∈ tops, (T t).weight Kw D x ∂μ) := by
  intro epsilon C err
  have hbound (x : ℝ×ℝ) (hx : x ∈ good) :=
    g.source_boundary_expected_error_mass L hbranch hsmall tops T w cutoff Kw D hw hKw hD hK M he
      a ha x packets assigned hassigned stop (value x) hmax A H hA (hlog x hx) (hB x hx)
  have hm : Measurable err :=
    g.measurable_source_boundary_error_origin_point tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cutoff (fun t x => (T t).weight Kw D x)
      (fun t _ => (div_pos hw (T t).length_pos).le) (fun t x => (T t).weight_pos hKw D x)
      (fun t => ((T t).continuous_weight hKw D).measurable) hK (g.sourceBoundaryGap L)
      packets assigned stop hassigned
      (fun s hs => g.eligible_of_le (div_pos hw (T (assigned s)).length_pos).le
        (hmax s hs) (he (assigned s) (hassigned s hs))) a value hv
  have hfi : ∀ᵐ x ∂μ.restrict good,
      IntervalIntegrable (fun origin => err (origin,x)) volume 0 g.rootWidth := by
    filter_upwards [ae_restrict_mem hgood] with x hx
    exact (hbound x hx).1
  have havg : ∀ᵐ x ∂μ.restrict good,
      (∫ origin in (0:ℝ)..g.rootWidth, err (origin,x))/g.rootWidth ≤
        C*(∑ t ∈ tops, (T t).weight Kw D x) := by
    filter_upwards [ae_restrict_mem hgood] with x hx
    exact (hbound x hx).2
  have hb := nonnegative_translation_average_integral_le (μ.restrict good) g.rootWidth g.rootWidth_pos
    err hm (fun z => norm_nonneg _) hfi (fun x => C*(∑ t ∈ tops, (T t).weight Kw D x))
    (hweight.const_mul C) havg
  simpa only [integral_const_mul] using hb

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedBoundaryError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integrated boundary error for the original selected physical
packets. Raw assigned-reference concentration supplies the prefix bounds;
the top cutoff and every packet cutoff are their actual last eligible levels. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem assigned_boundary_integrated_error
    (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (tops : Finset τ) (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
    (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (test : ℝ×ℝ → EuclideanSpace ℂ κ)
    (g : AngularGrid) (L maskExponent cutoff Kw D : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hsmall : 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2)
    (hKw : 0 < Kw) (hD : 0 ≤ D) {K : ℕ} (hK : 0 < K)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (hshort : ∀ s ∈ packets, P.length s.1 ≤ (T (assigned s)).length)
    (hcondition : ∀ s ∈ packets, P.referenceCondition oldSlope (T (assigned s)).slope
      (R (assigned s)) cone w s.1 s.2.1)
    (hstart : ∀ j, g.eligible cutoff (w/P.length j) 0)
    (htopstart : ∀ t ∈ tops, g.eligible cutoff (w/(T t).length) 0)
    (a A H : ℝ) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (μ : Measure (ℝ×ℝ)) [SFinite μ] (good : Set (ℝ×ℝ)) (hgood : MeasurableSet good)
    (hweight : IntegrableOn (fun x => ∑ t ∈ tops, (T t).weight Kw D x) good μ)
    (hlog : ∀ x ∈ good, Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D x)) ≤ H) :
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt
    (∀ x ∈ good, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v test j (orig t j l) u.val)
        0 lower upper x.1 (x.2-(T t).slope*x.1)‖ ≤ A*((T t).weight Kw D x)^8) →
    let stop := fun s : P.PacketIndex => g.lastEligible cutoff (w/P.length s.1)
      (div_pos hw (P.length_pos s.1))
    let value := P.physicalMaskedValue alt hAlt oldSlope b v test
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let C := 8*a*A*epsilon*((2:ℝ)^D)^7*(1+H)
    let err := fun z : ℝ×(ℝ×ℝ) => ‖(∑ s ∈ packets, value z.2 s)-
      ∑ s ∈ packets, (((g.withOrigin z.1).sourceBoundaryCoefficient tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cutoff (fun t x => (T t).weight Kw D x) K
        (g.sourceBoundaryGap L) (stop s) (assigned s) a z.2 : ℝ):ℂ) • value z.2 s‖
    Integrable err ((volume.restrict (Ioc 0 g.rootWidth)).prod (μ.restrict good)) ∧
      IntervalIntegrable (fun origin => ∫ x in good, err (origin,x) ∂μ) volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, ∫ x in good, err (origin,x) ∂μ)/g.rootWidth ≤
        C*(∫ x in good, ∑ t ∈ tops, (T t).weight Kw D x ∂μ) := by
  intro Q orig alts halt hinterval stop value epsilon C err
  let M := fun t => g.lastEligible cutoff (w/(T t).length) (div_pos hw (T t).length_pos)
  have he (t : τ) (ht : t ∈ tops) : g.eligible cutoff (w/(T t).length) (M t) :=
    g.eligible_lastEligible cutoff (w/(T t).length) (div_pos hw (T t).length_pos) (htopstart t ht)
  have hmax (s : P.PacketIndex) (hs : s ∈ packets) : stop s ≤ M (assigned s) :=
    g.lastEligible_antitone_precision cutoff (w/(T (assigned s)).length) (w/P.length s.1)
      (div_pos hw (T (assigned s)).length_pos) (div_pos hw (P.length_pos s.1))
      (div_le_div_of_nonneg_left hw.le (P.length_pos s.1) (hshort s hs))
      (htopstart (assigned s) (hassigned s hs)) (hstart s.1)
  have hv (s : P.PacketIndex) : Measurable (fun x => value x s) :=
    (P.physicalMaskedValue_continuous alt hAlt oldSlope b v test
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent s).measurable
  have hprefix (x : ℝ×ℝ) (hx : x ∈ good) (t : τ) (ht : t ∈ tops) (k : ℕ) (_hk : k ≤ M t) :
      ‖∑ s ∈ (packets.filter (fun s => assigned s = t)).filter (fun s => stop s ≤ k), value x s‖ ≤
        A*((T t).weight Kw D x)^8 := by
    apply P.assignedPhysicalSourcePrefix_norm_le packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v test L maskExponent x t
      (fun s hs hst => by simpa only [hst] using hcondition s hs)
      (A*((T t).weight Kw D x)^8) (hinterval x hx t ht) g cutoff hstart k
  exact g.source_boundary_integrated_error L hbranch hsmall tops T w cutoff Kw D hw hKw hD hK
    M he a ha packets assigned hassigned stop value hv hmax A H hA μ good hgood hweight hlog hprefix

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryErrorDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dyadic boundary radius beats every fixed polynomial.
This pays for the integrated packet error after its entropy bound. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_boundary_error_power_budget (C r Q : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      C*L^r*(4*SourceParameters.step L^(-(1/4:ℝ))) ≤ L^(-Q) := by
  have hlim : Tendsto (fun L => (4*C)*(L^(r+Q)*SourceParameters.step L^(-(1/4:ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (source_polynomial_step_decay (r+Q) (1/4) (by norm_num)).const_mul (4*C)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with L hL hsmall
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hpower : L^(r+Q)*L^(-Q) = L^r := by
    rw [←Real.rpow_add hL0]
    congr 1
    ring
  calc
    C*L^r*(4*SourceParameters.step L^(-(1/4:ℝ))) =
        ((4*C)*(L^(r+Q)*SourceParameters.step L^(-(1/4:ℝ))))*L^(-Q) := by
      rw [show (4*C)*(L^(r+Q)*SourceParameters.step L^(-(1/4:ℝ)))*L^(-Q) =
        C*(L^(r+Q)*L^(-Q))*(4*SourceParameters.step L^(-(1/4:ℝ))) by ring,hpower]
    _ ≤ 1*L^(-Q) := mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg hL0.le _)
    _ = L^(-Q) := one_mul _

theorem eventually_boundary_radius_small :
    ∀ᶠ L : ℝ in atTop, 4*SourceParameters.step L^(-(1/4:ℝ)) ≤ 1/2 := by
  have hlim : Tendsto (fun L => (4:ℝ)*(L^(0:ℝ)*SourceParameters.step L^(-(1/4:ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (source_polynomial_step_decay 0 (1/4) (by norm_num)).const_mul 4
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with L hL
  simpa only [Real.rpow_zero,one_mul] using hL.le

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryIntegratedGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The entropy prefactor in the original boundary error fits any
prescribed negative-power budget after all fixed exponents are chosen. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

/-- The boundary budget with the polynomial slack required at log ratio 2L. -/
theorem eventually_boundary_integrated_gain_wide (D q m Q : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ a Nmass Fmass S : ℝ,
      0 ≤ a → a ≤ 1 → 0 ≤ Nmass → 0 ≤ Fmass → S ≤ L^m*Nmass*Fmass →
      (8*a*L^q*(4*SourceParameters.step L^(-(1/4:ℝ)))*((2:ℝ)^D)^7*(1+3*L))*S ≤
        L^(-Q)*Nmass*Fmass := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_boundary_error_power_budget (32*((2:ℝ)^D)^7) (q+m+1) Q]
    with L hL hbudget
  intro a Nmass Fmass S ha ha1 hN hF hS
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let eps := 4*SourceParameters.step L^(-(1/4:ℝ))
  have heps : 0 ≤ eps := by
    dsimp only [eps]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (SourceParameters.step_pos L).le _)
  have hcoef : 0 ≤ 8*a*L^q*eps*((2:ℝ)^D)^7*(1+3*L) := by positivity
  have hsmall : 8*a*(1+3*L) ≤ 32*L := by
    have h := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ 8*(1+3*L) by positivity)
    nlinarith
  have hpower : L^(q+m+1) = L^q*L^m*L := by
    rw [Real.rpow_add hL0,Real.rpow_add hL0,Real.rpow_one]
  have hc : (8*a*L^q*eps*((2:ℝ)^D)^7*(1+3*L))*L^m ≤
      (32*((2:ℝ)^D)^7)*L^(q+m+1)*eps := by
    have hh := mul_le_mul_of_nonneg_right hsmall
      (show 0 ≤ L^q*L^m*eps*((2:ℝ)^D)^7 by positivity)
    rw [hpower]
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  calc
    _ ≤ (8*a*L^q*eps*((2:ℝ)^D)^7*(1+3*L))*(L^m*Nmass*Fmass) :=
      mul_le_mul_of_nonneg_left hS hcoef
    _ = ((8*a*L^q*eps*((2:ℝ)^D)^7*(1+3*L))*L^m)*(Nmass*Fmass) := by ring
    _ ≤ ((32*((2:ℝ)^D)^7)*L^(q+m+1)*eps)*(Nmass*Fmass) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hN hF)
    _ ≤ L^(-Q)*(Nmass*Fmass) := mul_le_mul_of_nonneg_right hbudget (mul_nonneg hN hF)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataAssignedBoundaryGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual assigned-packet boundary error has every prescribed
negative-power gain. Top-weight integrability is derived on the full
plane, and the polynomial mass budget absorbs the remaining integral. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_assigned_boundary_gain (D q m decay : ℝ) (hD : 2 < D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (tops : Finset τ) (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w Freq : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hFreq : 0 ≤ Freq) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ Freq/w)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
      (test : ℝ×ℝ → EuclideanSpace ℂ κ)
      (g : AngularGrid) (maskExponent cutoff Kw : ℝ),
      (g.branching:ℝ) = SourceParameters.step L → 0 < Kw →
    ∀ (K : ℕ), 0 < K →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, P.length s.1 ≤ (T (assigned s)).length) →
      (∀ s ∈ packets, P.referenceCondition oldSlope (T (assigned s)).slope
        (R (assigned s)) cone w s.1 s.2.1) →
      (∀ j, g.eligible cutoff (w/P.length j) 0) →
      (∀ t ∈ tops, g.eligible cutoff (w/(T t).length) 0) →
    ∀ (a Nmass Fmass : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ Nmass → 0 ≤ Fmass →
    ∀ good : Set (ℝ×ℝ), MeasurableSet good →
      (∀ x ∈ good, Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D x)) ≤ 3*L) →
      (∫ x in good, ∑ t ∈ tops, (T t).weight Kw D x ∂volume.prod volume) ≤
        L^m*Nmass*Fmass →
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency alt hAlt
    (∀ x ∈ good, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N →
        ‖((Q t).withProfile (alts t) (halt t)).rawInterval
          (fun j l u => P.physicalMultiplierCoefficient oldSlope b v test j (orig t j l) u.val)
          0 lower upper x.1 (x.2-(T t).slope*x.1)‖ ≤ L^q*((T t).weight Kw D x)^8) →
    let stop := fun s : P.PacketIndex => g.lastEligible cutoff (w/P.length s.1)
      (div_pos hw (P.length_pos s.1))
    let value := P.physicalMaskedValue alt hAlt oldSlope b v test
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let err := fun z : ℝ×(ℝ×ℝ) => ‖(∑ s ∈ packets, value z.2 s)-
      ∑ s ∈ packets, (((g.withOrigin z.1).sourceBoundaryCoefficient tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cutoff (fun t x => (T t).weight Kw D x) K
        (g.sourceBoundaryGap L) (stop s) (assigned s) a z.2 : ℝ):ℂ) • value z.2 s‖
    Integrable err ((volume.restrict (Ioc 0 g.rootWidth)).prod ((volume.prod volume).restrict good)) ∧
      IntervalIntegrable (fun origin => ∫ x in good, err (origin,x) ∂volume.prod volume) volume 0 g.rootWidth ∧
      (∫ origin in (0:ℝ)..g.rootWidth, ∫ x in good, err (origin,x) ∂volume.prod volume)/g.rootWidth ≤
        L^(-decay)*Nmass*Fmass := by
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_boundary_radius_small,
    eventually_boundary_integrated_gain_wide D q m decay] with L hL hsmall hgain
  intro τ κ _ N Label Item _ P packets assigned tops T oldSlope R cone w Freq hw hcone hFreq
    hwide hfrequency alt hAlt b v test g maskExponent cutoff Kw hbranch hKw K hK
    hassigned hshort hcondition hstart htopstart a Nmass Fmass ha ha1 hNmass hFmass
    good hgood hlog hmass Q orig alts halt hinterval stop value err
  have hweight : IntegrableOn (fun x => ∑ t ∈ tops, (T t).weight Kw D x) good (volume.prod volume) :=
    (integrable_finsetSum _ (fun t _ => (T t).weight_integrable hKw hD)).integrableOn
  have hresult := P.assigned_boundary_integrated_error packets assigned tops T oldSlope R cone w Freq
    hw hcone hFreq hwide hfrequency alt hAlt b v test g L maskExponent cutoff Kw D hbranch
    hsmall hKw (by linarith) hK hassigned hshort hcondition hstart htopstart a (L^q) (3*L)
    ha (Real.rpow_nonneg (by linarith) _) (volume.prod volume) good hgood hweight hlog hinterval
  refine ⟨hresult.1,hresult.2.1,hresult.2.2.trans ?_⟩
  exact hgain a Nmass Fmass _ ha ha1 hNmass hFmass hmass

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataOriginalIntegrability
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original finite packet sums and their top-masked versions are
integrable on the full plane. No exceptional set or finite-area bound
is needed for these qualitative facts. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)

theorem physicalMaskedValue_integrable
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (q : P.PacketIndex) :
    Integrable (fun z => P.physicalMaskedValue alt hAlt t b v f T L A z q) (volume.prod volume) := by
  have hi := (memLp_one_iff_integrable.mp (P.crossPacketValue_memLp alt hAlt t b v f 1 q))
  apply hi.norm.mono' (P.physicalMaskedValue_continuous alt hAlt t b v f T L A q).aestronglyMeasurable
  filter_upwards [] with z
  rw [P.physicalMaskedValue_eq_cross_at alt hAlt t b v f,norm_smul,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (topSincMask_abs_le_one L A _ _)

theorem physicalMaskedSum_integrable
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (packets : Finset P.PacketIndex) :
    Integrable (fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt t b v f T L A z q)
      (volume.prod volume) := by
  exact integrable_finsetSum _ (fun q _ => P.physicalMaskedValue_integrable alt hAlt t b v f T L A q)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBoundaryIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every fixed-translation boundary sum is integrable whenever its
original finite packet values are integrable. This supplies all sections
needed for recovery, in addition to the averaged Fubini estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ σ X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedSpace ℂ E]

theorem source_boundary_sum_integrable (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hwm : ∀ t, Measurable (weight t)) {K : ℕ} (hK : 0 < K)
    (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (he : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (a : ℝ) (ha : 0 ≤ a) (μ : Measure X) (value : X → σ → E)
    (hvalue : ∀ s ∈ packets, Integrable (fun x => value x s) μ) (origin : ℝ) :
    Integrable (fun x => ∑ s ∈ packets,
      (((g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) a x : ℝ):ℂ) • value x s) μ := by
  apply integrable_finsetSum
  intro s hs
  have hm := (g.measurable_sourceBoundaryCoefficient_origin_point tops slope precision cutoff
    weight hp hw hwm hK gap (stop s) (assigned s) (hassigned s hs) (he s hs) a).comp
      (measurable_const.prodMk measurable_id : Measurable (fun x : X => (origin,x)))
  have hb : ∀ᵐ x ∂μ,
      ‖(((g.withOrigin origin).sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) a x : ℝ):ℂ)‖ ≤ 1 := by
    filter_upwards [] with x
    have h := (g.withOrigin origin).sourceBoundaryCoefficient_bounds tops slope precision cutoff
      weight hp hw hK gap (stop s) (assigned s) (hassigned s hs) (he s hs) a ha x
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos h.1] using h.2
  exact (hvalue s hs).bdd_smul 1 hm.complex_ofReal.aestronglyMeasurable hb

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceFixedException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed concentration/count exception is charged to the original
L2 packet sum with the prescribed polynomial area budget. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem original_fixed_exception_cost (μ : Measure X) (P : X → E)
    (hP : MemLp P 2 μ) (bad testing : Set X) (hbad : μ bad ≠ ∞)
    (L q Q N : ℝ) (hL : 0 < L) (hN : 0 ≤ N)
    (hmodel : (∫ x, ‖P x‖^2 ∂μ) ≤ (L^q)^2*(N^2*μ.real testing))
    (harea : μ.real bad ≤ (L^(-q-Q))^2*μ.real testing) :
    IntegrableOn (fun x => ‖P x‖) bad μ ∧
      (∫ x in bad, ‖P x‖ ∂μ) ≤ L^(-Q)*N*μ.real testing := by
  obtain ⟨hi,hcs⟩ := integral_norm_on_set_le_l2 μ P hP hbad
  refine ⟨hi,hcs.trans ?_⟩
  calc
    _ ≤ Real.sqrt ((L^q)^2*(N^2*μ.real testing))*
        Real.sqrt ((L^(-q-Q))^2*μ.real testing) :=
      mul_le_mul (Real.sqrt_le_sqrt hmodel) (Real.sqrt_le_sqrt harea)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = L^(-Q)*N*μ.real testing := by
      rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Real.rpow_nonneg hL.le _),
        Real.sqrt_mul (sq_nonneg N),Real.sqrt_sq hN,
        Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Real.rpow_nonneg hL.le _)]
      have hpow : L^q*L^(-q-Q) = L^(-Q) := by
        rw [←Real.rpow_add hL]
        congr 1
        ring
      calc
        _ = (L^q*L^(-q-Q))*N*(Real.sqrt (μ.real testing)*Real.sqrt (μ.real testing)) := by ring
        _ = _ := by rw [hpow,Real.mul_self_sqrt measureReal_nonneg]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMovingException
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The moving good-path exceptional set is charged to the original
sum. Its exp(-9L) area beats every fixed polynomial L2 loss. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace LipschitzHilbert

theorem eventually_original_moving_exception (q m Q : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (X E : Type*) [MeasurableSpace X] [NormedAddCommGroup E],
    ∀ (μ : Measure X) (P : X → E), MemLp P 2 μ →
    ∀ (bad source testing : Set X), μ bad ≠ ∞ →
    ∀ N : ℝ, 0 ≤ N → μ.real source = N^2*μ.real testing → N ≤ Real.exp (2*L) →
      (∫ x, ‖P x‖^2 ∂μ) ≤ (L^q)^2*μ.real source →
      μ.real bad ≤ L^m*μ.real source*Real.exp (-9*L) →
      IntegrableOn (fun x => ‖P x‖) bad μ ∧
        (∫ x in bad, ‖P x‖ ∂μ) ≤ L^(-Q)*N*μ.real testing := by
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (q+m/2+Q) (5/2)
    (by norm_num : (0:ℝ) < 5/2)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with L hL hsmall
  intro X E _ _ μ P hP bad source testing hbad N hN hratio hNexp hmodel harea
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hb := counting_discard_cost μ P hP hbad (Real.rpow_nonneg hL0.le q)
    (Real.rpow_nonneg hL0.le m) hN hratio hNexp hmodel harea
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hpower : L^(q+m/2+Q)*L^(-Q) = L^(q+m/2) := by
    rw [←Real.rpow_add hL0]
    congr 1
    ring
  have hdecay : L^(q+m/2)*Real.exp (-(5/2:ℝ)*L) ≤ L^(-Q) := by
    have hh := mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg hL0.le (-Q))
    calc
      _ = (L^(q+m/2+Q)*Real.exp (-(5/2:ℝ)*L))*L^(-Q) := by
        rw [show L^(q+m/2+Q)*Real.exp (-(5/2:ℝ)*L)*L^(-Q) =
          (L^(q+m/2+Q)*L^(-Q))*Real.exp (-(5/2:ℝ)*L) by ring,hpower]
      _ ≤ 1*L^(-Q) := hh
      _ = _ := one_mul _
  have heq : (L^q*Real.sqrt (L^m))*Real.exp ((2-9/2)*L) =
      L^(q+m/2)*Real.exp (-(5/2:ℝ)*L) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hL0.le,←Real.rpow_add hL0]
    congr 2 <;> ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdecay hN) measureReal_nonneg

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceOriginalRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the original adjoint sum with the manuscript's fixed and
moving exceptional-area budgets. The common good set precedes all
translations, and only the boundary error is averaged. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace LipschitzHilbert

theorem eventually_original_recovery (q m decay : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (X E : Type*) [MeasurableSpace X] [NormedAddCommGroup E]
      (μ : Measure X) (P Q : X → E) (W : ℝ → X → E), MemLp P 2 μ →
    ∀ (F source Z0 : Set X) (Z : ℝ → Set X),
      MeasurableSet F → MeasurableSet Z0 → (∀ origin, MeasurableSet (Z origin)) →
      μ F ≠ ∞ → Z0 ⊆ F → (∀ origin, Z origin ⊆ Z0) →
    ∀ N : ℝ, 0 ≤ N → μ.real source = N^2*μ.real F → N ≤ Real.exp (2*L) →
      (∫ x, ‖P x‖^2 ∂μ) ≤ (L^q)^2*μ.real source →
      μ.real (F\Z0) ≤ (L^(-q-(decay+1)))^2*μ.real F →
      (∀ origin, μ.real (Z0\Z origin) ≤ L^m*μ.real source*Real.exp (-9*L)) →
      IntegrableOn (fun x => ‖P x-Q x‖) Z0 μ →
      (∀ origin, IntegrableOn (fun x => ‖Q x-W origin x‖) Z0 μ) →
      (∀ origin, IntegrableOn (fun x => ‖W origin x‖) (Z origin) μ) →
      (∫ x in Z0, ‖P x-Q x‖ ∂μ) ≤ L^(-(decay+1))*N*μ.real F →
      (∀ origin, (∫ x in Z origin, ‖W origin x‖ ∂μ) ≤ L^(-(decay+1))*N*μ.real F) →
    ∀ R : ℝ, 0 < R →
      IntervalIntegrable (fun origin => ∫ x in Z0, ‖Q x-W origin x‖ ∂μ) volume 0 R →
      (∫ origin in (0:ℝ)..R, ∫ x in Z0, ‖Q x-W origin x‖ ∂μ)/R ≤
        L^(-(decay+1))*N*μ.real F →
      (∫ x in F, ‖P x‖ ∂μ) ≤ L^(-decay)*N*μ.real F := by
  filter_upwards [eventually_ge_atTop (5:ℝ),
    eventually_original_moving_exception q m (decay+1)] with L hL hmove
  intro X E _ _ μ P Q W hP F source Z0 Z hF hZ0 hZ hFfin hZ0F hZZ0
    N hN hratio hNexp henergy hfixedArea hmoveArea hPQ hQW hW hmask hcentral
    R hR herror hboundary
  have hL0 : 0 < L := by linarith
  have hPint := (integral_norm_on_set_le_l2 μ P hP hFfin).1
  have hfixedFin : μ (F\Z0) ≠ ∞ := ne_top_of_le_ne_top hFfin (measure_mono sdiff_subset)
  have hfixed := original_fixed_exception_cost μ P hP (F\Z0) F hfixedFin
    L q (decay+1) N hL0 hN (by simpa only [hratio] using henergy) hfixedArea
  have hmoving (origin : ℝ) :
      (∫ x in Z0\Z origin, ‖P x‖ ∂μ) ≤ L^(-(decay+1))*N*μ.real F := by
    have hfin : μ (Z0\Z origin) ≠ ∞ := ne_top_of_le_ne_top hFfin
      (measure_mono (fun x hx => hZ0F hx.1))
    exact (hmove X E μ P hP (Z0\Z origin) source F hfin N hN hratio hNexp
      henergy (hmoveArea origin)).2
  let budget := L^(-(decay+1))*N*μ.real F
  have hr := recover_original_from_moving_good μ F Z0 Z hF hZ0 hZ hZ0F hZZ0
    P Q W hPint hPQ hQW hW R budget budget budget budget budget hR
    hfixed.2 hmoving hmask hcentral herror hboundary
  have hpower : L^(-(decay+1))*L = L^(-decay) := by
    calc
      _ = L^(-(decay+1))*L^(1:ℝ) := by rw [Real.rpow_one]
      _ = L^(-(decay+1)+1) := (Real.rpow_add hL0 _ _).symm
      _ = _ := by congr 1; ring
  have hcoef : 5*L^(-(decay+1)) ≤ L^(-decay) := by
    calc
      _ ≤ L^(-(decay+1))*L := by nlinarith [Real.rpow_nonneg hL0.le (-(decay+1))]
      _ = _ := hpower
  calc
    _ ≤ budget+budget+budget+budget+budget := hr
    _ = (5*L^(-(decay+1)))*N*μ.real F := by dsimp only [budget]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hN) measureReal_nonneg

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataPacketRecovery
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recovery for the literal original packet sum. Integrability of the
original, masked, and translated boundary sums follows from their actual
Schwartz packets; the hypotheses here are the quantitative local budgets. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.PacketLatticeData

theorem eventually_physical_packet_recovery (q m decay : ℝ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (oldSlope : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (tops : Finset τ) (T : τ → SlopeBox) (g : AngularGrid)
      (w cutoff Kw D maskExponent a : ℝ),
    ∀ (hw : 0 < w), 0 < Kw → 0 ≤ a →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, P.length s.1 ≤ (T (assigned s)).length) →
      (∀ j, g.eligible cutoff (w/P.length j) 0) →
    ∀ K : ℕ, 0 < K → ∀ gap : ℕ → ℝ,
    let value := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    let original := fun z => ∑ s ∈ packets,
      P.crossPacketValue alt hAlt oldSlope b v f z s
    let masked := fun z => ∑ s ∈ packets, value z s
    let stop := fun s : P.PacketIndex => g.lastEligible cutoff (w/P.length s.1)
      (div_pos hw (P.length_pos s.1))
    let weight := fun t z => (T t).weight Kw D z
    let central := fun origin z => ∑ s ∈ packets,
      (((g.withOrigin origin).sourceBoundaryCoefficient tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cutoff weight K gap (stop s) (assigned s) a z : ℝ):ℂ) •
          value z s
    ∀ (F source Z0 : Set (ℝ×ℝ)) (Z : ℝ → Set (ℝ×ℝ)),
      MeasurableSet F → MeasurableSet Z0 → (∀ origin, MeasurableSet (Z origin)) →
      (volume.prod volume) F ≠ ∞ → Z0 ⊆ F → (∀ origin, Z origin ⊆ Z0) →
    ∀ Nmass : ℝ, 0 ≤ Nmass →
      (volume.prod volume).real source = Nmass^2*(volume.prod volume).real F →
      Nmass ≤ Real.exp (2*L) →
      (∫ z, ‖original z‖^2 ∂volume.prod volume) ≤ (L^q)^2*(volume.prod volume).real source →
      (volume.prod volume).real (F\Z0) ≤ (L^(-q-(decay+1)))^2*(volume.prod volume).real F →
      (∀ origin, (volume.prod volume).real (Z0\Z origin) ≤
        L^m*(volume.prod volume).real source*Real.exp (-9*L)) →
      (∫ z in Z0, ‖original z-masked z‖ ∂volume.prod volume) ≤
        L^(-(decay+1))*Nmass*(volume.prod volume).real F →
      (∀ origin, (∫ z in Z origin, ‖central origin z‖ ∂volume.prod volume) ≤
        L^(-(decay+1))*Nmass*(volume.prod volume).real F) →
      IntervalIntegrable (fun origin => ∫ z in Z0, ‖masked z-central origin z‖ ∂volume.prod volume)
        volume 0 g.rootWidth →
      (∫ origin in (0:ℝ)..g.rootWidth,
        ∫ z in Z0, ‖masked z-central origin z‖ ∂volume.prod volume)/g.rootWidth ≤
          L^(-(decay+1))*Nmass*(volume.prod volume).real F →
      (∫ z in F, ‖original z‖ ∂volume.prod volume) ≤
        L^(-decay)*Nmass*(volume.prod volume).real F := by
  filter_upwards [eventually_original_recovery q m decay] with L hrec
  intro τ κ _ N Label Item _ P alt hAlt oldSlope b v f packets assigned tops T g
    w cutoff Kw D maskExponent a hw hKw ha hassigned hshort hstart K hK gap
    value original masked stop weight central F source Z0 Z hF hZ0 hZ hFfin hZ0F hZZ0
    Nmass hN hratio hNexp henergy hfixed hmove hmask hcentral hinterval hboundary
  have horiginal : Integrable original (volume.prod volume) :=
    memLp_one_iff_integrable.mp (P.crossSum_memLp alt hAlt oldSlope b v f 1 packets)
  have hmasked : Integrable masked (volume.prod volume) :=
    P.physicalMaskedSum_integrable alt hAlt oldSlope b v f _ L maskExponent packets
  have hcent (origin : ℝ) : Integrable (central origin) (volume.prod volume) := by
    apply g.source_boundary_sum_integrable tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cutoff weight
      (fun t _ => (div_pos hw (T t).length_pos).le)
      (fun t z => (T t).weight_pos hKw D z)
      (fun t => ((T t).continuous_weight hKw D).measurable)
      hK gap packets assigned stop hassigned _ a ha (volume.prod volume) value
      (fun s _ => P.physicalMaskedValue_integrable alt hAlt oldSlope b v f _ L maskExponent s)
    intro s hs
    have hle : w/(T (assigned s)).length ≤ w/P.length s.1 :=
      div_le_div_of_nonneg_left hw.le (P.length_pos s.1) (hshort s hs)
    exact (mul_le_mul_of_nonneg_right hle (by positivity)).trans
      (g.eligible_lastEligible cutoff (w/P.length s.1) (div_pos hw (P.length_pos s.1)) (hstart s.1))
  exact hrec (ℝ×ℝ) (EuclideanSpace ℂ κ) (volume.prod volume) original masked central
    (P.crossSum_memLp alt hAlt oldSlope b v f 2 packets)
    F source Z0 Z hF hZ0 hZ hFfin hZ0F hZZ0 Nmass hN hratio hNexp henergy hfixed hmove
    (horiginal.sub hmasked).norm.integrableOn
    (fun origin => (hmasked.sub (hcent origin)).norm.integrableOn)
    (fun origin => (hcent origin).norm.integrableOn)
    hmask hcentral g.rootWidth g.rootWidth_pos hinterval hboundary

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTotalWeightBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two different mass budgets used in the assembly: integrating
the top count on the testing set costs N|F|, whereas integrating all
weights on the plane costs N²|F|. Their polynomial losses are explicit. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert

theorem source_testing_weight_integral {τ : Type*} (tops : Finset τ) (T : τ → SlopeBox)
    (K D L c Nmass Fmass : ℝ) (hK : 0 < K) (hD : 2 < D) (hL : 0 < L)
    (hN : 0 ≤ Nmass) (good : Set (ℝ×ℝ)) (hgood : MeasurableSet good)
    (hfinite : (volume.prod volume) good ≠ ∞)
    (hmeasure : (volume.prod volume).real good ≤ Fmass)
    (hcount : ∀ x ∈ good, (∑ t ∈ tops, (T t).weight K D x) ≤ L^c*Nmass) :
    IntegrableOn (fun x => ∑ t ∈ tops, (T t).weight K D x) good (volume.prod volume) ∧
      (∫ x in good, ∑ t ∈ tops, (T t).weight K D x ∂volume.prod volume) ≤ L^c*Nmass*Fmass := by
  have hi : IntegrableOn (fun x => ∑ t ∈ tops, (T t).weight K D x) good (volume.prod volume) :=
    (integrable_finsetSum _ (fun t _ => (T t).weight_integrable hK hD)).integrableOn
  refine ⟨hi,?_⟩
  have hb := setIntegral_mono_on hi
    (integrableOn_const hfinite : IntegrableOn (fun _ : ℝ×ℝ => L^c*Nmass) good (volume.prod volume))
    hgood hcount
  calc
    _ ≤ (volume.prod volume).real good*(L^c*Nmass) := by
      simpa only [setIntegral_const,smul_eq_mul] using hb
    _ ≤ Fmass*(L^c*Nmass) := mul_le_mul_of_nonneg_right hmeasure
      (mul_nonneg (Real.rpow_nonneg hL.le _) hN)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataActualPacketRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original packet sum is recovered from a reference exception for every
common grid translation. Central and averaged boundary budgets follow from
the energy, fixed-set, mask, and geometric/concentration hypotheses on the
popular collection. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_actual_packet_recovery_oai (hVariation : LepingleInput)
    (qEnergy sArea pProfile qEnv Cmass Cweight F c0 A_M d m decay maskExponent cStar cEta CEta cb Cb Lip cone : ℝ) (Dweight Kcount Hcount : ℕ)
    (hpProfile : 0 ≤ pProfile) (hqEnv : 0 ≤ qEnv) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hF : 0 ≤ F) (hc0 : 0 < c0)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*pProfile+13) (2*pProfile+17)+3/2) ≤ A_M)
    (hDweight : 2 < (Dweight:ℝ)) (hd : 0 ≤ d) (hm : 0 ≤ m)
    (hqm : 2*(qEnv+6)+2 ≤ m) (hCmassM : Cmass ≤ m) (hdecay : 0 ≤ decay)
    (hMask : 1 < maskExponent) (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta)
    (hCEta : 0 ≤ CEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hLip : 0 ≤ Lip)
    (hgap : cStar < cEta*cb) (hcone : 0 ≤ cone) (hconeK : cone ≤ Kcount) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ κ : Type) [Fintype κ] (N : ℕ) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item),
    ∀ (tops : Finset τ) (T : τ → SlopeBox)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope w : ℝ) (hw : 0 < w)
      (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w),
      (∀ k, c0/w ≤ |P.frequency k|) →
      (F*cone+2)*P.referenceEnvelopeConstant ≤ L^pProfile →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ cone*(w/P.length j)) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
    (∀ j l k s, b j l k s ≠ 0 →
      cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
        |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
    (∀ j l u k xi eta,
      planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    (∀ j l u k xi eta,
      planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
        |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    let Kw := L^(maskExponent+2)
    let R := fun t => (T t).length
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt
    ∀ (_hwideResidual : (cone+(SourceParameters.branching L)^2)*w ≤ P.width)
      (_hwideParent : (cone+(SourceParameters.branching L)^3)*w ≤ P.width),
    (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hcount) →
    (∀ t ∈ tops, P.width ≤ Kw*(T t).width) →
    3+2*(8*Dweight+1) ≤ P.order →
    (∀ t ∈ tops, P.scale = 4*(Kw*(T t).width)) →
    (∀ u ∈ packets, |P.actualX u.1 u.2.1 u.2.2-(T (assigned u)).x|+P.length u.1 ≤
      Kw*(T (assigned u)).length) →
    (∀ u ∈ packets,
      |P.actualZ u.1 u.2.1 u.2.2+(oldSlope-(T (assigned u)).slope)*P.actualX u.1 u.2.1 u.2.2-
        ((T (assigned u)).y-(T (assigned u)).slope*(T (assigned u)).x)|+P.width ≤
      Kw*(T (assigned u)).width) →
    (∀ u ∈ packets, assigned u ∈ tops) →
    (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
    (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
      (R (assigned u)) cone w u.1 u.2.1) →
    ∀ (g : AngularGrid), (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/P.length j) 0) →
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) 0) →
    ∀ (_hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (Dphase Nmass A : ℝ), 2 ≤ Dphase → Dphase ≤ L^d → 0 < Nmass → Real.log Nmass ≤ 2*L →
      0 ≤ A → A ≤ L^qEnv →
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent
    ∀ (Z0 : Set (ℝ×ℝ)), MeasurableSet Z0 →
    (∀ z ∈ Z0, ∀ t ∈ tops, weight t z ≤ Cweight) →
    (∀ z ∈ Z0, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
    (∀ z ∈ Z0, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
    (∀ z ∈ Z0, ∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N → ∀ yy,
      |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      let V := ((Q t).withProfile (alts t) (halt t)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
        0 lower upper
      ‖V z.1 yy‖+(T t).width*
        ‖covariantSignal P.frequency (fun k zz => V z.1 zz k) yy‖ ≤ A*(weight t z)^8) →
    (∀ z ∈ Z0, ∀ rho : ℝ, 0 < rho → ∀ I : Finset τ, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, w/(T t).length ≤ rho/(SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ u ∈ I, |(T t).slope-(T u).slope| ≤ SourceParameters.branching L*rho) →
      (∀ t ∈ I, ∀ u ∈ I, t ≠ u → rho ≤ |(T t).slope-(T u).slope|) →
      (I.card:ℝ) ≤ Dphase/100) →
    ∀ (start Fmass : ℝ), 0 < Fmass → L/2 ≤ Real.log Nmass →
      (volume.prod volume) Z0 ≠ ∞ → (volume.prod volume).real Z0 ≤ Fmass →
      (∀ t ∈ tops, start ≤ (T t).slope ∧ (T t).slope ≤ start+g.rootWidth) →
      (∑ t ∈ tops, ∫ z, weight t z ∂volume.prod volume) ≤ L^m*Nmass^2*Fmass →
    ∀ (Fset Eset : Set (ℝ×ℝ)), MeasurableSet Fset →
      (volume.prod volume) Fset ≠ ∞ → Fmass = (volume.prod volume).real Fset →
      Z0 ⊆ Fset → (volume.prod volume).real Eset = Nmass^2*Fmass →
    let originalSum := fun z => ∑ u ∈ packets,
      P.crossPacketValue alt hAlt oldSlope b v f z u
    let maskedSum := fun z => ∑ u ∈ packets, original z u
    (∫ z, ‖originalSum z‖^2 ∂volume.prod volume) ≤
      (L^qEnergy)^2*(volume.prod volume).real Eset →
    (volume.prod volume).real (Fset\Z0) ≤ (L^(-qEnergy-(decay+1)))^2*Fmass →
    (∑ t ∈ tops, (T t).length*(T t).width) ≤ L^sArea*(volume.prod volume).real Eset →
    (∫ z in Z0, ‖originalSum z-maskedSum z‖ ∂volume.prod volume) ≤
      L^(-(decay+1))*Nmass*Fmass →
    (∫ z in Fset, ‖originalSum z‖ ∂volume.prod volume) ≤ L^(-decay)*Nmass*Fmass := by
  filter_upwards [eventually_actual_reference_central_gain hVariation
      pProfile qEnv Cmass Cweight F c0 A_M d m (decay+1) maskExponent cStar cEta CEta cb Cb Lip cone
      Dweight Kcount Hcount hpProfile hqEnv hCmass hCweight hF hc0 hAM hchoice hDweight hd hm
      hqm hCmassM (by linarith) hMask hcStar hcEta hCEta hcb hCb hLip hgap hcone hconeK,
    eventually_physical_packet_recovery qEnergy sArea decay,
    eventually_assigned_boundary_gain (Dweight:ℝ) qEnv m (decay+1) hDweight,
    eventually_ge_atTop (256:ℝ)] with L hcentralGain hrecover hboundaryGain hL
  intro τ κ _ N Label Item _ P tops T packets assigned oldSlope w hw hwide hfrequency
    hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 hmotion hactive hspectrum haltSpectrum
    Kw R Q orig alts halt hwideResidual hwideParent hlocal hwidth horder hscale hX hZ
    hassigned hshort hcondition g hbranch htopWidth hzero hroot hKb hKbL Dphase Nmass A
    hD hDL hNmass hlogN hA hAq weight original
    Z0 hZ0 hweight htotal hmass hconc hcount start Fmass hFmass hloglo
    hZ0finite hmeasure hslope hweightTotal Fset Eset hFset hFfinite hFmassEq hZ0F hratio
    originalSum maskedSum henergy hfixed harea hmask
  let a := PhaseCombinatorics.phaseMu Dphase (Real.sqrt L)/(SourceParameters.blockCount L:ℝ)
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let stop := fun j : Fin N => g.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
  let wide : ∀ i : Option (Fin (SourceParameters.blockCount L)),
      (cone+(SourceParameters.branching L)^(if i.isNone then 3 else 2))*w ≤ P.width := by
    intro i
    cases i with
    | none => exact hwideParent
    | some i => exact hwideResidual
  have hL1 : 1 ≤ L := by linarith
  have hKw : 0 < Kw := Real.rpow_pos_of_pos (by linarith) _
  have hmu := source_phaseMu_small (by linarith : 1 ≤ Dphase) hL
  have ha : 0 ≤ a := div_nonneg hmu.1.le (Nat.cast_nonneg _)
  have ha1 : a ≤ 1 := by
    apply (div_le_iff₀ (by exact_mod_cast hKb : (0:ℝ) < SourceParameters.blockCount L)).mpr
    have hK1 : (1:ℝ) ≤ SourceParameters.blockCount L := by exact_mod_cast hKb
    simpa only [one_mul] using (hmu.2.trans (by linarith : (1/12:ℝ) ≤ SourceParameters.blockCount L))
  let bad := fun origin => P.actualReferenceBad alt hAlt L oldSlope cone w F hw hcone hF wide
    hfrequency b v f (g.withOrigin origin) tops T packets assigned hKb maskExponent pProfile
  let good := fun origin => sourceGoodPathSet Z0 tops weight (bad origin) L
  let central := fun origin z => ∑ s ∈ packets,
    (((g.withOrigin origin).sourceBoundaryCoefficient tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut weight (SourceParameters.blockCount L)
      (g.sourceBoundaryGap L) (stop s.1) (assigned s) a z : ℝ):ℂ) • original z s
  have hc (origin : ℝ) :
      MeasurableSet (good origin) ∧ good origin ⊆ Z0 ∧
      (volume.prod volume) (Z0\good origin) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L)) ∧
      (∫ z in good origin, ‖central origin z‖ ∂volume.prod volume) ≤
        L^(-(decay+1))*Nmass*Fmass := by
    have h := hcentralGain τ κ N Label Item P tops T packets assigned oldSlope w hw hwide
      hfrequency hfrequencyLo hP alt hAlt b hb hb1 hsupp v hv f hf hf1 hmotion hactive
      hspectrum haltSpectrum hwideResidual hwideParent hlocal hwidth horder hscale hX hZ
      hassigned hshort hcondition (g.withOrigin origin) hbranch htopWidth hzero hroot hKb hKbL
      Dphase Nmass A hD hDL hNmass hlogN hA hAq Z0 hZ0 hweight htotal hmass hconc
      (by
        intro shift j hj z hz I hI hrad hprec hcluster hsep
        exact hcount z hz _ (g.sourceGap_pos L _) I hI hrad hprec hcluster hsep)
      start Fmass hFmass hloglo hZ0finite hmeasure hslope hweightTotal
    exact ⟨h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.2⟩
  have hmassInt : (∫ z in Z0, ∑ t ∈ tops, weight t z ∂volume.prod volume) ≤
      L^m*Nmass*Fmass := by
    apply (source_testing_weight_integral tops T Kw (Dweight:ℝ) L Cmass Nmass Fmass
      hKw hDweight (by linarith) hNmass.le Z0 hZ0 hZ0finite hmeasure hmass).2.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hL1 hCmassM) hNmass.le) hFmass.le
  have hbnd := hboundaryGain τ κ N Label Item P packets assigned tops T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f g maskExponent cut Kw hbranch hKw
    (SourceParameters.blockCount L) hKb hassigned hshort hcondition hzero hroot
    a Nmass Fmass ha ha1 hNmass.le hFmass.le Z0 hZ0 htotal hmassInt
    (by
      intro z hz t ht lower upper hlu hu
      have h := hconc z hz t ht lower upper hlu hu (z.2-(T t).slope*z.1)
        (by simpa only [sub_self,abs_zero] using (T t).width_pos.le)
      have hn : 0 ≤ (T t).width * ‖covariantSignal P.frequency
          (fun k yy => ((Q t).withProfile (alts t) (halt t)).rawInterval
            (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val)
            0 lower upper z.1 yy k) (z.2-(T t).slope*z.1)‖ :=
        mul_nonneg (T t).width_pos.le (norm_nonneg _)
      exact (le_add_of_nonneg_right hn).trans (h.trans
        (mul_le_mul_of_nonneg_right hAq (by positivity))))
  have hNexp : Nmass ≤ Real.exp (2*L) := (Real.log_le_iff_le_exp hNmass).mp hlogN
  have hmove (origin : ℝ) : (volume.prod volume).real (Z0\good origin) ≤
      L^sArea*(volume.prod volume).real Eset*Real.exp (-9*L) := by
    have hn : 0 ≤ (∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L) := by
      apply mul_nonneg _ (Real.exp_pos _).le
      exact Finset.sum_nonneg fun t _ => mul_nonneg (T t).length_pos.le (T t).width_pos.le
    have h := ENNReal.toReal_mono (by simp) (hc origin).2.2.1
    rw [ENNReal.toReal_ofReal hn] at h
    exact h.trans (mul_le_mul_of_nonneg_right harea (Real.exp_pos _).le)
  have hr := hrecover τ κ N Label Item P alt hAlt oldSlope b v f packets assigned tops T g
    w cut Kw (Dweight:ℝ) maskExponent a hw hKw ha hassigned hshort hzero
    (SourceParameters.blockCount L) hKb (g.sourceBoundaryGap L)
    Fset Eset Z0 good hFset hZ0 (fun origin => (hc origin).1) hFfinite hZ0F
    (fun origin => (hc origin).2.1) Nmass hNmass.le
    (by simpa only [←hFmassEq] using hratio) hNexp henergy
    (by simpa only [←hFmassEq] using hfixed) hmove
    (by simpa only [←hFmassEq] using hmask)
    (by intro origin; simpa only [←hFmassEq] using (hc origin).2.2.2)
    hbnd.2.1 (by simpa only [←hFmassEq] using hbnd.2.2)
  simpa only [←hFmassEq] using hr

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketLatticeData.eventually_actual_packet_recovery_oai := @OAI.LipschitzHilbert.PacketLatticeData.eventually_actual_packet_recovery_oai
