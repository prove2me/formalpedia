-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:46:02.320415+00:00
-- url     : https://prove2.me/submissions/86e5614b-b4d2-4d1c-9272-ebef02e36006

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/FiniteFlatness.lean:L13-L25
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_AsymptoticallyMinimalLittlewoodFiniteFlatness_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_LittlewoodFiniteFlatness
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy
import Definitions.Def_OAI_Analysis_Littlewood_ModeSampling
import Definitions.Def_OAI_Analysis_Littlewood_MinimizingFamily
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewoodFiniteFlatness_normalized_error_sq_bound
import Theorems.Thm_OAI_LittlewoodFiniteFlatness_tendsto_integral_rpow_of_bounded_moment
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_almost_sign_sampler
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_round_sample_once

-- ---- from OAI.Analysis.Littlewood.MinimizingFamily ----
namespace OAI

/-! A minimizing family with vanishing second error moment. -/
noncomputable section
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate

namespace AsymptoticallyMinimalLittlewoodFiniteFlatness

lemma fourier_nat (n : ℕ) (t : UnitAddCircle) :
    fourier (n : ℤ) t = (fourier (1 : ℤ) t) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

lemma circlePolynomial_apply {N : ℕ} (ε : Fin N → ℝ) (t : UnitAddCircle) :
    circlePolynomial ε t = littlewoodValue ε (fourier (1 : ℤ) t) := by
  simp only [circlePolynomial, littlewoodValue, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [fourier_nat]

lemma signVector_signing {N : ℕ} (b : Fin N → Bool) : IsRealSigning (signVector b) := by
  intro k
  cases h : b k <;> simp [signVector, boolSign, h]

lemma signing_eq_signVector {N : ℕ} (ε : Fin N → ℝ) (hε : IsRealSigning ε) :
    ∃ b : Fin N → Bool, signVector b = ε := by
  classical
  refine ⟨fun k => decide (ε k = 1), ?_⟩
  funext k
  rcases hε k with h | h <;> norm_num [signVector, boolSign, h]

lemma chosenSigns_signing (N : ℕ) : IsRealSigning (chosenSigns N) :=
  signVector_signing _

lemma chosenSigns_minimal {N : ℕ} (ε : Fin N → ℝ) (hε : IsRealSigning ε) :
    ‖circlePolynomial (chosenSigns N)‖ ≤ ‖circlePolynomial ε‖ := by
  obtain ⟨b, rfl⟩ := signing_eq_signVector ε hε
  exact Classical.choose_spec (exists_minimizing_signing N) b

/- An all-length upper-flatness bound for real-sign polynomials. -/
variable (hmain : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
  ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
    ∀ z : ℂ, ‖z‖ = 1 → ‖littlewoodValue ε z‖ ≤ (1 + η) * Real.sqrt N)

include hmain in
lemma chosenSigns_eventually_bound {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ t : UnitAddCircle,
      ‖circlePolynomial (chosenSigns N) t‖ ≤ (1 + η) * Real.sqrt (N : ℝ) := by
  obtain ⟨N₀, _, hN₀⟩ := hmain η hη
  filter_upwards [eventually_ge_atTop N₀] with N hN
  obtain ⟨ε, hε, hbound⟩ := hN₀ N hN
  have hsup : ‖circlePolynomial ε‖ ≤ (1 + η) * Real.sqrt (N : ℝ) := by
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro t
    rw [circlePolynomial_apply]
    exact hbound _ (Circle.norm_coe _)
  intro t
  exact (ContinuousMap.norm_coe_le_norm _ t).trans ((chosenSigns_minimal ε hε).trans hsup)

lemma normalized_nonneg (N : ℕ) (t : UnitAddCircle) : 0 ≤ normalized N t :=
  div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

lemma normalized_continuous (N : ℕ) : Continuous (normalized N) :=
  (circlePolynomial (chosenSigns N)).continuous.norm.div_const _

lemma normalized_measurable (N : ℕ) : Measurable (normalized N) :=
  (normalized_continuous N).measurable

include hmain in
lemma normalized_eventually_bound {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ t, normalized N t ≤ 1 + η := by
  filter_upwards [chosenSigns_eventually_bound hmain hη, eventually_ge_atTop (1 : ℕ)] with N hb hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  intro t
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hNr)).2 (hb t)

include hmain in
lemma normalized_eventually_le_two :
    ∀ᶠ N : ℕ in atTop, ∀ t, normalized N t ≤ 2 := by
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
    normalized_eventually_bound hmain (η := 1) (by norm_num)

include hmain in
lemma normalized_error_sq_tendsto :
    Tendsto (fun N : ℕ => ∫ t : UnitAddCircle, (normalized N t - 1) ^ 2 ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [normalized_eventually_bound hmain (η := ε / 4) (by positivity),
    eventually_ge_atTop (1 : ℕ)] with N hb hN
  have hlo : 0 ≤ ∫ t : UnitAddCircle, (normalized N t - 1) ^ 2 ∂μ :=
    integral_nonneg (fun t => sq_nonneg _)
  have hhi := normalized_error_sq_bound hN (η := ε / 4) (by positivity) hb
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  linarith

end AsymptoticallyMinimalLittlewoodFiniteFlatness

end

end OAI

-- ---- from OAI.MeasureTheory.Integral.BoundedMoments ----
namespace OAI

open Filter MeasureTheory
open scoped Topology

namespace LittlewoodFiniteFlatness

/-- The interface used by the normalized Littlewood family. -/
theorem tendsto_integral_abs_sub_one_rpow
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ℕ → α → ℝ) (hf : ∀ n, Measurable (f n))
    (h0 : ∀ n x, 0 ≤ f n x)
    (h2 : ∀ᶠ n in atTop, ∀ x, f n x ≤ 2)
    (hmoment : Tendsto (fun n => ∫ x, (f n x - 1) ^ (2 : ℕ) ∂μ) atTop (𝓝 0))
    (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n => ∫ x, |f n x - 1| ^ p ∂μ) atTop (𝓝 0) := by
  apply tendsto_integral_rpow_of_bounded_moment μ (fun n x => |f n x - 1|)
    (fun n => continuous_abs.measurable.comp ((hf n).sub measurable_const)) ?_ 2 (by decide) ?_ p hp
  · filter_upwards [h2] with n hn
    intro x
    exact ⟨abs_nonneg _, abs_le.2 ⟨by linarith [h0 n x], by linarith [hn x]⟩⟩
  · simpa only [sq_abs] using hmoment

end LittlewoodFiniteFlatness

end OAI

-- ---- from OAI.Analysis.Littlewood.Main ----
namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators
end
end AsymptoticallyMinimalLittlewood
namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped Topology
open Filter

lemma small_delta_budget {η : ℝ} (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ<1/20 ∧
      Real.sqrt ((1+δ)^3/(1-δ))+393216*Real.sqrt (δ*Real.log (20/δ))<1+η/2 := by
  let f (x : ℝ) := Real.sqrt ((1+x)^3/(1-x))+
    393216*Real.sqrt (x*Real.log 20-x*Real.log x)
  have hf : ContinuousAt f 0 := by
    apply ContinuousAt.add
    · exact Real.continuous_sqrt.continuousAt.comp
        (((continuousAt_const.add continuousAt_id).pow 3).div
          (continuousAt_const.sub continuousAt_id) (by norm_num))
    · exact continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
        ((continuousAt_id.mul continuousAt_const).sub Real.continuous_mul_log.continuousAt))
  have hf0 : f 0=1 := by norm_num [f]
  obtain ⟨r,hr,hh⟩ := Metric.continuousAt_iff.mp hf (η/2) (by positivity)
  let δ := min (r/2) (1/40)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδ20 : δ<1/20 := (min_le_right _ _).trans_lt (by norm_num)
  have hδr : δ<r := (min_le_left _ _).trans_lt (by linarith)
  have hd : dist δ (0:ℝ)<r := by simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using hδr
  have hval := hh hd
  rw [hf0,Real.dist_eq] at hval
  have he : f δ=Real.sqrt ((1+δ)^3/(1-δ))+393216*Real.sqrt (δ*Real.log (20/δ)) := by
    dsimp [f]
    rw [Real.log_div (by norm_num : (20:ℝ)≠0) hδ.ne',mul_sub]
  refine ⟨δ,hδ,hδ20,?_⟩
  rw [he] at hval
  have := (abs_lt.mp hval).2
  linarith

end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators Topology
open Filter

end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators Topology
open Filter

theorem main : MainStatement := by
  intro η hη
  obtain ⟨δ,hδ,hδ20,hbudget⟩ := small_delta_budget hη
  obtain ⟨X,L,C,hC,hL,hX,hE,hmax⟩ := almost_sign_sampler hδ hδ20
  let B := Real.sqrt ((1+δ)^3/(1-δ))+393216*Real.sqrt (δ*Real.log (20/δ))
  have hB : B<1+η := by dsimp [B]; linarith
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun N : ℕ ↦ Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hinv : Tendsto (fun N : ℕ ↦ 1/Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero.comp hsqrt) using 1
    funext N
    simp only [Function.comp_apply,one_div]
  have hrem : Tendsto (fun N : ℕ ↦ C/(N : ℝ)+196608*(1/Real.sqrt (N : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_add,mul_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat C).add (hinv.const_mul 196608)
  have her : ∀ᶠ N : ℕ in atTop,
      C/(N : ℝ)+196608*(1/Real.sqrt (N : ℝ))<1+η-B :=
    hrem.eventually (gt_mem_nhds (sub_pos.mpr hB))
  have hen : ∀ᶠ N : ℕ in atTop, 1-8*δ<(∑ k, (X N k)^2)/(N : ℝ) :=
    hE.eventually (lt_mem_nhds (show 1-8*δ<L by linarith))
  have hall : ∀ᶠ N : ℕ in atTop,
      1≤N ∧ 1-8*δ<(∑ k, (X N k)^2)/(N : ℝ) ∧
        C/(N : ℝ)+196608*(1/Real.sqrt (N : ℝ))<1+η-B := by
    filter_upwards [eventually_ge_atTop (1:ℕ),hen,her] with N hN hn hr
    exact ⟨hN,hn,hr⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hall
  refine ⟨N₀,(hN₀ N₀ le_rfl).1,?_⟩
  intro N hN
  obtain ⟨hN1,hen,her⟩ := hN₀ N hN
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hener : (1-8*δ)*(N : ℝ)≤∑ k, (X N k)^2 :=
    ((lt_div_iff₀ hNr).mp hen).le
  obtain ⟨ε,hε,hεb⟩ := round_sample_once hN1 hδ hδ20 (X N) (hX N hN1)
    hener (hmax N hN1)
  refine ⟨ε,hε,?_⟩
  intro z hz
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hNr)).mp
  have hb := hεb z hz
  dsimp [B] at her
  linarith

end
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- from OAI.Analysis.Littlewood.FiniteFlatness ----
namespace OAI

/-! Finite positive real power-moment flatness for one all-length real-sign family. -/
namespace AsymptoticallyMinimalLittlewoodFiniteFlatness

open MeasureTheory
open scoped BigOperators Topology

/-- One all-length real-sign family, simultaneously for every finite positive real exponent. -/
theorem main : MainStatement := by
  have hmain : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
        ∀ z : ℂ, ‖z‖ = 1 → ‖littlewoodValue ε z‖ ≤ (1 + η) * Real.sqrt N := by
    change AsymptoticallyMinimalLittlewood.MainStatement
    exact AsymptoticallyMinimalLittlewood.main
  refine ⟨chosenSigns, chosenSigns_signing, ?_⟩
  intro p hp
  have h := LittlewoodFiniteFlatness.tendsto_integral_abs_sub_one_rpow
    μ normalized normalized_measurable normalized_nonneg
    (normalized_eventually_le_two hmain) (normalized_error_sq_tendsto hmain) p hp
  simpa only [normalized, circlePolynomial_apply, μ, Real.rpow_eq_pow] using h

end AsymptoticallyMinimalLittlewoodFiniteFlatness

end OAI

-- ---- mission target ----
open OAI OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate
open MeasureTheory
open scoped BigOperators Topology

namespace OAI
namespace AsymptoticallyMinimalLittlewoodFiniteFlatness
theorem _root_.solution : MainStatement := by
  first
    | exact OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.main
    | (apply OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.main <;> assumption)
    | (intros; apply OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.main <;> assumption)
end AsymptoticallyMinimalLittlewoodFiniteFlatness
end OAI
