-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1868a690-5928-579e-a849-2e3c5dffded8

import Mathlib
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "LDatum LDatum.BoundedOnStrips"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "rs22GlobalIntegral IsRapidlyDecreasingOnSiegelSets IsUniformlySiegelBounded"
namespace ZAProof
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

section Generic

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) (S : Set X) (K : ℂ → X → ℂ)

def StripBounded : Prop :=
  ∀ a b : ℝ, ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ∀ x ∈ S, ‖K s x‖ ≤ M

variable {μ S K}

theorem aestronglyMeasurable_restrict (hKc : ∀ s, Continuous (K s)) (s : ℂ) :
    AEStronglyMeasurable (K s) (μ.restrict S) :=
  (hKc s).aestronglyMeasurable

theorem integrableOn (hS : MeasurableSet S) (hμS : μ S < ⊤) (hKc : ∀ s, Continuous (K s))
    (hKb : StripBounded S K) (s : ℂ) : IntegrableOn (K s) S μ := by
  obtain ⟨M, hM⟩ := hKb s.re s.re
  haveI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hμS.ne
  refine Integrable.of_bound (aestronglyMeasurable_restrict hKc s) M ?_
  filter_upwards [ae_restrict_mem hS] with x hx
  exact hM s le_rfl le_rfl x hx

omit [TopologicalSpace X] [BorelSpace X] in

theorem boundedOnStrips (hμS : μ S < ⊤) (hKb : StripBounded S K) :
    LDatum.BoundedOnStrips (fun s => ∫ x in S, K s x ∂μ) := by
  intro a b
  obtain ⟨M, hM⟩ := hKb a b
  refine ⟨M * μ.real S, fun s ha hb => ?_⟩
  exact norm_setIntegral_le_of_norm_le_const hμS (hM s ha hb)

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] in

theorem norm_deriv_le (hKd : ∀ x, Differentiable ℂ (fun s => K s x)) {a b M : ℝ}
    (hM : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ∀ x ∈ S, ‖K s x‖ ≤ M)
    {s : ℂ} (ha : a + 1 ≤ s.re) (hb : s.re ≤ b - 1) {x : X} (hx : x ∈ S) :
    ‖deriv (fun z => K z x) s‖ ≤ M := by
  have hsphere : ∀ z ∈ Metric.sphere s 1, ‖(fun z => K z x) z‖ ≤ M := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have hre : |z.re - s.re| ≤ 1 := by
      have := Complex.abs_re_le_norm (z - s)
      rw [Complex.sub_re] at this
      exact this.trans hz.le
    rw [abs_le] at hre
    exact hM z (by linarith) (by linarith) x hx
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun z => K z x) (c := s) (R := 1)
    one_pos (hKd x).diffContOnCl hsphere
  simpa using h

theorem measurable_deriv (hKc : ∀ s, Continuous (K s)) (hKd : ∀ x, Differentiable ℂ (fun s => K s x))
    (s : ℂ) : Measurable (fun x => deriv (fun z => K z x) s) := by
  set u : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) with hu
  have hu0 : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hune : ∀ n, u n ≠ 0 := fun n => by
    rw [hu]; exact one_div_ne_zero (Nat.cast_add_one_ne_zero n)
  have hu' : Tendsto u atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu0, Eventually.of_forall fun n => hune n⟩
  refine measurable_of_tendsto_metrizable (f := fun n x => (u n)⁻¹ • (K (s + u n) x - K s x)) ?_ ?_
  · intro n
    exact (((hKc (s + u n)).fun_sub (hKc s)).fun_const_smul _).measurable
  · rw [tendsto_pi_nhds]
    intro x
    have h := ((hKd x) s).hasDerivAt.tendsto_slope_zero
    exact h.comp hu'

theorem hasDerivAt_integral (hS : MeasurableSet S) (hμS : μ S < ⊤) (hKc : ∀ s, Continuous (K s))
    (hKd : ∀ x, Differentiable ℂ (fun s => K s x)) (hKb : StripBounded S K) (s₀ : ℂ) :
    HasDerivAt (fun s => ∫ x in S, K s x ∂μ) (∫ x in S, deriv (fun z => K z x) s₀ ∂μ) s₀ := by
  haveI : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hμS.ne
  obtain ⟨M, hM⟩ := hKb (s₀.re - 2) (s₀.re + 2)
  have hball : Metric.ball s₀ 1 ∈ 𝓝 s₀ := Metric.ball_mem_nhds _ one_pos
  have h1 : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (K s) (μ.restrict S) :=
    Eventually.of_forall fun s => aestronglyMeasurable_restrict hKc s
  have h2 : Integrable (K s₀) (μ.restrict S) := integrableOn hS hμS hKc hKb s₀
  have h3 : AEStronglyMeasurable (fun x => deriv (fun z => K z x) s₀) (μ.restrict S) :=
    (measurable_deriv hKc hKd s₀).aestronglyMeasurable
  have hstrip : ∀ s ∈ Metric.ball s₀ 1, s₀.re - 2 + 1 ≤ s.re ∧ s.re ≤ s₀.re + 2 - 1 := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    have hre : |s.re - s₀.re| < 1 := by
      have := Complex.abs_re_le_norm (s - s₀)
      rw [Complex.sub_re] at this
      exact lt_of_le_of_lt this hs
    rw [abs_lt] at hre
    constructor <;> linarith
  have h4 : ∀ᵐ x ∂μ.restrict S, ∀ s ∈ Metric.ball s₀ 1, ‖deriv (fun z => K z x) s‖ ≤ (fun _ => M) x := by
    filter_upwards [ae_restrict_mem hS] with x hx s hs
    exact norm_deriv_le hKd hM (hstrip s hs).1 (hstrip s hs).2 hx
  have h5 : Integrable (fun _ : X => M) (μ.restrict S) := integrable_const M
  have h6 : ∀ᵐ x ∂μ.restrict S, ∀ s ∈ Metric.ball s₀ 1,
      HasDerivAt (fun z => K z x) (deriv (fun z => K z x) s) s :=
    Eventually.of_forall fun x s _ => ((hKd x) s).hasDerivAt
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun s x => deriv (fun z => K z x) s) hball h1 h2 h3 h4 h5 h6).2

theorem differentiable_integral (hS : MeasurableSet S) (hμS : μ S < ⊤) (hKc : ∀ s, Continuous (K s))
    (hKd : ∀ x, Differentiable ℂ (fun s => K s x)) (hKb : StripBounded S K) :
    Differentiable ℂ (fun s => ∫ x in S, K s x ∂μ) :=
  fun s => (hasDerivAt_integral hS hμS hKc hKd hKb s).differentiableAt

end Generic

section Siegel

open NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
p2m_open "AutomorphicForm AutomorphicForm.WindowedSiegel LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded.LanglandsTunnell.RankinSelberg"

variable (F : Type) [Field F] [NumberField F]

theorem one_add_archHeight_pos {c u : ℝ} (hc : 0 < c) {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ integralWindowedSiegelSet F c u) : 0 < 1 + archHeight F (glArch (𝓞 F) F g) := by
  have : c ≤ archHeight F (glArch (𝓞 F) F g) := hg.2.1
  linarith

theorem stripBounded {c u : ℝ} (hc : 0 < c) (tset : Finset (AdelicGL2 (𝓞 F) F))
    {𝓕 : Set (AdelicGL2 (𝓞 F) F)} (h𝓕S : 𝓕 ⊆ ⋃ t ∈ tset, (· * t) '' integralWindowedSiegelSet F c u)
    {φ φ' : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsRapidlyDecreasingOnSiegelSets F φ) (hφ' : IsRapidlyDecreasingOnSiegelSets F φ')
    {H : ℂ → AdelicGL2 (𝓞 F) F → ℂ} (hHb : IsUniformlySiegelBounded F H) :
    StripBounded 𝓕 (fun s x => φ x * φ' x * H s x) := by
  intro a b
  choose A N hA using fun t : AdelicGL2 (𝓞 F) F => hHb a b c u t hc
  choose C hC using fun t : AdelicGL2 (𝓞 F) F => hφ c u t hc (N t)
  choose C' hC' using fun t : AdelicGL2 (𝓞 F) F => hφ'.bounded F c u t hc
  refine ⟨∑ t ∈ tset, max (C t) 0 * max (C' t) 0 * max (A t) 0, fun s ha hb x hx => ?_⟩
  obtain ⟨t, ht, g, hg, rfl⟩ : ∃ t ∈ tset, ∃ g ∈ integralWindowedSiegelSet F c u, g * t = x := by
    have := h𝓕S hx
    simp only [Set.mem_iUnion, Set.mem_image] at this
    obtain ⟨t, ht, g, hg, hgx⟩ := this
    exact ⟨t, ht, g, hg, hgx⟩
  have hpos := one_add_archHeight_pos F hc hg
  set h : ℝ := 1 + archHeight F (glArch (𝓞 F) F g) with hh_def
  have hHle : ‖H s (g * t)‖ ≤ max (A t) 0 * h ^ N t :=
    (hA t s ha hb g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hpos.le _))
  have hφle : ‖φ (g * t)‖ * h ^ N t ≤ max (C t) 0 := (hC t g hg).trans (le_max_left _ _)
  have hφ'le : ‖φ' (g * t)‖ ≤ max (C' t) 0 := (hC' t g hg).trans (le_max_left _ _)
  have hterm : ‖φ (g * t) * φ' (g * t) * H s (g * t)‖ ≤ max (C t) 0 * max (C' t) 0 * max (A t) 0 := by
    rw [norm_mul, norm_mul]
    calc ‖φ (g * t)‖ * ‖φ' (g * t)‖ * ‖H s (g * t)‖
        ≤ ‖φ (g * t)‖ * ‖φ' (g * t)‖ * (max (A t) 0 * h ^ N t) :=
          mul_le_mul_of_nonneg_left hHle (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖φ (g * t)‖ * h ^ N t) * ‖φ' (g * t)‖ * max (A t) 0 := by ring
      _ ≤ max (C t) 0 * max (C' t) 0 * max (A t) 0 := by
          refine mul_le_mul (mul_le_mul hφle hφ'le (norm_nonneg _) (le_max_right _ _)) le_rfl
            (le_max_right _ _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
  refine hterm.trans ?_
  have hnn : ∀ t' ∈ tset, 0 ≤ max (C t') 0 * max (C' t') 0 * max (A t') 0 := fun t' _ =>
    mul_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  exact Finset.single_le_sum hnn ht

end Siegel

end LanglandsTunnell.RankinSelberg.ZAProof

end

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm AutomorphicForm.WindowedSiegel
p2m_open "NumberField.AdelicHaar NumberField.AdelicLevel LanglandsTunnell.RankinSelberg P2MW.S_LanglandsTunnell_RankinSelberg_integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded.LanglandsTunnell.RankinSelberg"
open LanglandsTunnell.RankinSelberg.ZAProof

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u : ℝ) (hc : 0 < c) (tset : Finset (AdelicGL2 (𝓞 F) F))
    (𝓕 : Set (AdelicGL2 (𝓞 F) F)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕μ : adelicGLHaar (Fin 2) (𝓞 F) F 𝓕 < ⊤)
    (h𝓕S : 𝓕 ⊆ ⋃ t ∈ tset, (· * t) '' integralWindowedSiegelSet F c u)
    (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφ'c : Continuous φ')
    (hφ : IsRapidlyDecreasingOnSiegelSets F φ) (hφ' : IsRapidlyDecreasingOnSiegelSets F φ')
    (H : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hHd : ∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => H s g))
    (hHc : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2)
    (hHb : IsUniformlySiegelBounded F H) :
    (∀ s : ℂ, IntegrableOn (fun g => φ g * φ' g * H s g) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
    Differentiable ℂ (fun s : ℂ => rs22GlobalIntegral F 𝓕 φ φ' (H s)) ∧
    LanglandsTunnell.LDatum.BoundedOnStrips (fun s : ℂ => rs22GlobalIntegral F 𝓕 φ φ' (H s)) := by
  set K : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s x => φ x * φ' x * H s x with hK
  have hKc : ∀ s, Continuous (K s) := fun s =>
    (hφc.mul hφ'c).mul (hHc.comp (Continuous.prodMk_right s))
  have hKd : ∀ x, Differentiable ℂ (fun s => K s x) := fun x =>
    (hHd x).const_mul _
  have hKb : StripBounded 𝓕 K := stripBounded F hc tset h𝓕S hφ hφ' hHb
  refine ⟨fun s => integrableOn h𝓕m h𝓕μ hKc hKb s, ?_, ?_⟩
  · exact differentiable_integral h𝓕m h𝓕μ hKc hKd hKb
  · exact boundedOnStrips h𝓕μ hKb

end S_LanglandsTunnell_RankinSelberg_integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded (solution)
