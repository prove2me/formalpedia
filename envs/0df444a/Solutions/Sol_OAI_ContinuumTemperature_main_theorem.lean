-- Prove2me | solution 1 for OAI.ContinuumTemperature.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:07:55.20819+00:00
-- url     : https://prove2.me/submissions/6aa7eedf-6efa-4783-94e8-1ff344c85597

import Mathlib
import Definitions.Def_ContinuumTransition
import Definitions.Def_OAIQWCT000
import Theorems.Thm_OAI_ContinuumTemperature_convex_pointwise_locally_uniform
import Theorems.Thm_OAI_ContinuumTemperature_exists_constructionData

section
-- module Solutions.OAIQW_ContinuumTemperature.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PressureGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section

open scoped Topology BigOperators
open Set Filter

noncomputable section

namespace ContinuumTemperature

theorem fenchel_eq_of_support {Q : Parameter → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : IsPartialConjugate Q H) {β h s d : ℝ}
    (hβ : 0 < β) (hd : 0 ≤ d) (hv : Supports Q (β, h) (s, d)) :
    H β d = h * d - Q (β, h) := by
  have hL := hH β d hβ hd
  apply le_antisymm
  · apply hL.2
    rintro _ ⟨z, rfl⟩
    have hz := hv (β, z) hβ
    dsimp at hz
    nlinarith
  · exact hL.1 (mem_range_self h)

theorem supergradient_of_support {Q : Parameter → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : IsPartialConjugate Q H) {β h s d : ℝ}
    (hβ : 0 < β) (hd : 0 ≤ d) (hv : Supports Q (β, h) (s, d)) :
    ∀ β' : ℝ, 0 < β' → H β' d ≤ H β d - s * (β' - β) := by
  have heq := fenchel_eq_of_support hH hβ hd hv
  intro β' hβ'
  apply (hH β' d hβ' hd).2
  rintro _ ⟨z, rfl⟩
  have hz := hv (β', z) hβ'
  dsimp at hz
  nlinarith

theorem concave_one_sided_support {F : ℝ → ℝ}
    (hc : ConcaveOn ℝ (Ioi 0) F) {β : ℝ} (hβ : 0 < β) :
    ∃ l r : ℝ,
      HasDerivWithinAt F l (Iic β) β ∧
      HasDerivWithinAt F r (Ici β) β ∧
      ∀ u : ℝ, (∀ y : ℝ, 0 < y → F y ≤ F β + u * (y - β)) → r ≤ u ∧ u ≤ l := by
  have hmem : β ∈ interior (Ioi (0 : ℝ)) := by simpa using hβ
  let l := -derivWithin (-F) (Iio β) β
  let r := -derivWithin (-F) (Ioi β) β
  have hl : HasDerivWithinAt F l (Iio β) β := by
    simpa only [neg_neg] using (hc.neg.hasDerivWithinAt_leftDeriv_of_mem_interior hmem).neg
  have hr : HasDerivWithinAt F r (Ioi β) β := by
    simpa only [neg_neg] using (hc.neg.hasDerivWithinAt_rightDeriv_of_mem_interior hmem).neg
  refine ⟨l, r, hl.Iic_of_Iio, hr.Ici_of_Ioi, ?_⟩
  intro u hu
  have hposL : ∀ᶠ y : ℝ in 𝓝[<] β, 0 < y :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hβ)
  have hposR : ∀ᶠ y : ℝ in 𝓝[>] β, 0 < y :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hβ)
  constructor
  · apply le_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hr)
    filter_upwards [hposR, eventually_mem_nhdsWithin] with y hy hby
    rw [slope_def_field]
    apply (div_le_iff₀ (sub_pos.mpr hby)).mpr
    linarith [hu y hy]
  · apply ge_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hl)
    filter_upwards [hposL, eventually_mem_nhdsWithin] with y hy hyb
    rw [slope_def_field]
    apply (le_div_iff_of_neg (sub_neg.mpr hyb)).mpr
    linarith [hu y hy]

theorem canonical_jump_of_two_supports {Q : Parameter → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : IsPartialConjugate Q H) {t β h d s₁ s₂ : ℝ}
    (ht : 0 < t) (hβ : 0 < β) (hd : 0 ≤ d)
    (hc : ConcaveOn ℝ (Ioi 0) (fun b => H b d))
    (hs : s₁ < s₂) (hv₁ : Supports Q (β, h) (s₁, d))
    (hv₂ : Supports Q (β, h) (s₂, d)) :
    ∃ l r : ℝ,
      HasDerivWithinAt (fun b => t * H b d / b) l (Iic β) β ∧
      HasDerivWithinAt (fun b => t * H b d / b) r (Ici β) β ∧
      t / β * (s₂ - s₁) ≤ l - r ∧ r < l := by
  obtain ⟨l, r, hl, hr, hbounds⟩ := concave_one_sided_support hc hβ
  have hb₁ := (hbounds (-s₁) (by
    intro y hy
    simpa only [neg_mul, sub_eq_add_neg] using
      supergradient_of_support hH hβ hd hv₁ y hy)).2
  have hb₂ := (hbounds (-s₂) (by
    intro y hy
    simpa only [neg_mul, sub_eq_add_neg] using
      supergradient_of_support hH hβ hd hv₂ y hy)).1
  have hneq : β ≠ 0 := ne_of_gt hβ
  let l' := (t * l * β - t * H β d) / β ^ 2
  let r' := (t * r * β - t * H β d) / β ^ 2
  have hl' : HasDerivWithinAt (fun b => t * H b d / b) l' (Iic β) β := by
    simpa only [Pi.div_def, id_eq, mul_one, l'] using
      (hl.const_mul t).div (hasDerivAt_id β).hasDerivWithinAt hneq
  have hr' : HasDerivWithinAt (fun b => t * H b d / b) r' (Ici β) β := by
    simpa only [Pi.div_def, id_eq, mul_one, r'] using
      (hr.const_mul t).div (hasDerivAt_id β).hasDerivWithinAt hneq
  have heq : l' - r' = t / β * (l - r) := by
    dsimp [l', r']
    field_simp
    ring
  have hgap : t / β * (s₂ - s₁) ≤ l' - r' := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg ht.le hβ.le)
  refine ⟨l', r', hl', hr', hgap, ?_⟩
  have hstrict : 0 < t / β * (s₂ - s₁) := mul_pos (div_pos ht hβ) (sub_pos.mpr hs)
  linarith

theorem canonical_interval_of_support_ball {Q : Parameter → ℝ} {H : ℝ → ℝ → ℝ}
    (hH : IsPartialConjugate Q H) {t β h γ : ℝ} {g : Parameter}
    (ht : 0 < t) (hβ : 0 < β) (hγ : 0 < γ) (hg : 0 < g.2)
    (hc : ∀ d : ℝ, 0 < d → ConcaveOn ℝ (Ioi 0) (fun b => H b d))
    (hball : ∀ v ∈ SlopeBall g γ, Supports Q (β, h) v) :
    ∃ I : Set ℝ, IsOpen I ∧ OrdConnected I ∧ I.Nonempty ∧ I ⊆ Ioi 0 ∧
      ∀ d ∈ I, ∃ l r : ℝ,
        HasDerivWithinAt (fun b => t * H b d / b) l (Iic β) β ∧
        HasDerivWithinAt (fun b => t * H b d / b) r (Ici β) β ∧
        t * γ / β ≤ l - r ∧ r < l := by
  let δ := min (γ / 2) (g.2 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδγ : δ ≤ γ / 2 := min_le_left _ _
  have hδg : δ ≤ g.2 / 2 := min_le_right _ _
  let I := Ioo (g.2 - δ) (g.2 + δ)
  have hpos : I ⊆ Ioi 0 := by
    intro d hd
    dsimp [I] at hd
    change 0 < d
    linarith [hd.1]
  refine ⟨I, isOpen_Ioo, ordConnected_Ioo, ⟨g.2, ?_⟩, hpos, ?_⟩
  · change g.2 - δ < g.2 ∧ g.2 < g.2 + δ
    constructor <;> linarith
  · intro d hd
    have hdpos := hpos hd
    have hnear : |d - g.2| < γ / 2 := by
      rw [abs_lt]
      dsimp [I] at hd
      constructor <;> linarith [hd.1, hd.2]
    have hsq : (d - g.2) ^ 2 < (γ / 2) ^ 2 := by
      nlinarith [(abs_lt.mp hnear).1, (abs_lt.mp hnear).2]
    have hv₁ : (g.1 - γ / 2, d) ∈ SlopeBall g γ := by
      dsimp [SlopeBall]
      nlinarith [sq_pos_of_pos hγ]
    have hv₂ : (g.1 + γ / 2, d) ∈ SlopeBall g γ := by
      dsimp [SlopeBall]
      nlinarith [sq_pos_of_pos hγ]
    obtain ⟨l, r, hl, hr, hgap, hstrict⟩ := canonical_jump_of_two_supports hH
      ht hβ hdpos.le (hc d hdpos) (by linarith : g.1 - γ / 2 < g.1 + γ / 2)
      (hball _ hv₁) (hball _ hv₂)
    refine ⟨l, r, hl, hr, ?_, hstrict⟩
    convert hgap using 1
    ring

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConvexSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology
open Filter Set
noncomputable section
namespace ContinuumTemperature

lemma supports_iff_supportOn {F : Parameter → ℝ} {x v : Parameter} :
    Supports F x v ↔ SupportOn pressureDomain F x v := by
  simp only [Supports, SupportOn, pDot, Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h y hy <;> have := h y hy <;> linarith

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.RadialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

noncomputable section
open scoped ContDiff

theorem baseKernel_nonneg (x : Space) : 0 ≤ baseKernel x := Real.smoothTransition.nonneg _

theorem baseKernel_eq_one {x : Space} (hx : ‖x‖ ≤ 1 / 2) : baseKernel x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem baseKernel_eq_zero {x : Space} (hx : 1 ≤ ‖x‖) : baseKernel x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem contDiff_baseKernel : ContDiff ℝ ∞ baseKernel := by
  have heq : baseKernel = fun x : Space =>
      (ContDiffBumpBase.ofInnerProductSpace Space).toFun 2 ((2 : ℝ) • x) := by
    funext x
    norm_num [baseKernel, ContDiffBumpBase.ofInnerProductSpace, norm_smul]
  rw [heq]
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hmem : ((2 : ℝ), (2 : ℝ) • x) ∈ Ioi (1 : ℝ) ×ˢ (Set.univ : Set Space) := by
    norm_num
  have hdiff := (ContDiffBumpBase.ofInnerProductSpace Space).smooth.contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
  have hcomp := hdiff.comp x (contDiffAt_const.prodMk
    (ContDiffAt.const_smul (2 : ℝ) contDiffAt_id) :
      ContDiffAt ℝ ∞ (fun y : Space => ((2 : ℝ), (2 : ℝ) • y)) x)
  exact hcomp

theorem hasCompactSupport_baseKernel : HasCompactSupport baseKernel := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1)
  intro x hx
  exact baseKernel_eq_zero (by simpa using (not_lt.mp (fun h => hx (by simpa using h.le))))

theorem integrable_baseKernel : Integrable baseKernel :=
  contDiff_baseKernel.continuous.integrable_of_hasCompactSupport hasCompactSupport_baseKernel

theorem integral_baseKernel_pos : 0 < ∫ x : Space, baseKernel x := by
  rw [integral_pos_iff_support_of_nonneg baseKernel_nonneg integrable_baseKernel]
  have hball : (Metric.ball (0 : Space) (1 / 2 : ℝ)).Nonempty := ⟨0, by norm_num⟩
  apply lt_of_lt_of_le (Metric.isOpen_ball.measure_pos volume hball)
  apply measure_mono
  intro x hx
  have hn : ‖x‖ < 1 / 2 := by simpa using hx
  rw [Function.mem_support, baseKernel_eq_one hn.le]
  norm_num

theorem kernelProfile_nonneg (r : ℝ) : 0 ≤ kernelProfile r :=
  div_nonneg (Real.smoothTransition.nonneg _) integral_baseKernel_pos.le

theorem kernelProfile_le (r : ℝ) : kernelProfile r ≤ 1 / (∫ x : Space, baseKernel x) := by
  exact div_le_div_of_nonneg_right (Real.smoothTransition.le_one _) integral_baseKernel_pos.le

theorem continuous_kernelProfile : Continuous kernelProfile := by
  unfold kernelProfile
  exact (Real.smoothTransition.continuous.comp (continuous_const.sub
    (continuous_const.mul continuous_id))).div_const _

theorem kernelProfile_zero {r : ℝ} (hr : 1 ≤ r) : kernelProfile r = 0 := by
  unfold kernelProfile
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_div]

theorem scaledKernelProfile_nonneg {R : ℝ} (hR : 0 < R) (r : ℝ) :
    0 ≤ scaledKernelProfile R r :=
  mul_nonneg (by positivity) (kernelProfile_nonneg _)

theorem scaledKernelProfile_le {R : ℝ} (hR : 0 < R) (r : ℝ) :
    scaledKernelProfile R r ≤ R⁻¹ ^ 3 / (∫ x : Space, baseKernel x) := by
  dsimp [scaledKernelProfile]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (kernelProfile_le (r / R))
    (by positivity : (0 : ℝ) ≤ R⁻¹ ^ 3)

theorem scaledKernelProfile_zero {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    scaledKernelProfile R r = 0 := by
  unfold scaledKernelProfile
  rw [kernelProfile_zero ((le_div_iff₀ hR).mpr (by simpa using hr)), mul_zero]

theorem continuous_scaledKernelProfile (R : ℝ) : Continuous (scaledKernelProfile R) := by
  exact continuous_const.mul (continuous_kernelProfile.comp (continuous_id.div_const _))

theorem kernelHeight_pos : 0 < kernelHeight := one_div_pos.mpr integral_baseKernel_pos

theorem scaledKernelProfile_le_height {R : ℝ} (hR : 1 ≤ R) (r : ℝ) :
    scaledKernelProfile R r ≤ kernelHeight := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  calc
    _ ≤ R⁻¹ ^ 3 / (∫ x : Space, baseKernel x) := scaledKernelProfile_le hRp r
    _ ≤ kernelHeight := by
      unfold kernelHeight
      apply div_le_div_of_nonneg_right _ integral_baseKernel_pos.le
      exact pow_le_one₀ (inv_nonneg.mpr hRp.le) (inv_le_one_of_one_le₀ hR)

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ProfileTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

theorem summable_attraction_terms {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) (r : ℝ) :
    Summable (fun j => σ j * scaledKernelProfile (R j) r) := by
  apply (hs.mul_right kernelHeight).of_norm_bounded
  intro j
  rw [Real.norm_of_nonneg (mul_nonneg (hσ j)
    (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))]
  exact mul_le_mul_of_nonneg_left (scaledKernelProfile_le_height (hR j) r) (hσ j)

theorem attraction_nonneg {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (r : ℝ) :
    0 ≤ attraction t σ R r := by
  apply mul_nonneg ht
  exact tsum_nonneg (fun j => mul_nonneg (hσ j)
    (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))

theorem attraction_le {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) (r : ℝ) :
    attraction t σ R r ≤ t * (∑' j, σ j) * kernelHeight := by
  unfold attraction
  rw [mul_assoc, ← hs.tsum_mul_right]
  apply mul_le_mul_of_nonneg_left _ ht
  exact (summable_attraction_terms hσ hR hs r).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (scaledKernelProfile_le_height (hR j) r) (hσ j))
    (hs.mul_right kernelHeight)

theorem continuous_attraction (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Continuous (attraction t σ R) := by
  apply continuous_const.mul
  apply continuous_tsum (fun j => continuous_const.mul (continuous_scaledKernelProfile (R j)))
    (hs.mul_right kernelHeight)
  intro j r
  change ‖σ j * scaledKernelProfile (R j) r‖ ≤ σ j * kernelHeight
  rw [Real.norm_of_nonneg (mul_nonneg (hσ j)
    (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))]
  exact mul_le_mul_of_nonneg_left (scaledKernelProfile_le_height (hR j) r) (hσ j)

theorem weighted_scaledKernelProfile_le {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) :
    r ^ 3 * scaledKernelProfile R r ≤ kernelHeight := by
  by_cases h : R ≤ r
  · rw [scaledKernelProfile_zero hR h, mul_zero]
    exact kernelHeight_pos.le
  · have hrR : r ≤ R := (lt_of_not_ge h).le
    calc
      _ ≤ r ^ 3 * (R⁻¹ ^ 3 / (∫ x : Space, baseKernel x)) :=
        mul_le_mul_of_nonneg_left (scaledKernelProfile_le hR r) (by positivity)
      _ = (r / R) ^ 3 * kernelHeight := by dsimp [kernelHeight]; ring
      _ ≤ 1 * kernelHeight := mul_le_mul_of_nonneg_right
        (pow_le_one₀ (div_nonneg hr hR.le) ((div_le_one hR).mpr hrR)) kernelHeight_pos.le
      _ = kernelHeight := one_mul _

theorem tendsto_weighted_attraction (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Tendsto (fun r => r ^ 3 * attraction t σ R r) atTop (𝓝 0) := by
  have hlim : Tendsto (fun r : ℝ => ∑' j, r ^ 3 *
      (σ j * scaledKernelProfile (R j) r)) atTop (𝓝 (∑' _j : ℕ, (0 : ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence (hs.mul_right kernelHeight)
    · intro j
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (R j)] with r hr
      rw [scaledKernelProfile_zero (lt_of_lt_of_le zero_lt_one (hR j)) hr]
      simp
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr j
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
        (mul_nonneg (hσ j) (scaledKernelProfile_nonneg
          (lt_of_lt_of_le zero_lt_one (hR j)) r)))]
      calc
        _ = σ j * (r ^ 3 * scaledKernelProfile (R j) r) := by ring
        _ ≤ σ j * kernelHeight := mul_le_mul_of_nonneg_left
          (weighted_scaledKernelProfile_le (lt_of_lt_of_le zero_lt_one (hR j)) hr) (hσ j)
  simp only [tsum_zero] at hlim
  have heq (r : ℝ) : r ^ 3 * attraction t σ R r =
      t * ∑' j, r ^ 3 * (σ j * scaledKernelProfile (R j) r) := by
    rw [tsum_mul_left]
    unfold attraction
    ring
  simp_rw [heq]
  simpa using hlim.const_mul t

theorem coreProfile_eq_zero {t r : ℝ} (ht : 1 < t) (hr : 1 ≤ r) :
    coreProfile t r = 0 := by
  have he : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs : (1 + shellDelta) * Real.exp (-t) < 1 := by
    have ht' : Real.exp t > 1 + t := by simpa only [add_comm] using (Real.add_one_lt_exp (by linarith : t ≠ 0))
    rw [Real.exp_neg]
    unfold shellDelta
    apply (mul_inv_lt_iff₀ (Real.exp_pos t)).mpr
    linarith
  unfold coreProfile
  rw [ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_right (not_lt.mpr hr)]

theorem physicalProfile_isLittleO {t : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Asymptotics.IsLittleO atTop (physicalProfile t σ R) (fun r : ℝ => r ^ (-3 : ℤ)) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact fun h => False.elim ((zpow_ne_zero _ hr.ne') h)
  · have hl : Tendsto (fun r => -(r ^ 3 * attraction t σ R r)) atTop (𝓝 0) := by
      simpa only [neg_zero] using (tendsto_weighted_attraction t hσ hR hs).neg
    apply hl.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    rw [physicalProfile, coreProfile_eq_zero ht hr, zero_sub]
    simp only [zpow_neg, zpow_ofNat, div_inv_eq_mul]
    ring

theorem integrable_tsum_real {α : Type u_1} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → α → ℝ) (hF : ∀ j, Integrable (F j) μ)
    (hs : Summable (fun j => ∫ x, ‖F j x‖ ∂μ)) :
    Integrable (fun x => ∑' j, F j x) μ := by
  refine ⟨(AEMeasurable.tsum (fun j => (hF j).aemeasurable)).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc
    _ ≤ ∫⁻ x, ∑' j, ‖F j x‖ₑ ∂μ := lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' j, ∫⁻ x, ‖F j x‖ₑ ∂μ :=
      lintegral_tsum (fun j => (hF j).aemeasurable.enorm)
    _ = ∑' j, ENNReal.ofReal (∫ x, ‖F j x‖ ∂μ) := by
      congr 1
      funext j
      exact (ofReal_integral_norm_eq_lintegral_enorm (hF j)).symm
    _ < ⊤ := hs.tsum_ofReal_lt_top

theorem radialWeighted_nonneg {R : ℝ} (hR : 0 < R) (r : ℝ) :
    0 ≤ radialWeighted R r := by
  apply Set.indicator_nonneg
  intro s _
  exact mul_nonneg (sq_nonneg s) (scaledKernelProfile_nonneg hR s)

theorem radialWeighted_eq {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) :
    radialWeighted R r = r ^ 2 * scaledKernelProfile R r := by
  by_cases hh : r ≤ R
  · exact Set.indicator_of_mem (show r ∈ Icc (0 : ℝ) R from ⟨hr, hh⟩) _
  · rw [radialWeighted, Set.indicator_of_notMem (fun h => hh h.2),
      scaledKernelProfile_zero hR (le_of_not_ge hh), mul_zero]

theorem integrable_radialWeighted (R : ℝ) : Integrable (radialWeighted R) := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact (continuous_id.pow 2 |>.mul (continuous_scaledKernelProfile R)).integrableOn_Icc

theorem integral_radialWeighted_le {R : ℝ} (hR : 0 < R) :
    ∫ r : ℝ, radialWeighted R r ≤ kernelHeight / 3 := by
  let F : ℝ → ℝ := fun r => (Icc (0 : ℝ) R).indicator
    (fun s => s ^ 2 * (R⁻¹ ^ 3 * kernelHeight)) r
  have hFi : Integrable F := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact (continuous_id.pow 2 |>.mul continuous_const).integrableOn_Icc
  have hbound : ∀ r, radialWeighted R r ≤ F r := by
    intro r
    apply Set.indicator_le_indicator
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
    simpa only [kernelHeight, div_eq_mul_inv, one_mul] using scaledKernelProfile_le hR r
  apply (integral_mono (integrable_radialWeighted R) hFi hbound).trans_eq
  dsimp [F]
  rw [integral_indicator measurableSet_Icc, integral_mul_const,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR.le,
    integral_pow]
  dsimp [kernelHeight]
  norm_num
  field_simp

theorem integrable_weighted_attraction (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    IntegrableOn (fun r => r ^ 2 * attraction t σ R r) (Ioi (0 : ℝ)) := by
  have hi (j : ℕ) : Integrable (fun r => σ j * radialWeighted (R j) r) :=
    (integrable_radialWeighted (R j)).const_mul (σ j)
  have hs' : Summable (fun j => ∫ r : ℝ, ‖σ j * radialWeighted (R j) r‖) := by
    apply Summable.of_nonneg_of_le (fun j => integral_nonneg (fun _ => norm_nonneg _)) _
      (hs.mul_right (kernelHeight / 3))
    intro j
    simp_rw [Real.norm_of_nonneg (mul_nonneg (hσ j)
      (radialWeighted_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) _))]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_radialWeighted_le (lt_of_lt_of_le zero_lt_one (hR j))) (hσ j)
  apply ((integrable_tsum_real _ hi hs').const_mul t).integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [attraction]
  simp_rw [radialWeighted_eq (lt_of_lt_of_le zero_lt_one (hR _)) (le_of_lt hr)]
  rw [show (fun j => σ j * (r ^ 2 * scaledKernelProfile (R j) r)) =
      (fun j => r ^ 2 * (σ j * scaledKernelProfile (R j) r)) by funext j; ring,
    tsum_mul_left]
  ring

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

theorem measurable_coreProfile (t : ℝ) : Measurable (coreProfile t) := by
  unfold coreProfile
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.add ((measurable_const.div measurable_id).pow_const 12))
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

theorem coreProfile_nonneg (t r : ℝ) : 0 ≤ coreProfile t r := by
  unfold coreProfile
  split_ifs <;> positivity

theorem coreProfile_le {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (t : ℝ) :
    coreProfile t r ≤ t ^ 2 + (Real.exp (-t) / a) ^ 12 := by
  have hdiv : Real.exp (-t) / r ≤ Real.exp (-t) / a :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le ha har
  have hp := pow_le_pow_left₀ (div_nonneg (Real.exp_pos _).le (ha.le.trans har)) hdiv 12
  unfold coreProfile
  split_ifs <;> nlinarith [sq_nonneg t, even_two_mul 6 |>.pow_nonneg (Real.exp (-t) / a)]

theorem measurable_physicalProfile (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Measurable (physicalProfile t σ R) :=
  (measurable_coreProfile t).sub (continuous_attraction t hσ hR hs).measurable

theorem measurable_radialPotential {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (radialPotential φ) := by
  apply Measurable.ite (measurableSet_singleton (0 : Space)) measurable_const
  exact measurable_coe_real_ereal.comp (hφ.comp measurable_norm)

theorem physicalProfile_locally_bounded {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ)
    {a b : ℝ} (ha : 0 < a) :
    BddAbove (physicalProfile t σ R '' Icc a b) ∧
      BddBelow (physicalProfile t σ R '' Icc a b) := by
  constructor
  · refine ⟨t ^ 2 + (Real.exp (-t) / a) ^ 12, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact (sub_le_self _ (attraction_nonneg ht hσ hR r)).trans (coreProfile_le ha hr.1 t)
  · refine ⟨-(t * (∑' j, σ j) * kernelHeight), ?_⟩
    rintro _ ⟨r, _, rfl⟩
    dsimp [physicalProfile]
    have := attraction_le ht hσ hR hs r
    linarith [coreProfile_nonneg t r]

theorem physicalProfile_tendsto_zero {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Tendsto (physicalProfile t σ R) (𝓝[>] (0 : ℝ)) atTop := by
  let C := t * (∑' j, σ j) * kernelHeight
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg ht (tsum_nonneg hσ)) kernelHeight_pos.le
  apply tendsto_atTop.2
  intro M
  let K := |M| + C + 2
  have hK : 1 < K := by dsimp [K]; linarith [abs_nonneg M]
  have he := Real.exp_pos (-t)
  have hε : 0 < Real.exp (-t) / K := div_pos he (by linarith)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with r hr hrε
  have hrp : 0 < r := hr
  have hεe : Real.exp (-t) / K < Real.exp (-t) := (div_lt_self he hK)
  have hrr : r < Real.exp (-t) := hrε.trans hεe
  have hinv : K < Real.exp (-t) / r := (lt_div_iff₀ hrp).mpr
    (by have hh := (lt_div_iff₀ (show 0 < K by linarith)).mp hrε; nlinarith)
  have hp : Real.exp (-t) / r ≤ (Real.exp (-t) / r) ^ 12 :=
    le_self_pow₀ (by linarith) (by norm_num)
  rw [physicalProfile, coreProfile, ite_eq_left hrr]
  have hbound := attraction_le ht hσ hR hs r
  dsimp [C, K] at *
  nlinarith [sq_nonneg t, le_abs_self M]

theorem scaledKernelProfile_eq_height {R r : ℝ} (hR : 0 < R) (hr : r ≤ R / 2) :
    scaledKernelProfile R r = R⁻¹ ^ 3 * kernelHeight := by
  have hh : 1 ≤ 2 - 2 * (r / R) := by
    have hh : r / R ≤ (1 / 2 : ℝ) := (div_le_iff₀ hR).mpr (by linarith)
    linarith
  simp only [scaledKernelProfile, kernelProfile, Real.smoothTransition.one_of_one_le hh,
    kernelHeight]

theorem physicalProfile_negative_annulus {t : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ)
    (hσ0 : 0 < σ 0) (hR0 : 4 ≤ R 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ r ∈ Icc (1 : ℝ) 2, physicalProfile t σ R r ≤ -a := by
  refine ⟨t * σ 0 * (R 0)⁻¹ ^ 3 * kernelHeight, ?_, ?_⟩
  · exact mul_pos (mul_pos (mul_pos (by linarith) hσ0)
      (pow_pos (inv_pos.mpr (by linarith)) _)) kernelHeight_pos
  intro r hr
  obtain ⟨hr1, hr2⟩ := hr
  rw [physicalProfile, coreProfile_eq_zero ht hr1, zero_sub]
  apply neg_le_neg
  have hterm := (summable_attraction_terms hσ hR hs r).le_tsum 0
    (fun j _ => mul_nonneg (hσ j)
      (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))
  rw [scaledKernelProfile_eq_height (by linarith : 0 < R 0) (by linarith : r ≤ R 0 / 2)] at hterm
  have hh := mul_le_mul_of_nonneg_left hterm (by linarith : 0 ≤ t)
  simpa only [attraction, mul_assoc] using hh

theorem integrable_weighted_physicalProfile {t : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    IntegrableOn (fun r : ℝ => r ^ 2 * |physicalProfile t σ R r|) (Ioi (1 : ℝ)) := by
  apply ((integrable_weighted_attraction t hσ hR hs).mono_set
    (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [physicalProfile, coreProfile_eq_zero ht (le_of_lt hr), zero_sub, abs_neg,
    abs_of_nonneg (attraction_nonneg (by linarith) hσ hR r)]

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ShellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

open scoped InnerProductSpace

theorem affineIndependent_of_sq_dist_close {E : Type u_1} {ι : Type u_2}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (v : ι → E) {a ε : ℝ} (hε : 0 ≤ ε)
    (hgap : ε * Fintype.card ι < a)
    (hdist : ∀ i j, i ≠ j → |‖v i - v j‖ ^ 2 - a| ≤ ε) :
    AffineIndependent ℝ v := by
  classical
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv
  rw [Finset.univ.weightedVSub_eq_linear_combination hw] at hv
  have hid := inner_sum_smul_sum_smul_of_sum_eq_zero v hw v hw
  rw [hv, inner_zero_left] at hid
  have hzero : (∑ i, ∑ j, w i * w j * ‖v i - v j‖ ^ 2) = 0 := by
    simp only [← sq] at hid
    linarith
  have hpair (i j : ι) :
      w i * w j * ‖v i - v j‖ ^ 2 ≤
        a * w i * w j - (if i = j then a * w i ^ 2 else 0) +
          ε / 2 * (w i ^ 2 + w j ^ 2) := by
    by_cases hij : i = j
    · subst j
      simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, ↓reduceIte]
      nlinarith [mul_nonneg hε (sq_nonneg (w i))]
    · rw [ite_eq_right hij]
      have habs : w i * w j * (‖v i - v j‖ ^ 2 - a) ≤ |w i * w j| * ε := by
        calc
          _ ≤ |w i * w j * (‖v i - v j‖ ^ 2 - a)| := le_abs_self _
          _ = |w i * w j| * |‖v i - v j‖ ^ 2 - a| := abs_mul _ _
          _ ≤ |w i * w j| * ε := mul_le_mul_of_nonneg_left (hdist i j hij) (abs_nonneg _)
      have htwo : 2 * |w i * w j| ≤ w i ^ 2 + w j ^ 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|w i| - |w j|), sq_abs (w i), sq_abs (w j)]
      have := mul_le_mul_of_nonneg_left htwo hε
      nlinarith
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpair i j))
  have hdiag : (∑ i, ∑ j, if i = j then a * w i ^ 2 else 0) = a * ∑ i, w i ^ 2 := by
    simp [← Finset.mul_sum]
  have hmain : (∑ i, ∑ j, a * w i * w j) = 0 := by
    simp only [← Finset.mul_sum, hw, mul_zero, Finset.sum_const_zero]
  have herror : (∑ i, ∑ j, ε / 2 * (w i ^ 2 + w j ^ 2)) =
      ε * (Fintype.card ι : ℝ) * ∑ i, w i ^ 2 := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.card_univ]
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at htotal
  rw [hzero, hmain, hdiag, herror] at htotal
  have hsnonneg : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs0 : (∑ i, w i ^ 2) = 0 := by nlinarith
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
    sq_nonneg (w j))).mp hs0 i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi

theorem no_five_in_shell (v : Fin 5 → EuclideanSpace ℝ (Fin 3)) {r : ℝ}
    (hr : 0 < r)
    (hlow : ∀ i j, i ≠ j → r ≤ ‖v i - v j‖)
    (hupp : ∀ i j, i ≠ j → ‖v i - v j‖ ≤ (1 + shellDelta) * r) : False := by
  have hai : AffineIndependent ℝ v := by
    apply affineIndependent_of_sq_dist_close v
      (a := r ^ 2) (ε := (2 * shellDelta + shellDelta ^ 2) * r ^ 2)
    · dsimp [shellDelta]
      positivity
    · simp only [Fintype.card_fin]
      dsimp [shellDelta]
      nlinarith [sq_pos_of_pos hr]
    · intro i j hij
      have hlo := hlow i j hij
      have hup := hupp i j hij
      rw [abs_le]
      constructor
      · have hnorm := norm_nonneg (v i - v j)
        have hsq := sq_le_sq₀ hr.le hnorm |>.mpr hlo
        dsimp [shellDelta]
        nlinarith [sq_nonneg r]
      · have hnorm := norm_nonneg (v i - v j)
        have hsq := sq_le_sq₀ hnorm (by dsimp [shellDelta]; positivity) |>.mpr hup
        dsimp [shellDelta] at hsq ⊢
        nlinarith
  have hdim := hai.card_le_finrank_succ
  have hle := Submodule.finrank_le (vectorSpan ℝ (range v))
  have hthree : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hthree] at hle
  simp only [Fintype.card_fin] at hdim
  omega

theorem shellGraph_cliqueFree {ι : Type u_1} (v : ι → EuclideanSpace ℝ (Fin 3))
    {r : ℝ} (hr : 0 < r) : (shellGraph v r).CliqueFree 5 := by
  classical
  intro s hs
  let e : ↥s ≃ Fin 5 := Finset.equivFinOfCardEq hs.card_eq
  let q : Fin 5 → EuclideanSpace ℝ (Fin 3) := fun i => v (e.symm i)
  apply no_five_in_shell q hr
  · intro i j hij
    have hne : (e.symm i : ι) ≠ e.symm j := by
      intro he
      apply hij
      exact e.symm.injective (Subtype.ext he)
    exact (hs.isClique (e.symm i).property (e.symm j).property hne).2.1
  · intro i j hij
    have hne : (e.symm i : ι) ≠ e.symm j := by
      intro he
      apply hij
      exact e.symm.injective (Subtype.ext he)
    exact (hs.isClique (e.symm i).property (e.symm j).property hne).2.2

theorem shellGraph_edge_bound {ι : Type u_1} [Fintype ι]
    (v : ι → EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 < r) :
    letI := Classical.decRel (shellGraph v r).Adj
    8 * (shellGraph v r).edgeFinset.card ≤ 3 * (Fintype.card ι) ^ 2 := by
  classical
  have h := (shellGraph_cliqueFree v hr).card_edgeFinset_le (r := 4)
  simp only at h
  have hm : Fintype.card ι % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hle : (Fintype.card ι % 4) ^ 2 ≤ Fintype.card ι ^ 2 :=
    Nat.pow_le_pow_left (Nat.mod_le _ _) 2
  generalize Fintype.card ι % 4 = m at h hm hle
  generalize Fintype.card ι ^ 2 = N at h hle ⊢
  generalize (shellGraph v r).edgeFinset.card = E at h ⊢
  interval_cases m <;> simp at h hle ⊢ <;> omega

theorem coreProfile_ge_of_not_shell (t r : ℝ) (hr : r < 1)
    (hnot : ¬ (Real.exp (-t) ≤ r ∧ r ≤ (1 + shellDelta) * Real.exp (-t))) :
    t ^ 2 ≤ coreProfile t r := by
  unfold coreProfile
  split_ifs with hlow hhigh
  · have hp : 0 ≤ (Real.exp (-t) / r) ^ 12 := by positivity
    linarith
  · exact False.elim (hnot ⟨le_of_not_gt hlow, hhigh⟩)
  · rfl

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem two_mul_pairSum {ι : Type u_1} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hsym : ∀ i j, f i j = f j i) :
    2 * pairSum f = ∑ i, ∑ j, if i = j then 0 else f i j := by
  classical
  have hsplit (i j : ι) : (if i = j then 0 else f i j) =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le, hsym i j]
  simp_rw [hsplit]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : ι => if j < i then f j i else 0)]
  simp only [pairSum, Finset.sum_filter]
  ring

theorem sum_adjacency_indicator {ι : Type u_1} [Fintype ι] (G : SimpleGraph ι) :
    letI := Classical.decRel G.Adj
    (∑ i, ∑ j, if G.Adj i j then (1 : ℝ) else 0) = 2 * (G.edgeFinset.card : ℝ) := by
  classical
  have h := congrArg (fun n : ℕ => (n : ℝ)) G.two_mul_card_edgeFinset
  rw [Finset.card_filter] at h
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_ite] at h
  rw [Fintype.sum_prod_type] at h
  simpa only [Nat.cast_one, Nat.cast_zero] using h.symm

theorem core_one_cell_bound {ι : Type u_1} [Fintype ι] [LinearOrder ι]
    (v : ι → EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    (hdiam : ∀ i j, ‖v i - v j‖ < 1) :
    t ^ 2 / 8 * (Fintype.card ι : ℝ) ^ 2 - t ^ 2 / 2 * Fintype.card ι ≤
      pairSum (fun i j => coreProfile t ‖v i - v j‖) := by
  classical
  let G := shellGraph v (Real.exp (-t))
  have hpoint (i j : ι) :
      t ^ 2 * (1 - (if G.Adj i j then 1 else 0) - (if i = j then 1 else 0)) ≤
        if i = j then 0 else coreProfile t ‖v i - v j‖ := by
    by_cases hij : i = j
    · subst j
      simp
    · simp only [ite_eq_right hij, sub_zero]
      by_cases hadj : G.Adj i j
      · simp only [ite_eq_left hadj, sub_self, mul_zero]
        exact coreProfile_nonneg _ _
      · simp only [ite_eq_right hadj, sub_zero, mul_one]
        apply coreProfile_ge_of_not_shell _ _ (hdiam i j)
        intro hshell
        exact hadj ⟨hij, hshell⟩
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpoint i j))
  have horient := two_mul_pairSum (fun i j => coreProfile t ‖v i - v j‖)
    (fun i j => by rw [norm_sub_rev])
  have hadj := sum_adjacency_indicator G
  have hdiag : (∑ i : ι, ∑ j : ι, if i = j then (1 : ℝ) else 0) = Fintype.card ι := by simp
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib] at htotal
  rw [hadj, hdiag, ← horient] at htotal
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htotal
  have hedge := shellGraph_edge_bound v (Real.exp_pos (-t))
  have hedger : 8 * (G.edgeFinset.card : ℝ) ≤ 3 * (Fintype.card ι : ℝ) ^ 2 := by exact_mod_cast hedge
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hedger)]

theorem row_sum_quadratic_bound {ι : Type u_1} [Fintype ι]
    (J : ι → ι → ℝ) (n : ι → ℝ) (M : ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    ∑ i, ∑ j, J i j * n i * n j ≤ M * ∑ i, n i ^ 2 := by
  have hYoung (i j : ι) : 2 * (J i j * n i * n j) ≤
      J i j * n i ^ 2 + J i j * n j ^ 2 := by
    nlinarith [mul_nonneg (hJ i j) (sq_nonneg (n i - n j))]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hYoung i j))
  simp_rw [Finset.sum_add_distrib] at hs
  simp only [← Finset.mul_sum] at hs
  have hswap : (∑ i, ∑ j, J i j * n j ^ 2) = ∑ i, ∑ j, J i j * n i ^ 2 := by
    rw [Finset.sum_comm]
    congr 1
    funext i
    congr 1
    funext j
    rw [hsym j i]
  rw [hswap] at hs
  have hr : (∑ i, ∑ j, J i j * n i ^ 2) ≤ M * ∑ i, n i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  linarith

theorem superstable_algebra {ι : Type u_1} [Fintype ι]
    (J : ι → ι → ℝ) (n : ι → ℝ) (M t N Ucore Uattr : ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hsym : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M)
    (hcore : t ^ 2 / 8 * (∑ i, n i ^ 2) - t ^ 2 / 2 * N ≤ Ucore)
    (hattr : Uattr ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, J i j * n i * n j) :
    (t ^ 2 / 8 - M / 2) * (∑ i, n i ^ 2) - t ^ 2 / 2 * N ≤ Ucore - Uattr := by
  have hq := row_sum_quadratic_bound J n M hJ hsym hrow
  nlinarith

theorem sum_subtype_le_of_nonneg {ι : Type u_1} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i : {i // p i}, f i ≤ ∑ i, f i := by
  have h := Fintype.sum_subtype_add_sum_subtype p f
  have hp : 0 ≤ ∑ i : {i // ¬ p i}, f i := Finset.sum_nonneg (fun i _ => hf i)
  linarith

theorem core_partition_bound {ι : Type u_1} {κ : Type u_2} [Fintype ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] (c : ι → κ) (v : ι → EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    (hdiam : ∀ i j, c i = c j → ‖v i - v j‖ < 1) :
    t ^ 2 / 8 * (∑ k, (Fintype.card {i // c i = k} : ℝ) ^ 2) -
      t ^ 2 / 2 * Fintype.card ι ≤ pairSum (fun i j => coreProfile t ‖v i - v j‖) := by
  classical
  let f (i j : ι) : ℝ := if i = j then 0 else coreProfile t ‖v i - v j‖
  have hf (i j : ι) : 0 ≤ f i j := by
    dsimp [f]
    split_ifs
    · rfl
    · exact coreProfile_nonneg _ _
  let U (k : κ) : ℝ := pairSum (fun i j : {i // c i = k} => coreProfile t ‖v i - v j‖)
  have htwocell (k : κ) : 2 * U k = ∑ i : {i // c i = k}, ∑ j : {j // c j = k}, f i j := by
    dsimp [U]
    rw [two_mul_pairSum _ (fun i j => by rw [norm_sub_rev])]
    simp only [f, Subtype.ext_iff]
  have htwototal : 2 * pairSum (fun i j => coreProfile t ‖v i - v j‖) = ∑ i, ∑ j, f i j :=
    two_mul_pairSum _ (fun i j => by rw [norm_sub_rev])
  have hu : 2 * (∑ k, U k) ≤ 2 * pairSum (fun i j => coreProfile t ‖v i - v j‖) := by
    rw [Finset.mul_sum, htwototal]
    simp_rw [htwocell]
    calc
      _ ≤ ∑ k : κ, ∑ i : {i // c i = k}, ∑ j : ι, f i j := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro i _
        exact sum_subtype_le_of_nonneg (fun j => c j = k) (f i) (hf i)
      _ = _ := Fintype.sum_fiberwise c (fun i => ∑ j, f i j)
  have hs (k : κ) : t ^ 2 / 8 * (Fintype.card {i // c i = k} : ℝ) ^ 2 -
      t ^ 2 / 2 * Fintype.card {i // c i = k} ≤ U k := by
    apply core_one_cell_bound
    intro i j
    exact hdiam i j (i.property.trans j.property.symm)
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset κ)) => hs k)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hcard : (∑ k, (Fintype.card {i // c i = k} : ℝ)) = Fintype.card ι := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      Fintype.sum_fiberwise c (fun _ => (1 : ℝ))
  rw [hcard] at hsum
  linarith

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LatticeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem dist_lt_one_of_cellIndex_eq {x y : EuclideanSpace ℝ (Fin 3)}
    (h : cellIndex x = cellIndex y) : ‖x - y‖ < 1 := by
  have hcoord (k : Fin 3) : |x k - y k| < (1 / 4 : ℝ) := by
    have heq : ⌊4 * x k⌋ = ⌊4 * y k⌋ := congrFun h k
    have hxlo := Int.floor_le (4 * x k)
    have hxhi := Int.lt_floor_add_one (4 * x k)
    have hylo := Int.floor_le (4 * y k)
    have hyhi := Int.lt_floor_add_one (4 * y k)
    rw [heq] at hxlo hxhi
    rw [abs_lt]
    constructor <;> linarith
  have hsq (k : Fin 3) : (x k - y k) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    have hc := (hcoord k).le
    have := sq_le_sq₀ (abs_nonneg (x k - y k)) (by norm_num : (0 : ℝ) ≤ 1 / 4) |>.mpr hc
    simpa only [sq_abs] using this
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hsq k)
  have hnorm : ‖x - y‖ ^ 2 ≤ 3 * (1 / 4 : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [PiLp.sub_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat] using hsum
  nlinarith [norm_nonneg (x-y)]

theorem mem_nearCells_iff {R : ℝ} {i j : Lattice} :
    j ∈ nearCells R i ↔ ∀ k, |j k - i k| ≤ cellRadius R := by
  simp only [nearCells, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  refine forall_congr' (fun k => ?_)
  omega

theorem nearCells_symm {R : ℝ} {i j : Lattice} :
    j ∈ nearCells R i ↔ i ∈ nearCells R j := by
  simp only [mem_nearCells_iff, abs_sub_comm]

theorem cellRadius_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ cellRadius R :=
  Int.ceil_nonneg (by linarith)

theorem cellRadius_le {R : ℝ} (hR : 1 ≤ R) : (cellRadius R : ℝ) ≤ 6 * R := by
  have h := Int.ceil_lt_add_one (4 * R + 1)
  dsimp [cellRadius]
  linarith

theorem card_nearCells {R : ℝ} (hR : 0 ≤ R) (i : Lattice) :
    ((nearCells R i).card : ℝ) = (2 * (cellRadius R : ℝ) + 1) ^ 3 := by
  have hn := cellRadius_nonneg hR
  have hc (k : Fin 3) : ((Finset.Icc (i k - cellRadius R) (i k + cellRadius R)).card : ℝ) =
      2 * (cellRadius R : ℝ) + 1 := by
    have h := Int.card_Icc_of_le (i k - cellRadius R) (i k + cellRadius R) (by omega)
    exact_mod_cast h.trans (by ring)
  rw [nearCells, Fintype.card_piFinset, Nat.cast_prod]
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_nearCells_le {R : ℝ} (hR : 1 ≤ R) (i : Lattice) :
    ((nearCells R i).card : ℝ) ≤ 2197 * R ^ 3 := by
  rw [card_nearCells (by linarith)]
  have hn := cellRadius_nonneg (show 0 ≤ R by linarith)
  have hn' : (0 : ℝ) ≤ cellRadius R := by exact_mod_cast hn
  have h : 2 * (cellRadius R : ℝ) + 1 ≤ 13 * R := by
    have := cellRadius_le hR
    linarith
  have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 2 * cellRadius R + 1) h 3
  nlinarith only [hp]

theorem cellIndex_mem_nearCells {x y : EuclideanSpace ℝ (Fin 3)} {R : ℝ}
    (hd : ‖x - y‖ ≤ R) : cellIndex y ∈ nearCells R (cellIndex x) := by
  rw [mem_nearCells_iff]
  intro k
  have hx1 := Int.floor_le (4 * x k)
  have hx2 := Int.lt_floor_add_one (4 * x k)
  have hy1 := Int.floor_le (4 * y k)
  have hy2 := Int.lt_floor_add_one (4 * y k)
  have hcoord : |x k - y k| ≤ R := by
    have h := PiLp.norm_apply_le (x - y) k
    have hc : |x k - y k| ≤ ‖x - y‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using h
    exact hc.trans hd
  have hceil : 4 * R + 1 ≤ (cellRadius R : ℝ) := Int.le_ceil _
  have habs : |((cellIndex y k : ℤ) : ℝ) - (cellIndex x k : ℝ)| ≤
      (cellRadius R : ℝ) := by
    dsimp [cellIndex]
    rw [abs_le] at hcoord ⊢
    constructor <;> linarith
  exact_mod_cast habs

theorem latticeEnvelope_nonneg {R : ℝ} (hR : 0 ≤ R) (i j : Lattice) :
    0 ≤ latticeEnvelope R i j := by
  unfold latticeEnvelope
  split_ifs <;> positivity

theorem latticeEnvelope_symm (R : ℝ) (i j : Lattice) :
    latticeEnvelope R i j = latticeEnvelope R j i := by
  simp only [latticeEnvelope, nearCells_symm (i := i) (j := j)]

theorem latticeEnvelope_le {R : ℝ} (hR : 0 ≤ R) (i j : Lattice) :
    latticeEnvelope R i j ≤ R⁻¹ ^ 3 := by
  unfold latticeEnvelope
  split_ifs
  · rfl
  · positivity

theorem sum_latticeEnvelope_le {κ : Type u_1} [Fintype κ] (f : κ → Lattice)
    (hf : Function.Injective f) {R : ℝ} (hR : 1 ≤ R) (i : Lattice) :
    ∑ j, latticeEnvelope R i (f j) ≤ 2197 := by
  classical
  let s := Finset.univ.filter (fun j : κ => f j ∈ nearCells R i)
  have hcard : s.card ≤ (nearCells R i).card :=
    Finset.card_le_card_of_injOn f (by
      intro j hj
      exact (Finset.mem_filter.mp hj).2) hf.injOn
  have hsum : (∑ j, latticeEnvelope R i (f j)) = (s.card : ℝ) * R⁻¹ ^ 3 := by
    simp only [latticeEnvelope, ← Finset.sum_filter, s, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  calc
    _ ≤ ((nearCells R i).card : ℝ) * R⁻¹ ^ 3 := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hcard) (by positivity)
    _ ≤ (2197 * R ^ 3) * R⁻¹ ^ 3 := mul_le_mul_of_nonneg_right
      (card_nearCells_le hR i) (by positivity)
    _ = 2197 := by field_simp

theorem kernel_le_latticeEnvelope (w : ℝ → ℝ) (H R : ℝ)
    (hheight : ∀ r, w r ≤ R⁻¹ ^ 3 * H) (hsupport : ∀ r, R < r → w r = 0)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    w ‖x - y‖ ≤ H * latticeEnvelope R (cellIndex x) (cellIndex y) := by
  by_cases h : cellIndex y ∈ nearCells R (cellIndex x)
  · simpa only [latticeEnvelope, ite_eq_left h, mul_comm H] using hheight ‖x - y‖
  · have hd : R < ‖x - y‖ := lt_of_not_ge (fun hle => h (cellIndex_mem_nearCells hle))
    rw [hsupport _ hd, latticeEnvelope, ite_eq_right h, mul_zero]

theorem summable_mixedEnvelope_terms {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (i j : Lattice) :
    Summable (fun n => σ n * latticeEnvelope (R n) i j) := by
  apply hs.of_norm_bounded
  intro n
  have hRp : 0 ≤ R n := le_trans zero_le_one (hR n)
  rw [Real.norm_of_nonneg (mul_nonneg (hσ n) (latticeEnvelope_nonneg hRp i j))]
  have he : latticeEnvelope (R n) i j ≤ 1 :=
    (latticeEnvelope_le hRp i j).trans
      (pow_le_one₀ (inv_nonneg.mpr hRp) (inv_le_one_of_one_le₀ (hR n)))
  simpa using mul_le_mul_of_nonneg_left he (hσ n)

theorem mixedEnvelope_nonneg {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 0 ≤ R n) (i j : Lattice) :
    0 ≤ mixedEnvelope σ R i j :=
  tsum_nonneg (fun n => mul_nonneg (hσ n) (latticeEnvelope_nonneg (hR n) i j))

theorem mixedEnvelope_symm (σ R : ℕ → ℝ) (i j : Lattice) :
    mixedEnvelope σ R i j = mixedEnvelope σ R j i := by
  unfold mixedEnvelope
  congr 1
  funext n
  rw [latticeEnvelope_symm]

theorem sum_mixedEnvelope_le {κ : Type u_1} [Fintype κ] (f : κ → Lattice)
    (hf : Function.Injective f) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (i : Lattice) :
    ∑ j, mixedEnvelope σ R i (f j) ≤ 2197 * ∑' n, σ n := by
  have hsum : Summable (fun n => ∑ j, σ n * latticeEnvelope (R n) i (f j)) := by
    apply Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hσ n) (latticeEnvelope_nonneg (le_trans zero_le_one (hR n)) i (f j)))) _
      (hs.mul_left 2197)
    intro n
    rw [← Finset.mul_sum]
    have hh := mul_le_mul_of_nonneg_left (sum_latticeEnvelope_le f hf (hR n) i) (hσ n)
    nlinarith only [hh]
  unfold mixedEnvelope
  rw [← Summable.tsum_finsetSum (fun j _ => summable_mixedEnvelope_terms hσ hR hs i (f j)),
    ← hs.tsum_mul_left]
  apply hsum.tsum_le_tsum _ (hs.mul_left 2197)
  intro n
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (sum_latticeEnvelope_le f hf (hR n) i) (hσ n)
  nlinarith only [hh]

theorem attraction_le_mixedEnvelope {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (x y : Space) :
    attraction t σ R ‖x - y‖ ≤
      (t * kernelHeight) * mixedEnvelope σ R (cellIndex x) (cellIndex y) := by
  unfold attraction mixedEnvelope
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ ht
  rw [← tsum_mul_left]
  apply (summable_attraction_terms hσ hR hs _).tsum_le_tsum _
    ((summable_mixedEnvelope_terms hσ hR hs _ _).mul_left kernelHeight)
  intro n
  have hh := kernel_le_latticeEnvelope (scaledKernelProfile (R n)) kernelHeight (R n)
    (fun r => by simpa only [kernelHeight, div_eq_mul_inv, one_mul] using
      scaledKernelProfile_le (lt_of_lt_of_le zero_lt_one (hR n)) r)
    (fun r hr => scaledKernelProfile_zero (lt_of_lt_of_le zero_lt_one (hR n)) hr.le) x y
  have hh' := mul_le_mul_of_nonneg_left hh (hσ n)
  nlinarith only [hh']

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Stability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem sum_comp_eq_sum_fibres {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (c : ι → κ) (f : κ → ℝ) :
    (∑ i, f (c i)) = ∑ k, (Fintype.card {i // c i = k} : ℝ) * f k := by
  symm
  calc
    _ = ∑ k, ∑ _i : {i // c i = k}, f k := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ k, ∑ i : {i // c i = k}, f (c i) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [i.property]
    _ = _ := Fintype.sum_fiberwise c (fun i => f (c i))

theorem pairSum_le_cell_quadratic {ι : Type u_1} {κ : Type u_2} [Fintype ι] [LinearOrder ι]
    [Fintype κ] [DecidableEq κ] (c : ι → κ) (J : κ → κ → ℝ) (F : ι → ι → ℝ)
    (hJ : ∀ k l, 0 ≤ J k l) (hsym : ∀ i j, F i j = F j i)
    (hF : ∀ i j, F i j ≤ J (c i) (c j)) :
    pairSum F ≤ (1 / 2 : ℝ) * ∑ k, ∑ l,
      J k l * (Fintype.card {i // c i = k} : ℝ) * (Fintype.card {i // c i = l} : ℝ) := by
  classical
  have hh (i j : ι) : (if i = j then 0 else F i j) ≤ J (c i) (c j) := by
    split_ifs
    · exact hJ _ _
    · exact hF _ _
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hh i j))
  rw [← two_mul_pairSum F hsym] at hs
  have hsum : (∑ i, ∑ j, J (c i) (c j)) = ∑ k, ∑ l,
      J k l * (Fintype.card {i // c i = k} : ℝ) * (Fintype.card {i // c i = l} : ℝ) := by
    calc
      _ = ∑ i, ∑ l, (Fintype.card {j // c j = l} : ℝ) * J (c i) l := by
        apply Finset.sum_congr rfl
        intro i _
        exact sum_comp_eq_sum_fibres c (fun l => J (c i) l)
      _ = ∑ k, (Fintype.card {i // c i = k} : ℝ) *
          (∑ l, (Fintype.card {j // c j = l} : ℝ) * J k l) :=
        sum_comp_eq_sum_fibres c (fun k => ∑ l, (Fintype.card {j // c j = l} : ℝ) * J k l)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  rw [hsum] at hs
  linarith

theorem physicalProfile_pairSum_lower {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    {ι : Type u_1} [Fintype ι] [LinearOrder ι] (x : ι → Space) :
    -(t ^ 2 / 2) * Fintype.card ι ≤ pairSum (fun i j => physicalProfile t σ R ‖x i - x j‖) := by
  classical
  let s := Finset.univ.image (fun i : ι => cellIndex (x i))
  let c (i : ι) : s := ⟨cellIndex (x i), Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let J (k l : s) := (t * kernelHeight) * mixedEnvelope σ R k l
  let M := 2197 * t * kernelHeight * (∑' n, σ n)
  have hJ (k l : s) : 0 ≤ J k l := mul_nonneg (mul_nonneg ht kernelHeight_pos.le)
    (mixedEnvelope_nonneg hσ (fun n => le_trans zero_le_one (hR n)) k l)
  have hJsym (k l : s) : J k l = J l k := by simp only [J, mixedEnvelope_symm]
  have hrow (k : s) : ∑ l, J k l ≤ M := by
    have hh := mul_le_mul_of_nonneg_left
      (sum_mixedEnvelope_le (fun l : s => (l : Lattice)) Subtype.val_injective hσ hR hs k)
      (mul_nonneg ht kernelHeight_pos.le)
    simpa only [J, M, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hh
  have hcore := core_partition_bound c x t (fun i j hij =>
    dist_lt_one_of_cellIndex_eq (congrArg Subtype.val hij))
  have hattr := pairSum_le_cell_quadratic c J (fun i j => attraction t σ R ‖x i - x j‖)
    hJ (fun i j => by rw [norm_sub_rev]) (fun i j => attraction_le_mixedEnvelope ht hσ hR hs _ _)
  have hb := superstable_algebra J (fun k : s => (Fintype.card {i // c i = k} : ℝ)) M t
    (Fintype.card ι) _ _ hJ hJsym hrow hcore hattr
  have hn : 0 ≤ ∑ k : s, (Fintype.card {i // c i = k} : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm : 0 ≤ t ^ 2 / 8 - M / 2 := sub_nonneg.mpr hsmall
  have hp := mul_nonneg hm hn
  have heq : pairSum (fun i j => physicalProfile t σ R ‖x i - x j‖) =
      pairSum (fun i j => coreProfile t ‖x i - x j‖) -
      pairSum (fun i j => attraction t σ R ‖x i - x j‖) := by
    simp only [pairSum, physicalProfile, Finset.sum_sub_distrib]
  rw [heq]
  linarith

theorem ereal_coe_sum {ι : Type u_1} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simpa only [Finset.sum_insert hi, EReal.coe_add] using congrArg (fun z => (f i : EReal) + z) ih

theorem coe_pairSum_le_energy (φ : ℝ → ℝ) {N : ℕ} (x : Fin N → Space) :
    ((pairSum (fun i j => φ ‖x i - x j‖) : ℝ) : EReal) ≤ energy φ x := by
  classical
  simp only [pairSum, energy, ereal_coe_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  unfold radialPotential
  split_ifs
  · exact le_top
  · rfl

theorem physicalProfile_stable {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    (N : ℕ) (x : Fin N → Space) :
    ((-(t ^ 2 / 2) * (N : ℝ) : ℝ) : EReal) ≤ energy (physicalProfile t σ R) x := by
  apply le_trans _ (coe_pairSum_le_energy _ x)
  apply EReal.coe_le_coe_iff.mpr
  simpa only [Fintype.card_fin] using physicalProfile_pairSum_lower ht hσ hR hs hsmall x

theorem admissible_physicalProfile {t : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    (hσ0 : 0 < σ 0) (hR0 : 4 ≤ R 0) : Admissible (physicalProfile t σ R) := by
  refine ⟨measurable_radialPotential (measurable_physicalProfile t hσ hR hs), ?_,
    physicalProfile_tendsto_zero (by linarith) hσ hR hs, ?_, ?_, ?_⟩
  · intro a b ha _
    exact physicalProfile_locally_bounded (by linarith) hσ hR hs ha
  · obtain ⟨a, ha, hneg⟩ := physicalProfile_negative_annulus ht hσ hR hs hσ0 hR0
    exact ⟨1, 2, a, by norm_num, by norm_num, ha, hneg⟩
  · exact ⟨1, by norm_num, integrable_weighted_physicalProfile ht hσ hR hs⟩
  · exact ⟨t ^ 2 / 2, physicalProfile_stable (by linarith) hσ hR hs hsmall⟩

theorem physicalProfile_superstable {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {ι : Type u_1} {κ : Type u_2} [Fintype ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]
    (x : ι → Space) (c : ι → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i, cellIndex (x i) = e (c i)) :
    (t ^ 2 / 8 - 2197 * t * kernelHeight * (∑' n, σ n) / 2) *
      (∑ k, (Fintype.card {i // c i = k} : ℝ) ^ 2) -
      t ^ 2 / 2 * Fintype.card ι ≤
      pairSum (fun i j => physicalProfile t σ R ‖x i - x j‖) := by
  classical
  let J (k l : κ) := (t * kernelHeight) * mixedEnvelope σ R (e k) (e l)
  let M := 2197 * t * kernelHeight * (∑' n, σ n)
  have hJ (k l : κ) : 0 ≤ J k l := mul_nonneg (mul_nonneg ht kernelHeight_pos.le)
    (mixedEnvelope_nonneg hσ (fun n => le_trans zero_le_one (hR n)) (e k) (e l))
  have hJsym (k l : κ) : J k l = J l k := by simp only [J, mixedEnvelope_symm]
  have hrow (k : κ) : ∑ l, J k l ≤ M := by
    have hh := mul_le_mul_of_nonneg_left (sum_mixedEnvelope_le e he hσ hR hs (e k))
      (mul_nonneg ht kernelHeight_pos.le)
    simpa only [J, M, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hh
  have hcore := core_partition_bound c x t (fun i j hij =>
    dist_lt_one_of_cellIndex_eq ((hc i).trans ((congrArg e hij).trans (hc j).symm)))
  have hattr := pairSum_le_cell_quadratic c J (fun i j => attraction t σ R ‖x i - x j‖)
    hJ (fun i j => by rw [norm_sub_rev]) (fun i j => by
      have hh := attraction_le_mixedEnvelope ht hσ hR hs (x i) (x j)
      simpa only [hc, J] using hh)
  have hb := superstable_algebra J (fun k : κ => (Fintype.card {i // c i = k} : ℝ)) M t
    (Fintype.card ι) _ _ hJ hJsym hrow hcore hattr
  simpa only [pairSum, physicalProfile, Finset.sum_sub_distrib] using hb

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CubeCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff
open scoped InnerProductSpace

theorem cellIndex_mem_cubeCells {L : ℝ} {x : Space} (hx : x ∈ cube L) :
    cellIndex x ∈ cubeCells L := by
  classical
  simp only [cubeCells, Fintype.mem_piFinset, Finset.mem_Icc, cellIndex]
  intro k
  constructor
  · apply Int.floor_mono
    have h := (hx k).1
    linarith
  · apply Int.floor_mono
    have h := (hx k).2
    linarith

theorem card_cubeCells_le {L : ℝ} (hL : 0 ≤ L) :
    ((cubeCells L).card : ℝ) ≤ (4 * L + 2) ^ 3 := by
  classical
  let m := (Finset.Icc ⌊-2 * L⌋ ⌊2 * L⌋).card
  have horder : ⌊-2 * L⌋ ≤ ⌊2 * L⌋ + 1 := by
    have hh := Int.floor_mono (show -2 * L ≤ 2 * L by linarith)
    omega
  have hcInt := Int.card_Icc_of_le ⌊-2 * L⌋ ⌊2 * L⌋ horder
  have hcReal : (m : ℝ) = (⌊2 * L⌋ : ℝ) + 1 - (⌊-2 * L⌋ : ℝ) := by
    dsimp only [m]
    exact_mod_cast hcInt
  have hm : (m : ℝ) ≤ 4 * L + 2 := by
    rw [hcReal]
    have hu := Int.floor_le (2 * L)
    have hl := Int.lt_floor_add_one (-2 * L)
    linarith
  have hc : ((cubeCells L).card : ℝ) = (m : ℝ) ^ 3 := by
    simp [cubeCells, Fintype.card_piFinset, m]
  rw [hc]
  exact pow_le_pow_left₀ (Nat.cast_nonneg m) hm 3

theorem physicalProfile_energy_coercive {t L : ℝ} (ht : 0 ≤ t) (hL : 0 ≤ L)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197 * t * kernelHeight * (∑' n, σ n) / 2 ≤ t ^ 2 / 8)
    (N : ℕ) (x : Fin N → Space) (hx : ∀ i, x i ∈ cube L) :
    (((t ^ 2 / 8 - 2197 * t * kernelHeight * (∑' n, σ n) / 2) *
      ((N : ℝ) ^ 2 / (4 * L + 2) ^ 3) - t ^ 2 / 2 * N : ℝ) : EReal) ≤
      energy (physicalProfile t σ R) x := by
  classical
  let κ := (cubeCells L : Type)
  let c (i : Fin N) : κ := ⟨cellIndex (x i), cellIndex_mem_cubeCells (hx i)⟩
  let n (k : κ) : ℝ := Fintype.card {i // c i = k}
  have hsN : (∑ k : κ, n k) = N := by
    have hh := sum_comp_eq_sum_fibres c (fun _ => (1 : ℝ))
    simpa only [n, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] using hh.symm
  have hquad : (N : ℝ) ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ k, n k ^ 2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset κ) (fun _ => (1 : ℝ)) n
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, hsN] using hh
  have hquad' : (N : ℝ) ^ 2 ≤ (4 * L + 2) ^ 3 * ∑ k, n k ^ 2 := by
    apply hquad.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    simpa only [κ, Fintype.card_coe] using card_cubeCells_le hL
  have hden : 0 < (4 * L + 2) ^ 3 := by positivity
  have hquot : (N : ℝ) ^ 2 / (4 * L + 2) ^ 3 ≤ ∑ k, n k ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm] using hquad'
  have hsuper := physicalProfile_superstable ht hσ hR hs x c
    (fun k : κ => (k : Lattice)) Subtype.val_injective (fun _ => rfl)
  have he := coe_pairSum_le_energy (physicalProfile t σ R) x
  apply le_trans _ he
  apply EReal.coe_le_coe_iff.mpr
  have hm := mul_le_mul_of_nonneg_left hquot (sub_nonneg.mpr hsmall)
  simp only [Fintype.card_fin] at hsuper
  exact (sub_le_sub_right hm _).trans hsuper

end

end ContinuumTemperature

end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CanonicalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

theorem ereal_sum_ne_bot {α : Type u_1} (s : Finset α) (f : α → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) : ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, EReal.add_ne_bot_iff]
    exact ⟨hf i (Finset.mem_insert_self i s), ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))⟩

theorem measurable_energy {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    (N : ℕ) : Measurable (fun x : Fin N → Space => energy φ x) := by
  classical
  unfold energy
  fun_prop

theorem measurable_boltzmann {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    (β : ℝ) (N : ℕ) : Measurable (fun x : Fin N → Space => boltzmann φ β x) := by
  have hE := measurable_energy hφ N
  exact Measurable.ite (hE (measurableSet_singleton ⊤)) measurable_const
    ((measurable_const.mul hE.ereal_toReal).exp)

theorem boltzmann_nonneg (φ : ℝ → ℝ) (β : ℝ) {N : ℕ} (x : Fin N → Space) :
    0 ≤ boltzmann φ β x := by
  unfold boltzmann
  split_ifs
  · rfl
  · exact (Real.exp_pos _).le

theorem boltzmann_le_of_stable {φ : ℝ → ℝ} {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {N : ℕ} (x : Fin N → Space) :
    boltzmann φ β x ≤ Real.exp (β * B * N) := by
  unfold boltzmann
  split_ifs with htop
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    have he := EReal.toReal_le_toReal (hstable N x) (EReal.coe_ne_bot _) htop
    simp only [EReal.toReal_coe] at he
    nlinarith [mul_le_mul_of_nonneg_left he hβ]

theorem isCompact_cube (L : ℝ) : IsCompact (cube L) := by
  have h := isCompact_pi_infinite (fun _ : Fin 3 => isCompact_Icc (a := -L / 2) (b := L / 2))
  exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isCompact_preimage.mpr h

theorem measurableSet_cube (L : ℝ) : MeasurableSet (cube L) :=
  (isCompact_cube L).measurableSet

theorem isCompact_configurations (L : ℝ) (N : ℕ) :
    IsCompact {x : Fin N → Space | ∀ i, x i ∈ cube L} :=
  isCompact_pi_infinite (fun _ => isCompact_cube L)

theorem integrableOn_boltzmann {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (L : ℝ) (N : ℕ) :
    IntegrableOn (fun x : Fin N → Space => boltzmann φ β x)
      {x : Fin N → Space | ∀ i, x i ∈ cube L} := by
  have hK := isCompact_configurations L N
  have : IsFiniteMeasure (volume.restrict {x : Fin N → Space | ∀ i, x i ∈ cube L}) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  apply (integrable_const (Real.exp (β * B * N))).mono'
    (measurable_boltzmann hφ β N).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ β x)]
  exact boltzmann_le_of_stable hβ hstable x

theorem energy_eq_real_of_injective (φ : ℝ → ℝ) {N : ℕ} {x : Fin N → Space}
    (hx : Function.Injective x) :
    energy φ x = ((∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
      φ ‖x i - x j‖ : ℝ) : EReal) := by
  classical
  unfold energy
  simp only [ereal_coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
  exact ite_eq_right (sub_ne_zero.mpr (hx.ne hij))

theorem boltzmann_pos_of_injective (φ : ℝ → ℝ) (β : ℝ) {N : ℕ}
    {x : Fin N → Space} (hx : Function.Injective x) : 0 < boltzmann φ β x := by
  unfold boltzmann
  rw [ite_eq_right (by rw [energy_eq_real_of_injective φ hx]; exact EReal.coe_ne_top _)]
  exact Real.exp_pos _

theorem isOpen_openConfigurations (L : ℝ) (N : ℕ) :
    IsOpen (openConfigurations L N) := by
  have hbox : IsOpen {x : Fin N → Space | ∀ i k, x i k ∈ Ioo (-L / 2) (L / 2)} := by
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_Ioo.preimage ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp
      (continuous_apply i))
  have hinj : IsOpen {x : Fin N → Space | Function.Injective x} := by
    have heq : {x : Fin N → Space | Function.Injective x} =
        ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {x | x i ≠ x j} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter]
      exact ⟨fun h i j hij => h.ne hij, fun h i j hij => by_contra fun hij' => h i j hij' hij⟩
    rw [heq]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact (isClosed_eq (continuous_apply i) (continuous_apply j)).isOpen_compl
  exact hbox.inter hinj

theorem openConfigurations_nonempty {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (openConfigurations L N).Nonempty := by
  let c : ℝ := L / (4 * ((N : ℝ) + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  let x : Fin N → Space := fun i => WithLp.toLp 2 (fun _ : Fin 3 => (i : ℝ) * c)
  refine ⟨x, ?_, ?_⟩
  · intro i k
    change -L / 2 < (i : ℝ) * c ∧ (i : ℝ) * c < L / 2
    have hi : (i : ℝ) < N := by exact_mod_cast i.isLt
    have hinonneg : 0 ≤ (i : ℝ) := by positivity
    constructor
    · nlinarith [mul_nonneg hinonneg hc.le]
    · dsimp [c]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hL (by exact_mod_cast Nat.zero_lt_succ N : 0 < (N : ℝ) + 1)]
  · intro i j he
    have hij := congrArg (fun y : Space => y 0) he
    change (i : ℝ) * c = (j : ℝ) * c at hij
    have hij' := mul_right_cancel₀ hc.ne' hij
    exact Fin.ext (by exact_mod_cast hij')

theorem partition_pos {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) : 0 < partition φ β L N := by
  classical
  unfold partition
  split_ifs
  · norm_num
  · apply mul_pos (by positivity)
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (boltzmann_nonneg φ β)) (integrableOn_boltzmann hφ hβ hstable L N)]
    apply lt_of_lt_of_le ((isOpen_openConfigurations L N).measure_pos volume
      (openConfigurations_nonempty hL N))
    apply measure_mono
    intro x hx
    exact ⟨(boltzmann_pos_of_injective φ β hx.2).ne',
      fun i k => ⟨(hx.1 i k).1.le, (hx.1 i k).2.le⟩⟩

theorem boltzmann_add (φ : ℝ → ℝ) (β γ : ℝ) {N : ℕ} (x : Fin N → Space) :
    boltzmann φ (β + γ) x = boltzmann φ β x * boltzmann φ γ x := by
  unfold boltzmann
  split_ifs
  · ring
  · rw [← Real.exp_add]
    congr 1
    ring

theorem boltzmann_rpow (φ : ℝ → ℝ) (β : ℝ) {p : ℝ} (hp : 0 < p)
    {N : ℕ} (x : Fin N → Space) :
    boltzmann φ β x ^ p = boltzmann φ (p * β) x := by
  unfold boltzmann
  split_ifs
  · exact Real.zero_rpow hp.ne'
  · rw [← Real.exp_mul]
    congr 1
    ring

theorem integral_boltzmann_logconvex {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B : ℝ}
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (L : ℝ) (N : ℕ) {β γ a b : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ (a * β + b * γ) x) ≤
      (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x) ^ a *
      (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ γ x) ^ b := by
  let μ : Measure (Fin N → Space) :=
    volume.restrict {x : Fin N → Space | ∀ i, x i ∈ cube L}
  have hp (c u : ℝ) (hc : 0 < c) (x : Fin N → Space) :
      ‖boltzmann φ (c * u) x‖ ^ (1 / c) = boltzmann φ u x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ (c * u) x),
      boltzmann_rpow φ (c * u) (one_div_pos.mpr hc)]
    congr 1
    field_simp
  have hLp (c u : ℝ) (hc : 0 < c) (hu : 0 < u) :
      MemLp (fun x : Fin N → Space => boltzmann φ (c * u) x) (ENNReal.ofReal (1 / c)) μ := by
    have A : ENNReal.ofReal (1 / c) ≠ 0 := by positivity
    have B' : ENNReal.ofReal (1 / c) ≠ ∞ := ENNReal.ofReal_ne_top
    rw [← memLp_norm_rpow_iff _ A B', ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / c),
      ENNReal.div_self A B', memLp_one_iff_integrable]
    · apply (integrableOn_boltzmann hφ hu.le hstable L N).congr
      exact ae_of_all _ (fun x => (hp c u hc x).symm)
    · exact (measurable_boltzmann hφ (c * u) N).aestronglyMeasurable
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (Real.holderConjugate_one_div ha hb hab)
    (ae_of_all μ (boltzmann_nonneg φ (a * β)))
    (ae_of_all μ (boltzmann_nonneg φ (b * γ)))
    (hLp a β ha hβ) (hLp b γ hb hγ)
  simp only [one_div_one_div] at hHolder
  convert hHolder using 1
  · exact integral_congr_ae (ae_of_all μ (boltzmann_add φ (a * β) (b * γ)))
  · congr 2
    · apply integral_congr_ae
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ (a * β) x)]
        using (hp a β ha x).symm
    · apply integral_congr_ae
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ (b * γ) x)]
        using (hp b γ hb x).symm

theorem integral_boltzmann_pos {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) :
    0 < ∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (boltzmann_nonneg φ β)) (integrableOn_boltzmann hφ hβ hstable L N)]
  apply lt_of_lt_of_le ((isOpen_openConfigurations L N).measure_pos volume
    (openConfigurations_nonempty hL N))
  apply measure_mono
  intro x hx
  exact ⟨(boltzmann_pos_of_injective φ β hx.2).ne',
    fun i k => ⟨(hx.1 i k).1.le, (hx.1 i k).2.le⟩⟩

theorem convexOn_log_integral_boltzmann {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B L : ℝ} (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) : ConvexOn ℝ (Ioi 0) (fun β => Real.log
      (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x)) := by
  refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _, ?_⟩
  intro β hβ γ hγ a b ha hb hab
  simp only [smul_eq_mul]
  have hβ' := integral_boltzmann_pos hφ hβ.le hL hstable N
  have hγ' := integral_boltzmann_pos hφ hγ.le hL hstable N
  have hac : 0 < a * β + b * γ := add_pos (mul_pos ha hβ) (mul_pos hb hγ)
  have hc := integral_boltzmann_pos hφ hac.le hL hstable N
  have hHolder := integral_boltzmann_logconvex hφ hstable L N hβ hγ ha hb hab
  calc
    _ ≤ Real.log ((∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x) ^ a *
          (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ γ x) ^ b) :=
      Real.log_le_log hc hHolder
    _ = _ := by rw [Real.log_mul (Real.rpow_pos_of_pos hβ' a).ne' (Real.rpow_pos_of_pos hγ' b).ne',
      Real.log_rpow hβ', Real.log_rpow hγ']

theorem convexOn_log_partition {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B L : ℝ} (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) : ConvexOn ℝ (Ioi 0) (fun β => Real.log (partition φ β L N)) := by
  by_cases hN : N = 0
  · simp only [hN, partition, ↓reduceIte, Real.log_one]
    exact convexOn_const _ (convex_Ioi _)
  · have hlog (β : ℝ) (hβ : 0 < β) : Real.log (partition φ β L N) =
        Real.log (1 / (N.factorial : ℝ)) + Real.log
          (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x) := by
      unfold partition
      rw [ite_eq_right hN, Real.log_mul (one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)))
        (integral_boltzmann_pos hφ hβ.le hL hstable N).ne']
    have hc := convexOn_log_integral_boltzmann hφ hL hstable N
    refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _, ?_⟩
    intro β hβ γ hγ a b ha hb hab
    simp only [smul_eq_mul]
    rw [hlog _ (add_pos (mul_pos ha hβ) (mul_pos hb hγ)), hlog β hβ, hlog γ hγ]
    have hi := hc.2 hβ hγ ha.le hb.le hab
    simp only [smul_eq_mul] at hi
    have hcst : a * Real.log (1 / (N.factorial : ℝ)) +
        b * Real.log (1 / (N.factorial : ℝ)) = Real.log (1 / (N.factorial : ℝ)) := by
      rw [← add_mul, hab, one_mul]
    nlinarith only [hi, hcst]

theorem volume_cube (L : ℝ) : volume (cube L) = (ENNReal.ofReal L) ^ 3 := by
  have heq : cube L = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      (Set.pi Set.univ (fun _ : Fin 3 => Icc (-L / 2) (L / 2))) := by
    ext x
    simp only [cube, mem_preimage, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_const]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    ((MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)).nullMeasurableSet)]
  change (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) _ = _
  rw [Measure.pi_pi]
  simp only [Real.volume_Icc]
  have ha : L / 2 - -L / 2 = L := by ring
  simp [ha]

theorem volume_configurations (L : ℝ) (N : ℕ) :
    volume {x : Fin N → Space | ∀ i, x i ∈ cube L} = (ENNReal.ofReal L) ^ (3 * N) := by
  have heq : {x : Fin N → Space | ∀ i, x i ∈ cube L} =
      Set.pi Set.univ (fun _ : Fin N => cube L) := by ext x; simp
  rw [heq]
  change (Measure.pi (fun _ : Fin N => (volume : Measure Space))) _ = _
  rw [Measure.pi_pi]
  simp only [volume_cube, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

theorem partition_nonneg (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) :
    0 ≤ partition φ β L N := by
  unfold partition
  split_ifs
  · norm_num
  · apply mul_nonneg (by positivity)
    exact integral_nonneg (boltzmann_nonneg φ β)

theorem partition_le_exp_of_stable {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    partition φ β L N ≤ (L ^ 3 * Real.exp (β * B)) ^ N / (N.factorial : ℝ) := by
  by_cases hN : N = 0
  · simp [hN, partition]
  · have : IsFiniteMeasure (volume.restrict {x : Fin N → Space | ∀ i, x i ∈ cube L}) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        (isCompact_configurations L N).measure_lt_top (μ := volume)⟩
    have hi := integral_mono_ae (integrableOn_boltzmann hφ hβ hstable L N)
      (integrable_const (Real.exp (β * B * N)))
      (ae_of_all _ (boltzmann_le_of_stable hβ hstable (N := N)))
    rw [integral_const] at hi
    simp only [Measure.real, Measure.restrict_apply_univ, volume_configurations,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hL, smul_eq_mul] at hi
    unfold partition
    rw [ite_eq_right hN]
    have hfac : 0 ≤ (1 / (N.factorial : ℝ)) := by positivity
    apply (mul_le_mul_of_nonneg_left hi hfac).trans_eq
    rw [show β * B * (N : ℝ) = (N : ℝ) * (β * B) by ring, Real.exp_nat_mul,
      mul_pow, pow_mul]
    ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem summable_grandPartition {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (t h : ℝ) :
    Summable (fun N : ℕ => Real.exp (t * h * N) * partition φ β L N) := by
  apply Summable.of_nonneg_of_le (fun N => mul_nonneg (Real.exp_pos _).le
    (partition_nonneg φ β L N)) _
    (Real.summable_pow_div_factorial (Real.exp (t * h) * (L ^ 3 * Real.exp (β * B))))
  intro N
  have hb := mul_le_mul_of_nonneg_left (partition_le_exp_of_stable hφ hβ hL hstable N)
    (Real.exp_pos (t * h * N)).le
  apply hb.trans_eq
  rw [show t * h * (N : ℝ) = (N : ℝ) * (t * h) by ring, Real.exp_nat_mul, mul_pow]
  ring

theorem grandPartition_le_exp {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (t h : ℝ) :
    grandPartition φ t β h L ≤ Real.exp (L ^ 3 * Real.exp (t * h + β * B)) := by
  let z := L ^ 3 * Real.exp (t * h + β * B)
  have hz : HasSum (fun N : ℕ => z ^ N / (N.factorial : ℝ)) (Real.exp z) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  unfold grandPartition
  rw [← hz.tsum_eq]
  apply (summable_grandPartition hφ hβ hL hstable t h).tsum_le_tsum _ hz.summable
  intro N
  apply (mul_le_mul_of_nonneg_left (partition_le_exp_of_stable hφ hβ hL hstable N)
    (Real.exp_pos _).le).trans_eq
  dsimp [z]
  rw [show t * h * (N : ℝ) = (N : ℝ) * (t * h) by ring, Real.exp_nat_mul,
    Real.exp_add, mul_pow, mul_pow]
  ring

theorem tsum_logconvex_bound {f g k : ℕ → ℝ} {a b : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (hk : Summable k)
    (hfS : Summable f) (hgS : Summable g) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hbound : ∀ n, k n ≤ f n ^ a * g n ^ b) :
    (∑' n, k n) ≤ (∑' n, f n) ^ a * (∑' n, g n) ^ b := by
  have heq (x c : ℝ) (hx : 0 ≤ x) (hc : 0 < c) : (x ^ c) ^ (1 / c) = x := by
    rw [← Real.rpow_mul hx, mul_one_div_cancel hc.ne', Real.rpow_one]
  have hu : Summable (fun n => (f n ^ a) ^ (1 / a)) := by
    simpa only [heq _ a (hf _) ha] using hfS
  have hv : Summable (fun n => (g n ^ b) ^ (1 / b)) := by
    simpa only [heq _ b (hg _) hb] using hgS
  obtain ⟨hS, hH⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (Real.holderConjugate_one_div ha hb hab)
    (fun n => Real.rpow_nonneg (hf n) a) (fun n => Real.rpow_nonneg (hg n) b) hu hv
  simp only [heq _ a (hf _) ha, heq _ b (hg _) hb, one_div_one_div] at hH
  exact (hk.tsum_le_tsum hbound hS).trans hH

theorem convexOn_log_tsum {E : Type u_1} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) (F : ℕ → E → ℝ)
    (hpos : ∀ n x, x ∈ s → 0 < F n x)
    (hconv : ∀ n, ConvexOn ℝ s (fun x => Real.log (F n x)))
    (hS : ∀ x, x ∈ s → Summable (fun n => F n x)) :
    ConvexOn ℝ s (fun x => Real.log (∑' n, F n x)) := by
  have hp (x : E) (hx : x ∈ s) : 0 < ∑' n, F n x :=
    (hpos 0 x hx).trans_le ((hS x hx).le_tsum 0 (fun n _ => (hpos n x hx).le))
  refine convexOn_iff_forall_pos.mpr ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hs hx hy ha.le hb.le hab
  have hbnd (n : ℕ) : F n (a • x + b • y) ≤ F n x ^ a * F n y ^ b := by
    have hc := (hconv n).2 hx hy ha.le hb.le hab
    simp only [smul_eq_mul] at hc
    apply (Real.log_le_log_iff (hpos n _ hz) (mul_pos
      (Real.rpow_pos_of_pos (hpos n x hx) a) (Real.rpow_pos_of_pos (hpos n y hy) b))).mp
    rw [Real.log_mul (Real.rpow_pos_of_pos (hpos n x hx) a).ne'
      (Real.rpow_pos_of_pos (hpos n y hy) b).ne', Real.log_rpow (hpos n x hx),
      Real.log_rpow (hpos n y hy)]
    exact hc
  have hHolder := tsum_logconvex_bound (fun n => (hpos n x hx).le)
    (fun n => (hpos n y hy).le) (hS _ hz) (hS x hx) (hS y hy) ha hb hab hbnd
  calc
    _ ≤ Real.log ((∑' n, F n x) ^ a * (∑' n, F n y) ^ b) :=
      Real.log_le_log (hp _ hz) hHolder
    _ = _ := by rw [Real.log_mul (Real.rpow_pos_of_pos (hp x hx) a).ne'
      (Real.rpow_pos_of_pos (hp y hy) b).ne',
      Real.log_rpow (hp x hx), Real.log_rpow (hp y hy)]; rfl

theorem convexOn_log_grandPartition {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B L : ℝ} (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (t : ℝ) :
    ConvexOn ℝ {x : ℝ × ℝ | 0 < x.1}
      (fun x => Real.log (grandPartition φ t x.1 x.2 L)) := by
  have hdomain : Convex ℝ {x : ℝ × ℝ | 0 < x.1} := by
    intro x hx y hy a b ha hb hab
    change 0 < a * x.1 + b * y.1
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb' : b = 1 := by simpa using hab
      simpa [hb'] using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
  apply convexOn_log_tsum hdomain
    (fun N x => Real.exp (t * x.2 * N) * partition φ x.1 L N)
  · intro N x hx
    exact mul_pos (Real.exp_pos _) (partition_pos hφ hx.le hL hstable N)
  · intro N
    have hc := convexOn_log_partition hφ hL hstable N
    refine convexOn_iff_forall_pos.mpr ⟨hdomain, ?_⟩
    intro x hx y hy a b ha hb hab
    have hz := hdomain hx hy ha.le hb.le hab
    have log_eq (z : ℝ × ℝ) (hz : 0 < z.1) :
        Real.log (Real.exp (t * z.2 * N) * partition φ z.1 L N) =
          t * z.2 * N + Real.log (partition φ z.1 L N) := by
      rw [Real.log_mul (Real.exp_pos _).ne'
        (partition_pos hφ hz.le hL hstable N).ne', Real.log_exp]
    rw [log_eq _ hz, log_eq _ hx, log_eq _ hy]
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have hi := hc.2 hx hy ha.le hb.le hab
    simp only [smul_eq_mul] at hi
    nlinarith only [hi]
  · intro x hx
    exact summable_grandPartition hφ hx.le hL.le hstable t x.2

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.FiniteBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem log_factorial_lower (N : ℕ) :
    (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  by_cases hN : N = 0
  · simp [hN]
  · have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hf : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
    have hh := Real.pow_div_factorial_le_exp (N : ℝ) hpos.le N
    have hl := Real.log_le_log (div_pos (pow_pos hpos _) hf) hh
    rw [Real.log_div (pow_ne_zero _ hpos.ne') hf.ne', Real.log_pow, Real.log_exp] at hl
    linarith

theorem boltzmann_le_of_energy_lower {φ : ℝ → ℝ} {β E : ℝ} (hβ : 0 ≤ β)
    {N : ℕ} {x : Fin N → Space} (hE : (E : EReal) ≤ energy φ x) :
    boltzmann φ β x ≤ Real.exp (-β * E) := by
  unfold boltzmann
  split_ifs with htop
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    have he := EReal.toReal_le_toReal hE (EReal.coe_ne_bot _) htop
    simp only [EReal.toReal_coe] at he
    exact mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hβ)

theorem partition_le_factorial_of_energy_bound {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L E : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) {N : ℕ} (hN : N ≠ 0)
    (hE : ∀ x : Fin N → Space, (∀ i, x i ∈ cube L) → (E : EReal) ≤ energy φ x) :
    partition φ β L N ≤ (L ^ 3) ^ N / (N.factorial : ℝ) * Real.exp (-β * E) := by
  let S := {x : Fin N → Space | ∀ i, x i ∈ cube L}
  have hS : MeasurableSet S := (isCompact_configurations L N).measurableSet
  have hfin : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_configurations L N).measure_lt_top (μ := volume)⟩
  have hh : ∀ᵐ x ∂volume.restrict S, boltzmann φ β x ≤ Real.exp (-β * E) := by
    apply (ae_restrict_iff' hS).mpr
    exact ae_of_all _ (fun x hx => boltzmann_le_of_energy_lower hβ (hE x hx))
  have hi := integral_mono_ae (integrableOn_boltzmann hφ hβ hstable L N)
    (integrable_const (Real.exp (-β * E))) hh
  have hc : (∫ x in S, Real.exp (-β * E)) = L ^ (3 * N) * Real.exp (-β * E) := by
    rw [setIntegral_const, Measure.real, volume_configurations, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hL, smul_eq_mul]
  rw [hc] at hi
  unfold partition
  rw [ite_eq_right hN]
  calc
    _ ≤ (1 / (N.factorial : ℝ)) * (L ^ (3 * N) * Real.exp (-β * E)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [pow_mul]; ring

theorem neg_log_partition_lower {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L E : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) {N : ℕ} (hN : N ≠ 0)
    (hE : ∀ x : Fin N → Space, (∀ i, x i ∈ cube L) → (E : EReal) ≤ energy φ x) :
    β * E + N * Real.log ((N : ℝ) / L ^ 3) - N ≤ -Real.log (partition φ β L N) := by
  have hnpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hfp : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hLp : 0 < L ^ 3 := pow_pos hL _
  have hZ := partition_pos hφ hβ hL hstable N
  have hu := partition_le_factorial_of_energy_bound hφ hβ hL.le hstable hN hE
  have hl := Real.log_le_log hZ hu
  rw [Real.log_mul (div_pos (pow_pos hLp _) hfp).ne' (Real.exp_pos _).ne',
    Real.log_div (pow_pos hLp _).ne' hfp.ne', Real.log_pow, Real.log_exp] at hl
  rw [Real.log_div hnpos.ne' hLp.ne']
  have hf := log_factorial_lower N
  nlinarith

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PairEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem ereal_sum_eq_top_of_exists {α : Type u_1} (s : Finset α) (f : α → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) (ht : ∃ i ∈ s, f i = ⊤) : ∑ i ∈ s, f i = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at ht
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    obtain ⟨j, hj, hjt⟩ := ht
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [hjt]
      exact EReal.top_add_of_ne_bot (ereal_sum_ne_bot s f
        (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
    · rw [ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)) ⟨j, hj, hjt⟩]
      exact EReal.add_top_of_ne_bot (hf i (Finset.mem_insert_self _ _))

theorem energy_eq_top_iff (φ : ℝ → ℝ) {N : ℕ} (x : Fin N → Space) :
    energy φ x = ⊤ ↔ ¬Function.Injective x := by
  constructor
  · intro he hx
    rw [energy_eq_real_of_injective φ hx] at he
    exact EReal.coe_ne_top _ he
  · intro hx
    have hh : ∃ i j, i ≠ j ∧ x i = x j := by
      by_contra hc
      apply hx
      intro i j heq
      by_contra hne
      exact hc ⟨i, j, hne, heq⟩
    obtain ⟨i, j, hij, he⟩ := hh
    have hpair {i j : Fin N} (hij : i < j) (he : x i = x j) : energy φ x = ⊤ := by
      apply ereal_sum_eq_top_of_exists _ _
        (fun i _ => ereal_sum_ne_bot _ _ (fun j _ => radialPotential_ne_bot _ _))
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply ereal_sum_eq_top_of_exists _ _ (fun j _ => radialPotential_ne_bot _ _)
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, by
        simp [he, radialPotential]⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact hpair h he
    · exact hpair h he.symm

theorem realPairEnergy_eq_ordered (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι] [LinearOrder ι]
    (x : ι → Space) :
    realPairEnergy φ x = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), φ ‖x i - x j‖ := by
  classical
  have hsplit (i j : ι) : (if i = j then 0 else φ ‖x i - x j‖) =
      (if i < j then φ ‖x i - x j‖ else 0) +
      (if j < i then φ ‖x j - x i‖ else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le, norm_sub_rev]
  calc
    realPairEnergy φ x = (1/2 : ℝ) * ∑ i, ∑ j,
        ((if i < j then φ ‖x i - x j‖ else 0) +
          (if j < i then φ ‖x j - x i‖ else 0)) := by
      unfold realPairEnergy
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · simpa only [ite_eq_left hij] using hsplit i j
      · simpa only [ite_eq_right hij] using hsplit i j
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j : ι => if j < i then φ ‖x j - x i‖ else 0)]
      simp only [Finset.sum_filter]
      ring

theorem boltzmann_eq_symmetricWeight (φ : ℝ → ℝ) (β : ℝ)
    {N : ℕ} (x : Fin N → Space) : boltzmann φ β x = symmetricWeight φ β x := by
  classical
  by_cases hx : Function.Injective x
  · simp only [boltzmann, energy_eq_real_of_injective φ hx, EReal.coe_ne_top,
      ite_false, EReal.toReal_coe, symmetricWeight, ite_eq_left hx, realPairEnergy_eq_ordered]
  · simp only [boltzmann, (energy_eq_top_iff φ x).2 hx, ite_true, symmetricWeight, ite_eq_right hx]

theorem realPairEnergy_relabel (φ : ℝ → ℝ) {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → Space) : realPairEnergy φ (x ∘ e) = realPairEnergy φ x := by
  classical
  unfold realPairEnergy
  simp only [Function.comp_apply, ← e.injective.eq_iff]
  congr 1
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp e (fun j => if e i = j then 0 else φ ‖x (e i) - x j‖)

theorem symmetricWeight_relabel (φ : ℝ → ℝ) (β : ℝ) {ι : Type u_1} {κ : Type u_2}
    [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → Space) :
    symmetricWeight φ β (x ∘ e) = symmetricWeight φ β x := by
  classical
  have hh : Function.Injective (x ∘ e) ↔ Function.Injective x :=
    by
      constructor
      · intro hx i j hij
        obtain ⟨i, rfl⟩ := e.surjective i
        obtain ⟨j, rfl⟩ := e.surjective j
        exact congrArg e (hx hij)
      · exact fun hx => hx.comp e.injective
  simp only [symmetricWeight, hh, realPairEnergy_relabel]

theorem symmetric_matrix_split {ι : Type u_1} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (F : ι → ι → ℝ) (hsym : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, F i j) =
      (∑ i : {i // p i}, ∑ j : {j // p j}, F i j) +
      (∑ i : {i // ¬p i}, ∑ j : {j // ¬p j}, F i j) +
      2 * (∑ i : {i // p i}, ∑ j : {j // ¬p j}, F i j) := by
  classical
  have houter := Fintype.sum_subtype_add_sum_subtype p (fun i => ∑ j, F i j)
  have hinner (i : ι) := Fintype.sum_subtype_add_sum_subtype p (F i)
  rw [← houter]
  simp_rw [← hinner, Finset.sum_add_distrib]
  have hh : (∑ i : {i // ¬p i}, ∑ j : {j // p j}, F i j) =
      ∑ i : {i // p i}, ∑ j : {j // ¬p j}, F i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hsym _ _
  rw [hh]
  ring

theorem realPairEnergy_split (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (x : ι → Space) :
    realPairEnergy φ x =
      realPairEnergy φ (fun i : {i // p i} => x i) +
      realPairEnergy φ (fun i : {i // ¬p i} => x i) +
      ∑ i : {i // p i}, ∑ j : {j // ¬p j}, φ ‖x i - x j‖ := by
  classical
  have heq := symmetric_matrix_split p (fun i j => if i = j then 0 else φ ‖x i - x j‖)
    (fun i j => by by_cases h : i = j <;> simp [h, eq_comm, norm_sub_rev])
  have hcross (i : {i // p i}) (j : {i // ¬p i}) : (i : ι) ≠ j := by
    intro h
    exact j.property (h ▸ i.property)
  have hself (a b : {i // p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  have hself' (a b : {i // ¬p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  unfold realPairEnergy
  rw [heq]
  simp only [hself, hself', hcross, ite_false]
  ring

theorem symmetricWeight_nonneg (φ : ℝ → ℝ) (β : ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) : 0 ≤ symmetricWeight φ β x := by
  unfold symmetricWeight
  split_ifs
  · positivity
  · rfl

theorem symmetricWeight_separated (φ : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {ι : Type u_1} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    {A B : Set Space} (hd : Disjoint A B)
    (hφ : ∀ a ∈ A, ∀ b ∈ B, φ ‖a - b‖ ≤ 0)
    (x : ι → Space) (hA : ∀ i, p i → x i ∈ A) (hB : ∀ i, ¬p i → x i ∈ B) :
    symmetricWeight φ β (fun i : {i // p i} => x i) *
      symmetricWeight φ β (fun i : {i // ¬p i} => x i) ≤ symmetricWeight φ β x := by
  classical
  by_cases ha : Function.Injective (fun i : {i // p i} => x i)
  swap
  · simpa only [symmetricWeight, ite_eq_right ha, zero_mul] using symmetricWeight_nonneg φ β x
  by_cases hb : Function.Injective (fun i : {i // ¬p i} => x i)
  swap
  · simpa only [symmetricWeight, ite_eq_right hb, mul_zero] using symmetricWeight_nonneg φ β x
  have hx : Function.Injective x := by
    intro i j hij
    by_cases hi : p i <;> by_cases hj : p j
    · exact congrArg Subtype.val (ha (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
    · exact False.elim (Set.disjoint_left.mp hd (hA i hi) (hij ▸ hB j hj))
    · exact False.elim (Set.disjoint_left.mp hd (hA j hj) (hij ▸ hB i hi))
    · exact congrArg Subtype.val (hb (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
  have hc : (∑ i : {i // p i}, ∑ j : {j // ¬p j}, φ ‖x i - x j‖) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    exact Finset.sum_nonpos (fun j _ => hφ _ (hA i i.property) _ (hB j j.property))
  simp only [symmetricWeight, ite_eq_left ha, ite_eq_left hb, ite_eq_left hx, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [realPairEnergy_split φ p x]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ hc]

theorem realPairEnergy_translate (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) (v : Space) :
    realPairEnergy φ (fun i => x i + v) = realPairEnergy φ x := by
  classical
  simp only [realPairEnergy, add_sub_add_right_eq_sub]

theorem symmetricWeight_translate (φ : ℝ → ℝ) (β : ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) (v : Space) :
    symmetricWeight φ β (fun i => x i + v) = symmetricWeight φ β x := by
  classical
  have hh : Function.Injective (fun i => x i + v) ↔ Function.Injective x := by
    simp only [Function.Injective, add_left_inj]
  simp only [symmetricWeight, hh, realPairEnergy_translate]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Assignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

section Assignments
variable {X : Type u_1} [MeasurableSpace X] {ι : Type u_2} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem measurableSet_assignmentRegion {B : ι → Set X} (hB : ∀ i, MeasurableSet (B i))
    (e : Equiv.Perm ι) : MeasurableSet (assignmentRegion B e) := by
  convert MeasurableSet.iInter (fun i => (hB (e i)).preimage (measurable_pi_apply i)) using 1
  ext x
  simp [assignmentRegion]

omit [MeasurableSpace X] in
theorem assignmentRegion_pairwiseDisjoint {B : ι → Set X}
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) :
    Pairwise (fun e f : Equiv.Perm ι => Disjoint (assignmentRegion B e) (assignmentRegion B f)) := by
  intro e f hef
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hne : ∃ i, e i ≠ f i := by
    by_contra! h
    exact hef (Equiv.ext h)
  obtain ⟨i, hi⟩ := hne
  exact Set.disjoint_left.mp (hB hi) (hx i) (hy i)

theorem measure_assignment_union (μ : Measure X) [SigmaFinite μ] {B : ι → Set X}
    (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (Measure.pi (fun _ : ι => μ)) (⋃ e : Equiv.Perm ι, assignmentRegion B e) =
      (Fintype.card ι).factorial * ∏ i, μ (B i) := by
  rw [measure_iUnion (assignmentRegion_pairwiseDisjoint hd)
    (measurableSet_assignmentRegion hB), tsum_fintype]
  have hh (e : Equiv.Perm ι) :
      (Measure.pi (fun _ : ι => μ)) (assignmentRegion B e) = ∏ i, μ (B i) := by
    have heq : assignmentRegion B e = Set.univ.pi (fun i => B (e i)) := by
      ext x
      simp [assignmentRegion]
    rw [heq, Measure.pi_pi, Equiv.prod_comp e (fun i => μ (B i))]
  simp_rw [hh]
  simp [Fintype.card_perm]

theorem integral_lower_of_disjoint_assignments (μ : Measure X) [SigmaFinite μ]
    {B : ι → Set X} (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hfinite : ∀ i, μ (B i) ≠ ⊤) {Ω : Set (ι → X)} {F : (ι → X) → ℝ}
    (hF : IntegrableOn F Ω (Measure.pi (fun _ : ι => μ)))
    (hF0 : ∀ x, 0 ≤ F x) {c : ℝ}
    (hinc : ∀ e, assignmentRegion B e ⊆ Ω)
    (hbound : ∀ e, ∀ x ∈ assignmentRegion B e, c ≤ F x) :
    (Fintype.card ι).factorial * (∏ i, (μ (B i)).toReal) * c ≤
      ∫ x in Ω, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  let S := ⋃ e : Equiv.Perm ι, assignmentRegion B e
  have hS : MeasurableSet S := MeasurableSet.iUnion (measurableSet_assignmentRegion hB)
  have hsub : S ⊆ Ω := iUnion_subset hinc
  have hmass := measure_assignment_union μ hB hd
  have hSfin : (Measure.pi (fun _ : ι => μ)) S ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.mul_ne_top (by simp) (ENNReal.prod_ne_top (fun i _ => hfinite i))
  have hconst : IntegrableOn (fun _ : ι → X => c) S (Measure.pi (fun _ : ι => μ)) :=
    integrableOn_const hSfin
  have hle : (∫ x in S, c ∂(Measure.pi (fun _ : ι => μ))) ≤
      ∫ x in S, F x ∂(Measure.pi (fun _ : ι => μ)) := by
    apply setIntegral_mono_on hconst (hF.mono_set hsub) hS
    intro x hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    exact hbound e x he
  have hle' := setIntegral_mono_set hF (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall hsub)
  have hval : (∫ x in S, c ∂(Measure.pi (fun _ : ι => μ))) =
      (Fintype.card ι).factorial * (∏ i, (μ (B i)).toReal) * c := by
    rw [setIntegral_const, Measure.real, hmass, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_prod, smul_eq_mul]
  rw [hval] at hle
  exact hle.trans hle'

omit [DecidableEq ι] in

theorem setIntegral_coordinatePerm (μ : Measure X) [SigmaFinite μ]
    (e : Equiv.Perm ι) (S : Set (ι → X)) (F : (ι → X) → ℝ)
    (hsym : ∀ x, F (x ∘ e) = F x) :
    (∫ x in {x | (x ∘ e) ∈ S}, F x ∂(Measure.pi (fun _ : ι => μ))) =
      ∫ x in S, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  let p : (ι → X) ≃ᵐ (ι → X) := MeasurableEquiv.piCongrLeft (fun _ : ι => X) e.symm
  have hpx (x : ι → X) : p x = x ∘ e := by
    ext i
    simpa only [p, Equiv.symm_apply_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : ι => X) x (e i))
  have hp : MeasurePreserving p (Measure.pi (fun _ : ι => μ))
      (Measure.pi (fun _ : ι => μ)) := measurePreserving_piCongrLeft (fun _ : ι => μ) e.symm
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding F S
  simpa only [hpx, hsym, Set.preimage] using heq

theorem measurableSet_binaryRegion {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (s : Finset ι) : MeasurableSet (binaryRegion A B s) := by
  have hh (i : ι) : MeasurableSet ((fun x : ι → X => x i) ⁻¹' (if i ∈ s then A else B)) := by
    by_cases hi : i ∈ s
    · simpa only [ite_eq_left hi] using hA.preimage (measurable_pi_apply i)
    · simpa only [ite_eq_right hi] using hB.preimage (measurable_pi_apply i)
  convert MeasurableSet.iInter hh using 1
  ext x
  simp only [binaryRegion, mem_ofPred_eq, mem_iInter, mem_preimage]
  apply forall_congr'
  intro i
  split_ifs <;> rfl

omit [MeasurableSpace X] [Fintype ι] in
theorem binaryRegion_pairwiseDisjoint {A B : Set X} (hd : Disjoint A B) :
    Pairwise (fun s t : Finset ι => Disjoint (binaryRegion A B s) (binaryRegion A B t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hst
  ext i
  constructor
  · intro hi
    by_contra ht
    exact Set.disjoint_left.mp hd (by simpa only [ite_eq_left hi] using hx i)
      (by simpa only [ite_eq_right ht] using hy i)
  · intro hi
    by_contra hs
    exact Set.disjoint_left.mp hd (by simpa only [ite_eq_left hi] using hy i)
      (by simpa only [ite_eq_right hs] using hx i)

theorem setIntegral_binaryRegion_eq (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} {s t : Finset ι} (hst : s.card = t.card) (F : (ι → X) → ℝ)
    (hsym : ∀ (e : Equiv.Perm ι) x, F (x ∘ e) = F x) :
    (∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ))) =
      ∫ x in binaryRegion A B t, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq s t hst
  have hmem (i : ι) : e i ∈ t ↔ i ∈ s := by
    rw [← he]
    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨j, hj, hji⟩
      exact e.injective hji ▸ hj
    · exact fun hi => ⟨i, hi, rfl⟩
  have hpre : {x : ι → X | (x ∘ e) ∈ binaryRegion A B s} = binaryRegion A B t := by
    ext x
    change (∀ i, if i ∈ s then x (e i) ∈ A else x (e i) ∈ B) ↔
      (∀ i, if i ∈ t then x i ∈ A else x i ∈ B)
    simp_rw [← hmem]
    constructor
    · intro hh j
      obtain ⟨i, rfl⟩ := e.surjective j
      exact hh i
    · intro hh i
      exact hh (e i)
  have hh := setIntegral_coordinatePerm μ e (binaryRegion A B s) F (hsym e)
  rw [hpre] at hh
  exact hh.symm

theorem integral_lower_binary_assignments (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (s : Finset ι) {Ω : Set (ι → X)} {F : (ι → X) → ℝ}
    (hF : IntegrableOn F Ω (Measure.pi (fun _ : ι => μ)))
    (hF0 : ∀ x, 0 ≤ F x)
    (hsym : ∀ (e : Equiv.Perm ι) x, F (x ∘ e) = F x)
    (hinc : ∀ t : Finset ι, t.card = s.card → binaryRegion A B t ⊆ Ω) :
    (Fintype.card ι).choose s.card *
        (∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ))) ≤
      ∫ x in Ω, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  classical
  let T := (Finset.univ : Finset ι).powersetCard s.card
  have hcard (t : Finset ι) (ht : t ∈ T) : t.card = s.card := (Finset.mem_powersetCard.mp ht).2
  have hsub : (⋃ t ∈ T, binaryRegion A B t) ⊆ Ω := by
    intro x hx
    obtain ⟨t, ht, hx⟩ := mem_iUnion₂.mp hx
    exact hinc t (hcard t ht) hx
  have hh := integral_biUnion_finset T (fun t _ => measurableSet_binaryRegion hA hB t)
    (fun _ _ _ _ hne => binaryRegion_pairwiseDisjoint hd hne)
    (fun t ht => hF.mono_set (hinc t (hcard t ht)))
  have hEq : (∫ x in ⋃ t ∈ T, binaryRegion A B t, F x ∂(Measure.pi (fun _ : ι => μ))) =
      (Fintype.card ι).choose s.card *
        (∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ))) := by
    rw [hh]
    calc
      _ = ∑ _t ∈ T, ∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ)) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact setIntegral_binaryRegion_eq μ (hcard t ht) F hsym
      _ = _ := by simp [T]
  rw [← hEq]
  exact setIntegral_mono_set hF (Filter.Eventually.of_forall hF0)
    (Filter.Eventually.of_forall hsub)

theorem setIntegral_binary_product (μ : Measure X) [SigmaFinite μ]
    (A B : Set X) (s : Finset ι)
    (f : ({i : ι // i ∈ s} → X) → ℝ) (g : ({i : ι // i ∉ s} → X) → ℝ) :
    (∫ x in binaryRegion A B s,
      f (fun i : {i : ι // i ∈ s} => x i) * g (fun i : {i : ι // i ∉ s} => x i)
      ∂(Measure.pi (fun _ : ι => μ))) =
    (∫ x in {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}, f x ∂(Measure.pi (fun _ : {i : ι // i ∈ s} => μ))) *
    (∫ x in {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}, g x
      ∂(Measure.pi (fun _ : {i : ι // i ∉ s} => μ))) := by
  let p := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (fun i => i ∈ s)
  let SA := {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}
  let SB := {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ s)
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  rw [hfi] at hp
  have hpre : p ⁻¹' (SA ×ˢ SB) = binaryRegion A B s := by
    ext x
    change ((∀ i : {i : ι // i ∈ s}, x i ∈ A) ∧ (∀ i : {i : ι // i ∉ s}, x i ∈ B)) ↔
      (∀ i, if i ∈ s then x i ∈ A else x i ∈ B)
    constructor
    · rintro ⟨ha, hb⟩ i
      split_ifs with hi
      · exact ha ⟨i, hi⟩
      · exact hb ⟨i, hi⟩
    · intro hh
      constructor
      · intro i
        simpa only [ite_eq_left i.property] using hh i
      · intro i
        simpa only [ite_eq_right i.property] using hh i
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding
    (fun z => f z.1 * g z.2) (SA ×ˢ SB)
  rw [hpre, setIntegral_prod_mul] at heq
  exact heq

theorem integrableOn_binary_product (μ : Measure X) [SigmaFinite μ]
    (A B : Set X) (s : Finset ι)
    {f : ({i : ι // i ∈ s} → X) → ℝ} {g : ({i : ι // i ∉ s} → X) → ℝ}
    (hf : IntegrableOn f {x | ∀ i, x i ∈ A} (Measure.pi (fun _ : {i : ι // i ∈ s} => μ)))
    (hg : IntegrableOn g {x | ∀ i, x i ∈ B}
      (Measure.pi (fun _ : {i : ι // i ∉ s} => μ))) :
    IntegrableOn (fun x : ι → X =>
      f (fun i : {i : ι // i ∈ s} => x i) * g (fun i : {i : ι // i ∉ s} => x i))
      (binaryRegion A B s) (Measure.pi (fun _ : ι => μ)) := by
  let p := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (fun i => i ∈ s)
  let SA := {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}
  let SB := {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ s)
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
    Subsingleton.elim _ _
  rw [hfi] at hp
  have hpre : p ⁻¹' (SA ×ˢ SB) = binaryRegion A B s := by
    ext x
    change ((∀ i : {i : ι // i ∈ s}, x i ∈ A) ∧ (∀ i : {i : ι // i ∉ s}, x i ∈ B)) ↔
      (∀ i, if i ∈ s then x i ∈ A else x i ∈ B)
    constructor
    · rintro ⟨ha, hb⟩ i
      split_ifs with hi
      · exact ha ⟨i, hi⟩
      · exact hb ⟨i, hi⟩
    · intro hh
      constructor
      · intro i
        simpa only [ite_eq_left i.property] using hh i
      · intro i
        simpa only [ite_eq_right i.property] using hh i
  have hprod : IntegrableOn (fun z => f z.1 * g z.2) (SA ×ˢ SB)
      ((Measure.pi (fun _ : {i : ι // i ∈ s} => μ)).prod
      (Measure.pi (fun _ : {i : ι // i ∉ s} => μ))) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hf.mul_prod hg
  have hh := (hp.integrableOn_comp_preimage p.measurableEmbedding).2 hprod
  rw [hpre] at hh
  exact hh

theorem integral_lower_separated_product (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (s : Finset ι) {Ω : Set (ι → X)} {F : (ι → X) → ℝ}
    (hF : IntegrableOn F Ω (Measure.pi (fun _ : ι => μ)))
    (hF0 : ∀ x, 0 ≤ F x)
    (hsym : ∀ (e : Equiv.Perm ι) x, F (x ∘ e) = F x)
    (hinc : ∀ t : Finset ι, t.card = s.card → binaryRegion A B t ⊆ Ω)
    {f : ({i : ι // i ∈ s} → X) → ℝ} {g : ({i : ι // i ∉ s} → X) → ℝ}
    (hf : IntegrableOn f {x | ∀ i, x i ∈ A} (Measure.pi (fun _ : {i : ι // i ∈ s} => μ)))
    (hg : IntegrableOn g {x | ∀ i, x i ∈ B}
      (Measure.pi (fun _ : {i : ι // i ∉ s} => μ)))
    (hbound : ∀ x ∈ binaryRegion A B s,
      f (fun i : {i : ι // i ∈ s} => x i) * g (fun i : {i : ι // i ∉ s} => x i) ≤ F x) :
    (Fintype.card ι).choose s.card *
      ((∫ x in {x : {i : ι // i ∈ s} → X | ∀ i, x i ∈ A}, f x ∂(Measure.pi (fun _ : {i : ι // i ∈ s} => μ))) *
      (∫ x in {x : {i : ι // i ∉ s} → X | ∀ i, x i ∈ B}, g x
        ∂(Measure.pi (fun _ : {i : ι // i ∉ s} => μ)))) ≤
      ∫ x in Ω, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  have hle := setIntegral_mono_on (integrableOn_binary_product μ A B s hf hg)
    (hF.mono_set (hinc s rfl)) (measurableSet_binaryRegion hA hB s) hbound
  rw [setIntegral_binary_product] at hle
  exact (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)).trans
    (integral_lower_binary_assignments μ hA hB hd s hF hF0 hsym hinc)

omit [MeasurableSpace X] [Fintype ι] [DecidableEq ι] in

theorem binomial_factorial_cancel {n k : ℕ} (hk : k ≤ n) {a b I : ℝ}
    (h : (n.choose k : ℝ) * (a * b) ≤ I) :
    (a / (k.factorial : ℝ)) * (b / ((n-k).factorial : ℝ)) ≤ I / (n.factorial : ℝ) := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply (le_div_iff₀ hn).2
  rw [Nat.cast_choose ℝ hk] at h
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

end Assignments

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GeneralLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

section GeneralLabels
variable {ι : Type u_1} [Fintype ι]

theorem measurable_symmetricWeight {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) (β : ℝ) :
    Measurable (fun x : ι → Space => symmetricWeight φ β x) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hm : Measurable (fun x : ι → Space => x ∘ e) := by
    apply Measurable.of_eval
    intro i
    exact measurable_pi_apply (e i)
  have hh := (measurable_boltzmann hφ β (Fintype.card ι)).comp hm
  change Measurable (fun x => boltzmann φ β (x ∘ e)) at hh
  simpa only [boltzmann_eq_symmetricWeight, symmetricWeight_relabel] using hh

theorem symmetricWeight_le_of_stable {φ : ℝ → ℝ} {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (x : ι → Space) :
    symmetricWeight φ β x ≤ Real.exp (β * B * Fintype.card ι) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hh := boltzmann_le_of_stable hβ hstable (x ∘ e)
  simpa only [boltzmann_eq_symmetricWeight, symmetricWeight_relabel] using hh

theorem integrableOn_symmetricWeight {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {Ω : Set (ι → Space)} (hΩ : volume Ω ≠ ⊤) :
    IntegrableOn (fun x : ι → Space => symmetricWeight φ β x) Ω := by
  have : IsFiniteMeasure (volume.restrict Ω) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hΩ⟩
  apply (integrable_const (Real.exp (β * B * Fintype.card ι))).mono'
    (measurable_symmetricWeight hφ β).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (symmetricWeight_nonneg φ β x)]
  exact symmetricWeight_le_of_stable hβ hstable x

theorem generalPartition_nonneg (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) :
    0 ≤ generalPartition φ β A ι := by
  apply div_nonneg
  · apply integral_nonneg
    exact symmetricWeight_nonneg φ β
  · positivity

theorem generalPartition_eq_partition (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) :
    generalPartition φ β (cube L) (Fin N) = partition φ β L N := by
  classical
  by_cases hN : N = 0
  · subst N
    have hinj (x : Fin 0 → Space) : Function.Injective x := Function.injective_of_subsingleton x
    have hv : volume.real (Set.univ : Set (Fin 0 → Space)) = 1 := by
      simp [Measure.real, volume_pi]
    simp [generalPartition, partition, symmetricWeight, realPairEnergy, hinj, hv]
  · simp only [generalPartition, partition, hN, ite_false, Fintype.card_fin,
      ← boltzmann_eq_symmetricWeight, div_eq_mul_inv, one_mul]
    ring

theorem volume_generalConfigurations (A : Set Space) :
    volume {x : ι → Space | ∀ i, x i ∈ A} = (volume A) ^ Fintype.card ι := by
  have heq : {x : ι → Space | ∀ i, x i ∈ A} = Set.univ.pi (fun _ : ι => A) := by
    ext x
    simp
  rw [heq, volume_pi_pi]
  simp

theorem generalPartition_binary_lower [DecidableEq ι] {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B₀ : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B₀ * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {A B C : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : volume C ≠ ⊤) (hd : Disjoint A B) (haC : A ⊆ C) (hbC : B ⊆ C)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, φ ‖a - b‖ ≤ 0)
    (s : Finset ι) :
    generalPartition φ β A {i : ι // i ∈ s} *
      generalPartition φ β B {i : ι // i ∉ s} ≤ generalPartition φ β C ι := by
  classical
  have hΩ : volume {x : ι → Space | ∀ i, x i ∈ C} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hC
  have hmA : volume A ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono haC)
  have hmB : volume B ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono hbC)
  have hΩA : volume {x : {i : ι // i ∈ s} → Space | ∀ i, x i ∈ A} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hmA
  have hΩB : volume {x : {i : ι // i ∉ s} → Space | ∀ i, x i ∈ B} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hmB
  have hInt := integral_lower_separated_product volume hA hB hd s
    (integrableOn_symmetricWeight hφ hβ hstable hΩ)
    (symmetricWeight_nonneg φ β)
    (symmetricWeight_relabel φ β)
    (fun t _ x hx i => by
      by_cases hi : i ∈ t
      · exact haC (by simpa only [ite_eq_left hi] using hx i)
      · exact hbC (by simpa only [ite_eq_right hi] using hx i))
    (integrableOn_symmetricWeight hφ hβ hstable hΩA)
    (integrableOn_symmetricWeight hφ hβ hstable hΩB)
    (fun x hx => by
      have hh := symmetricWeight_separated φ hβ (fun i => i ∈ s) hd hcross x
        (fun i hi => by simpa only [ite_eq_left hi] using hx i)
        (fun i hi => by simpa only [ite_eq_right hi] using hx i)
      have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s :=
        Subsingleton.elim _ _
      rw [hfi] at hh
      exact hh)
  have hh := binomial_factorial_cancel (Finset.card_le_univ s) hInt
  simpa only [generalPartition, Fintype.card_subtype_compl,
    Fintype.card_coe, volume_pi] using hh

end GeneralLabels

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TrialConfigurations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable section

theorem trialBall_coord {q : ℝ} {i : Lattice} {x : Space} (hx : x ∈ trialBall q i)
    (k : Fin 3) : |x k - q * (i k : ℝ)| < q / 8 := by
  have hh := PiLp.norm_apply_le (x - gridPoint q i) k
  have hd : ‖x - gridPoint q i‖ < q / 8 := by
    simpa only [trialBall, Metric.mem_ball, dist_eq_norm] using hx
  have hc : |x k - q * (i k : ℝ)| ≤ ‖x - gridPoint q i‖ := by
    simpa [gridPoint] using hh
  exact hc.trans_lt hd

theorem trialBall_separation {q : ℝ} (hq : 0 < q) {i j : Lattice} (hij : i ≠ j)
    {x y : Space} (hx : x ∈ trialBall q i) (hy : y ∈ trialBall q j) :
    3 * q / 4 < ‖x - y‖ := by
  obtain ⟨k, hk⟩ : ∃ k, i k ≠ j k := by
    by_contra! h
    exact hij (funext h)
  have hxk := trialBall_coord hx k
  have hyk := trialBall_coord hy k
  have hc : |x k - y k| ≤ ‖x - y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) k
  rw [abs_lt] at hxk hyk
  rw [abs_le] at hc
  rcases lt_or_gt_of_ne hk with h | h
  · have hh : (i k : ℝ) + 1 ≤ (j k : ℝ) := by exact_mod_cast h
    nlinarith
  · have hh : (j k : ℝ) + 1 ≤ (i k : ℝ) := by exact_mod_cast h
    nlinarith

theorem trialBall_disjoint {q : ℝ} (hq : 0 < q) :
    Pairwise (fun i j : Lattice => Disjoint (trialBall q i) (trialBall q j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hh := trialBall_separation hq hij hi hj
  simp only [sub_self, norm_zero] at hh
  linarith

theorem mem_gridNeighbors_iff {q : ℝ} {i j : Lattice} :
    j ∈ gridNeighbors q i ↔ ∀ k, |j k - i k| ≤ gridRadius q := by
  simp only [gridNeighbors, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  constructor <;> intro h k <;> have hh := h k <;> constructor <;> omega

theorem trialBall_close_mem {q : ℝ} (hq : 0 < q) {i j : Lattice} {x y : Space}
    (hx : x ∈ trialBall q i) (hy : y ∈ trialBall q j) (hxy : ‖x-y‖ < 1) :
    j ∈ gridNeighbors q i := by
  rw [mem_gridNeighbors_iff]
  intro k
  have hxk := trialBall_coord hx k
  have hyk := trialBall_coord hy k
  have hn : |x k - y k| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) k
  have hc : |x k - y k| < 1 := hn.trans_lt hxy
  have hceil : q⁻¹ + 1 ≤ (gridRadius q : ℝ) := Int.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hceil hq.le
  have hcancel : q * (q⁻¹ + 1) = 1 + q := by field_simp
  rw [hcancel] at hmul
  have hh : |((j k : ℤ) : ℝ) - (i k : ℝ)| ≤ (gridRadius q : ℝ) := by
    rw [abs_lt] at hxk hyk hc
    rw [abs_le]
    constructor <;> nlinarith
  exact_mod_cast hh

theorem gridRadius_nonneg {q : ℝ} (hq : 0 < q) : 0 ≤ gridRadius q := by
  exact Int.ceil_nonneg (by positivity)

theorem card_gridNeighbors {q : ℝ} (hq : 0 < q) (i : Lattice) :
    (gridNeighbors q i).card = (2 * (gridRadius q).toNat + 1) ^ 3 := by
  have hr := gridRadius_nonneg hq
  simp only [gridNeighbors, Fintype.card_piFinset, Int.card_Icc]
  have hh (k : Fin 3) : (i k + gridRadius q + 1 - (i k - gridRadius q)).toNat =
      2 * (gridRadius q).toNat + 1 := by omega
  simp only [hh, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem grid_close_card_le {ι : Type u_1} [Fintype ι] {q : ℝ} (hq : 0 < q)
    (f : ι → Lattice) (hf : Function.Injective f) (x : ι → Space)
    (hx : ∀ i, x i ∈ trialBall q (f i)) (i : ι) :
    ((Finset.univ.filter fun j => ‖x i - x j‖ < 1).card : ℕ) ≤
      (2 * (gridRadius q).toNat + 1)^3 := by
  classical
  rw [← card_gridNeighbors hq (f i)]
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    exact trialBall_close_mem hq (hx i) (hx j) (Finset.mem_filter.mp hj).2
  · exact hf.injOn

theorem trialEnergyConstant_nonneg (t q : ℝ) : 0 ≤ trialEnergyConstant t q := by
  unfold trialEnergyConstant
  positivity

theorem trial_core_row_le {ι : Type u_1} [Fintype ι] [DecidableEq ι] {q t : ℝ} (hq : 0 < q) (ht : 1 < t)
    (f : ι → Lattice) (hf : Function.Injective f) (x : ι → Space)
    (hx : ∀ i, x i ∈ trialBall q (f i)) (i : ι) :
    ∑ j, (if i = j then 0 else coreProfile t ‖x i-x j‖) ≤ trialEnergyConstant t q := by
  classical
  let C := t^2 + (Real.exp (-t) / (3*q/4))^12
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : (∑ j, (if i = j then 0 else coreProfile t ‖x i-x j‖)) ≤
      ∑ j, (if ‖x i-x j‖ < 1 then C else 0) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · simp only [ite_eq_left hij]
      split_ifs <;> positivity
    · rw [ite_eq_right hij]
      by_cases hdist : ‖x i-x j‖ < 1
      · rw [ite_eq_left hdist]
        exact coreProfile_le (by linarith : 0 < 3*q/4)
          (trialBall_separation hq (fun h => hij (hf h)) (hx i) (hx j)).le t
      · rw [ite_eq_right hdist, coreProfile_eq_zero ht (le_of_not_gt hdist)]
  have hh := grid_close_card_le hq f hf x hx i
  have hcard : ((Finset.univ.filter fun j => ‖x i - x j‖ < 1).card : ℝ) ≤
      (2 * (gridRadius q).toNat + 1 : ℝ)^3 := by exact_mod_cast hh
  calc
    _ ≤ _ := hsum
    _ = ((Finset.univ.filter fun j => ‖x i - x j‖ < 1).card : ℝ) * C := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (2 * (gridRadius q).toNat + 1 : ℝ)^3 * C := mul_le_mul_of_nonneg_right hcard hC
    _ = trialEnergyConstant t q := rfl

theorem interiorGrid_ball_subset {q L : ℝ} (hq : 0 < q) (hL : 2*q ≤ L)
    {i : Lattice} (hi : i ∈ interiorGrid q L) : trialBall q i ⊆ cube L := by
  intro x hx k
  have hk : -(⌊L/(2*q)-1⌋₊ : ℤ) ≤ i k ∧ i k ≤ (⌊L/(2*q)-1⌋₊ : ℤ) := by
    have hh : ∀ k, -(⌊L/(2*q)-1⌋₊ : ℤ) ≤ i k ∧ i k ≤ (⌊L/(2*q)-1⌋₊ : ℤ) := by
      simpa only [interiorGrid, Fintype.mem_piFinset, Finset.mem_Icc] using hi
    exact hh k
  have hk1 : -(⌊L/(2*q)-1⌋₊ : ℝ) ≤ (i k : ℝ) := by exact_mod_cast hk.1
  have hk2 : (i k : ℝ) ≤ (⌊L/(2*q)-1⌋₊ : ℝ) := by exact_mod_cast hk.2
  have hnonneg : 0 ≤ L/(2*q)-1 := by
    have : 1 ≤ L/(2*q) := (le_div_iff₀ (by positivity)).2 (by nlinarith)
    linarith
  have hn := Nat.floor_le hnonneg
  have heq : (L/(2*q)-1)*(2*q) = L-2*q := by field_simp
  have hmul := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ 2*q)
  rw [heq] at hmul
  have hxk := trialBall_coord hx k
  rw [abs_lt] at hxk
  constructor <;> nlinarith

theorem card_interiorGrid (q L : ℝ) :
    (interiorGrid q L).card = (2*⌊L/(2*q)-1⌋₊+1)^3 := by
  simp only [interiorGrid, Fintype.card_piFinset, Int.card_Icc]
  have hh : ((⌊L/(2*q)-1⌋₊ : ℤ) + 1 - -(⌊L/(2*q)-1⌋₊ : ℤ)).toNat =
      2*⌊L/(2*q)-1⌋₊+1 := by omega
  simp only [hh, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_interiorGrid_lower {q L : ℝ} (hq : 0 < q) (hL : 8*q ≤ L) :
    (L/(2*q))^3 ≤ ((interiorGrid q L).card : ℝ) := by
  rw [card_interiorGrid]
  push_cast
  have hh := Nat.lt_floor_add_one (L/(2*q)-1)
  have heq : (L/(2*q))*(2*q) = L := by field_simp
  have hmul := mul_lt_mul_of_pos_right hh (by positivity : 0 < 2*q)
  have hL0 : 0 ≤ L := by linarith
  have hden : 0 ≤ L/(2*q) := div_nonneg hL0 (by positivity)
  have hle : L/(2*q) ≤ 2*(⌊L/(2*q)-1⌋₊ : ℝ)+1 := by nlinarith
  exact pow_le_pow_left₀ hden hle 3

theorem exists_trial_sites {q L D : ℝ} (hq : 0 < q) (hL : 8*q ≤ L)
    (hD : D ≤ (2*q)⁻¹ ^ 3) {N : ℕ} (hN : (N : ℝ) ≤ D*L^3) :
    ∃ f : Fin N → Lattice, Function.Injective f ∧
      ∀ i, trialBall q (f i) ⊆ cube L := by
  have hL0 : 0 ≤ L := by linarith
  have hc : (N : ℝ) ≤ ((interiorGrid q L).card : ℝ) := calc
    _ ≤ D*L^3 := hN
    _ ≤ (2*q)⁻¹ ^ 3 * L^3 := mul_le_mul_of_nonneg_right hD (by positivity)
    _ = (L/(2*q))^3 := by ring
    _ ≤ _ := card_interiorGrid_lower hq hL
  have hcard : Fintype.card (Fin N) ≤ Fintype.card (interiorGrid q L) := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (show N ≤ (interiorGrid q L).card by exact_mod_cast hc)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  intro i
  exact interiorGrid_ball_subset hq (by linarith) (e i).property

theorem trialVolume_pos {q : ℝ} (hq : 0 < q) : 0 < trialVolume q := by
  unfold trialVolume
  positivity

theorem real_volume_trialBall {q : ℝ} (hq : 0 < q) (i : Lattice) :
    (volume (trialBall q i)).toReal = trialVolume q := by
  simp only [trialBall, EuclideanSpace.volume_ball_fin_three, trialVolume,
    ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ q/8),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]

theorem symmetricWeight_grid_lower {ι : Type u_1} [Fintype ι] {q t β : ℝ}
    (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β) {φ : ℝ → ℝ}
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (f : ι → Lattice) (hf : Function.Injective f) (x : ι → Space)
    (hx : ∀ i, x i ∈ trialBall q (f i)) :
    Real.exp (-β * (trialEnergyConstant t q * Fintype.card ι)) ≤ symmetricWeight φ β x := by
  classical
  have hdist (i j : ι) (hij : i ≠ j) : 0 < ‖x i-x j‖ :=
    lt_trans (by linarith) (trialBall_separation hq (fun h => hij (hf h)) (hx i) (hx j))
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    have hh := hdist i j hne
    simp only [hij, sub_self, norm_zero, lt_self_iff_false] at hh
  have hrow (i : ι) : (∑ j, if i = j then 0 else φ ‖x i-x j‖) ≤ trialEnergyConstant t q := by
    apply le_trans _ (trial_core_row_le hq ht f hf x hx i)
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · simp only [ite_eq_left hij, le_refl]
    · simp only [ite_eq_right hij]
      exact hcore _ (hdist i j hij)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  have hsum' : (∑ i, ∑ j, if i = j then 0 else φ ‖x i-x j‖) ≤
      trialEnergyConstant t q * (Fintype.card ι : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hsum
  have hpos : 0 ≤ trialEnergyConstant t q * (Fintype.card ι : ℝ) :=
    mul_nonneg (trialEnergyConstant_nonneg t q) (Nat.cast_nonneg _)
  have he : realPairEnergy φ x ≤ trialEnergyConstant t q * Fintype.card ι := by
    unfold realPairEnergy
    nlinarith only [hsum', hpos]
  rw [symmetricWeight, ite_eq_left hinj]
  apply Real.exp_le_exp.mpr
  nlinarith only [he, hβ]

theorem partition_grid_lower {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {q t β B L : ℝ} (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    {N : ℕ} (f : Fin N → Lattice) (hf : Function.Injective f)
    (hinc : ∀ i, trialBall q (f i) ⊆ cube L) :
    trialVolume q ^ N * Real.exp (-β*(trialEnergyConstant t q * N)) ≤ partition φ β L N := by
  classical
  let Bs := fun i : Fin N => trialBall q (f i)
  have hm : ∀ i, MeasurableSet (Bs i) := fun _ => measurableSet_ball
  have hd : Pairwise (fun i j => Disjoint (Bs i) (Bs j)) :=
    fun _ _ hij => trialBall_disjoint hq (fun h => hij (hf h))
  have hfin : ∀ i, volume (Bs i) ≠ ⊤ := fun _ => measure_ball_ne_top
  have hΩ : volume {x : Fin N → Space | ∀ i, x i ∈ cube L} ≠ ⊤ := by
    exact (isCompact_configurations L N).measure_lt_top.ne
  have hi := integral_lower_of_disjoint_assignments volume hm hd hfin
    (show IntegrableOn (fun x : Fin N → Space => symmetricWeight φ β x)
      {x | ∀ i, x i ∈ cube L} (Measure.pi fun _ => volume) by
      simpa only [← volume_pi] using integrableOn_symmetricWeight hφ hβ hstable hΩ)
    (symmetricWeight_nonneg φ β)
    (fun e x hx i => hinc (e i) (hx i))
    (fun e x hx => symmetricWeight_grid_lower hq ht hβ hcore (f ∘ e)
      (hf.comp e.injective) x hx)
  have hv : (∏ i : Fin N, (volume (Bs i)).toReal) = trialVolume q ^ N := by
    simp only [Bs, real_volume_trialBall hq, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hv, Fintype.card_fin] at hi
  have hn : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [← generalPartition_eq_partition, generalPartition, Fintype.card_fin]
  apply (le_div_iff₀ hn).2
  simpa only [mul_comm, mul_assoc, mul_left_comm, volume_pi] using hi

theorem partition_trial_lower {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {q t β B L D : ℝ} (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (hL : 8*q ≤ L) (hD : D ≤ (2*q)⁻¹ ^ 3) {N : ℕ} (hN : (N : ℝ) ≤ D*L^3) :
    trialVolume q ^ N * Real.exp (-β*(trialEnergyConstant t q * N)) ≤ partition φ β L N := by
  obtain ⟨f, hf, hinc⟩ := exists_trial_sites hq hL hD hN
  exact partition_grid_lower hφ hq ht hβ hstable hcore f hf hinc

end

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.SpatialProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem generalPartition_relabel {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (e : ι ≃ κ) :
    generalPartition φ β A ι = generalPartition φ β A κ := by
  let p : (ι → Space) ≃ᵐ (κ → Space) := MeasurableEquiv.piCongrLeft (fun _ : κ => Space) e
  have hp : MeasurePreserving p volume volume := by
    simpa only [volume_pi] using measurePreserving_piCongrLeft (fun _ : κ => volume) e
  have hpx (x : ι → Space) : p x = x ∘ e.symm := by
    funext i
    simpa only [p, Equiv.apply_symm_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ : κ => Space) x (e.symm i))
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding (symmetricWeight φ β)
    {x : κ → Space | ∀ i, x i ∈ A}
  have hpre : p ⁻¹' {x : κ → Space | ∀ i, x i ∈ A} =
      {x : ι → Space | ∀ i, x i ∈ A} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hpx, Function.comp_apply]
    constructor
    · intro h i
      simpa only [Equiv.symm_apply_apply] using h (e i)
    · intro h i
      exact h (e.symm i)
  rw [hpre] at heq
  simp only [hpx, symmetricWeight_relabel] at heq
  unfold generalPartition
  rw [Fintype.card_congr e, heq]

theorem generalPartition_eq_setPartition {ι : Type u_1} [Fintype ι]
    (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) :
    generalPartition φ β A ι = setPartition φ β A (Fintype.card ι) :=
  generalPartition_relabel φ β A (Fintype.equivFin ι)

theorem setPartition_zero (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) :
    setPartition φ β A 0 = 1 := by
  have hinj (x : Fin 0 → Space) : Function.Injective x := Function.injective_of_subsingleton x
  simp [setPartition, generalPartition, symmetricWeight, realPairEnergy, hinj,
    Measure.real, volume_pi]

theorem setPartition_nonneg (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (N : ℕ) :
    0 ≤ setPartition φ β A N := generalPartition_nonneg φ β A

theorem setPartition_translate (φ : ℝ → ℝ) (β : ℝ) (A : Set Space) (N : ℕ) (a : Space) :
    setPartition φ β ((fun x => x+a) '' A) N = setPartition φ β A N := by
  let p : (Fin N → Space) ≃ᵐ (Fin N → Space) := MeasurableEquiv.addRight (fun _ => a)
  have hp : MeasurePreserving p volume volume := measurePreserving_add_right volume (fun _ => a)
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding (symmetricWeight φ β)
    {x : Fin N → Space | ∀ i, x i ∈ (fun x => x+a) '' A}
  have hpre : p ⁻¹' {x : Fin N → Space | ∀ i, x i ∈ (fun x => x+a) '' A} =
      {x : Fin N → Space | ∀ i, x i ∈ A} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq]
    apply forall_congr'
    intro i
    change x i + a ∈ (fun y => y+a) '' A ↔ x i ∈ A
    simp only [mem_image, add_left_inj, exists_eq_right]
  have hsym (x : Fin N → Space) : symmetricWeight φ β (p x) = symmetricWeight φ β x :=
    symmetricWeight_translate φ β x a
  rw [hpre] at heq
  simp only [hsym] at heq
  simpa only [setPartition, generalPartition, Fintype.card_fin] using
    congrArg (fun z : ℝ => z / (N.factorial : ℝ)) heq.symm

theorem setPartition_binary_lower {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B₀ : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B₀ * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {A B C : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : volume C ≠ ⊤) (hd : Disjoint A B) (haC : A ⊆ C) (hbC : B ⊆ C)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, φ ‖a-b‖ ≤ 0) (n m : ℕ) :
    setPartition φ β A n * setPartition φ β B m ≤ setPartition φ β C (n+m) := by
  classical
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (show n ≤ (Finset.univ : Finset (Fin (n+m))).card by simp)
  have hh := generalPartition_binary_lower hφ hβ hstable hA hB hC hd haC hbC hcross s
  simpa only [generalPartition_eq_setPartition, Fintype.card_coe, Fintype.card_subtype_compl,
    Fintype.card_fin, hs, Nat.add_sub_cancel_left] using hh

theorem setPartition_product_lower {κ : Type u_1} {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B₀ : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B₀ * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (A : κ → Set Space) (n : κ → ℕ) (s : Finset κ)
    (hA : ∀ i ∈ s, MeasurableSet (A i))
    (hd : (s : Set κ).Pairwise (fun i j => Disjoint (A i) (A j)))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, φ ‖a-b‖ ≤ 0)
    {C : Set Space} (hC : volume C ≠ ⊤) (hinc : ∀ i ∈ s, A i ⊆ C) :
    (∏ i ∈ s, setPartition φ β (A i) (n i)) ≤ setPartition φ β C (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty => simp [setPartition_zero]
  | @insert i s hi ih =>
    let U := ⋃ j ∈ s, A j
    have hU : MeasurableSet U := MeasurableSet.biUnion s.finite_toSet.countable (fun j hj =>
      hA j (Finset.mem_insert_of_mem hj))
    have hUC : U ⊆ C := iUnion₂_subset (fun j hj => hinc j (Finset.mem_insert_of_mem hj))
    have hUf : volume U ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono hUC)
    have hsub : ∀ j ∈ s, A j ⊆ U := fun j hj => subset_iUnion₂_of_subset j hj Subset.rfl
    have ih' := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (hd.mono (Finset.subset_insert _ _))
      (fun j hj k hk => hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)) hUf hsub
    have hdis : Disjoint (A i) U := by
      apply Set.disjoint_iUnion₂_right.mpr
      intro j hj
      exact hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))
    have henergy : ∀ a ∈ A i, ∀ b ∈ U, φ ‖a-b‖ ≤ 0 := by
      intro a ha b hb
      obtain ⟨j, hj, hjb⟩ := mem_iUnion₂.mp hb
      exact hcross i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj)) a ha b hjb
    have hbin := setPartition_binary_lower hφ hβ hstable
      (hA i (Finset.mem_insert_self _ _)) hU hC hdis
      (hinc i (Finset.mem_insert_self _ _)) hUC henergy (n i) (∑ j ∈ s, n j)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (mul_le_mul_of_nonneg_left ih' (setPartition_nonneg φ β (A i) (n i))).trans hbin

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.BoxTiling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem isCompact_tileBox (ℓ L : ℝ) {k : ℕ} (i : Fin 3 → Fin k) :
    IsCompact (tileBox ℓ L i) :=
  (isCompact_cube ℓ).image (continuous_id.add continuous_const)

theorem tileBox_subset {ℓ L : ℝ} {k : ℕ} (hℓ : 0 ≤ ℓ)
    (hk : (k : ℝ)*(ℓ+2) ≤ L) (i : Fin 3 → Fin k) : tileBox ℓ L i ⊆ cube L := by
  rintro x ⟨y, hy, rfl⟩ j
  have hyj := hy j
  have hij : (i j : ℝ)+1 ≤ k := by exact_mod_cast (i j).isLt
  have h0 : (0 : ℝ) ≤ (i j : ℝ) := Nat.cast_nonneg _
  change y j + ((ℓ+2)*((i j : ℝ)+1/2)-L/2) ∈ Icc (-L/2) (L/2)
  constructor <;> nlinarith [hyj.1, hyj.2]

theorem tileBox_separation {ℓ L : ℝ} {k : ℕ} (hℓ : 0 ≤ ℓ)
    {i j : Fin 3 → Fin k} (hij : i ≠ j) {x y : Space}
    (hx : x ∈ tileBox ℓ L i) (hy : y ∈ tileBox ℓ L j) : 2 ≤ ‖x-y‖ := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨r, hr⟩ : ∃ r, i r ≠ j r := by
    by_contra! h
    exact hij (funext h)
  have har := ha r
  have hbr := hb r
  have hnorm : |(a+tileCenter ℓ L i) r - (b+tileCenter ℓ L j) r| ≤
      ‖(a+tileCenter ℓ L i)-(b+tileCenter ℓ L j)‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le ((a+tileCenter ℓ L i)-(b+tileCenter ℓ L j)) r
  change |a r + ((ℓ+2)*((i r : ℝ)+1/2)-L/2) -
    (b r + ((ℓ+2)*((j r : ℝ)+1/2)-L/2))| ≤
      ‖(a+tileCenter ℓ L i)-(b+tileCenter ℓ L j)‖ at hnorm
  rw [abs_le] at hnorm
  rcases lt_or_gt_of_ne hr with h | h
  · have hh : (i r : ℝ)+1 ≤ (j r : ℝ) := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ ℓ+2)
    nlinarith [har.1, har.2, hbr.1, hbr.2]
  · have hh : (j r : ℝ)+1 ≤ (i r : ℝ) := by exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ ℓ+2)
    nlinarith [har.1, har.2, hbr.1, hbr.2]

theorem tileBox_pairwiseDisjoint {ℓ L : ℝ} {k : ℕ} (hℓ : 0 ≤ ℓ) :
    Pairwise (fun i j : Fin 3 → Fin k => Disjoint (tileBox ℓ L i) (tileBox ℓ L j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := tileBox_separation hℓ hij hx hy
  simp only [sub_self, norm_zero] at hh
  norm_num at hh

theorem partition_tiling_lower {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B ℓ L : ℝ} (hβ : 0 ≤ β) (hℓ : 0 ≤ ℓ) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hsign : ∀ r, 1 ≤ r → φ r ≤ 0)
    (n : (Fin 3 → Fin ⌊L/(ℓ+2)⌋₊) → ℕ) :
    (∏ i, partition φ β ℓ (n i)) ≤ partition φ β L (∑ i, n i) := by
  classical
  have hden : 0 < ℓ+2 := by linarith
  have hk : (⌊L/(ℓ+2)⌋₊ : ℝ)*(ℓ+2) ≤ L := by
    apply (le_div_iff₀ hden).mp
    exact Nat.floor_le (div_nonneg hL hden.le)
  have hh := setPartition_product_lower hφ hβ hstable (tileBox ℓ L) n Finset.univ
    (fun i _ => (isCompact_tileBox ℓ L i).measurableSet)
    (fun i _ j _ hij => tileBox_pairwiseDisjoint hℓ hij)
    (fun i _ j _ hij a ha b hb => hsign _ (le_trans (by norm_num)
      (tileBox_separation hℓ hij ha hb)))
    (isCompact_cube L).measure_lt_top.ne (fun i _ => tileBox_subset hℓ hk i)
  have hv (i : Fin 3 → Fin ⌊L/(ℓ+2)⌋₊) :
      setPartition φ β (tileBox ℓ L i) (n i) = partition φ β ℓ (n i) := by
    rw [tileBox, setPartition_translate, setPartition, generalPartition_eq_partition]
  simp_rw [hv] at hh
  simpa only [setPartition, generalPartition_eq_partition] using hh

theorem exists_concentrated_counts (K H N : ℕ) (hN : N ≤ K*H) :
    ∃ r : Fin K → ℕ, (∑ i, r i) = N ∧ (∀ i, r i ≤ H) ∧
      (∑ i, if r i = 0 then 0 else 1) * H ≤ N+H := by
  induction K generalizing N with
  | zero =>
    have hzero : N = 0 := by omega
    subst N
    exact ⟨Fin.elim0, by simp, (fun i => Fin.elim0 i), by simp⟩
  | succ K ih =>
    by_cases hh : N ≤ H
    · refine ⟨Fin.cons N (fun _ => 0), ?_, ?_, ?_⟩
      · simp [Fin.sum_univ_succ]
      · intro i
        refine Fin.cases hh (fun _ => Nat.zero_le _) i
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ite_true, Finset.sum_const_zero,
          add_zero]
        split_ifs <;> omega
    · have hHK : N-H ≤ K*H := by
        rw [Nat.succ_mul] at hN
        omega
      obtain ⟨r, hr, hbound, hc⟩ := ih (N-H) hHK
      have hH : 0 < H := by
        by_contra hzero
        have hz : H = 0 := by omega
        simp only [hz, Nat.mul_zero, Nat.le_zero] at hN
        omega
      refine ⟨Fin.cons H r, ?_, ?_, ?_⟩
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hr]
        omega
      · intro i
        exact Fin.cases (le_refl H) hbound i
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ite_eq_right hH.ne']
        have hsub := Nat.sub_add_cancel (show H ≤ N by omega)
        nlinarith

theorem exists_adjusted_counts (K b H N : ℕ) (hb : 0 < b) (hH : 2*b ≤ H)
    (hN : N ≤ K*H) :
    ∃ r : Fin K → ℕ, (∑ i, r i) = N ∧ (∀ i, r i ≤ H) ∧
      ((∑ i, if r i = b then 0 else 1 : ℕ) : ℝ) * b ≤
        |(N : ℝ) - (K : ℝ)*b| + H := by
  have hbH : b ≤ H := by omega
  by_cases hNb : K*b ≤ N
  · have hdel : N-K*b ≤ K*(H-b) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    obtain ⟨d, hsum, hbound, hc⟩ := exists_concentrated_counts K (H-b) (N-K*b) hdel
    refine ⟨fun i => b+d i, ?_, ?_, ?_⟩
    · simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, hsum]
      omega
    · intro i
      change b+d i ≤ H
      have hh := hbound i
      omega
    · have heq : (∑ i, if b+d i = b then 0 else 1 : ℕ) =
          ∑ i, if d i = 0 then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Nat.add_eq_left]
      rw [heq]
      have hineq : (∑ i, if d i = 0 then 0 else 1) * b ≤ (N-K*b)+H := by
        have hh := Nat.mul_le_mul_left (∑ i, if d i = 0 then 0 else 1) (show b ≤ H-b by omega)
        omega
      have hsub : ((N-K*b : ℕ) : ℝ) = (N : ℝ)-(K : ℝ)*b := by
        rw [Nat.cast_sub hNb, Nat.cast_mul]
      have hsgn : 0 ≤ (N : ℝ)-(K : ℝ)*b := by
        have hh : (K : ℝ)*b ≤ (N : ℝ) := by exact_mod_cast hNb
        linarith
      rw [abs_of_nonneg hsgn]
      have hh : ((∑ i, if d i = 0 then 0 else 1 : ℕ) : ℝ)*b ≤ ((N-K*b : ℕ) : ℝ)+H := by
        exact_mod_cast hineq
      rwa [hsub] at hh
  · have hNb' : N ≤ K*b := by omega
    obtain ⟨d, hsum, hbound, hc⟩ := exists_concentrated_counts K b (K*b-N) (Nat.sub_le _ _)
    refine ⟨fun i => b-d i, ?_, ?_, ?_⟩
    · have hh : (∑ i : Fin K, (b - d i)) + (∑ i : Fin K, d i) = K*b := by
        rw [← Finset.sum_add_distrib]
        simp only [Nat.sub_add_cancel (hbound _), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      change (∑ i : Fin K, (b - d i)) = N
      rw [hsum] at hh
      omega
    · intro i
      exact (Nat.sub_le b _).trans hbH
    · have heq : (∑ i, if b-d i = b then 0 else 1 : ℕ) =
          ∑ i, if d i = 0 then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro i _
        have hh : b-d i = b ↔ d i = 0 := by omega
        simp only [hh]
      rw [heq]
      have hineq : (∑ i, if d i = 0 then 0 else 1) * b ≤ (K*b-N)+H := by omega
      have hsub : ((K*b-N : ℕ) : ℝ) = (K : ℝ)*b-N := by
        rw [Nat.cast_sub hNb', Nat.cast_mul]
      have hsgn : (N : ℝ)-(K : ℝ)*b ≤ 0 := by
        have hh : (N : ℝ) ≤ (K : ℝ)*b := by exact_mod_cast hNb'
        linarith
      rw [abs_of_nonpos hsgn]
      have hh : ((∑ i, if d i = 0 then 0 else 1 : ℕ) : ℝ)*b ≤ ((K*b-N : ℕ) : ℝ)+H := by
        exact_mod_cast hineq
      rw [hsub] at hh
      linarith

theorem sum_baseline_le {K b H : ℕ} {r : Fin K → ℕ} {a : ℕ → ℝ} {M : ℝ}
    (hr : ∀ i, r i ≤ H) (ha : ∀ n, n ≤ H → a n ≤ M) (hb : -M ≤ a b) :
    ∑ i, a (r i) ≤ K*a b + 2*M*(∑ i, if r i = b then 0 else 1 : ℕ) := by
  classical
  calc
    ∑ i, a (r i) ≤ ∑ i, (a b + 2*M*(if r i = b then 0 else 1 : ℕ)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hh : r i = b
      · simp [hh]
      · simp only [ite_eq_right hh, Nat.cast_one, mul_one]
        linarith [ha (r i) (hr i)]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, Nat.cast_sum]

theorem adjusted_box_comparison (a : ℝ → ℕ → ℝ) {ℓ L M : ℝ} {b H N : ℕ}
    (hℓ : 0 < ℓ) (hL : 0 < L) (hM : 0 ≤ M) (hb : 0 < b) (hH : 2*b ≤ H)
    (hN : N ≤ tileCount ℓ L * H)
    (hbox : ∀ r : Fin (tileCount ℓ L) → ℕ, (∑ i, r i) = N →
      a L N ≤ ℓ^3/L^3 * ∑ i, a ℓ (r i))
    (hbound : ∀ n, n ≤ H → a ℓ n ≤ M) (hbase : -M ≤ a ℓ b) :
    a L N ≤ ((tileCount ℓ L : ℝ)/L^3)*ℓ^3*a ℓ b +
      (2*M*ℓ^3/(b : ℝ)) * (|(N : ℝ)/L^3 - ((tileCount ℓ L : ℝ)/L^3)*b| + H/L^3) := by
  classical
  obtain ⟨r, hr, hcounts, hchange⟩ := exists_adjusted_counts (tileCount ℓ L) b H N hb hH hN
  have hs := sum_baseline_le hcounts hbound hbase
  have hm : 0 ≤ ℓ^3/L^3 := div_nonneg (pow_nonneg hℓ.le _) (pow_nonneg hL.le _)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hc : (∑ i, if r i = b then 0 else 1 : ℕ) ≤
      (|(N : ℝ) - (tileCount ℓ L : ℝ)*b|+H)/(b : ℝ) :=
    (le_div_iff₀ hbR).2 hchange
  calc
    a L N ≤ ℓ^3/L^3 * ∑ i, a ℓ (r i) := hbox r hr
    _ ≤ ℓ^3/L^3 * ((tileCount ℓ L : ℝ)*a ℓ b +
        2*M*((|(N : ℝ)-(tileCount ℓ L : ℝ)*b|+H)/(b : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hm
      exact hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*M by positivity)))
    _ = _ := by
      have heq : (N : ℝ)/L^3 - ((tileCount ℓ L : ℝ)/L^3)*b =
          ((N : ℝ)-(tileCount ℓ L : ℝ)*b)/L^3 := by ring
      rw [heq, abs_div, abs_of_pos (pow_pos hL 3)]
      ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.DensityLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem densityFilter_length (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => p.1) (densityFilter d) atTop := by
  have h : Tendsto (fun p : ℝ × ℕ => (p.1, (p.2 : ℝ)/p.1^3))
      (densityFilter d) (atTop ×ˢ 𝓝 d) := Filter.tendsto_comap
  simpa only [Function.comp_def] using
    (tendsto_fst : Tendsto (Prod.fst : ℝ × ℝ → ℝ) (atTop ×ˢ 𝓝 d) atTop).comp h

theorem densityFilter_density (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => (p.2 : ℝ)/p.1^3) (densityFilter d) (𝓝 d) :=
  tendsto_snd.comp (Filter.tendsto_comap : Tendsto _ (densityFilter d) _)

theorem tendsto_densityFilter_iff {α : Type u_1} {l : Filter α} {d : ℝ} {p : α → ℝ × ℕ} :
    Tendsto p l (densityFilter d) ↔
      Tendsto (fun x => (p x).1) l atTop ∧
      Tendsto (fun x => ((p x).2 : ℝ)/(p x).1^3) l (𝓝 d) := by
  rw [densityFilter, tendsto_comap_iff, tendsto_prod_iff']
  rfl

theorem floor_density_tendsto {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun L : ℝ => (L, ⌊d*L^3⌋₊)) atTop (densityFilter d) := by
  apply tendsto_densityFilter_iff.2
  exact ⟨tendsto_id, (tendsto_nat_floor_mul_div_atTop hd).comp
    (tendsto_pow_atTop (by norm_num : 3 ≠ 0))⟩

instance densityFilter_neBot (d : ℝ) [Fact (0 ≤ d)] : (densityFilter d).NeBot :=
  (floor_density_tendsto (Fact.out : 0 ≤ d)).neBot

theorem tileCount_asymptotic {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    Tendsto (fun L : ℝ => (tileCount ℓ L : ℝ)/L^3) atTop (𝓝 ((ℓ+2)⁻¹^3)) := by
  have hh : 0 ≤ (ℓ+2)⁻¹ := inv_nonneg.mpr (by linarith)
  have ht := (tendsto_nat_floor_mul_div_atTop hh).pow 3
  simpa only [tileCount, Nat.cast_pow, div_pow, div_eq_mul_inv, mul_comm,
    mul_pow, inv_pow] using ht

theorem length_inv_cube_tendsto (d : ℝ) :
    Tendsto (fun p : ℝ × ℕ => (p.1^3)⁻¹) (densityFilter d) (𝓝 0) := by
  simpa only [Function.comp_def, ← inv_pow, zero_pow (by norm_num : 3 ≠ 0)] using
    (tendsto_inv_atTop_zero.pow 3).comp (densityFilter_length d)

theorem density_eventually_bounded {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    {d : ℝ} (hd : 0 ≤ d) :
    ∃ M : ℝ, ∀ᶠ p in densityFilter d, |a p.1 p.2| ≤ M := by
  obtain ⟨M, R, -, hR, hb⟩ := ha (d+1) (by linarith)
  refine ⟨M, ?_⟩
  filter_upwards [(densityFilter_length d).eventually (eventually_ge_atTop R),
    (densityFilter_density d).eventually (eventually_le_nhds (by linarith : d < d+1))] with p hp hpd
  exact hb p.1 hp p.2 ((div_le_iff₀ (pow_pos (hR.trans_le hp) 3)).1 hpd)

theorem densityFilter_bounded {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    {d : ℝ} (hd : 0 ≤ d) :
    (densityFilter d).IsBoundedUnder (· ≤ ·) (fun p => a p.1 p.2) ∧
    (densityFilter d).IsBoundedUnder (· ≥ ·) (fun p => a p.1 p.2) := by
  obtain ⟨M, hM⟩ := density_eventually_bounded ha hd
  exact ⟨⟨M, hM.mono (fun _ h => (abs_le.mp h).2)⟩,
    ⟨-M, hM.mono (fun _ h => (abs_le.mp h).1)⟩⟩

theorem limsup_box_comparison {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    (hbox : HasBoxInequality a) {d ℓ M : ℝ} {b H : ℕ}
    (hd : 0 ≤ d) (hℓ : 0 < ℓ) (hM : 0 ≤ M) (hb : 0 < b) (hH : 2*b ≤ H)
    (hcap : d < (ℓ+2)⁻¹^3 * H)
    (hbound : ∀ n, n ≤ H → a ℓ n ≤ M) (hbase : -M ≤ a ℓ b) :
    limsup (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d) ≤
      (ℓ+2)⁻¹^3 * ℓ^3 * a ℓ b + (2*M*ℓ^3/(b : ℝ)) * |d-(ℓ+2)⁻¹^3*b| := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  have ht := (tileCount_asymptotic hℓ.le).comp (densityFilter_length d)
  have hcap' := (densityFilter_density d).eventually_lt (ht.mul_const (H : ℝ)) hcap
  have hcomp : (fun p : ℝ × ℕ => a p.1 p.2) ≤ᶠ[densityFilter d]
      (fun p : ℝ × ℕ => ((tileCount ℓ p.1 : ℝ)/p.1^3)*ℓ^3*a ℓ b +
        (2*M*ℓ^3/(b : ℝ)) * (|(p.2 : ℝ)/p.1^3 - ((tileCount ℓ p.1 : ℝ)/p.1^3)*b| + H/p.1^3)) := by
    filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0), hcap'] with p hp hc
    have hnc : p.2 ≤ tileCount ℓ p.1 * H := by
      have hh : (p.2 : ℝ) < (tileCount ℓ p.1 : ℝ)*H := by
        apply (div_lt_div_iff_of_pos_right (pow_pos hp 3)).mp
        simpa only [div_mul_eq_mul_div, Function.comp_def] using hc
      exact_mod_cast hh.le
    exact adjusted_box_comparison a hℓ hp hM hb hH hnc
      (fun r hr => hr ▸ hbox ℓ p.1 hℓ hp r) hbound hbase
  have htail : Tendsto (fun p : ℝ × ℕ => (H : ℝ)/p.1^3) (densityFilter d) (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (length_inv_cube_tendsto d).const_mul (H : ℝ)
  have hlim := ((ht.mul_const (ℓ^3)).mul_const (a ℓ b)).add
    ((((densityFilter_density d).sub (ht.mul_const (b : ℝ))).abs.add htail).const_mul (2*M*ℓ^3/(b : ℝ)))
  simp only [add_zero, Function.comp_def] at hlim
  have hle := limsup_le_limsup hcomp (densityFilter_bounded ha hd).2.isCobounded_le hlim.isBoundedUnder_le
  rwa [hlim.limsup_eq] at hle

 theorem dilution_tendsto_one :
    Tendsto (fun L : ℝ => (L+2)⁻¹^3*L^3) atTop (𝓝 1) := by
  have hh : Tendsto (fun L : ℝ => 1/(1+2*L⁻¹)) atTop (𝓝 1) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).div
      (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul 2))
        (by norm_num : (1 : ℝ)+2*0 ≠ 0))
    change Tendsto (fun L : ℝ => 1/(1+2*L⁻¹)) atTop (𝓝 (1/(1+2*0))) at hh
    simpa only [mul_zero, add_zero, div_one] using hh
  have hpow : Tendsto (fun L : ℝ => (1/(1+2*L⁻¹))^3) atTop (𝓝 1) := by
    simpa only [one_pow] using hh.pow 3
  apply hpow.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have h1 : 1+2*L⁻¹ ≠ 0 := by positivity
  have h2 : L+2 ≠ 0 := by linarith
  field_simp

theorem exists_density_limit {a : ℝ → ℕ → ℝ} (ha : DensityBounded a)
    (hbox : HasBoxInequality a) {d : ℝ} (hd : 0 < d) :
    ∃ I : ℝ, Tendsto (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d) (𝓝 I) := by
  let : Fact (0 ≤ d) := ⟨hd.le⟩
  obtain ⟨hbup, hbdown⟩ := densityFilter_bounded ha hd.le
  obtain ⟨p, hpA, hp⟩ := exists_seq_tendsto_liminf hbup.isCobounded_ge hbdown
  obtain ⟨hpL, hpd⟩ := tendsto_densityFilter_iff.mp hp
  let D : ℝ := 4*d+4
  have hD : 0 < D := by dsimp [D]; linarith
  obtain ⟨M, R, hM, hR, hbound⟩ := ha D hD
  let H : ℕ → ℕ := fun j => ⌊D*(p j).1^3⌋₊
  have hα : Tendsto (fun j => ((p j).1+2)⁻¹^3*(p j).1^3) atTop (𝓝 1) := by
    simpa only [Function.comp_def] using dilution_tendsto_one.comp hpL
  have hHratio : Tendsto (fun j => (H j : ℝ)/(p j).1^3) atTop (𝓝 D) := by
    exact (tendsto_nat_floor_mul_div_atTop hD.le).comp
      ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp hpL)
  have hbd : Tendsto (fun j => ((p j).1+2)⁻¹^3*((p j).2 : ℝ)) atTop (𝓝 d) := by
    have hh : Tendsto (fun j => (((p j).1+2)⁻¹^3*(p j).1^3)*
        ((p j).2 : ℝ)/(p j).1^3) atTop (𝓝 d) := by
      simpa only [one_mul, mul_div_assoc] using hα.mul hpd
    apply hh.congr'
    filter_upwards [hpL.eventually (eventually_gt_atTop 0)] with j hj
    field_simp
  have hHd : Tendsto (fun j => ((p j).1+2)⁻¹^3*(H j : ℝ)) atTop (𝓝 D) := by
    have hh := hα.mul hHratio
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [hpL.eventually (eventually_gt_atTop 0)] with j hj
    field_simp
  have hcoef : Tendsto (fun j => 2*M*(p j).1^3/((p j).2 : ℝ)) atTop (𝓝 (2*M/d)) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2*M) atTop (𝓝 (2*M))).div hpd hd.ne'
    change Tendsto (fun j => (2*M)/(((p j).2 : ℝ)/(p j).1^3)) atTop (𝓝 (2*M/d)) at hh
    simpa only [div_div_eq_mul_div] using hh
  have hfit : ∀ᶠ j in atTop, 2*(p j).2 ≤ H j := by
    have hh := (hpd.const_mul 2).eventually_lt hHratio (show 2*d < D by dsimp [D]; linarith)
    filter_upwards [hh, hpL.eventually (eventually_gt_atTop 0)] with j hj hL
    have hh' : (2 : ℝ)*(p j).2 < H j := by
      apply (div_lt_div_iff_of_pos_right (pow_pos hL 3)).mp
      simpa only [mul_div_assoc] using hj
    exact_mod_cast hh'.le
  have hpositive : ∀ᶠ j in atTop, 0 < (p j).2 := by
    filter_upwards [hpd.eventually (eventually_gt_nhds hd),
      hpL.eventually (eventually_gt_atTop 0)] with j hj hL
    have hh : (0 : ℝ) < (p j).2 := (div_pos_iff_of_pos_right (pow_pos hL 3)).1 hj
    exact_mod_cast hh
  have hcomp : ∀ᶠ j in atTop,
      limsup (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d) ≤
        ((p j).1+2)⁻¹^3 * (p j).1^3 * a (p j).1 (p j).2 +
        (2*M*(p j).1^3/((p j).2 : ℝ)) * |d-((p j).1+2)⁻¹^3*(p j).2| := by
    filter_upwards [hpL.eventually (eventually_ge_atTop R), hfit, hpositive,
      hHd.eventually (eventually_gt_nhds (show d < D by dsimp [D]; linarith))] with j hL hfit hb hcap
    have hLpos := hR.trans_le hL
    have hHle : (H j : ℝ) ≤ D*(p j).1^3 := Nat.floor_le (by positivity)
    apply limsup_box_comparison ha hbox hd.le hLpos hM.le hb hfit hcap
    · intro n hn
      exact (abs_le.mp (hbound (p j).1 hL n ((by exact_mod_cast hn : (n : ℝ) ≤ H j).trans hHle))).2
    · have hn : (p j).2 ≤ H j := by omega
      exact (abs_le.mp (hbound (p j).1 hL (p j).2
        ((by exact_mod_cast hn : ((p j).2 : ℝ) ≤ H j).trans hHle))).1
  have hlim := (hα.mul hpA).add (hcoef.mul (((tendsto_const_nhds (x := d)).sub hbd).abs))
  simp only [one_mul, sub_self, abs_zero, mul_zero, add_zero, Function.comp_def] at hlim
  have hle := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hcomp
  exact ⟨liminf (fun p : ℝ × ℕ => a p.1 p.2) (densityFilter d),
    tendsto_of_le_liminf_of_limsup_le le_rfl hle hbup hbdown⟩

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CanonicalLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem finiteCanonical_lower_constant {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    -Real.exp (β*B) ≤ finiteCanonical φ β L N := by
  have hc := (summable_grandPartition hφ hβ hL.le hstable 1 0).le_tsum N
    (fun n _ => mul_nonneg (Real.exp_pos _).le (partition_nonneg φ β L n))
  have hc' : partition φ β L N ≤ grandPartition φ 1 β 0 L := by
    simpa only [mul_zero, zero_mul, Real.exp_zero, one_mul, grandPartition] using hc
  have hZ := hc'.trans (grandPartition_le_exp hφ hβ hL.le hstable 1 0)
  simp only [mul_zero, zero_add] at hZ
  have hlog := Real.log_le_log (partition_pos hφ hβ hL hstable N) hZ
  rw [Real.log_exp] at hlog
  unfold finiteCanonical
  apply (le_div_iff₀ (pow_pos hL 3)).2
  nlinarith only [hlog]

theorem finiteCanonical_upper_trial {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {q t β B L D : ℝ} (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (hL : 8*q ≤ L) (hD : D ≤ (2*q)⁻¹^3) {N : ℕ} (hN : (N : ℝ) ≤ D*L^3) :
    finiteCanonical φ β L N ≤ (β*trialEnergyConstant t q-Real.log (trialVolume q)) * (N : ℝ)/L^3 := by
  have hpos : 0 < trialVolume q ^ N * Real.exp (-β*(trialEnergyConstant t q*N)) := by
    exact mul_pos (pow_pos (trialVolume_pos hq) N) (Real.exp_pos _)
  have hlow := partition_trial_lower hφ hq ht hβ hstable hcore hL hD hN
  have hlog := Real.log_le_log hpos hlow
  rw [Real.log_mul (pow_pos (trialVolume_pos hq) N).ne' (Real.exp_pos _).ne',
    Real.log_pow, Real.log_exp] at hlog
  unfold finiteCanonical
  apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith : 0 ≤ L) 3)
  nlinarith only [hlog]

theorem finiteCanonical_densityBounded {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    DensityBounded (finiteCanonical φ β) := by
  intro D hD
  let q : ℝ := (2*(D+1))⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hdmesh : D ≤ (2*q)⁻¹^3 := by
    have hh : (2*q)⁻¹ = D+1 := by dsimp [q]; field_simp
    rw [hh]
    nlinarith [sq_nonneg D]
  let C : ℝ := |β*trialEnergyConstant t q-Real.log (trialVolume q)|
  refine ⟨Real.exp (β*B)+C*D+1, 8*q, by dsimp [C]; positivity, by positivity, ?_⟩
  intro L hL N hN
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hlo := finiteCanonical_lower_constant hφ hβ hLpos hstable N
  have hup := finiteCanonical_upper_trial hφ hq ht hβ hstable hcore hL hdmesh hN
  have hup' : finiteCanonical φ β L N ≤ C*D := by
    calc
      _ ≤ (β*trialEnergyConstant t q-Real.log (trialVolume q)) * ((N : ℝ)/L^3) := by
        simpa only [mul_div_assoc] using hup
      _ ≤ C*((N : ℝ)/L^3) := mul_le_mul_of_nonneg_right (le_abs_self _)
        (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hLpos.le 3))
      _ ≤ C*D := mul_le_mul_of_nonneg_left ((div_le_iff₀ (pow_pos hLpos 3)).2 hN) (abs_nonneg _)
  apply abs_le.mpr
  have hCD : 0 ≤ C*D := mul_nonneg (abs_nonneg _) hD.le
  have he := (Real.exp_pos (β*B)).le
  constructor <;> linarith

theorem finiteCanonical_hasBoxInequality {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hsign : ∀ r, 1 ≤ r → φ r ≤ 0) : HasBoxInequality (finiteCanonical φ β) := by
  intro ℓ L hℓ hL r
  classical
  let e : (Fin 3 → Fin ⌊L/(ℓ+2)⌋₊) ≃ Fin (tileCount ℓ L) :=
    Fintype.equivFinOfCardEq (by simp [tileCount])
  have htile := partition_tiling_lower hφ hβ hℓ.le hL.le hstable hsign (fun i => r (e i))
  rw [e.sum_comp] at htile
  have hprod := e.prod_comp (fun i => partition φ β ℓ (r i))
  rw [hprod] at htile
  have hlog := Real.log_le_log (Finset.prod_pos (fun i _ => partition_pos hφ hβ hℓ hstable (r i))) htile
  rw [Real.log_prod (fun i _ => (partition_pos hφ hβ hℓ hstable (r i)).ne')] at hlog
  unfold finiteCanonical
  calc
    -Real.log (partition φ β L (∑ i, r i))/L^3 ≤ -(∑ i, Real.log (partition φ β ℓ (r i)))/L^3 :=
      div_le_div_of_nonneg_right (neg_le_neg hlog) (pow_nonneg hL.le 3)
    _ = ℓ^3/L^3 * ∑ i, -Real.log (partition φ β ℓ (r i))/ℓ^3 := by
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
      field_simp

theorem exists_canonical_density_limit {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) {d : ℝ} (hd : 0 < d) :
    ∃ I : ℝ, Tendsto (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2) (densityFilter d) (𝓝 I) := by
  apply exists_density_limit (finiteCanonical_densityBounded hφ ht hβ hstable hcore)
    (finiteCanonical_hasBoxInequality hφ hβ hstable _) hd
  intro r hr
  exact (hcore r (lt_of_lt_of_le (by norm_num) hr)).trans_eq (coreProfile_eq_zero ht hr)

theorem finiteCanonical_lower_entropy {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    -β * B * ((N : ℝ) / L ^ 3) + ((N : ℝ) / L ^ 3) * Real.log ((N : ℝ) / L ^ 3)
      - (N : ℝ) / L ^ 3 ≤ finiteCanonical φ β L N := by
  by_cases hN : N = 0
  · simp [hN]
  have hh := neg_log_partition_lower hφ hβ hL hstable hN
    (fun x _ => hstable N x)
  have hh' := div_le_div_of_nonneg_right hh (pow_pos hL 3).le
  unfold finiteCanonical
  calc
    _ = (β * (-B * (N : ℝ)) + N * Real.log ((N : ℝ) / L ^ 3) - N) / L ^ 3 := by ring
    _ ≤ _ := hh'

theorem finiteCanonical_tendsto_zero_density {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    Tendsto (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2) (densityFilter 0) (𝓝 0) := by
  have hden := densityFilter_density 0
  have hlo : Tendsto (fun p : ℝ × ℕ =>
      -β * B * ((p.2 : ℝ) / p.1 ^ 3) + ((p.2 : ℝ) / p.1 ^ 3) *
        Real.log ((p.2 : ℝ) / p.1 ^ 3) - (p.2 : ℝ) / p.1 ^ 3)
      (densityFilter 0) (𝓝 0) := by
    simpa only [mul_zero, Real.log_zero, add_zero, sub_zero, Function.comp_def] using
      ((hden.const_mul (-β * B)).add (Real.continuous_mul_log.tendsto 0 |>.comp hden)).sub hden
  let C := β * trialEnergyConstant t (1/2) - Real.log (trialVolume (1/2))
  have hup : Tendsto (fun p : ℝ × ℕ => C * ((p.2 : ℝ) / p.1 ^ 3))
      (densityFilter 0) (𝓝 0) := by
    simpa only [mul_zero] using hden.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [(densityFilter_length 0).eventually (eventually_gt_atTop 0)] with p hp
    exact finiteCanonical_lower_entropy hφ hβ hp hstable p.2
  · filter_upwards [(densityFilter_length 0).eventually (eventually_ge_atTop 4),
      hden.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with p hp hpd
    have hL : 0 < p.1 := by linarith
    have hh := finiteCanonical_upper_trial hφ (by norm_num : (0 : ℝ) < 1 / 2)
      ht hβ hstable hcore (by linarith : 8*(1/2 : ℝ) ≤ p.1)
      (by norm_num : (1 : ℝ) ≤ (2*(1/2))⁻¹^3)
      ((div_le_iff₀ (pow_pos hL 3)).1 hpd)
    simpa only [C, mul_div_assoc] using hh

theorem finiteCanonical_tendsto {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    Tendsto (fun p : ℝ × ℕ => finiteCanonical φ β p.1 p.2)
      (densityFilter d) (𝓝 (canonicalDensity φ β d)) := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  obtain hzero | hpos := hd.eq_or_lt
  · subst d
    have hz := finiteCanonical_tendsto_zero_density hφ ht hβ hstable hcore
    simpa only [canonicalDensity, hz.liminf_eq] using hz
  · obtain ⟨I, hI⟩ := exists_canonical_density_limit hφ ht hβ hstable hcore hpos
    simpa only [canonicalDensity, hI.liminf_eq] using hI

@[simp] theorem canonicalDensity_zero {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) : canonicalDensity φ β 0 = 0 := by
  let : Fact (0 ≤ (0 : ℝ)) := ⟨le_rfl⟩
  exact (finiteCanonical_tendsto_zero_density hφ ht hβ hstable hcore).liminf_eq

theorem hasCanonicalFreeEnergy_of_core {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    HasCanonicalFreeEnergy φ (canonicalFreeEnergy φ) := by
  intro β d hβ hd
  have hlim := (finiteCanonical_tendsto hφ ht hβ.le hstable hcore hd.le).comp
    (floor_density_tendsto hd.le)
  have hneg := hlim.neg
  convert hneg using 1
  · ext L
    simp only [Function.comp_def, finiteCanonical, div_eq_mul_inv, inv_pow]
    ring
  · simp only [canonicalFreeEnergy]
    field_simp

theorem concaveOn_canonicalDensity {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B d : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    ConcaveOn ℝ (Ioi 0) (fun β => canonicalDensity φ β d) := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  refine ⟨convex_Ioi _, ?_⟩
  intro β hβ γ hγ a b ha hb hab
  simp only [smul_eq_mul]
  have hc : 0 < a * β + b * γ := by
    have hh := (convex_Ioi (0 : ℝ)) hβ hγ ha hb hab
    exact hh
  have hβlim := (finiteCanonical_tendsto hφ ht hβ.le hstable hcore hd)
  have hγlim := (finiteCanonical_tendsto hφ ht hγ.le hstable hcore hd)
  have hclim := (finiteCanonical_tendsto hφ ht hc.le hstable hcore hd)
  apply le_of_tendsto_of_tendsto ((hβlim.const_mul a).add (hγlim.const_mul b)) hclim
  filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
  have hh := (convexOn_log_partition hφ hp hstable p.2).2 hβ hγ ha hb hab
  simp only [smul_eq_mul] at hh
  dsimp [finiteCanonical]
  have hden : 0 < p.1 ^ 3 := pow_pos hp 3
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  exact div_le_div_of_nonneg_right (by linarith only [hh]) hden.le

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LaplaceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter Set

namespace ContinuumTemperature

theorem tsum_le_low_sector_add_tail {w b : ℕ → ℝ} (hw : Summable w) (hb : Summable b)
    (hb0 : ∀ n, 0 ≤ b n) {M : ℕ} {A : ℝ}
    (hlow : ∀ n, n < M → w n ≤ A) (hhigh : ∀ n, M ≤ n → w n ≤ b n) :
    ∑' n, w n ≤ (M : ℝ)*A + ∑' n, b n := by
  have hst : Summable (fun n : ℕ => w (n+M)) :=
    hw.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hbt : Summable (fun n : ℕ => b (n+M)) :=
    hb.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have ht : (∑' n : ℕ, w (n+M)) ≤ ∑' n : ℕ, b (n+M) :=
    hst.tsum_le_tsum (fun n => hhigh _ (Nat.le_add_left M n)) hbt
  have htail : (∑' n : ℕ, b (n+M)) ≤ ∑' n, b n := by
    rw [← hb.sum_add_tsum_nat_add M]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun n _ => hb0 n))
  have hsum : (∑ n ∈ Finset.range M, w n) ≤ (M : ℝ)*A := by
    calc
      (∑ n ∈ Finset.range M, w n) ≤ ∑ n ∈ Finset.range M, A :=
        Finset.sum_le_sum (fun n hn => hlow n (Finset.mem_range.mp hn))
      _ = _ := by simp
  rw [← hw.sum_add_tsum_nat_add M]
  exact add_le_add hsum (ht.trans htail)

theorem log_affine_cube_div_tendsto_zero {D C : ℝ} (hD : 0 < D) :
    Tendsto (fun L : ℝ => Real.log (D*L^3+C)/L^3) atTop (𝓝 0) := by
  have hv : Tendsto (fun L : ℝ => L^3) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hz : Tendsto (fun L : ℝ => D*L^3+C) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop C (hv.const_mul_atTop hD)
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hz
  have hi : Tendsto (fun L : ℝ => (L^3)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hv
  have hr : Tendsto (fun L : ℝ => D+C*(L^3)⁻¹) atTop (𝓝 D) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (hi.const_mul C)
  have hh := hlog.mul hr
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [hv.eventually (eventually_gt_atTop 0), hz.eventually (eventually_gt_atTop 0)] with L hL hzL
  change Real.log (D*L^3+C)/(D*L^3+C)*(D+C*(L^3)⁻¹) = _
  have hn : L ≠ 0 := by rintro rfl; simp at hL
  field_simp [hn, ne_of_gt hzL]

theorem log_tsum_div_le {w b : ℕ → ℝ} (hw : Summable w) (hb : Summable b)
    (hb0 : ∀ n, 0 ≤ b n) (hpos : 0 < ∑' n, w n) {M : ℕ} (hM : 0 < M)
    {V c : ℝ} (hV : 0 < V) (hc : 0 ≤ c)
    (hlow : ∀ n, n < M → w n ≤ Real.exp (V*c))
    (hhigh : ∀ n, M ≤ n → w n ≤ b n) :
    Real.log (∑' n, w n)/V ≤ c + Real.log ((M : ℝ)+∑' n, b n)/V := by
  have hbS : 0 ≤ ∑' n, b n := tsum_nonneg hb0
  have he : 1 ≤ Real.exp (V*c) := Real.one_le_exp (mul_nonneg hV.le hc)
  have hbound := tsum_le_low_sector_add_tail hw hb hb0 hlow hhigh
  have hbound' : ∑' n, w n ≤ ((M : ℝ)+∑' n, b n)*Real.exp (V*c) := by
    have hh := mul_le_mul_of_nonneg_left he hbS
    nlinarith only [hbound, hh]
  have hp : 0 < (M : ℝ)+∑' n, b n := by positivity
  have hlog := Real.log_le_log hpos hbound'
  rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  calc
    Real.log (∑' n, w n)/V ≤ (Real.log ((M : ℝ)+∑' n, b n)+V*c)/V :=
      div_le_div_of_nonneg_right hlog hV.le
    _ = _ := by field_simp; ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LaplacePrinciple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem density_compact_eventually {K : Set ℝ} (hK : IsCompact K)
    {P : ℝ × ℕ → Prop} (hP : ∀ d ∈ K, ∀ᶠ p in densityFilter d, P p) :
    ∀ᶠ L in atTop, ∀ n : ℕ, (n : ℝ)/L^3 ∈ K → P (L,n) := by
  have hp : ∀ᶠ p in Filter.comap
      (fun p : ℝ × ℕ => (p.1, (p.2 : ℝ)/p.1^3)) (atTop ×ˢ 𝓝ˢ K), P p := by
    rw [hK.prod_nhdsSet_eq_biSup, comap_iSup]
    simp only [comap_iSup, eventually_iSup]
    exact hP
  obtain ⟨S, hS, hsub⟩ := Filter.mem_comap.mp hp
  obtain ⟨T, hT, U, hU, hTU⟩ := Filter.mem_prod_iff.mp hS
  filter_upwards [hT] with L hL
  intro n hn
  exact hsub (hTU ⟨hL, (subset_of_mem_nhdsSet hU) hn⟩)

theorem canonicalDensity_lower_entropy {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    d*Real.log d-(β*B+1)*d ≤ canonicalDensity φ β d := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  have hlim := finiteCanonical_tendsto hφ ht hβ hstable hcore hd
  have he := ((Real.continuous_mul_log.continuousAt.tendsto).comp
    (densityFilter_density d)).sub ((densityFilter_density d).const_mul (β*B+1))
  apply le_of_tendsto_of_tendsto he hlim
  filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
  have hh := finiteCanonical_lower_entropy hφ hβ hp hstable p.2
  dsimp only [Function.comp_def] at *
  nlinarith only [hh]

theorem entropy_dual_bound (c : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    (c+1)*d-d*Real.log d ≤ Real.exp c := by
  obtain rfl | hd := hd.eq_or_lt
  · simp only [mul_zero, zero_mul, sub_self]
    exact (Real.exp_pos c).le
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (c-Real.log d)) hd.le
  rw [Real.exp_sub, Real.exp_log hd, div_mul_cancel₀ _ hd.ne'] at hh
  nlinarith only [hh]

theorem canonicalPressure_bddAbove {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    BddAbove ((fun d : ℝ => μ*d-canonicalDensity φ β d) '' Ici 0) := by
  refine ⟨Real.exp (μ+β*B), ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  have hh := canonicalDensity_lower_entropy hφ ht hβ hstable hcore hd
  have he := entropy_dual_bound (μ+β*B) hd
  linarith

theorem laplace_low_sector {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {D S ε : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hD : 0 < D) (hε : 0 < ε)
    (hF : ∀ d, 0 ≤ d → F d ≤ S)
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d))) :
    ∀ᶠ L in atTop, ∀ n : ℕ, n < ⌊D*L^3⌋₊+1 →
      w L n ≤ Real.exp (L^3*(S+ε)) := by
  have he : ∀ᶠ L in atTop, ∀ n : ℕ, (n : ℝ)/L^3 ∈ Icc 0 D →
      Real.log (w L n)/L^3 < S+ε := by
    apply density_compact_eventually (K := Icc 0 D)
      (P := fun p => Real.log (w p.1 p.2)/p.1^3 < S+ε) isCompact_Icc
    intro d hd
    apply (hlim d hd.1).eventually_lt_const
    linarith [hF d hd.1]
  filter_upwards [he, eventually_gt_atTop 0] with L hL hp
  intro n hn
  have hn' : (n : ℝ) ≤ D*L^3 :=
    (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hn)).trans (Nat.floor_le (by positivity))
  have hr : (n : ℝ)/L^3 ∈ Icc 0 D :=
    ⟨div_nonneg (Nat.cast_nonneg n) (pow_pos hp 3).le, (div_le_iff₀ (pow_pos hp 3)).2 hn'⟩
  apply (Real.log_le_iff_le_exp (hw L hp n)).1
  have hh := (div_lt_iff₀ (pow_pos hp 3)).1 (hL n hr)
  nlinarith only [hh]

theorem laplace_upper_eventually {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ}
    {D S : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ L > 0, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hS : 0 ≤ S)
    (hF : ∀ d, 0 ≤ d → F d ≤ S)
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    ∀ q > S, ∀ᶠ L in atTop, Real.log (∑' n, w L n)/L^3 < q := by
  intro q hq
  let ε := (q-S)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlog := log_affine_cube_div_tendsto_zero (C := 1+∑' n, b n) hD
  have he := hlog.eventually_lt_const hε
  filter_upwards [laplace_low_sector hw hD hε hF hlim, htail, he,
    eventually_gt_atTop 0] with L hlow hhigh hsmall hL
  let M : ℕ := ⌊D*L^3⌋₊+1
  have hV : 0 < L^3 := pow_pos hL 3
  have hpos : 0 < ∑' n, w L n :=
    (hw L hL 0).trans_le ((hsum L hL).le_tsum 0 (fun n _ => (hw L hL n).le))
  have hh := log_tsum_div_le (hsum L hL) hb hb0 hpos (Nat.succ_pos _ : 0 < M)
    hV (show 0 ≤ S+ε by linarith) hlow (fun n hn => hhigh n (by
      apply (le_div_iff₀ hV).2
      have hm : D*L^3 < (M : ℝ) := by simpa [M] using Nat.lt_floor_add_one (D*L^3)
      exact hm.le.trans (Nat.cast_le.mpr hn)))
  have hbS : 0 ≤ ∑' n, b n := tsum_nonneg hb0
  have hM : (M : ℝ)+∑' n, b n ≤ D*L^3+(1+∑' n, b n) := by
    have hf := Nat.floor_le (mul_nonneg hD.le hV.le)
    dsimp [M]
    push_cast
    linarith
  have hMpos : 0 < (M : ℝ)+∑' n, b n := by
    have hp : 0 < (M : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
    linarith
  have hl := div_le_div_of_nonneg_right (Real.log_le_log hMpos hM) hV.le
  dsimp [ε] at *
  linarith only [hh, hl, hsmall]

theorem laplace_principle {w : ℝ → ℕ → ℝ} {F : ℝ → ℝ} {b : ℕ → ℝ} {D : ℝ}
    (hw : ∀ L > 0, ∀ n, 0 < w L n) (hsum : ∀ L > 0, Summable (w L))
    (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n) (hD : 0 < D) (hF0 : F 0 = 0)
    (hbdd : BddAbove (F '' Ici 0))
    (hlim : ∀ d, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => Real.log (w p.1 p.2)/p.1^3)
      (densityFilter d) (𝓝 (F d)))
    (htail : ∀ᶠ L in atTop, ∀ n : ℕ, D ≤ (n : ℝ)/L^3 → w L n ≤ b n) :
    Tendsto (fun L => Real.log (∑' n, w L n)/L^3) atTop (𝓝 (sSup (F '' Ici 0))) := by
  have hnon : (F '' Ici 0).Nonempty := ⟨F 0, ⟨0, by simp, rfl⟩⟩
  have hF : ∀ d, 0 ≤ d → F d ≤ sSup (F '' Ici 0) :=
    fun d hd => le_csSup hbdd ⟨d, hd, rfl⟩
  have hS : 0 ≤ sSup (F '' Ici 0) := by simpa [hF0] using hF 0 le_rfl
  apply tendsto_order.2
  constructor
  · intro q hq
    obtain ⟨_, ⟨d, hd, rfl⟩, hqd⟩ := exists_lt_of_lt_csSup hnon hq
    have hdlim := (hlim d hd).comp (floor_density_tendsto hd)
    filter_upwards [hdlim.eventually_const_lt hqd, eventually_gt_atTop 0] with L hL hp
    have hh := (hsum L hp).le_tsum ⌊d*L^3⌋₊ (fun n _ => (hw L hp n).le)
    exact hL.trans_le (div_le_div_of_nonneg_right (Real.log_le_log (hw L hp _) hh)
      (pow_pos hp 3).le)
  · exact laplace_upper_eventually hw hsum hb hb0 hD hS hF hlim htail

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem log_grand_weight_div {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L μ : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    Real.log (Real.exp (μ*N)*partition φ β L N)/L^3 =
      μ*((N : ℝ)/L^3)-finiteCanonical φ β L N := by
  rw [Real.log_mul (Real.exp_pos _).ne' (partition_pos hφ hβ hL hstable N).ne',
    Real.log_exp]
  unfold finiteCanonical
  ring

theorem grand_weight_high_density {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L μ : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) {N : ℕ}
    (hN : Real.exp (μ+β*B+2) ≤ (N : ℝ)/L^3) :
    Real.exp (μ*N)*partition φ β L N ≤ (Real.exp (-1))^N := by
  have hden : 0 ≤ (N : ℝ)/L^3 := div_nonneg (Nat.cast_nonneg _) (pow_pos hL 3).le
  have hlog := Real.log_le_log (Real.exp_pos (μ+β*B+2)) hN
  rw [Real.log_exp] at hlog
  have he := finiteCanonical_lower_entropy hφ hβ hL hstable N
  have hm := mul_le_mul_of_nonneg_right hlog hden
  have hbound : μ*((N : ℝ)/L^3)-finiteCanonical φ β L N ≤ -((N : ℝ)/L^3) := by
    nlinarith only [he, hm]
  rw [← log_grand_weight_div hφ hβ hL hstable N, ← neg_div] at hbound
  have hh := (div_le_div_iff_of_pos_right (pow_pos hL 3)).1 hbound
  have hw : 0 < Real.exp (μ*N)*partition φ β L N :=
    mul_pos (Real.exp_pos _) (partition_pos hφ hβ hL hstable N)
  rw [← Real.exp_nat_mul]
  apply (Real.log_le_iff_le_exp hw).1
  simpa using hh

theorem grandPartition_pressure_tendsto {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    Tendsto (fun L => Real.log (grandPartition φ 1 β μ L)/L^3) atTop
      (𝓝 (canonicalPressure φ β μ)) := by
  have hw : ∀ L > 0, ∀ N : ℕ, 0 < Real.exp (μ*N)*partition φ β L N :=
    fun L hL N => mul_pos (Real.exp_pos _) (partition_pos hφ hβ hL hstable N)
  have hs : ∀ L > 0, Summable (fun N : ℕ => Real.exp (μ*N)*partition φ β L N) := by
    intro L hL
    simpa only [one_mul] using summable_grandPartition hφ hβ hL.le hstable 1 μ
  have hb : Summable (fun n : ℕ => (Real.exp (-1))^n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simp)
  have hz : μ*0-canonicalDensity φ β 0 = 0 := by
    rw [canonicalDensity_zero hφ ht hβ hstable hcore]; ring
  have hlim : ∀ d, 0 ≤ d →
      Tendsto (fun p : ℝ × ℕ => Real.log (Real.exp (μ*p.2)*partition φ β p.1 p.2)/p.1^3)
        (densityFilter d) (𝓝 (μ*d-canonicalDensity φ β d)) := by
    intro d hd
    have hh := ((densityFilter_density d).const_mul μ).sub
      (finiteCanonical_tendsto hφ ht hβ hstable hcore hd)
    apply hh.congr'
    filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
    exact (log_grand_weight_div hφ hβ hp hstable p.2).symm
  have ht' : ∀ᶠ L in atTop, ∀ N : ℕ, Real.exp (μ+β*B+2) ≤ (N : ℝ)/L^3 →
      Real.exp (μ*N)*partition φ β L N ≤ (Real.exp (-1))^N := by
    filter_upwards [eventually_gt_atTop 0] with L hL
    exact fun _ hN => grand_weight_high_density hφ hβ hL hstable hN
  have hh := laplace_principle hw hs hb (fun n => (pow_pos (Real.exp_pos _) n).le)
    (Real.exp_pos (μ+β*B+2)) hz (canonicalPressure_bddAbove hφ ht hβ hstable hcore) hlim ht'
  simpa only [grandPartition, one_mul, canonicalPressure] using hh

theorem physicalPressure_tendsto {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B h : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    Tendsto (fun L => Real.log (grandPartition φ t β h L)/(t*L^3)) atTop
      (𝓝 (physicalPressure φ t (β,h))) := by
  change Tendsto _ atTop (𝓝 (canonicalPressure φ β (t*h)/t))
  have hh := (grandPartition_pressure_tendsto hφ ht hβ hstable hcore (μ := t*h)).div_const t
  convert hh using 1
  ext L
  simp only [grandPartition, one_mul]
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ExactAssignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
section
variable {X : Type u_1} [MeasurableSpace X] {ι : Type u_2} [Fintype ι] [DecidableEq ι]

omit [MeasurableSpace X] [Fintype ι] in
theorem binaryRegion_subset_union (A B : Set X) (s : Finset ι) :
    binaryRegion A B s ⊆ {x : ι → X | ∀ i, x i ∈ A ∪ B} := by
  intro x hx i
  by_cases hi : i ∈ s
  · exact Or.inl (by simpa only [ite_eq_left hi] using hx i)
  · exact Or.inr (by simpa only [ite_eq_right hi] using hx i)

omit [MeasurableSpace X] in

theorem iUnion_binaryRegion (A B : Set X) :
    (⋃ s : Finset ι, binaryRegion A B s) = {x : ι → X | ∀ i, x i ∈ A ∪ B} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    exact binaryRegion_subset_union A B s hs
  · intro hx
    refine mem_iUnion.mpr ⟨Finset.univ.filter (fun i => x i ∈ A), ?_⟩
    intro i
    by_cases hi : x i ∈ A
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_left hi] using hi
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_right hi] using
        (hx i).resolve_left hi

theorem integral_binary_assignments_eq (μ : Measure X) [SigmaFinite μ]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    {F : (ι → X) → ℝ}
    (hF : IntegrableOn F {x : ι → X | ∀ i, x i ∈ A ∪ B} (Measure.pi (fun _ : ι => μ))) :
    (∫ x in {x : ι → X | ∀ i, x i ∈ A ∪ B}, F x ∂(Measure.pi (fun _ : ι => μ))) =
      ∑ s : Finset ι, ∫ x in binaryRegion A B s, F x ∂(Measure.pi (fun _ : ι => μ)) := by
  have hh := integral_biUnion_finset (Finset.univ : Finset (Finset ι))
    (fun s _ => measurableSet_binaryRegion hA hB s)
    (fun _ _ _ _ hne => binaryRegion_pairwiseDisjoint hd hne)
    (fun s _ => hF.mono_set (binaryRegion_subset_union A B s))
  simpa only [Finset.mem_univ, iUnion_true, iUnion_binaryRegion] using hh

end
end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GeneralGrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem familyIntegral_relabel (F : ConfigFamily) (hF : RelabelInvariant F)
    (A : Set Space) {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    familyIntegral F A ι = familyIntegral F A κ := by
  let p : (ι → Space) ≃ᵐ (κ → Space) := MeasurableEquiv.piCongrLeft (fun _ : κ => Space) e
  have hp : MeasurePreserving p volume volume := by
    simpa only [volume_pi] using measurePreserving_piCongrLeft (fun _ : κ => volume) e
  have hpx (x : ι → Space) : p x = x ∘ e.symm := by
    funext i
    simpa only [p, Equiv.apply_symm_apply, Function.comp_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ : κ => Space) x (e.symm i))
  have heq := hp.setIntegral_preimage_emb p.measurableEmbedding (F κ)
    {x : κ → Space | ∀ i, x i ∈ A}
  have hpre : p ⁻¹' {x : κ → Space | ∀ i, x i ∈ A} =
      {x : ι → Space | ∀ i, x i ∈ A} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, hpx, Function.comp_apply]
    constructor
    · intro hh i
      simpa only [Equiv.symm_apply_apply] using hh (e i)
    · intro hh i
      exact hh (e.symm i)
  rw [hpre] at heq
  simpa only [familyIntegral, hpx, hF κ ι e.symm] using heq

theorem familyIntegral_eq_Fin (F : ConfigFamily) (hF : RelabelInvariant F)
    (A : Set Space) (ι : Type) [Fintype ι] :
    familyIntegral F A ι = familyIntegral F A (Fin (Fintype.card ι)) :=
  familyIntegral_relabel F hF A (Fintype.equivFin ι)

theorem integral_binary_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B : Set Space} (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    {F : (ι → Space) → ℝ} (a b : ℕ → ℝ)
    (hF : IntegrableOn F {x : ι → Space | ∀ i, x i ∈ A ∪ B})
    (hbound : ∀ s : Finset ι, (∫ x in binaryRegion A B s, F x) ≤
      a s.card*b (Fintype.card ι-s.card)) :
    (∫ x in {x : ι → Space | ∀ i, x i ∈ A ∪ B}, F x) ≤
      ∑ k ∈ Finset.range (Fintype.card ι+1),
        ((Fintype.card ι).choose k : ℝ)*a k*b (Fintype.card ι-k) := by
  rw [show volume = Measure.pi (fun _ : ι => (volume : Measure Space)) by exact volume_pi]
  rw [integral_binary_assignments_eq volume hA hB hd (by simpa only [← volume_pi] using hF)]
  calc
    _ ≤ ∑ s : Finset ι, a s.card*b (Fintype.card ι-s.card) := by
      apply Finset.sum_le_sum
      intro s _
      simpa only [← volume_pi] using hbound s
    _ = _ := by
      have hh := Finset.sum_powerset_apply_card (fun k => a k*b (Fintype.card ι-k))
        (x := (Finset.univ : Finset ι))
      simpa only [Finset.powerset_univ, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hh

theorem factorial_binomial_sum (a b : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), (N.choose k : ℝ)*a k*b (N-k))/(N.factorial : ℝ) =
      ∑ k ∈ Finset.range (N+1), (a k/(k.factorial : ℝ))*(b (N-k)/((N-k).factorial : ℝ)) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.cast_choose ℝ (by have := Finset.mem_range.mp hk; omega)]
  have hN : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  field_simp

theorem familyTerm_nonneg (F : ConfigFamily) (A : Set Space)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x) (n : ℕ) :
    0 ≤ familyTerm F A n := by
  apply div_nonneg (integral_nonneg (hF (Fin n)))
  positivity

theorem integrableOn_family_of_bound (F : ConfigFamily) {A : Set Space}
    (hA : volume A ≠ ⊤) {ι : Type} [Fintype ι]
    (hFm : Measurable (F ι)) (hF0 : ∀ x, 0 ≤ F ι x)
    {C : ℝ} (hbound : ∀ x, F ι x ≤ C) :
    IntegrableOn (F ι) {x : ι → Space | ∀ i, x i ∈ A} := by
  have hvol : volume {x : ι → Space | ∀ i, x i ∈ A} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hA
  let : IsFiniteMeasure (volume.restrict {x : ι → Space | ∀ i, x i ∈ A}) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hvol⟩
  apply (integrable_const C).mono' hFm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hF0 x)]
  exact hbound x

theorem familyTerm_le_exponential (F : ConfigFamily) {A : Set Space}
    (hA : volume A ≠ ⊤) {d : ℝ}
    (hFm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hbound : ∀ (ι : Type) [Fintype ι] (x : ι → Space),
      F ι x ≤ Real.exp (d*Fintype.card ι)) (n : ℕ) :
    familyTerm F A n ≤ (volume.real A*Real.exp d)^n/(n.factorial : ℝ) := by
  have hvol : volume {x : Fin n → Space | ∀ i, x i ∈ A} ≠ ⊤ := by
    rw [volume_generalConfigurations]
    exact ENNReal.pow_ne_top hA
  let : IsFiniteMeasure (volume.restrict {x : Fin n → Space | ∀ i, x i ∈ A}) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hvol⟩
  have hh := integral_mono (integrableOn_family_of_bound F hA (hFm (Fin n))
    (hF0 (Fin n)) (hbound (Fin n))) (integrable_const _) (hbound (Fin n))
  have hn : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  apply (div_le_div_of_nonneg_right hh hn).trans_eq
  rw [setIntegral_const, Measure.real, volume_generalConfigurations, ENNReal.toReal_pow,
    Fintype.card_fin, smul_eq_mul, mul_comm d (n : ℝ), Real.exp_nat_mul, mul_pow]
  rfl

theorem summable_familyTerm_of_bound (F : ConfigFamily) {A : Set Space}
    (hA : volume A ≠ ⊤) {d : ℝ}
    (hFm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hbound : ∀ (ι : Type) [Fintype ι] (x : ι → Space),
      F ι x ≤ Real.exp (d*Fintype.card ι)) : Summable (familyTerm F A) :=
  Summable.of_nonneg_of_le (familyTerm_nonneg F A hF0)
    (familyTerm_le_exponential F hA hFm hF0 hbound)
    (Real.summable_pow_div_factorial _)

theorem tsum_le_convolution {f a b : ℕ → ℝ} (hf : Summable f)
    (ha : Summable a) (hb : Summable b)
    (hle : ∀ n, f n ≤ ∑ k ∈ Finset.range (n+1), a k*b (n-k)) :
    (∑' n, f n) ≤ (∑' n, a n)*(∑' n, b n) := by
  have hab : Summable (fun p : ℕ × ℕ => a p.1*b p.2) :=
    summable_mul_of_summable_norm (summable_norm_iff.mpr ha) (summable_norm_iff.mpr hb)
  rw [ha.tsum_mul_tsum_eq_tsum_sum_range hb hab]
  exact hf.tsum_le_tsum hle (summable_sum_mul_range_of_summable_mul hab)

theorem grandIntegral_insertion_bound (F G : ConfigFamily)
    (hG : RelabelInvariant G) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B)
    (hAfin : volume A ≠ ⊤)
    (hFi : ∀ n, IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ A ∪ B})
    (hGi : ∀ (ι : Type) [Fintype ι], IntegrableOn (G ι) {x | ∀ i, x i ∈ B})
    (hFs : Summable (familyTerm F (A ∪ B))) (hGs : Summable (familyTerm G B))
    {d : ℝ}
    (hbound : ∀ (n : ℕ) (s : Finset (Fin n)) (x : Fin n → Space),
      x ∈ binaryRegion A B s → F (Fin n) x ≤
        Real.exp (d*s.card) * G {i : Fin n // i ∉ s} (fun i => x i)) :
    grandIntegral F (A ∪ B) ≤
      Real.exp (volume.real A*Real.exp d)*grandIntegral G B := by
  let a (n : ℕ) := (volume.real A*Real.exp d)^n/(n.factorial : ℝ)
  have ha : HasSum a (Real.exp (volume.real A*Real.exp d)) :=
    by
      simpa only [a, Real.exp_eq_exp_ℝ] using
        NormedSpace.expSeries_div_hasSum_exp (volume.real A*Real.exp d)
  change (∑' n, familyTerm F (A ∪ B) n) ≤
    Real.exp (volume.real A*Real.exp d)*(∑' n, familyTerm G B n)
  rw [← ha.tsum_eq]
  apply tsum_le_convolution hFs ha.summable hGs
  intro n
  have hb := integral_binary_bound hA hB hd
    (fun k => (volume.real A)^k*Real.exp (d*k))
    (fun k => familyIntegral G B (Fin k)) (hFi n) ?_
  swap
  · intro s
    have hv : volume {x : {i : Fin n // i ∈ s} → Space | ∀ i, x i ∈ A} ≠ ⊤ := by
      rw [volume_generalConfigurations]
      exact ENNReal.pow_ne_top hAfin
    let : IsFiniteMeasure (volume.restrict
        {x : {i : Fin n // i ∈ s} → Space | ∀ i, x i ∈ A}) := ⟨by
      simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hv⟩
    have hprod := integrableOn_binary_product volume A B s
      (integrable_const (Real.exp (d*s.card))) (by simpa only [← volume_pi] using hGi {i : Fin n // i ∉ s})
    have hi := setIntegral_mono_on
      ((hFi n).mono_set (binaryRegion_subset_union A B s))
      (by simpa only [← volume_pi] using hprod)
      (measurableSet_binaryRegion hA hB s) (hbound n s)
    rw [show volume = Measure.pi (fun _ : Fin n => (volume : Measure Space)) by exact volume_pi,
      setIntegral_binary_product volume A B s (fun _ => Real.exp (d*s.card))
        (G {i : Fin n // i ∉ s})] at hi
    simp only [← volume_pi] at hi
    have heg := familyIntegral_eq_Fin G hG B {i : Fin n // i ∉ s}
    have hgc : familyIntegral G B {i : Fin n // i ∉ s} =
        familyIntegral G B (Fin (n-s.card)) := by
      have hc : Fintype.card {i : Fin n // i ∉ s} = n-s.card := by
        rw [Fintype.card_subtype_compl (fun i : Fin n => i ∈ s),
          Fintype.card_fin, Fintype.card_coe]
      rw [hc] at heg
      exact heg
    rw [setIntegral_const, Measure.real, volume_generalConfigurations, ENNReal.toReal_pow,
      Fintype.card_coe, smul_eq_mul] at hi
    exact hi.trans_eq (by
      change volume.real A ^ s.card * Real.exp (d*s.card) *
        familyIntegral G B {i : Fin n // i ∉ s} = _
      rw [hgc, Fintype.card_fin])
  have hf : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  have hh := div_le_div_of_nonneg_right hb hf
  rw [Fintype.card_fin, factorial_binomial_sum
    (fun k => (volume.real A)^k*Real.exp (d*k))
    (fun k => familyIntegral G B (Fin k)) n] at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [a, familyTerm]
  rw [mul_comm d (k : ℝ), Real.exp_nat_mul, mul_pow]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.MomentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem weighted_field_sq {ι : Type u_1} [Fintype ι] (J n : ι → ℝ)
    (hJ : ∀ j, 0 ≤ J j) {M : ℝ} (hrow : ∑ j, J j ≤ M) :
    (∑ j, J j * n j)^2 ≤ M * ∑ j, J j * (n j)^2 := by
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ)
    Finset.univ (f := J) (g := fun j => J j*(n j)^2)
    (r := fun j => J j*n j) (fun j _ => hJ j)
    (fun j _ => mul_nonneg (hJ j) (sq_nonneg (n j)))
    (fun j _ => by ring_nf; exact le_rfl)
  exact hh.trans (mul_le_mul_of_nonneg_right hrow
    (Finset.sum_nonneg (fun j _ => mul_nonneg (hJ j) (sq_nonneg (n j)))))

theorem cell_insertion_exponent {A M J β B h c n X : ℝ}
    (hA : 0 < A) (hM : M ≤ A/8) (hJ : J ≤ M) (hβ : 0 ≤ β)
    (hc : c = β*A/4) :
    c*n^2+h*n-β*(A-J/2)*n^2+β*B*n+β*n*X ≤
      β*X^2/A+(h+β*B)*n := by
  rw [hc]
  have hsq := sq_nonneg (A*n/2-X)
  have hm := mul_nonneg (show 0 ≤ A/2-J/2 by linarith) (sq_nonneg n)
  have hh := add_nonneg (mul_nonneg (div_nonneg hβ hA.le) hsq) (mul_nonneg hβ hm)
  have he : β*X^2/A+(h+β*B)*n -
      (β*A/4*n^2+h*n-β*(A-J/2)*n^2+β*B*n+β*n*X) =
      β/A*(A*n/2-X)^2+β*((A/2-J/2)*n^2) := by
    field_simp
    ring
  exact sub_nonneg.mp (he ▸ hh)

theorem exp_half_le {C u : ℝ} (hC : 0 < C) :
    Real.exp (u/2) ≤ Real.exp u/(2*C)+C/2 := by
  have he : (Real.exp (u/2))^2 = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hh := sq_nonneg (Real.exp (u/2)-C)
  apply (mul_le_mul_iff_left₀ (show 0 < 2*C by positivity)).mp
  calc
    Real.exp (u/2)*(2*C) ≤ Real.exp u+C^2 := by nlinarith only [he, hh]
    _ = (Real.exp u/(2*C)+C/2)*(2*C) := by field_simp

theorem finite_moment_bootstrap {ι : Type u_1} [Fintype ι]
    (F H : ι → ℝ) (θ : ι → ι → ℝ) {C : ℝ} (hC : 0 < C)
    (hF : ∀ i, 0 ≤ F i) (hθ : ∀ i j, 0 ≤ θ i j)
    (hrow : ∀ i, ∑ j, θ i j ≤ 1)
    (hhalf : ∀ i, H i ≤ F i/(2*C)+C/2)
    (hinsert : ∀ i, F i ≤ C*(1+∑ j, θ i j*H j)) :
    ∀ i, F i ≤ 2*C+C^2 := by
  classical
  intro i
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ F ⟨i, Finset.mem_univ i⟩
  have hmax : ∀ j, F j ≤ F k := fun j => hk j (Finset.mem_univ j)
  have hFk := hF k
  have hp : 0 ≤ F k/(2*C)+C/2 := by positivity
  have hsum : ∑ j, θ k j*H j ≤ F k/(2*C)+C/2 := by
    calc
      _ ≤ ∑ j, θ k j*(F k/(2*C)+C/2) := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left ((hhalf j).trans (by gcongr; exact hmax j))
          (hθ k j))
      _ = (∑ j, θ k j)*(F k/(2*C)+C/2) := by rw [Finset.sum_mul]
      _ ≤ 1*(F k/(2*C)+C/2) := mul_le_mul_of_nonneg_right (hrow k) hp
      _ = F k/(2*C)+C/2 := one_mul _
  have hb := (hinsert k).trans (mul_le_mul_of_nonneg_left (show 1+∑ j, θ k j*H j ≤ 1+(F k/(2*C)+C/2) by linarith only [hsum]) hC.le)
  have he : C*(1+(F k/(2*C)+C/2)) = C+F k/2+C^2/2 := by field_simp; ring
  rw [he] at hb
  exact (hmax i).trans (by nlinarith only [hb])

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.MomentExpectations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem exp_exterior_field_le {ι : Type u_1} [Fintype ι] (J n : ι → ℝ)
    {A β : ℝ} (hA : 0 < A) (hβ : 0 ≤ β) (hJ : ∀ j, 0 ≤ J j)
    (hrow : ∑ j, J j ≤ A/8) :
    Real.exp (β*(∑ j, J j*n j)^2/A) ≤
      1+∑ j, J j/A*Real.exp (β*A/8*(n j)^2) := by
  have hs := weighted_field_sq J n hJ hrow
  have hfield : β*(∑ j, J j*n j)^2/A ≤ ∑ j, (J j/A)*(β*A/8*(n j)^2) := by
    calc
      _ = β/A*(∑ j, J j*n j)^2 := by ring
      _ ≤ β/A*(A/8*∑ j, J j*(n j)^2) :=
        mul_le_mul_of_nonneg_left hs (div_nonneg hβ hA.le)
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        field_simp
  have hweights : ∑ j, J j/A ≤ 1 := by
    rw [← Finset.sum_div]
    apply (div_le_one hA).2
    linarith
  have hj := convexOn_exp.map_add_sum_le (t := Finset.univ)
    (w := fun j => J j/A) (p := fun j => β*A/8*(n j)^2)
    (v := 1-∑ j, J j/A) (q := 0)
    (fun j _ => div_nonneg (hJ j) hA.le) (by ring)
    (fun _ _ => mem_univ _) (sub_nonneg.mpr hweights) (mem_univ _)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hj
  have hw0 : 0 ≤ ∑ j, J j/A := Finset.sum_nonneg (fun j _ => div_nonneg (hJ j) hA.le)
  exact ((Real.exp_le_exp.mpr hfield).trans hj).trans (by linarith only [hw0])

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GenericGibbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem occupation_nonneg {ι : Type} [Fintype ι] (C : Set Space) (x : ι → Space) :
    0 ≤ occupation C x := Nat.cast_nonneg _

theorem occupation_eq_sum {ι : Type} [Fintype ι] (C : Set Space) (x : ι → Space) :
    occupation C x = ∑ i, if x i ∈ C then (1 : ℝ) else 0 := by
  classical
  simp only [occupation, ← Finset.sum_boole, Fintype.card_subtype]

theorem measurable_occupation {ι : Type} [Fintype ι] {C : Set Space} (hC : MeasurableSet C) :
    Measurable (fun x : ι → Space => occupation C x) := by
  classical
  simp_rw [occupation_eq_sum]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite (hC.preimage (measurable_pi_apply i)) measurable_const measurable_const

theorem occupation_relabel {ι κ : Type} [Fintype ι] [Fintype κ]
    (C : Set Space) (e : ι ≃ κ) (x : κ → Space) : occupation C (x ∘ e) = occupation C x := by
  classical
  simp_rw [occupation_eq_sum, Function.comp_apply]
  exact Equiv.sum_comp e (fun i => if x i ∈ C then (1 : ℝ) else 0)

theorem gibbsEnergy_relabel (V : Space → Space → ℝ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → Space) : gibbsEnergy V (x ∘ e) = gibbsEnergy V x := by
  classical
  unfold gibbsEnergy
  simp only [Function.comp_apply, ← e.injective.eq_iff]
  congr 1
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp e (fun j => if e i = j then 0 else V (x (e i)) (x j))

theorem gibbsFamily_relabel (V : Space → Space → ℝ) (β h : ℝ) :
    RelabelInvariant (gibbsFamily V β h) := by
  intro ι κ _ _ e x
  have hh : Function.Injective (x ∘ e) ↔ Function.Injective x := by
    constructor
    · intro hx i j hij
      obtain ⟨i, rfl⟩ := e.surjective i
      obtain ⟨j, rfl⟩ := e.surjective j
      exact congrArg e (hx hij)
    · exact fun hx => hx.comp e.injective
  simp only [gibbsFamily, hh, gibbsEnergy_relabel, Fintype.card_congr e]

theorem gibbsFamily_nonneg (V : Space → Space → ℝ) (β h : ℝ) (ι : Type) [Fintype ι]
    (x : ι → Space) : 0 ≤ gibbsFamily V β h ι x := by
  unfold gibbsFamily
  split_ifs
  · exact (Real.exp_pos _).le
  · rfl

theorem gibbsEnergy_split (V : Space → Space → ℝ) (hsym : ∀ x y, V x y = V y x)
    {ι : Type} [Fintype ι] (p : ι → Prop) [DecidablePred p] (x : ι → Space) :
    gibbsEnergy V x = gibbsEnergy V (fun i : {i // p i} => x i) +
      gibbsEnergy V (fun i : {i // ¬p i} => x i) +
      ∑ i : {i // p i}, ∑ j : {j // ¬p j}, V (x i) (x j) := by
  classical
  have heq := symmetric_matrix_split p (fun i j => if i = j then 0 else V (x i) (x j))
    (fun i j => by by_cases hh : i = j <;> simp [hh, eq_comm, hsym])
  have hcross (i : {i // p i}) (j : {j // ¬p j}) : (i : ι) ≠ j := by
    intro hh
    exact j.property (hh ▸ i.property)
  have hself (a b : {i // p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  have hself' (a b : {i // ¬p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  unfold gibbsEnergy
  rw [heq]
  simp only [hself, hself', hcross, ite_false]
  ring

theorem measurable_gibbsEnergy {V : Space → Space → ℝ}
    (hV : Measurable (Function.uncurry V)) {ι : Type} [Fintype ι] :
    Measurable (fun x : ι → Space => gibbsEnergy V x) := by
  unfold gibbsEnergy
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases hij : i = j
  · simp only [ite_eq_left hij]
    exact measurable_const
  · simp only [ite_eq_right hij]
    have hp : Measurable (fun x : ι → Space => (x i, x j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    exact hV.comp hp

theorem measurableSet_injective_config (ι : Type) [Fintype ι] :
    MeasurableSet {x : ι → Space | Function.Injective x} := by
  have he : {x : ι → Space | Function.Injective x} =
      ⋂ i : ι, ⋂ j : ι, {x : ι → Space | x i = x j → i = j} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, Function.Injective]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i = j
  · simp only [hij, implies_true, ofPred_true]
    exact MeasurableSet.univ
  · have hm : MeasurableSet {x : ι → Space | x i = x j} :=
      measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
    convert hm.compl using 1
    ext x
    simp [hij]

theorem measurable_gibbsFamily {V : Space → Space → ℝ}
    (hV : Measurable (Function.uncurry V)) (β h : ℝ) (ι : Type) [Fintype ι] :
    Measurable (gibbsFamily V β h ι) := by
  apply Measurable.ite (measurableSet_injective_config ι) _ measurable_const
  exact (measurable_const.sub (measurable_const.mul (measurable_gibbsEnergy hV))).exp

theorem momentFamily_relabel (F : ConfigFamily) (hF : RelabelInvariant F)
    (C : Set Space) (c : ℝ) : RelabelInvariant (momentFamily F C c) := by
  intro ι κ _ _ e x
  simp only [momentFamily, occupation_relabel, hF ι κ e x]

theorem momentFamily_nonneg (F : ConfigFamily)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (C : Set Space) (c : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    0 ≤ momentFamily F C c ι x := mul_nonneg (hF ι x) (Real.exp_pos _).le

theorem measurable_momentFamily (F : ConfigFamily) {C : Set Space} (hC : MeasurableSet C)
    (c : ℝ) {ι : Type} [Fintype ι] (hF : Measurable (F ι)) :
    Measurable (momentFamily F C c ι) :=
  hF.mul ((measurable_occupation hC).pow_const 2 |>.const_mul c |>.exp)

theorem gibbs_moment_stable_bound (V : Space → Space → ℝ) (β h B c : ℝ)
    (C : Set Space) {ι : Type} [Fintype ι] (x : ι → Space)
    (hbound : c*(occupation C x)^2 ≤ β*gibbsEnergy V x+β*B*Fintype.card ι) :
    momentFamily (gibbsFamily V β h) C c ι x ≤
      Real.exp ((h+β*B)*Fintype.card ι) := by
  by_cases hx : Function.Injective x
  · simp only [momentFamily, gibbsFamily, ite_eq_left hx, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hbound]
  · simp only [momentFamily, gibbsFamily, ite_eq_right hx, zero_mul]
    exact (Real.exp_pos _).le

theorem gibbs_moment_insertion (V : Space → Space → ℝ)
    {A M J β B h : ℝ} (hA : 0 < A) (hM : M ≤ A/8) (hJ : J ≤ M) (hβ : 0 ≤ β)
    (C : Set Space) {ι : Type} [Fintype ι] (s : Finset ι) (x : ι → Space) (X : ℝ)
    (hn : occupation C x = s.card)
    (hE : (A-J/2)*(s.card : ℝ)^2-B*s.card-s.card*X ≤
      gibbsEnergy V x-gibbsEnergy V (fun i : {i // i ∉ s} => x i)) :
    momentFamily (gibbsFamily V β h) C (β*A/4) ι x ≤
      Real.exp ((h+β*B)*s.card) *
        (gibbsFamily V β h {i : ι // i ∉ s} (fun i => x i)*Real.exp (β*X^2/A)) := by
  by_cases hx : Function.Injective x
  swap
  · simp only [momentFamily, gibbsFamily, ite_eq_right hx, zero_mul]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (gibbsFamily_nonneg V β h _ _) (Real.exp_pos _).le)
  have hout : Function.Injective (fun i : {i : ι // i ∉ s} => x i) :=
    hx.comp Subtype.val_injective
  have hcard : (Fintype.card ι : ℝ) = s.card+Fintype.card {i : ι // i ∉ s} := by
    have hc : Fintype.card {i : ι // i ∉ s} = Fintype.card ι-s.card := by
      rw [Fintype.card_subtype_compl (fun i : ι => i ∈ s), Fintype.card_coe]
    rw [hc]
    rw [Nat.cast_sub (Finset.card_le_univ s)]
    ring
  have he := mul_le_mul_of_nonneg_left hE hβ
  have hex := cell_insertion_exponent (B := B) (h := h) (n := (s.card : ℝ))
    (X := X) hA hM hJ hβ rfl
  simp only [momentFamily, gibbsFamily, ite_eq_left hx, ite_eq_left hout, hn, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hcard]
  nlinarith only [he, hex]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.MomentEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem measurable_cellIndex : Measurable cellIndex := by
  apply Measurable.of_eval
  intro k
  exact ((EuclideanSpace.proj k).continuous.measurable.const_mul 4).floor

theorem measurableSet_latticeCell (z : Lattice) : MeasurableSet (latticeCell z) :=
  measurable_cellIndex (measurableSet_singleton z)

theorem gibbsEnergy_eq_pairSum (V : Space → Space → ℝ)
    (hV : ∀ x y, V x y = V y x) {ι : Type} [Fintype ι] [LinearOrder ι] (x : ι → Space) :
    gibbsEnergy V x = pairSum (fun i j => V (x i) (x j)) := by
  have hh := two_mul_pairSum (fun i j => V (x i) (x j)) (fun i j => hV (x i) (x j))
  unfold gibbsEnergy
  apply (div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  rw [mul_comm]
  convert hh.symm using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j <;> simp only [hij, ite_eq_left, ite_false]

theorem gibbsEnergy_sub (U W : Space → Space → ℝ) {ι : Type} [Fintype ι] (x : ι → Space) :
    gibbsEnergy (fun x y => U x y-W x y) x = gibbsEnergy U x-gibbsEnergy W x := by
  unfold gibbsEnergy
  have he (i j : ι) : (if i = j then 0 else U (x i) (x j)-W (x i) (x j)) =
      (if i = j then 0 else U (x i) (x j))-(if i = j then 0 else W (x i) (x j)) := by
    split_ifs <;> ring
  simp_rw [he, Finset.sum_sub_distrib]
  ring

theorem gibbsEnergy_nonneg (U : Space → Space → ℝ)
    (hU : ∀ x y, 0 ≤ U x y) {ι : Type} [Fintype ι] (x : ι → Space) :
    0 ≤ gibbsEnergy U x := by
  unfold gibbsEnergy
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · rfl
  · exact hU _ _

theorem gibbsEnergy_le_card_sq (W : Space → Space → ℝ) {ι : Type} [Fintype ι]
    (x : ι → Space) {J : ℝ} (hJ : 0 ≤ J) (hW : ∀ i j, W (x i) (x j) ≤ J) :
    gibbsEnergy W x ≤ J/2*(Fintype.card ι : ℝ)^2 := by
  have hh : (∑ i, ∑ j, if i = j then 0 else W (x i) (x j)) ≤
      ∑ _ : ι, ∑ _ : ι, J := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact hJ
    · exact hW i j
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  unfold gibbsEnergy
  nlinarith only [hh]

theorem core_gibbsEnergy_one_cell (t : ℝ) {ι : Type} [Fintype ι]
    (x : ι → Space) (z : Lattice) (hx : ∀ i, x i ∈ latticeCell z) :
    t^2/8*(Fintype.card ι : ℝ)^2-t^2/2*Fintype.card ι ≤
      gibbsEnergy (fun x y => coreProfile t ‖x-y‖) x := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [gibbsEnergy_eq_pairSum _ (fun x y => by rw [norm_sub_rev])]
  apply core_one_cell_bound
  intro i j
  exact dist_lt_one_of_cellIndex_eq ((hx i).trans (hx j).symm)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem physicalCoupling_nonneg {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (z w : Lattice) :
    0 ≤ physicalCoupling t σ R z w := mul_nonneg (mul_nonneg ht kernelHeight_pos.le)
      (mixedEnvelope_nonneg hσ (fun n => le_trans zero_le_one (hR n)) z w)

theorem physicalCoupling_row {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {κ : Type} [Fintype κ] (e : κ → Lattice) (he : Function.Injective e) (z : Lattice) :
    ∑ j, physicalCoupling t σ R z (e j) ≤ 2197*t*kernelHeight*(∑' n, σ n) := by
  simp only [physicalCoupling, ← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (sum_mixedEnvelope_le e he hσ hR hs z)
    (mul_nonneg ht kernelHeight_pos.le)
  nlinarith only [hh]

theorem physicalCoupling_self_le {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (z : Lattice) :
    physicalCoupling t σ R z z ≤ 2197*t*kernelHeight*(∑' n, σ n) := by
  simpa only [Finset.univ_unique, Finset.sum_singleton] using
    physicalCoupling_row ht hσ hR hs (fun _ : Unit => z) (fun _ _ _ => Subsingleton.elim _ _) z

theorem occupation_eq_fiber {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → Space) (c : ι → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i, cellIndex (x i) = e (c i)) (k : κ) :
    occupation (latticeCell (e k)) x = (Fintype.card {i : ι // c i = k} : ℝ) := by
  unfold occupation
  congr 1
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  change cellIndex (x i) = e k ↔ c i = k
  rw [hc i, he.eq_iff]

theorem sum_physicalCoupling_occupations {ι κ : Type} [Fintype ι] [Fintype κ]
    (t : ℝ) (σ R : ℕ → ℝ) (z : Lattice)
    (x : ι → Space) (c : ι → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i, cellIndex (x i) = e (c i)) :
    ∑ j, physicalCoupling t σ R z (cellIndex (x j)) =
      ∑ k, physicalCoupling t σ R z (e k)*occupation (latticeCell (e k)) x := by
  simp_rw [hc, occupation_eq_fiber x c e he hc]
  rw [sum_comp_eq_sum_fibres c (fun k => physicalCoupling t σ R z (e k))]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ModifiedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsEnergy_mono {U V : Space → Space → ℝ} {ι : Type} [Fintype ι]
    (x : ι → Space) (h : ∀ i j, U (x i) (x j) ≤ V (x i) (x j)) :
    gibbsEnergy U x ≤ gibbsEnergy V x := by
  unfold gibbsEnergy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · rfl
  · exact h i j

theorem gibbsEnergy_partition_le (U : Space → Space → ℝ)
    (hU : ∀ x y, 0 ≤ U x y) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (x : ι → Space) :
    (∑ k, gibbsEnergy U (fun i : {i : ι // c i = k} => x i)) ≤ gibbsEnergy U x := by
  let f (i j : ι) := if i = j then 0 else U (x i) (x j)
  have hf (i j : ι) : 0 ≤ f i j := by dsimp only [f]; split_ifs; rfl; exact hU _ _
  have he (k : κ) : gibbsEnergy U (fun i : {i : ι // c i = k} => x i) =
      (∑ i : {i : ι // c i = k}, ∑ j : {j : ι // c j = k}, f i j)/2 := by
    unfold gibbsEnergy
    simp only [f, Subtype.ext_iff]
  simp_rw [he]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ k : κ, ∑ i : {i : ι // c i = k}, ∑ j : ι, f i j := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro i _
      exact sum_subtype_le_of_nonneg (fun j => c j = k) (f i) (hf i)
    _ = _ := Fintype.sum_fiberwise c (fun i => ∑ j, f i j)

theorem retained_core_partition_bound (t : ℝ) {ι κ : Type}
    [Fintype ι] [Fintype κ] [DecidableEq κ] (x : ι → Space) (c : ι → κ) (e : κ → Lattice)
    (hc : ∀ i, cellIndex (x i) = e (c i)) :
    t^2/8*(∑ k, (Fintype.card {i : ι // c i = k} : ℝ)^2)-t^2/2*Fintype.card ι ≤
      gibbsEnergy (fun x y => if cellIndex x = cellIndex y then coreProfile t ‖x-y‖ else 0) x := by
  let U : Space → Space → ℝ := fun x y => if cellIndex x = cellIndex y then coreProfile t ‖x-y‖ else 0
  have hU (x y : Space) : 0 ≤ U x y := by dsimp only [U]; split_ifs; exact coreProfile_nonneg _ _; rfl
  have he (k : κ) : gibbsEnergy U (fun i : {i : ι // c i = k} => x i) =
      gibbsEnergy (fun x y => coreProfile t ‖x-y‖) (fun i : {i : ι // c i = k} => x i) := by
    unfold gibbsEnergy
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hij : cellIndex (x i) = cellIndex (x j) := by rw [hc i, hc j, i.property, j.property]
    simp only [U, ite_eq_left hij]
  have hs (k : κ) := core_gibbsEnergy_one_cell t (fun i : {i : ι // c i = k} => x i) (e k)
    (fun i => by change cellIndex (x i) = e k; rw [hc i, i.property])
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset κ)) => hs k)
  have hp := gibbsEnergy_partition_le U hU c x
  simp_rw [he] at hp
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hh
  have hcard : (∑ k, (Fintype.card {i : ι // c i = k} : ℝ)) = Fintype.card ι := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      Fintype.sum_fiberwise c (fun _ => (1 : ℝ))
  rw [hcard] at hh
  exact hh.trans hp

theorem cellLowerBound_superstable {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V)
    {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (x : ι → Space) (c : ι → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i, cellIndex (x i) = e (c i)) :
    (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)*
      (∑ k, (Fintype.card {i : ι // c i = k} : ℝ)^2)-t^2/2*Fintype.card ι ≤ gibbsEnergy V x := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let U : Space → Space → ℝ := fun x y => if cellIndex x = cellIndex y then coreProfile t ‖x-y‖ else 0
  let W : Space → Space → ℝ := fun x y => physicalCoupling t σ R (cellIndex x) (cellIndex y)
  have hWsym (x y : Space) : W x y = W y x := by simp only [W, physicalCoupling, mixedEnvelope_symm]
  have hwl := pairSum_le_cell_quadratic c (fun k l => physicalCoupling t σ R (e k) (e l))
    (fun i j => W (x i) (x j)) (fun _ _ => physicalCoupling_nonneg ht hσ hR _ _)
    (fun i j => hWsym _ _) (fun i j => le_of_eq (by dsimp only [W]; rw [hc i, hc j]))
  rw [← gibbsEnergy_eq_pairSum W hWsym x] at hwl
  have hquad := row_sum_quadratic_bound (fun k l => physicalCoupling t σ R (e k) (e l))
    (fun k => (Fintype.card {i : ι // c i = k} : ℝ)) (2197*t*kernelHeight*(∑' n, σ n))
    (fun _ _ => physicalCoupling_nonneg ht hσ hR _ _)
    (fun k l => by simp only [physicalCoupling, mixedEnvelope_symm])
    (fun k => physicalCoupling_row ht hσ hR hs e he (e k))
  have hcore := retained_core_partition_bound t x c e hc
  have hlo := gibbsEnergy_mono (U := fun x y => U x y-W x y) (V := V) x
    (fun i j => hV (x i) (x j))
  change gibbsEnergy (fun x y => U x y-W x y) x ≤ gibbsEnergy V x at hlo
  rw [gibbsEnergy_sub] at hlo
  change _ ≤ gibbsEnergy U x at hcore
  nlinarith only [hwl, hquad, hcore, hlo]

theorem cellLowerBound_moment_energy {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V)
    {ι : Type} [Fintype ι] (x : ι → Space) (z : Lattice) :
    (t^2/8)/4*(occupation (latticeCell z) x)^2 ≤ gibbsEnergy V x+t^2/2*Fintype.card ι := by
  let S : Finset Lattice := insert z (Finset.univ.image (fun i => cellIndex (x i)))
  let c (i : ι) : S := ⟨cellIndex (x i), Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨i, Finset.mem_univ i, rfl⟩)⟩
  let k : S := ⟨z, Finset.mem_insert_self _ _⟩
  have hcard : (Fintype.card {i : ι // c i = k} : ℝ) = occupation (latticeCell z) x := by
    unfold occupation
    congr 1
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun i => by simp only [Subtype.ext_iff, c, k, latticeCell,
      mem_ofPred_eq])
  have hsq : (occupation (latticeCell z) x)^2 ≤ ∑ j : S, (Fintype.card {i : ι // c i = j} : ℝ)^2 := by
    rw [← hcard]
    exact Finset.single_le_sum (s := Finset.univ) (f := fun j : S => (Fintype.card {i : ι // c i = j} : ℝ)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have hp := cellLowerBound_superstable ht hσ hR hs hV x c
    (fun j : S => (j : Lattice)) Subtype.val_injective (fun _ => rfl)
  have hcoef : (t^2/8)/4 ≤ t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2 := by
    nlinarith only [hsmall, sq_nonneg t]
  have h0 : 0 ≤ (t^2/8)/4 := by positivity
  have hb := (mul_le_mul_of_nonneg_left hsq h0).trans
    (mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  linarith only [hb, hp]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GibbsBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsEnergy_radial (φ : ℝ → ℝ) {ι : Type} [Fintype ι] (x : ι → Space) :
    gibbsEnergy (fun x y => φ ‖x-y‖) x = realPairEnergy φ x := by
  unfold gibbsEnergy realPairEnergy
  ring

theorem gibbsFamily_radial (φ : ℝ → ℝ) (β h : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    gibbsFamily (fun x y => φ ‖x-y‖) β h ι x =
      Real.exp (h*Fintype.card ι)*symmetricWeight φ β x := by
  unfold gibbsFamily symmetricWeight
  split_ifs
  · rw [gibbsEnergy_radial, ← Real.exp_add]
    congr 1
    ring
  · simp

theorem familyTerm_radial (φ : ℝ → ℝ) (β h L : ℝ) (n : ℕ) :
    familyTerm (gibbsFamily (fun x y => φ ‖x-y‖) β h) (cube L) n =
      Real.exp (h*n)*partition φ β L n := by
  unfold familyTerm familyIntegral
  simp_rw [gibbsFamily_radial, Fintype.card_fin]
  rw [integral_const_mul, mul_div_assoc]
  simpa only [generalPartition, Fintype.card_fin] using
    congrArg (fun a : ℝ => Real.exp (h*n)*a) (generalPartition_eq_partition φ β L n)

theorem grandIntegral_radial (φ : ℝ → ℝ) (t β h L : ℝ) :
    grandIntegral (gibbsFamily (fun x y => φ ‖x-y‖) β (t*h)) (cube L) =
      grandPartition φ t β h L := by
  unfold grandIntegral grandPartition
  simp_rw [familyTerm_radial]

theorem CellLowerBound.mono {t : ℝ} {σ R : ℕ → ℝ} {U V : Space → Space → ℝ}
    (hU : CellLowerBound t σ R U) (hUV : ∀ x y, U x y ≤ V x y) : CellLowerBound t σ R V :=
  fun x y => (hU x y).trans (hUV x y)

theorem physical_cellLowerBound {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) :
    CellLowerBound t σ R (fun x y => physicalProfile t σ R ‖x-y‖) := by
  intro x y
  have hb := attraction_le_mixedEnvelope ht hσ hR hs x y
  change attraction t σ R ‖x-y‖ ≤ physicalCoupling t σ R (cellIndex x) (cellIndex y) at hb
  dsimp only [physicalProfile]
  split_ifs
  · linarith only [hb]
  · linarith only [hb, coreProfile_nonneg t ‖x-y‖]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem attraction_add (t : ℝ) {σ τ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ) (r : ℝ) :
    attraction t (fun n => σ n+τ n) R r = attraction t σ R r+attraction t τ R r := by
  unfold attraction
  simp_rw [add_mul]
  rw [Summable.tsum_add (summable_attraction_terms hσ hR hs r) (summable_attraction_terms hτ hR hτs r)]
  ring

theorem physicalProfile_add_mono {t : ℝ} (ht : 0 ≤ t) {σ τ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ) (r : ℝ) :
    physicalProfile t (fun n => σ n+τ n) R r ≤ physicalProfile t σ R r := by
  rw [physicalProfile, physicalProfile, attraction_add t hσ hτ hR hs hτs r]
  linarith only [attraction_nonneg ht hτ hR r]

theorem physicalProfile_add_diff (t : ℝ) {σ τ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ) (r : ℝ) :
    physicalProfile t σ R r-physicalProfile t (fun n => σ n+τ n) R r = attraction t τ R r := by
  simp only [physicalProfile, attraction_add t hσ hτ hR hs hτs r]
  ring

theorem measurable_physical_interaction (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) :
    Measurable (fun p : Space × Space => physicalProfile t σ R ‖p.1-p.2‖) :=
  (measurable_physicalProfile t hσ hR hs).comp ((measurable_fst.sub measurable_snd).norm)

theorem physicalProfile_le_core {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (r : ℝ) :
    physicalProfile t σ R r ≤ coreProfile t r :=
  sub_le_self _ (attraction_nonneg ht hσ hR r)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.CoerciveCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem finiteCanonical_lower_coercive {t β L : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hL : 0 < L)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) (N : ℕ) :
    β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/L)^3)*((N : ℝ)/L^3)^2 +
      ((N : ℝ)/L^3)*Real.log ((N : ℝ)/L^3)-(β*t^2/2+1)*((N : ℝ)/L^3) ≤
      finiteCanonical (physicalProfile t σ R) β L N := by
  by_cases hN : N = 0
  · simp [hN]
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht hσ hR hs hsmall
  have hh := neg_log_partition_lower hφ hβ hL hst hN
    (physicalProfile_energy_coercive ht hL.le hσ hR hs hsmall N)
  have hd := div_le_div_of_nonneg_right hh (pow_pos hL 3).le
  unfold finiteCanonical
  convert hd using 1; try rfl
  field_simp
  ring

theorem canonicalDensity_lower_coercive {t β d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) (hd : 0 ≤ d) :
    β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)*d^2 +
      d*Real.log d-(β*t^2/2+1)*d ≤ canonicalDensity (physicalProfile t σ R) β d := by
  let : Fact (0 ≤ d) := ⟨hd⟩
  have ht0 : 0 ≤ t := (lt_trans zero_lt_one ht).le
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0 hσ hR hs hsmall
  have hcore (r : ℝ) (_ : 0 < r) := physicalProfile_le_core ht0 hσ hR r
  have hlim := finiteCanonical_tendsto hφ ht hβ hst hcore hd
  have hi := tendsto_inv_atTop_zero.comp (densityFilter_length d)
  have hc : Tendsto (fun p : ℝ × ℕ =>
      (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/p.1)^3)
      (densityFilter d) (𝓝 ((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)) := by
    have hh := (tendsto_const_nhds (x := t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)).div
      ((tendsto_const_nhds.add (hi.const_mul 2)).pow 3)
      (by norm_num : (4+2*(0 : ℝ))^3 ≠ 0)
    change Tendsto (fun p : ℝ × ℕ =>
      (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2*(p.1)⁻¹)^3)
      (densityFilter d) (𝓝 ((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/((4+2*(0 : ℝ))^3))) at hh
    simpa only [mul_zero, add_zero, div_eq_mul_inv, Function.comp_def, Pi.mul_apply, Pi.inv_apply,
      show (4 : ℝ)^3 = 64 by norm_num] using hh
  have he := (((hc.const_mul β).mul ((densityFilter_density d).pow 2)).add
    (Real.continuous_mul_log.continuousAt.tendsto.comp (densityFilter_density d))).sub
    ((densityFilter_density d).const_mul (β*t^2/2+1))
  apply le_of_tendsto_of_tendsto he hlim
  filter_upwards [(densityFilter_length d).eventually (eventually_gt_atTop 0)] with p hp
  exact finiteCanonical_lower_coercive ht0 hβ hp hσ hR hs hsmall p.2

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.QuadraticLaplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem quadraticPressure_bddAbove {t β μ a : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (ha : a ≤ β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)) :
    BddAbove ((fun d : ℝ => μ*d+a*d^2-canonicalDensity (physicalProfile t σ R) β d) '' Ici 0) := by
  refine ⟨Real.exp (μ+β*t^2/2), ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  have hh := canonicalDensity_lower_coercive ht hβ hσ hR hs hsmall hd
  have he := entropy_dual_bound (μ+β*t^2/2) hd
  have hq := mul_le_mul_of_nonneg_right ha (sq_nonneg d)
  linarith

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ThermodynamicExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

theorem sum_twoBoxCounts {M : Type u_1} [AddCommMonoid M] (f : ℕ → M)
    {K k : ℕ} (hk : k ≤ K) (n₁ n₂ : ℕ) :
    ∑ i, f (twoBoxCounts K k n₁ n₂ i) = k • f n₁ + (K-k) • f n₂ := by
  induction K generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    simp [hk0]
  | succ K ih =>
    cases k with
    | zero => simp [twoBoxCounts]
    | succ k =>
      have hkle : k ≤ K := by omega
      simp only [twoBoxCounts, Fin.sum_univ_succ, Fin.val_zero, Nat.zero_lt_succ,
        ite_true, Fin.val_succ, Nat.succ_lt_succ_iff]
      rw [show (∑ i : Fin K, f (if (i : ℕ) < k then n₁ else n₂)) =
          k • f n₁ + (K-k) • f n₂ from ih hkle]
      simp only [Nat.succ_sub_succ_eq_sub, succ_nsmul]
      abel

theorem tileCount_exact {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (k : ℕ) :
    tileCount ℓ ((k : ℝ) * (ℓ+2)) = k^3 := by
  have hh : ℓ+2 ≠ 0 := by linarith
  simp [tileCount, mul_div_cancel_right₀ _ hh]

theorem mixCount_le {θ : ℝ} (hθ1 : θ ≤ 1) (n : ℕ) : mixCount θ n ≤ n^3 := by
  have hx : θ*(n : ℝ)^3 ≤ (n : ℝ)^3 :=
    mul_le_of_le_one_left (pow_nonneg (Nat.cast_nonneg n) 3) hθ1
  simpa only [mixCount, ← Nat.cast_pow, Nat.floor_natCast] using Nat.floor_mono hx

theorem tendsto_mixCount {θ : ℝ} (hθ : 0 ≤ θ) :
    Tendsto (fun n : ℕ => (mixCount θ n : ℝ)/(n : ℝ)^3) atTop (𝓝 θ) :=
  (tendsto_nat_floor_mul_div_atTop hθ).comp
    ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp tendsto_natCast_atTop_atTop)

theorem tendsto_mixSide : Tendsto mixSide atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [] with n
  dsimp [mixSide]
  nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]

theorem mixTotal_ratio {θ d₁ d₂ : ℝ} (hθ1 : θ ≤ 1) {n : ℕ} (hn : 0 < n) :
    (mixTotal θ d₁ d₂ n : ℝ)/(mixSide n)^3 =
      ((n : ℝ)+2)⁻¹^3*(n : ℝ)^3 *
        (((mixCount θ n : ℝ)/(n : ℝ)^3)*((mixCount d₁ n : ℝ)/(n : ℝ)^3) +
        (1-(mixCount θ n : ℝ)/(n : ℝ)^3)*((mixCount d₂ n : ℝ)/(n : ℝ)^3)) := by
  have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hn2 : (n : ℝ)+2 ≠ 0 := by positivity
  unfold mixTotal mixSide
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (mixCount_le hθ1 n), Nat.cast_pow]
  field_simp

theorem tendsto_mixTotal {θ d₁ d₂ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) :
    Tendsto (fun n : ℕ => (mixTotal θ d₁ d₂ n : ℝ)/(mixSide n)^3)
      atTop (𝓝 (θ*d₁+(1-θ)*d₂)) := by
  have hdil := dilution_tendsto_one.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := hdil.mul (((tendsto_mixCount hθ).mul (tendsto_mixCount hd₁)).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_mixCount hθ)).mul (tendsto_mixCount hd₂)))
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (mixTotal_ratio hθ1 hn).symm

theorem mixBox_inequality {a : ℝ → ℕ → ℝ} (hbox : HasBoxInequality a)
    {θ d₁ d₂ : ℝ} (hθ1 : θ ≤ 1) {n : ℕ} (hnpos : 0 < n) :
    a (mixSide n) (mixTotal θ d₁ d₂ n) ≤
      ((n : ℝ)+2)⁻¹^3*(n : ℝ)^3 *
        (((mixCount θ n : ℝ)/(n : ℝ)^3)*a (n : ℝ) (mixCount d₁ n) +
        (1-(mixCount θ n : ℝ)/(n : ℝ)^3)*a (n : ℝ) (mixCount d₂ n)) := by
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hcount : tileCount (n : ℝ) (mixSide n) = n^3 := tileCount_exact hnp.le n
  have hk : mixCount θ n ≤ n^3 := mixCount_le hθ1 n
  have hk' : mixCount θ n ≤ tileCount (n : ℝ) (mixSide n) := hcount.symm ▸ hk
  have hx := hbox (n : ℝ) (mixSide n) hnp (by dsimp [mixSide]; positivity)
    (twoBoxCounts (tileCount (n : ℝ) (mixSide n)) (mixCount θ n)
      (mixCount d₁ n) (mixCount d₂ n))
  rw [sum_twoBoxCounts (fun m : ℕ => m) hk', sum_twoBoxCounts (a (n : ℝ)) hk'] at hx
  simp only [nsmul_eq_mul, hcount] at hx
  change a (mixSide n) (mixTotal θ d₁ d₂ n) ≤ _ at hx
  refine hx.trans_eq ?_
  unfold mixSide
  rw [Nat.cast_sub hk, Nat.cast_pow]
  have hn2 : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp

theorem convexOn_of_box_limits {a : ℝ → ℕ → ℝ} {F : ℝ → ℝ}
    (hbox : HasBoxInequality a)
    (hlim : ∀ d : ℝ, 0 ≤ d → Tendsto (fun p : ℝ × ℕ => a p.1 p.2)
      (densityFilter d) (𝓝 (F d))) : ConvexOn ℝ (Ici 0) F := by
  refine ⟨convex_Ici _, ?_⟩
  intro d₁ hd₁ d₂ hd₂ θ η hθ hη hsum
  simp only [smul_eq_mul]
  have hθ1 : θ ≤ 1 := by linarith
  have hηeq : η = 1-θ := by linarith
  subst η
  have hd : 0 ≤ θ*d₁+(1-θ)*d₂ := add_nonneg (mul_nonneg hθ hd₁) (mul_nonneg hη hd₂)
  have hdil := dilution_tendsto_one.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hseq : Tendsto (fun n : ℕ => (mixSide n, mixTotal θ d₁ d₂ n))
      atTop (densityFilter (θ*d₁+(1-θ)*d₂)) :=
    tendsto_densityFilter_iff.mpr ⟨tendsto_mixSide, tendsto_mixTotal hθ hθ1 hd₁ hd₂⟩
  have hvN : Tendsto (fun n => a (mixSide n) (mixTotal θ d₁ d₂ n))
      atTop (𝓝 (F (θ*d₁+(1-θ)*d₂))) := (hlim _ hd).comp hseq
  have hva₁ : Tendsto (fun n : ℕ => a (n : ℝ) (mixCount d₁ n)) atTop (𝓝 (F d₁)) :=
    (hlim _ hd₁).comp ((floor_density_tendsto hd₁).comp tendsto_natCast_atTop_atTop)
  have hva₂ : Tendsto (fun n : ℕ => a (n : ℝ) (mixCount d₂ n)) atTop (𝓝 (F d₂)) :=
    (hlim _ hd₂).comp ((floor_density_tendsto hd₂).comp tendsto_natCast_atTop_atTop)
  have hR := hdil.mul (((tendsto_mixCount hθ).mul hva₁).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_mixCount hθ)).mul hva₂))
  simp only [one_mul] at hR
  apply le_of_tendsto_of_tendsto hvN hR
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hnpos
  exact mixBox_inequality hbox hθ1 hnpos

theorem convexOn_canonicalDensity {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    ConvexOn ℝ (Ici 0) (canonicalDensity φ β) := by
  apply convexOn_of_box_limits
    (finiteCanonical_hasBoxInequality hφ hβ hstable (fun r hr =>
      (hcore r (lt_of_lt_of_le (by norm_num) hr)).trans_eq (coreProfile_eq_zero ht hr)))
  exact fun d hd => finiteCanonical_tendsto hφ ht hβ hstable hcore hd

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PressureDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem convex_rightDeriv_support {f : ℝ → ℝ} {S : Set ℝ} (hf : ConvexOn ℝ S f)
    {x : ℝ} (hx : x ∈ interior S) :
    ∀ y ∈ S, f x + derivWithin f (Ioi x) x * (y-x) ≤ f y := by
  intro y hy
  obtain hxy | rfl | hyx := lt_trichotomy x y
  · have hh := hf.rightDeriv_le_slope_of_mem_interior hx hy hxy
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr hxy)).1 hh
    linarith
  · simp
  · have hh := (hf.slope_le_leftDeriv_of_mem_interior hy hx hyx).trans
      (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr hyx)).1 hh
    nlinarith only [hh']

theorem canonicalPressure_le_exp {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    canonicalPressure φ β μ ≤ Real.exp (μ+β*B) := by
  unfold canonicalPressure
  apply csSup_le (s := (fun d : ℝ => μ*d-canonicalDensity φ β d) '' Ici 0)
      ⟨μ*0-canonicalDensity φ β 0, ⟨0, by simp, rfl⟩⟩
  rintro _ ⟨d, hd, rfl⟩
  have hh := canonicalDensity_lower_entropy hφ ht hβ hstable hcore hd
  have he := entropy_dual_bound (μ+β*B) hd
  linarith

theorem canonical_fenchel_inequality {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B μ d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    μ*d-canonicalPressure φ β μ ≤ canonicalDensity φ β d := by
  have hh := le_csSup (canonicalPressure_bddAbove hφ ht hβ hstable hcore (μ := μ))
    (mem_image_of_mem (fun d : ℝ => μ*d-canonicalDensity φ β d) hd)
  change μ*d-canonicalDensity φ β d ≤ canonicalPressure φ β μ at hh
  linarith

theorem canonical_fenchel_attained {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 < d) :
    ∃ μ, canonicalPressure φ β μ = μ*d-canonicalDensity φ β d := by
  let μ := derivWithin (canonicalDensity φ β) (Ioi d) d
  have hs := convex_rightDeriv_support (convexOn_canonicalDensity hφ ht hβ hstable hcore)
    (show d ∈ interior (Ici (0 : ℝ)) by simpa using hd)
  refine ⟨μ, le_antisymm ?_ ?_⟩
  · unfold canonicalPressure
    apply csSup_le (s := (fun d : ℝ => μ*d-canonicalDensity φ β d) '' Ici 0)
      ⟨μ*0-canonicalDensity φ β 0, ⟨0, by simp, rfl⟩⟩
    rintro _ ⟨c, hc, rfl⟩
    have hh := hs c hc
    dsimp [μ]
    nlinarith only [hh]
  · exact le_csSup (canonicalPressure_bddAbove hφ ht hβ hstable hcore (μ := μ))
      ⟨d, hd.le, rfl⟩

theorem canonical_partialConjugate {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    IsPartialConjugate (fun x => canonicalPressure φ x.1 x.2) (canonicalDensity φ) := by
  intro β d hβ hd
  constructor
  · rintro _ ⟨μ, rfl⟩
    exact canonical_fenchel_inequality hφ ht hβ.le hstable hcore hd
  · intro z hz
    obtain rfl | hd := hd.eq_or_lt
    · rw [canonicalDensity_zero hφ ht hβ.le hstable hcore]
      by_contra hneg
      have hzneg : z < 0 := lt_of_not_ge hneg
      let μ := Real.log (-z/2)-β*B
      have hQ := canonicalPressure_le_exp hφ ht hβ.le hstable hcore (μ := μ)
      have he : Real.exp (μ+β*B) = -z/2 := by
        dsimp [μ]
        rw [sub_add_cancel, Real.exp_log (by linarith)]
      rw [he] at hQ
      have hbound := hz (mem_range_self μ)
      dsimp at hbound
      linarith
    · obtain ⟨μ, hμ⟩ := canonical_fenchel_attained hφ ht hβ.le hstable hcore hd
      have hh := hz (mem_range_self μ)
      dsimp at hh
      rw [hμ] at hh
      linarith

theorem physical_partialConjugate {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    IsPartialConjugate (physicalPressure φ t) (physicalCanonical φ t) := by
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  intro β d hβ hd
  have hh := canonical_partialConjugate hφ ht hstable hcore β d hβ hd
  constructor
  · rintro _ ⟨h, rfl⟩
    have hz := hh.1 (mem_range_self (t*h))
    dsimp [physicalPressure, physicalCanonical]
    apply (le_div_iff₀ ht0).2
    have hne : t ≠ 0 := ht0.ne'
    field_simp [hne]
    dsimp only at hz
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hz
  · intro z hz
    apply (div_le_iff₀ ht0).2
    apply hh.2
    rintro _ ⟨μ, rfl⟩
    have hm := hz (mem_range_self (μ/t))
    dsimp [physicalPressure] at hm
    rw [mul_div_cancel₀ _ ht0.ne'] at hm
    have hm' := mul_le_mul_of_nonneg_right hm ht0.le
    dsimp [physicalCanonical]
    field_simp [ht0.ne'] at hm'
    nlinarith only [hm']

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PressureRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem convexOn_physicalPressure {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    ConvexOn ℝ pressureDomain (physicalPressure φ t) := by
  have hcD : Convex ℝ pressureDomain :=
    (convexOn_log_grandPartition hφ (by norm_num : (0 : ℝ) < 1) hstable t).1
  refine ⟨hcD, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hcD hx hy ha hb hab
  have hl := physicalPressure_tendsto hφ ht (le_of_lt hz) hstable hcore (h := (a • x+b • y).2)
  have hr := ((physicalPressure_tendsto hφ ht (le_of_lt hx) hstable hcore (h := x.2)).const_mul a).add
    ((physicalPressure_tendsto hφ ht (le_of_lt hy) hstable hcore (h := y.2)).const_mul b)
  simp only [smul_eq_mul]
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hh := (convexOn_log_grandPartition hφ hL hstable t).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh
  have hV : 0 ≤ t*L^3 := mul_nonneg (by linarith) (pow_pos hL 3).le
  have hbound := div_le_div_of_nonneg_right hh hV
  simpa only [add_div, mul_div_assoc] using hbound

theorem isOpen_pressureDomain : IsOpen pressureDomain :=
  isOpen_lt continuous_const continuous_fst

theorem continuousOn_physicalPressure {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    ContinuousOn (physicalPressure φ t) pressureDomain :=
  (convexOn_physicalPressure hφ ht hstable hcore).continuousOn isOpen_pressureDomain

theorem concaveOn_physicalCanonical {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t B d : ℝ} (ht : 1 < t)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) (hd : 0 ≤ d) :
    ConcaveOn ℝ (Ioi 0) (fun β => physicalCanonical φ t β d) := by
  have hh := ConcaveOn.smul (show 0 ≤ t⁻¹ by positivity)
    (concaveOn_canonicalDensity hφ ht hstable hcore hd)
  simpa only [physicalCanonical, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.QuadraticTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma convolution_isLUB {Q H : ℝ → ℝ} {P β h a : ℝ} (hba : 0 ≤ β*a)
    (hQ : ∀ k, IsLUB ((fun d => k*d-H d) '' Ici 0) (Q k))
    (hP : IsLUB ((fun d => h*d+β*a*d^2/2-H d) '' Ici 0) P) :
    IsLUB (range (fun d => Q (h+β*a*d)-β*a*d^2/2)) P := by
  constructor
  · rintro _ ⟨d,rfl⟩
    have hu : Q (h+β*a*d) ≤ P+β*a*d^2/2 := by
      apply (hQ _).2
      rintro _ ⟨r,hr,rfl⟩
      have hh := hP.1 (mem_image_of_mem (fun r => h*r+β*a*r^2/2-H r) hr)
      have hs := mul_nonneg hba (sq_nonneg (r-d))
      nlinarith
    linarith
  · intro z hz
    apply hP.2
    rintro _ ⟨d,hd,rfl⟩
    have hh := (hQ (h+β*a*d)).1 (mem_image_of_mem (fun r => (h+β*a*d)*r-H r) hd)
    have hz' := hz (mem_range_self d)
    nlinarith

lemma isMeanField_meanField {Q P : Parameter → ℝ} {a : ℝ} (h : IsMeanField Q a P) :
    IsMeanField Q a (meanField Q a) := by
  intro x hx
  simpa only [meanField,(h x hx).csSup_eq (range_nonempty _)] using h x hx

lemma meanField_convex {Q P : Parameter → ℝ} {a : ℝ}
    (hQ : ConvexOn ℝ pressureDomain Q) (hP : IsMeanField Q a P) :
    ConvexOn ℝ pressureDomain P := by
  refine ⟨hQ.1,?_⟩
  intro x hx y hy u v hu hv huv
  have hz := hQ.1 hx hy hu hv huv
  apply (hP _ hz).2
  rintro _ ⟨d,rfl⟩
  have hh := hQ.2 (show shiftedField a x d ∈ pressureDomain from hx)
    (show shiftedField a y d ∈ pressureDomain from hy) hu hv huv
  have he : u • shiftedField a x d+v • shiftedField a y d =
      shiftedField a (u • x+v • y) d := by ext <;> dsimp [shiftedField]; ring
  rw [he] at hh
  have h1 := mul_le_mul_of_nonneg_left ((hP x hx).1 (mem_range_self d)) hu
  have h2 := mul_le_mul_of_nonneg_left ((hP y hy).1 (mem_range_self d)) hv
  dsimp [quadraticCost] at *
  nlinarith only [hh,h1,h2]

lemma quadraticCost_continuous {Q : Parameter → ℝ} (hQ : ContinuousOn Q pressureDomain)
    {a : ℝ} {x : Parameter} (hx : x ∈ pressureDomain) :
    Continuous (quadraticCost Q a x) := by
  have hc : Continuous (fun d => Q (shiftedField a x d)) :=
    hQ.comp_continuous (by unfold shiftedField; fun_prop) (fun _ => hx)
  exact hc.sub (by fun_prop)

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TransformAttainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter
namespace ContinuumTemperature

lemma quadratic_bound_attains {f : ℝ → ℝ} (hf : Continuous f) {A B c : ℝ} (hc : 0 < c)
    (hb : ∀ d, f d ≤ A+B*|d|-c*d^2) : ∃ d, ∀ r, f r ≤ f d := by
  let D : ℝ := max 1 (max (2*|B|/c) (2*|A-f 0|/c))
  have hD : 1 ≤ D := le_max_left _ _
  have hDB : 2*|B|/c ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hDA : 2*|A-f 0|/c ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hB : 2*|B| ≤ c*D := by have := (div_le_iff₀ hc).mp hDB; linarith
  have hA : 2*|A-f 0| ≤ c*D := by have := (div_le_iff₀ hc).mp hDA; linarith
  have hout (r : ℝ) (hr : D < |r|) : f r ≤ f 0 := by
    have hr1 : 1 ≤ |r| := hD.trans hr.le
    have hb' := hb r
    have hs : |r|^2 = r^2 := sq_abs r
    have hbmul := mul_le_mul_of_nonneg_right hB (abs_nonneg r)
    have hDmul := mul_le_mul_of_nonneg_left hr.le (show 0 ≤ c*|r| by positivity)
    have hDmul' := mul_le_mul_of_nonneg_left hr.le hc.le
    have hrmul := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ c*|r| by positivity)
    have hbm := mul_le_mul_of_nonneg_right (le_abs_self B) (abs_nonneg r)
    have ha := le_abs_self (A-f 0)
    nlinarith
  obtain ⟨d,hd,hmax⟩ := (isCompact_Icc : IsCompact (Icc (-D) D)).exists_isMaxOn
    (show (Icc (-D) D).Nonempty from ⟨0,by constructor <;> linarith⟩) hf.continuousOn
  refine ⟨d,fun r => ?_⟩
  by_cases hr : |r| ≤ D
  · exact hmax (abs_le.mp hr)
  · exact (hout r (lt_of_not_ge hr)).trans (hmax (show (0 : ℝ) ∈ Icc (-D) D by constructor <;> linarith))

lemma quadratic_upper_bound {Q H : ℝ → ℝ} {c b k : ℝ} (hc : 0 < c)
    (hQ : ∀ h, IsLUB ((fun d => h*d-H d) '' Ici 0) (Q h))
    (hH : ∀ d, 0 ≤ d → c*d^2-b*d-k ≤ H d) (h : ℝ) :
    Q h ≤ (h+b)^2/(4*c)+k := by
  apply (hQ h).2
  rintro _ ⟨d,hd,rfl⟩
  have hh := hH d hd
  have hs := sq_nonneg (2*c*d-(h+b))
  have he : ((h+b)^2/(4*c))*(4*c) = (h+b)^2 := by field_simp
  have hm := mul_le_mul_of_nonneg_right hh (show 0 ≤ 4*c by positivity)
  nlinarith

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalMeanField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter MeasureTheory
noncomputable section
namespace ContinuumTemperature

lemma isLUB_div_image {f : ℝ → ℝ} {S : Set ℝ} {c z : ℝ}
    (hc : 0 < c) (hz : IsLUB (f '' S) z) :
    IsLUB ((fun d => f d/c) '' S) (z/c) := by
  have hh := hz.mul_right (inv_pos.mpr hc).le
  simpa only [image_image,Function.comp_def,← div_eq_mul_inv] using hh

lemma physicalPressure_isLUB {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {t β B h : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r) :
    IsLUB ((fun d => h*d-physicalCanonical φ t β d) '' Ici 0)
      (physicalPressure φ t (β,h)) := by
  have hh : IsLUB ((fun d => (t*h)*d-canonicalDensity φ β d) '' Ici 0)
      (canonicalPressure φ β (t*h)) :=
    isLUB_csSup (Set.Nonempty.image _ nonempty_Ici)
      (canonicalPressure_bddAbove hφ ht hβ hstable hcore)
  have hh' := isLUB_div_image (lt_trans zero_lt_one ht) hh
  convert hh' using 2
  dsimp [physicalCanonical]
  field_simp
  rfl

lemma physical_meanField {t a : ℝ} (ht : 1 < t) (ha : 0 ≤ a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (hgap : t*a/2 ≤ (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64) :
    IsMeanField (physicalPressure (physicalProfile t σ R) t) a
      (fun x => quadraticPressure (physicalProfile t σ R) x.1 (t*x.2) (x.1*(t*a)/2)/t) := by
  intro x hx
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0.le hσ hR hs hsmall
  have hcore := fun r (_ : 0 < r) => physicalProfile_le_core ht0.le hσ hR r
  have hb : x.1*(t*a)/2 ≤ x.1*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64) := by
    have := mul_le_mul_of_nonneg_left hgap (le_of_lt hx)
    nlinarith only [this]
  have hp : IsLUB ((fun d => (t*x.2)*d+(x.1*(t*a)/2)*d^2-
      canonicalDensity (physicalProfile t σ R) x.1 d) '' Ici 0)
      (quadraticPressure (physicalProfile t σ R) x.1 (t*x.2) (x.1*(t*a)/2)) :=
    isLUB_csSup (Set.Nonempty.image _ nonempty_Ici)
      (quadraticPressure_bddAbove ht (le_of_lt hx) hσ hR hs hsmall hb)
  have hpn := isLUB_div_image ht0 hp
  have hpn' : IsLUB ((fun d => x.2*d+x.1*a*d^2/2-
      physicalCanonical (physicalProfile t σ R) t x.1 d) '' Ici 0)
      (quadraticPressure (physicalProfile t σ R) x.1 (t*x.2) (x.1*(t*a)/2)/t) := by
    convert hpn using 2
    dsimp [physicalCanonical]
    field_simp
  exact convolution_isLUB (mul_nonneg (le_of_lt hx) ha)
    (fun h => physicalPressure_isLUB hφ ht (le_of_lt hx) hst hcore (h := h)) hpn'

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.MeanFieldAttainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter
noncomputable section
namespace ContinuumTemperature

lemma meanField_attained {Q P : Parameter → ℝ} {a : ℝ} (ha : 0 < a)
    (hQ : ContinuousOn Q pressureDomain) (hP : IsMeanField Q a P)
    {x : Parameter} (hx : x ∈ pressureDomain) {H : ℝ → ℝ}
    (hdual : ∀ h, IsLUB ((fun d => h*d-H d) '' Ici 0) (Q (x.1,h)))
    {c b k : ℝ} (hc : x.1*a/2 < c)
    (hH : ∀ d, 0 ≤ d → c*d^2-b*d-k ≤ H d) :
    ∃ d, quadraticCost Q a x d = P x := by
  have hba : 0 < x.1*a := mul_pos hx ha
  have hc0 : 0 < c := lt_trans (half_pos hba) hc
  let C := x.1*a/2-(x.1*a)^2/(4*c)
  have hC : 0 < C := by
    have he : ((x.1*a)^2/(4*c))*(4*c) = (x.1*a)^2 := by field_simp
    have hp := mul_pos hba (show 0 < 2*c-x.1*a by linarith)
    dsimp [C]
    nlinarith only [he,hp,hc0]
  let A := (x.2+b)^2/(4*c)+k
  let B := |2*(x.2+b)*(x.1*a)/(4*c)|
  have hbound (d : ℝ) : quadraticCost Q a x d ≤ A+B*|d|-C*d^2 := by
    have hu := quadratic_upper_bound hc0 hdual hH (x.2+x.1*a*d)
    have hb := le_abs_self ((2*(x.2+b)*(x.1*a)/(4*c))*d)
    rw [abs_mul] at hb
    have he : (x.2+x.1*a*d+b)^2/(4*c)+k-x.1*a*d^2/2 =
        A+(2*(x.2+b)*(x.1*a)/(4*c))*d-C*d^2 := by dsimp [A,C]; ring
    change Q (x.1,x.2+x.1*a*d)-x.1*a*d^2/2 ≤ _
    calc
      _ ≤ (x.2+x.1*a*d+b)^2/(4*c)+k-x.1*a*d^2/2 := sub_le_sub_right hu _
      _ = _ := he
      _ ≤ _ := by dsimp [B]; linarith only [hb]
  obtain ⟨d,hd⟩ := quadratic_bound_attains (quadraticCost_continuous hQ hx) hC hbound
  refine ⟨d,le_antisymm ((hP x hx).1 (mem_range_self d)) ?_⟩
  apply (hP x hx).2
  rintro _ ⟨r,rfl⟩
  exact hd r

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.DensityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter MeasureTheory
noncomputable section
namespace ContinuumTemperature

lemma physicalCanonical_quadratic_lower {t β d : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8) (hd : 0 ≤ d) :
    (β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)/t)*d^2-
      (β*t/2)*d-1/t ≤ physicalCanonical (physicalProfile t σ R) t β d := by
  have hh := canonicalDensity_lower_coercive ht hβ hσ hR hs hsmall hd
  have he := entropy_dual_bound 0 hd
  norm_num only [zero_mul,Real.exp_zero,zero_sub] at he
  apply (le_div_iff₀ (lt_trans zero_lt_one ht)).mpr
  have hne : t ≠ 0 := (lt_trans zero_lt_one ht).ne'
  field_simp [hne]
  nlinarith only [he,hh]

lemma physical_meanField_attained {t a : ℝ} (ht : 1 < t) (ha : 0 < a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (hgap : t*a/2 < (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)
    {x : Parameter} (hx : x ∈ pressureDomain) :
    ∃ d, quadraticCost (physicalPressure (physicalProfile t σ R) t) a x d =
      meanField (physicalPressure (physicalProfile t σ R) t) a x := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht0.le hσ hR hs hsmall
  have hcore := fun r (_ : 0 < r) => physicalProfile_le_core ht0.le hσ hR r
  have hP := isMeanField_meanField (physical_meanField ht ha.le hσ hR hs hsmall hgap.le)
  apply meanField_attained ha (continuousOn_physicalPressure hφ ht hst hcore) hP hx
    (fun h => physicalPressure_isLUB hφ ht (le_of_lt hx) hst hcore (h := h))
    (c := x.1*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)/t)
    (b := x.1*t/2) (k := 1/t)
  · apply (lt_div_iff₀ ht0).mpr
    have hh := mul_lt_mul_of_pos_left hgap hx
    nlinarith only [hh]
  · exact fun d hd => physicalCanonical_quadratic_lower ht (le_of_lt hx) hσ hR hs hsmall hd

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TransformBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter MeasureTheory Metric
noncomputable section
namespace ContinuumTemperature

lemma strengthened_smallness {t m : ℝ} (ht : 0 < t)
    (hm : 17576*kernelHeight*m ≤ t) :
    2197*t*kernelHeight*m/2 ≤ t^2/8 ∧
    t^2/16 ≤ t^2/8-2197*t*kernelHeight*m/2 := by
  have hh := mul_le_mul_of_nonneg_left hm ht.le
  constructor <;> nlinarith only [hh,sq_nonneg t]

lemma strengthened_gap {t m a : ℝ} (ht : 0 < t)
    (hm : 17576*kernelHeight*m ≤ t) (ha : 1024*a < t) :
    t*a/2 < (t^2/8-2197*t*kernelHeight*m/2)/64 := by
  have hh := (strengthened_smallness ht hm).2
  have hh' := mul_lt_mul_of_pos_left ha ht
  nlinarith only [hh,hh',sq_nonneg t]

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem isPacking_zero (L : ℝ) : IsPacking L 0 := by
  refine ⟨Fin.elim0, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i

theorem packing_card_cubeCells {ι : Type u_1} [Fintype ι] {L : ℝ}
    (x : ι → Space) (hx : ∀ i, x i ∈ cube L)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖x i-x j‖) : Fintype.card ι ≤ (cubeCells L).card := by
  let f : ι → {k // k ∈ cubeCells L} := fun i =>
    ⟨cellIndex (x i), cellIndex_mem_cubeCells (hx i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hh := dist_lt_one_of_cellIndex_eq (congrArg Subtype.val hij)
    exact (not_lt_of_ge (hsep i j hne)) hh
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem IsPacking.card_bound {L : ℝ} {n : ℕ} (h : IsPacking L n) :
    n ≤ (cubeCells L).card := by
  obtain ⟨x,hx,hs⟩ := h
  simpa only [Fintype.card_fin] using packing_card_cubeCells x hx hs

theorem packingNumber_realized (L : ℝ) : IsPacking L (packingNumber L) := by
  exact Nat.findGreatest_spec (show 0 ≤ (cubeCells L).card from Nat.zero_le _)
    (isPacking_zero L)

theorem IsPacking.le_packingNumber {L : ℝ} {n : ℕ} (h : IsPacking L n) :
    n ≤ packingNumber L := by
  exact Nat.le_findGreatest h.card_bound h

theorem packingNumber_bound {L : ℝ} (hL : 0 ≤ L) :
    (packingNumber L : ℝ) ≤ (4*L+2)^3 :=
  (Nat.cast_le.mpr (packingNumber_realized L).card_bound).trans (card_cubeCells_le hL)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem grandIntegral_mono (F G : ConfigFamily) {A : Set Space} (hA : MeasurableSet A)
    (hFi : ∀ n, IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ A})
    (hGi : ∀ n, IntegrableOn (G (Fin n)) {x | ∀ i, x i ∈ A})
    (hFs : Summable (familyTerm F A)) (hGs : Summable (familyTerm G A))
    (hbound : ∀ n (x : Fin n → Space), (∀ i, x i ∈ A) → F (Fin n) x ≤ G (Fin n) x) :
    grandIntegral F A ≤ grandIntegral G A := by
  apply hFs.tsum_le_tsum _ hGs
  intro n
  change familyIntegral F A (Fin n)/(n.factorial : ℝ) ≤
    familyIntegral G A (Fin n)/(n.factorial : ℝ)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  unfold familyIntegral
  apply setIntegral_mono_on (hFi n) (hGi n)
  · convert MeasurableSet.iInter (fun i : Fin n => hA.preimage
      (measurable_pi_apply i : Measurable (fun x : Fin n → Space => x i))) using 1
    ext x
    simp
  · exact hbound n

theorem grandIntegral_nonneg (F : ConfigFamily) (A : Set Space)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x) :
    0 ≤ grandIntegral F A := tsum_nonneg (familyTerm_nonneg F A hF)

theorem grandIntegral_mono_set (F : ConfigFamily) {A B : Set Space} (hAB : A ⊆ B)
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFi : ∀ n, IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ B})
    (hAs : Summable (familyTerm F A)) (hBs : Summable (familyTerm F B)) :
    grandIntegral F A ≤ grandIntegral F B := by
  apply hAs.tsum_le_tsum _ hBs
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply setIntegral_mono_set (hFi n) (Filter.Eventually.of_forall (hF0 (Fin n)))
  exact Filter.Eventually.of_forall (fun x hx i => hAB (hx i))

theorem familyTerm_const_mul (F : ConfigFamily) (A : Set Space) (c : ℝ) (n : ℕ) :
    familyTerm (fun ι _ x => c*F ι x) A n = c*familyTerm F A n := by
  unfold familyTerm familyIntegral
  rw [integral_const_mul]
  ring

theorem grandIntegral_const_mul (F : ConfigFamily) (A : Set Space) (c : ℝ) :
    grandIntegral (fun ι _ x => c*F ι x) A = c*grandIntegral F A := by
  unfold grandIntegral
  simp_rw [familyTerm_const_mul]
  exact tsum_mul_left

theorem familyTerm_add (F G : ConfigFamily) (A : Set Space) (n : ℕ)
    (hFi : IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ A})
    (hGi : IntegrableOn (G (Fin n)) {x | ∀ i, x i ∈ A}) :
    familyTerm (fun ι _ x => F ι x+G ι x) A n = familyTerm F A n+familyTerm G A n := by
  unfold familyTerm familyIntegral
  rw [integral_add hFi hGi, add_div]

theorem grandIntegral_add (F G : ConfigFamily) (A : Set Space)
    (hFi : ∀ n, IntegrableOn (F (Fin n)) {x | ∀ i, x i ∈ A})
    (hGi : ∀ n, IntegrableOn (G (Fin n)) {x | ∀ i, x i ∈ A})
    (hFs : Summable (familyTerm F A)) (hGs : Summable (familyTerm G A)) :
    grandIntegral (fun ι _ x => F ι x+G ι x) A = grandIntegral F A+grandIntegral G A := by
  unfold grandIntegral
  simp_rw [familyTerm_add F G A _ (hFi _) (hGi _)]
  exact hFs.tsum_add hGs

theorem familyTerm_sum {κ : Type} [Fintype κ] (F : κ → ConfigFamily)
    (A : Set Space) (n : ℕ)
    (hFi : ∀ j, IntegrableOn (F j (Fin n)) {x | ∀ i, x i ∈ A}) :
    familyTerm (fun ι _ x => ∑ j, F j ι x) A n = ∑ j, familyTerm (F j) A n := by
  unfold familyTerm familyIntegral
  rw [integral_finsetSum _ (fun j _ => hFi j), Finset.sum_div]

theorem grandIntegral_sum {κ : Type} [Fintype κ] (F : κ → ConfigFamily)
    (A : Set Space)
    (hFi : ∀ j n, IntegrableOn (F j (Fin n)) {x | ∀ i, x i ∈ A})
    (hFs : ∀ j, Summable (familyTerm (F j) A)) :
    grandIntegral (fun ι _ x => ∑ j, F j ι x) A = ∑ j, grandIntegral (F j) A := by
  unfold grandIntegral
  simp_rw [familyTerm_sum F A _ (fun j => hFi j _)]
  exact Summable.tsum_finsetSum (fun j _ => hFs j)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem GrandFinite.of_bound (F : ConfigFamily) {D : Set Space} (hD : volume D ≠ ⊤)
    {d : ℝ} (hm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hb : ∀ (ι : Type) [Fintype ι] (x : ι → Space), F ι x ≤ Real.exp (d*Fintype.card ι)) :
    GrandFinite F D where
  integrable := fun ι _ => integrableOn_family_of_bound F hD (hm ι) (h0 ι) (hb ι)
  summable := summable_familyTerm_of_bound F hD hm h0 hb

theorem GrandFinite.const_mul {F : ConfigFamily} {D : Set Space}
    (hF : GrandFinite F D) (c : ℝ) : GrandFinite (fun ι _ x => c*F ι x) D where
  integrable := fun ι _ => (hF.integrable ι).const_mul c
  summable := by
    change Summable (fun n => familyTerm (fun ι _ x => c*F ι x) D n)
    simp_rw [familyTerm_const_mul]
    exact hF.summable.mul_left c

theorem GrandFinite.add {F G : ConfigFamily} {D : Set Space}
    (hF : GrandFinite F D) (hG : GrandFinite G D) :
    GrandFinite (fun ι _ x => F ι x+G ι x) D where
  integrable := fun ι _ => (hF.integrable ι).add (hG.integrable ι)
  summable := by
    change Summable (fun n => familyTerm (fun ι _ x => F ι x+G ι x) D n)
    simp_rw [familyTerm_add F G D _ (hF.integrable _) (hG.integrable _)]
    exact hF.summable.add hG.summable

theorem GrandFinite.sum {κ : Type} [Fintype κ] (F : κ → ConfigFamily) {D : Set Space}
    (hF : ∀ j, GrandFinite (F j) D) : GrandFinite (fun ι _ x => ∑ j, F j ι x) D where
  integrable := fun ι _ => integrable_finsetSum _ (fun j _ => (hF j).integrable ι)
  summable := by
    change Summable (fun n => familyTerm (fun ι _ x => ∑ j, F j ι x) D n)
    simp_rw [familyTerm_sum F D _ (fun j => (hF j).integrable _)]
    exact summable_sum (fun j _ => (hF j).summable)

theorem GrandFinite.mono_set {F : ConfigFamily} {A D : Set Space}
    (hF : GrandFinite F D) (hAD : A ⊆ D)
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x) : GrandFinite F A where
  integrable := fun ι _ => (hF.integrable ι).mono_set (fun _ hx i => hAD (hx i))
  summable := by
    apply Summable.of_nonneg_of_le (familyTerm_nonneg F A h0) _ hF.summable
    intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply setIntegral_mono_set (hF.integrable (Fin n)) (Filter.Eventually.of_forall (h0 (Fin n)))
    exact Filter.Eventually.of_forall (fun _ hx i => hAD (hx i))

theorem grandIntegral_half_moment_le (F : ConfigFamily) {D Cset : Set Space}
    (hD : MeasurableSet D) {c K : ℝ} (hK : 0 < K)
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hF : GrandFinite F D) (hfull : GrandFinite (momentFamily F Cset c) D)
    (hhalf : GrandFinite (momentFamily F Cset (c/2)) D) :
    grandIntegral (momentFamily F Cset (c/2)) D ≤
      grandIntegral (momentFamily F Cset c) D/(2*K)+(K/2)*grandIntegral F D := by
  let G : ConfigFamily := fun ι _ x => (2*K)⁻¹*momentFamily F Cset c ι x+(K/2)*F ι x
  have hg : GrandFinite G D := (hfull.const_mul _).add (hF.const_mul _)
  have hb := grandIntegral_mono (momentFamily F Cset (c/2)) G hD
    (fun n => hhalf.integrable (Fin n)) (fun n => hg.integrable (Fin n))
    hhalf.summable hg.summable (fun n x _ => ?_)
  swap
  · have hh := mul_le_mul_of_nonneg_left (exp_half_le (u := c*(occupation Cset x)^2) hK)
      (hF0 (Fin n) x)
    simpa only [momentFamily, G, div_mul_eq_mul_div, mul_add, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm] using hh
  have he : grandIntegral G D = grandIntegral (momentFamily F Cset c) D/(2*K)+
      (K/2)*grandIntegral F D := by
    rw [grandIntegral_add _ _ _ (fun _ => (hfull.const_mul _).integrable _)
      (fun _ => (hF.const_mul _).integrable _) (hfull.const_mul _).summable
      (hF.const_mul _).summable, grandIntegral_const_mul, grandIntegral_const_mul]
    simp only [div_eq_mul_inv]
    ring
  exact hb.trans_eq he

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem GrandFinite.of_le {F G : ConfigFamily} {D : Set Space} (hG : GrandFinite G D)
    (hm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFG : ∀ (ι : Type) [Fintype ι] (x : ι → Space), F ι x ≤ G ι x) : GrandFinite F D := by
  have hi (ι : Type) [Fintype ι] : IntegrableOn (F ι) {x | ∀ i, x i ∈ D} := by
    apply (hG.integrable ι).mono' (hm ι).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 ι x)] using hFG ι x)
  refine ⟨fun ι _ => hi ι, ?_⟩
  apply Summable.of_nonneg_of_le (familyTerm_nonneg F D h0) _ hG.summable
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact integral_mono (hi (Fin n)) (hG.integrable (Fin n)) (hFG (Fin n))

theorem square_product_le_exponentials {c : ℝ} (hc : 0 < c) (x y : ℝ) :
    x*y ≤ (Real.exp (c*x^2)+Real.exp (c*y^2))/(2*c) := by
  have hx := Real.add_one_le_exp (c*x^2)
  have hy := Real.add_one_le_exp (c*y^2)
  apply (le_div_iff₀ (by positivity : 0 < 2*c)).2
  nlinarith [mul_nonneg hc.le (sq_nonneg (x-y))]

theorem occupationPairFamily_nonneg (F : ConfigFamily)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (C D : Set Space) (ι : Type) [Fintype ι] (x : ι → Space) :
    0 ≤ occupationPairFamily F C D ι x :=
  mul_nonneg (hF ι x) (mul_nonneg (occupation_nonneg C x) (occupation_nonneg D x))

theorem occupationPairFamily_le (F : ConfigFamily)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (C D : Set Space) {c : ℝ} (hc : 0 < c) (ι : Type) [Fintype ι] (x : ι → Space) :
    occupationPairFamily F C D ι x ≤
      (2*c)⁻¹*momentFamily F C c ι x+(2*c)⁻¹*momentFamily F D c ι x := by
  have hh := mul_le_mul_of_nonneg_left (square_product_le_exponentials hc (occupation C x) (occupation D x)) (hF ι x)
  simpa only [occupationPairFamily, momentFamily, mul_add, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh

theorem GrandFinite.occupationPair {F : ConfigFamily} {D C₁ C₂ : Set Space}
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFmeas : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (hC₁ : MeasurableSet C₁) (hC₂ : MeasurableSet C₂) {c : ℝ} (hc : 0 < c)
    (h₁ : GrandFinite (momentFamily F C₁ c) D) (h₂ : GrandFinite (momentFamily F C₂ c) D) :
    GrandFinite (occupationPairFamily F C₁ C₂) D := by
  apply GrandFinite.of_le ((h₁.const_mul (2*c)⁻¹).add (h₂.const_mul (2*c)⁻¹))
    (fun ι _ => (hFmeas ι).mul ((measurable_occupation hC₁).mul (measurable_occupation hC₂)))
    (occupationPairFamily_nonneg F hF0 C₁ C₂)
  exact occupationPairFamily_le F hF0 C₁ C₂ hc

theorem grand_pair_moment_le {F : ConfigFamily} {D C₁ C₂ : Set Space}
    (hD : MeasurableSet D)
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFmeas : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (hC₁ : MeasurableSet C₁) (hC₂ : MeasurableSet C₂) {c M : ℝ} (hc : 0 < c)
    (h₁ : GrandFinite (momentFamily F C₁ c) D) (h₂ : GrandFinite (momentFamily F C₂ c) D)
    (hZ : 0 < grandIntegral F D)
    (hb₁ : grandIntegral (momentFamily F C₁ c) D/grandIntegral F D ≤ M)
    (hb₂ : grandIntegral (momentFamily F C₂ c) D/grandIntegral F D ≤ M) :
    grandIntegral (occupationPairFamily F C₁ C₂) D/grandIntegral F D ≤ M/c := by
  let G : ConfigFamily := fun ι _ x => (2*c)⁻¹*momentFamily F C₁ c ι x+(2*c)⁻¹*momentFamily F C₂ c ι x
  have hG : GrandFinite G D := (h₁.const_mul _).add (h₂.const_mul _)
  have hp := GrandFinite.occupationPair hF0 hFmeas hC₁ hC₂ hc h₁ h₂
  have hh := grandIntegral_mono (occupationPairFamily F C₁ C₂) G hD
    (fun n => hp.integrable (Fin n)) (fun n => hG.integrable (Fin n)) hp.summable hG.summable
    (fun n x _ => occupationPairFamily_le F hF0 C₁ C₂ hc (Fin n) x)
  have he : grandIntegral G D = (2*c)⁻¹*grandIntegral (momentFamily F C₁ c) D+
      (2*c)⁻¹*grandIntegral (momentFamily F C₂ c) D := by
    rw [grandIntegral_add _ _ D (fun _ => (h₁.const_mul _).integrable _)
      (fun _ => (h₂.const_mul _).integrable _) (h₁.const_mul _).summable (h₂.const_mul _).summable,
      grandIntegral_const_mul, grandIntegral_const_mul]
  rw [he] at hh
  apply (div_le_div_of_nonneg_right hh hZ.le).trans
  rw [add_div, mul_div_assoc, mul_div_assoc]
  have hci : 0 ≤ (2*c)⁻¹ := by positivity
  have hb := add_le_add (mul_le_mul_of_nonneg_left hb₁ hci) (mul_le_mul_of_nonneg_left hb₂ hci)
  apply hb.trans_eq
  field_simp
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem measurableSet_generalConfigurations {D : Set Space} (hD : MeasurableSet D)
    (ι : Type) [Fintype ι] : MeasurableSet {x : ι → Space | ∀ i, x i ∈ D} := by
  convert MeasurableSet.iInter (fun i : ι => hD.preimage
    (measurable_pi_apply i : Measurable (fun x : ι → Space => x i))) using 1
  ext x
  simp

theorem GrandFinite.of_le_on {F G : ConfigFamily} {D : Set Space} (hD : MeasurableSet D)
    (hG : GrandFinite G D) (hm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFG : ∀ (ι : Type) [Fintype ι] (x : ι → Space), (∀ i, x i ∈ D) → F ι x ≤ G ι x) :
    GrandFinite F D := by
  have hi (ι : Type) [Fintype ι] : IntegrableOn (F ι) {x | ∀ i, x i ∈ D} := by
    apply (hG.integrable ι).mono' (hm ι).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_generalConfigurations hD ι)] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 ι x)] using hFG ι x hx
  refine ⟨fun ι _ => hi ι, ?_⟩
  apply Summable.of_nonneg_of_le (familyTerm_nonneg F D h0) _ hG.summable
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact setIntegral_mono_on (hi (Fin n)) (hG.integrable (Fin n))
    (measurableSet_generalConfigurations hD (Fin n)) (hFG (Fin n))

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GibbsIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem volume_latticeCell_le_one (z : Lattice) : volume (latticeCell z) ≤ 1 := by
  let a : Space := WithLp.toLp 2 (fun k => ((z k : ℝ)+1/2)/4)
  have hsub : latticeCell z ⊆ (fun x : Space => x+(-a)) ⁻¹' cube 1 := by
    intro x hx k
    have he : ⌊4*x k⌋ = z k := congrFun hx k
    have hlo := Int.floor_le (4*x k)
    have hhi := Int.lt_floor_add_one (4*x k)
    rw [he] at hlo hhi
    change -(1 : ℝ)/2 ≤ x k-a k ∧ x k-a k ≤ 1/2
    dsimp only [a]
    constructor <;> linarith
  have hp := (measurePreserving_add_right volume (-a)).measure_preimage (measurableSet_cube 1).nullMeasurableSet
  have hv : volume ((fun x : Space => x+(-a)) ⁻¹' cube 1) = 1 := by
    rw [hp, volume_cube]
    norm_num
  exact (measure_mono hsub).trans_eq hv

theorem real_volume_cropped_cell_le_one (D : Set Space) (z : Lattice) :
    volume.real (D ∩ latticeCell z) ≤ 1 := by
  have hh := (measure_mono (inter_subset_right : D ∩ latticeCell z ⊆ latticeCell z)).trans
    (volume_latticeCell_le_one z)
  simpa only [Measure.real, ENNReal.toReal_one] using ENNReal.toReal_mono (by norm_num) hh

theorem gibbsFamily_term_zero (V : Space → Space → ℝ) (β h : ℝ) (D : Set Space) :
    familyTerm (gibbsFamily V β h) D 0 = 1 := by
  have hf : gibbsFamily V β h (Fin 0) = fun _ => 1 := by
    funext x
    simp only [gibbsFamily, ite_eq_left (Function.injective_of_subsingleton x),
      gibbsEnergy, Fintype.card_fin, Nat.cast_zero, mul_zero, Finset.univ_eq_empty,
      Finset.sum_empty, zero_div, sub_zero, Real.exp_zero]
  dsimp only [familyTerm, familyIntegral]
  rw [hf, setIntegral_const, Measure.real, volume_generalConfigurations]
  norm_num

theorem grandIntegral_gibbs_pos (V : Space → Space → ℝ) (β h : ℝ) (D : Set Space)
    (hs : Summable (familyTerm (gibbsFamily V β h) D)) :
    0 < grandIntegral (gibbsFamily V β h) D := by
  have hh := hs.le_tsum 0 (fun n _ => familyTerm_nonneg _ D (gibbsFamily_nonneg V β h) n)
  rw [gibbsFamily_term_zero] at hh
  exact lt_of_lt_of_le zero_lt_one hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PackingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter Set
namespace ContinuumTemperature

theorem packing_fractions_bddAbove :
    BddAbove ((fun L : ℝ => (packingNumber L : ℝ)/(L+2)^3) '' Ici 0) := by
  refine ⟨64, ?_⟩
  rintro _ ⟨L,hL,rfl⟩
  change 0 ≤ L at hL
  apply (div_le_iff₀ (pow_pos (by linarith : 0 < L+2) 3)).2
  have hh := pow_le_pow_left₀ (by linarith : 0 ≤ 4*L+2)
    (by linarith : 4*L+2 ≤ 4*(L+2)) 3
  have hp := packingNumber_bound hL
  nlinarith only [hp,hh]

theorem packing_fraction_le {L : ℝ} (hL : 0 ≤ L) :
    (packingNumber L : ℝ)/(L+2)^3 ≤ packingDensity :=
  le_csSup packing_fractions_bddAbove ⟨L,hL,rfl⟩

theorem packingDensity_pos : 0 < packingDensity := by
  have hp : IsPacking 0 1 := by
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i j; simp
    · intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
  have hn : (1 : ℝ) ≤ packingNumber 0 := by exact_mod_cast hp.le_packingNumber
  have hh := packing_fraction_le (L := 0) (le_refl 0)
  norm_num at hh
  linarith

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.MomentBootstrap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem grand_local_moment_bound {κ : Type} [Fintype κ]
    (F : ConfigFamily) (Cset : κ → Set Space) (θ : κ → κ → ℝ)
    {D : Set Space} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (hCset : ∀ i, MeasurableSet (Cset i)) {c d v : ℝ}
    (hFrel : RelabelInvariant F)
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hF : GrandFinite F D)
    (hfull : ∀ i, GrandFinite (momentFamily F (Cset i) c) D)
    (hhalf : ∀ i, GrandFinite (momentFamily F (Cset i) (c/2)) D)
    (hZ : 0 < grandIntegral F D)
    (hθ : ∀ i j, 0 ≤ θ i j) (hrow : ∀ i, ∑ j, θ i j ≤ 1)
    (hvol : ∀ i, volume.real (D ∩ Cset i) ≤ v)
    (hinsert : ∀ i (n : ℕ) (s : Finset (Fin n)) (x : Fin n → Space),
      x ∈ binaryRegion (D ∩ Cset i) (D \ Cset i) s →
        momentFamily F (Cset i) c (Fin n) x ≤ Real.exp (d*s.card)*
          (F {j : Fin n // j ∉ s} (fun j => x j)+
            ∑ k, θ i k*momentFamily F (Cset k) (c/2) {j : Fin n // j ∉ s} (fun j => x j))) :
    ∀ i, grandIntegral (momentFamily F (Cset i) c) D/grandIntegral F D ≤
      2*Real.exp (v*Real.exp d)+(Real.exp (v*Real.exp d))^2 := by
  let K := Real.exp (v*Real.exp d)
  have hK : 0 < K := Real.exp_pos _
  let G (i : κ) : ConfigFamily := fun ι _ x => F ι x+
    ∑ j, θ i j*momentFamily F (Cset j) (c/2) ι x
  have hG (i : κ) : GrandFinite (G i) D :=
    hF.add (GrandFinite.sum _ (fun j => (hhalf j).const_mul (θ i j)))
  have hG0 (i : κ) (ι : Type) [Fintype ι] (x : ι → Space) : 0 ≤ G i ι x :=
    add_nonneg (hF0 ι x) (Finset.sum_nonneg (fun j _ => mul_nonneg (hθ i j)
      (momentFamily_nonneg F hF0 _ _ ι x)))
  have hGrel (i : κ) : RelabelInvariant (G i) := by
    intro ι ν _ _ e x
    dsimp only [G]
    rw [hFrel ι ν e x]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [momentFamily_relabel F hFrel (Cset j) (c/2) ι ν e x]
  have hlin (i : κ) : grandIntegral (G i) D = grandIntegral F D+
      ∑ j, θ i j*grandIntegral (momentFamily F (Cset j) (c/2)) D := by
    rw [grandIntegral_add _ _ D (fun n => hF.integrable (Fin n))
      (fun n => (GrandFinite.sum _ (fun j => (hhalf j).const_mul (θ i j))).integrable (Fin n))
      hF.summable (GrandFinite.sum _ (fun j => (hhalf j).const_mul (θ i j))).summable]
    rw [grandIntegral_sum _ D (fun j n => ((hhalf j).const_mul (θ i j)).integrable (Fin n))
      (fun j => ((hhalf j).const_mul (θ i j)).summable)]
    simp_rw [grandIntegral_const_mul]
  have hamb (i : κ) : (D ∩ Cset i) ∪ (D \ Cset i) = D := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_sdiff]
    tauto
  have hb (i : κ) : grandIntegral (momentFamily F (Cset i) c) D ≤
      K*(grandIntegral F D+∑ j, θ i j*grandIntegral (momentFamily F (Cset j) (c/2)) D) := by
    have hBG := (hG i).mono_set (A := D \ Cset i) sdiff_subset (hG0 i)
    have hi := grandIntegral_insertion_bound (momentFamily F (Cset i) c) (G i) (hGrel i)
      (hD.inter (hCset i)) (hD.diff (hCset i))
      (by exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx.2))
      (ne_top_of_le_ne_top hDfin (measure_mono inter_subset_left))
      (fun n => by rw [hamb i]; exact (hfull i).integrable (Fin n))
      (fun ι _ => hBG.integrable ι)
      (by rw [hamb i]; exact (hfull i).summable) hBG.summable (hinsert i)
    rw [hamb i] at hi
    have hm := grandIntegral_mono_set (G i) sdiff_subset (hG0 i)
      (fun n => (hG i).integrable (Fin n)) hBG.summable (hG i).summable
    have he : Real.exp (volume.real (D ∩ Cset i)*Real.exp d) ≤ K :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hvol i) (Real.exp_pos _).le)
    exact hi.trans ((mul_le_mul he hm (grandIntegral_nonneg (G i) _ (hG0 i)) hK.le).trans_eq
      (by rw [hlin i]))
  apply finite_moment_bootstrap
    (fun i => grandIntegral (momentFamily F (Cset i) c) D/grandIntegral F D)
    (fun i => grandIntegral (momentFamily F (Cset i) (c/2)) D/grandIntegral F D)
    θ hK (fun i => div_nonneg (grandIntegral_nonneg _ _ (momentFamily_nonneg F hF0 _ _)) hZ.le)
    hθ hrow
  · intro i
    have hh := grandIntegral_half_moment_le F hD hK hF0 hF (hfull i) (hhalf i)
    apply (div_le_div_of_nonneg_right hh hZ.le).trans_eq
    field_simp
  · intro i
    apply (div_le_div_of_nonneg_right (hb i) hZ.le).trans_eq
    rw [mul_div_assoc, add_div, div_self hZ.ne', Finset.sum_div]
    simp_rw [mul_div_assoc]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PhysicalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem occupation_card_binary {ι : Type} [Fintype ι] (D C : Set Space)
    (s : Finset ι) (x : ι → Space) (hx : x ∈ binaryRegion (D ∩ C) (D \ C) s) :
    occupation C x = (s.card : ℝ) := by
  unfold occupation
  rw [← Fintype.card_coe s]
  congr 1
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  have hh := hx i
  by_cases hi : i ∈ s
  · simp only [ite_eq_left hi] at hh
    exact iff_of_true hh.2 hi
  · simp only [ite_eq_right hi] at hh
    exact iff_of_false hh.2 hi

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ModifiedInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem cellLowerBound_ge_negative {t : ℝ} {σ R : ℕ → ℝ} {V : Space → Space → ℝ}
    (hV : CellLowerBound t σ R V) (x y : Space) :
    -physicalCoupling t σ R (cellIndex x) (cellIndex y) ≤ V x y := by
  have hc : 0 ≤ if cellIndex x = cellIndex y then coreProfile t ‖x-y‖ else 0 := by
    split_ifs; exact coreProfile_nonneg _ _; rfl
  calc
    _ ≤ (if cellIndex x = cellIndex y then coreProfile t ‖x-y‖ else 0)-
        physicalCoupling t σ R (cellIndex x) (cellIndex y) := by linarith only [hc]
    _ ≤ _ := hV x y

theorem cellLowerBound_energy_insertion {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V) (hVsym : ∀ x y, V x y = V y x)
    {ι κ : Type} [Fintype ι] [Fintype κ] (x : ι → Space) (s : Finset ι) (z : Lattice)
    (hx : ∀ i ∈ s, x i ∈ latticeCell z)
    (c : {i : ι // i ∉ s} → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i : {i : ι // i ∉ s}, cellIndex (x i) = e (c i)) :
    (t^2/8-physicalCoupling t σ R z z/2)*(s.card : ℝ)^2-t^2/2*s.card-
      s.card*(∑ k, physicalCoupling t σ R z (e k)*
        occupation (latticeCell (e k)) (fun i : {i : ι // i ∉ s} => x i)) ≤
      gibbsEnergy V x-gibbsEnergy V (fun i : {i : ι // i ∉ s} => x i) := by
  have hfi : Subtype.fintype (fun i : ι => i ∈ s) = Finset.Subtype.fintype s := Subsingleton.elim _ _
  have hsplit := gibbsEnergy_split V hVsym (fun i : ι => i ∈ s) x
  rw [hfi] at hsplit
  have hcore := core_gibbsEnergy_one_cell t (fun i : s => x i) z (fun i => hx i i.property)
  let W : Space → Space → ℝ := fun _ _ => physicalCoupling t σ R z z
  have hw := gibbsEnergy_le_card_sq W (fun i : s => x i)
    (physicalCoupling_nonneg ht hσ hR z z) (fun _ _ => le_refl _)
  have hlo := gibbsEnergy_mono (U := fun x y => coreProfile t ‖x-y‖-W x y) (V := V)
    (fun i : s => x i) (fun i j => by
      have hh := hV (x i) (x j)
      rw [show cellIndex (x i) = z from hx i i.property,
        show cellIndex (x j) = z from hx j j.property, ite_eq_left rfl] at hh
      exact hh)
  rw [gibbsEnergy_sub] at hlo
  have hin : (t^2/8-physicalCoupling t σ R z z/2)*(s.card : ℝ)^2-t^2/2*s.card ≤
      gibbsEnergy V (fun i : s => x i) := by
    simp only [Fintype.card_coe] at hcore hw
    linarith only [hcore, hw, hlo]
  have hcross : -(s.card : ℝ)*(∑ k, physicalCoupling t σ R z (e k)*
      occupation (latticeCell (e k)) (fun i : {i : ι // i ∉ s} => x i)) ≤
      ∑ i : s, ∑ j : {i : ι // i ∉ s}, V (x i) (x j) := by
    have hpoint (i : s) (j : {i : ι // i ∉ s}) :
        -physicalCoupling t σ R z (cellIndex (x j)) ≤ V (x i) (x j) := by
      have hh := cellLowerBound_ge_negative hV (x i) (x j)
      rw [show cellIndex (x i) = z from hx i i.property] at hh
      exact hh
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset s)) =>
      Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset {i : ι // i ∉ s})) => hpoint i j))
    simp only [Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul] at hh
    rw [sum_physicalCoupling_occupations t σ R z (fun i : {i : ι // i ∉ s} => x i) c e he hc] at hh
    simpa only [neg_mul, mul_neg] using hh
  linarith only [hin, hcross, hsplit]

theorem cellLowerBound_insertion_half_moments {t β : ℝ} (ht : 0 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V) (hVsym : ∀ x y, V x y = V y x)
    (h : ℝ) {D : Set Space} {ι κ : Type} [Fintype ι] [Fintype κ]
    (x : ι → Space) (s : Finset ι) (z : Lattice)
    (hx : x ∈ binaryRegion (D ∩ latticeCell z) (D \ latticeCell z) s)
    (e : κ → Lattice) (he : Function.Injective e)
    (c : {i : ι // i ∉ s} → κ) (hc : ∀ i : {i : ι // i ∉ s}, cellIndex (x i) = e (c i)) :
    momentFamily (gibbsFamily V β h) (latticeCell z) (β*(t^2/8)/4) ι x ≤
      Real.exp ((h+β*(t^2/2))*s.card)*
        (gibbsFamily V β h {i : ι // i ∉ s} (fun i => x i)+
        ∑ k, (physicalCoupling t σ R z (e k)/(t^2/8))*
          momentFamily (gibbsFamily V β h) (latticeCell (e k)) ((β*(t^2/8)/4)/2)
            {i : ι // i ∉ s} (fun i => x i)) := by
  have hA : 0 < t^2/8 := by positivity
  have hi := gibbs_moment_insertion V (h := h) hA hsmall
    (physicalCoupling_self_le ht.le hσ hR hs z) hβ (latticeCell z) s x
    (∑ k, physicalCoupling t σ R z (e k)*occupation (latticeCell (e k))
      (fun i : {i : ι // i ∉ s} => x i))
    (occupation_card_binary D (latticeCell z) s x hx)
    (cellLowerBound_energy_insertion ht.le hσ hR hV hVsym x s z
      (fun i hi => by
        have hh := hx i
        simp only [ite_eq_left hi] at hh
        exact hh.2) c e he hc)
  have hh := exp_exterior_field_le (fun k => physicalCoupling t σ R z (e k))
    (fun k => occupation (latticeCell (e k)) (fun i : {i : ι // i ∉ s} => x i))
    hA hβ (fun k => physicalCoupling_nonneg ht.le hσ hR z (e k))
    ((physicalCoupling_row ht.le hσ hR hs e he z).trans hsmall)
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply (mul_le_mul_of_nonneg_left hh (gibbsFamily_nonneg _ β h _ _)).trans_eq
  rw [mul_add, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [momentFamily]
  have hec : β*(t^2/8)/8 = β*(t^2/8)/4/2 := by ring
  rw [hec]
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ModifiedFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem cellLowerBound_gibbs_moment_finite {t β : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V)
    (hVm : Measurable (Function.uncurry V)) {D : Set Space} (hDfin : volume D ≠ ⊤) (h : ℝ) (z : Lattice)
    {c : ℝ} (hc : c ≤ β*(t^2/8)/4) :
    GrandFinite (momentFamily
      (gibbsFamily V β h) (latticeCell z) c) D := by
  apply GrandFinite.of_bound _ hDfin
    (fun ι _ => measurable_momentFamily _ (measurableSet_latticeCell z) c (measurable_gibbsFamily hVm β h ι))
    (momentFamily_nonneg _ (gibbsFamily_nonneg _ β h) _ _)
  intro ι _ x
  apply gibbs_moment_stable_bound _ β h (t^2/2) c _ x
  have he := mul_le_mul_of_nonneg_left (cellLowerBound_moment_energy ht hσ hR hs hsmall hV x z) hβ
  have hcc := mul_le_mul_of_nonneg_right hc (sq_nonneg (occupation (latticeCell z) x))
  nlinarith only [he, hcc]

theorem cellLowerBound_gibbs_finite {t β : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V)
    (hVm : Measurable (Function.uncurry V)) {D : Set Space} (hDfin : volume D ≠ ⊤) (h : ℝ) :
    GrandFinite (gibbsFamily V β h) D := by
  have h0 : (0 : ℝ) ≤ β*(t^2/8)/4 := by positivity
  have hh := cellLowerBound_gibbs_moment_finite ht hβ hσ hR hs hsmall hV hVm hDfin h (fun _ => 0) h0
  have he : momentFamily (gibbsFamily V β h)
      (latticeCell (fun _ => 0)) 0 = gibbsFamily V β h := by
    funext ι inst x
    simp only [momentFamily, zero_mul, Real.exp_zero, mul_one]
  rw [he] at hh
  exact hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ModifiedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem cellLowerBound_exponential_moment_bound {t β : ℝ} (ht : 0 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V)
    (hVm : Measurable (Function.uncurry V)) (hVsym : ∀ x y, V x y = V y x)
    (h L : ℝ) (z : cubeCells L) :
    grandIntegral (momentFamily (gibbsFamily V β h)
      (latticeCell z) (β*(t^2/8)/4)) (cube L)/
      grandIntegral (gibbsFamily V β h) (cube L) ≤
        2*Real.exp (Real.exp (h+β*(t^2/2)))+(Real.exp (Real.exp (h+β*(t^2/2))))^2 := by
  have hfin : volume (cube L) ≠ ⊤ := by rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hF := cellLowerBound_gibbs_finite ht.le hβ hσ hR hs hsmall hV hVm hfin h
  have hA : 0 < t^2/8 := by positivity
  have hc : 0 ≤ β*(t^2/8)/4 := by positivity
  have hfull (i : cubeCells L) := cellLowerBound_gibbs_moment_finite ht.le hβ hσ hR hs hsmall
    hV hVm hfin h i (le_refl (β*(t^2/8)/4))
  have hhalf (i : cubeCells L) := cellLowerBound_gibbs_moment_finite ht.le hβ hσ hR hs hsmall
    hV hVm hfin h i (show (β*(t^2/8)/4)/2 ≤ β*(t^2/8)/4 by linarith only [hc])
  have hb := grand_local_moment_bound
    (gibbsFamily V β h)
    (fun i : cubeCells L => latticeCell i)
    (fun i j => physicalCoupling t σ R i j/(t^2/8))
    (measurableSet_cube L) hfin (fun i => measurableSet_latticeCell i)
    (c := β*(t^2/8)/4) (d := h+β*(t^2/2)) (v := 1)
    (gibbsFamily_relabel _ β h) (gibbsFamily_nonneg _ β h) hF hfull hhalf
    (grandIntegral_gibbs_pos _ β h (cube L) hF.summable)
    (fun i j => div_nonneg (physicalCoupling_nonneg ht.le hσ hR i j) hA.le)
    (fun i => ?_) (fun i => real_volume_cropped_cell_le_one (cube L) i) (fun i n s x hx => ?_) z
  · simpa only [one_mul] using hb
  · rw [← Finset.sum_div]
    apply (div_le_one hA).2
    have hh := (physicalCoupling_row ht.le hσ hR hs
      (fun j : cubeCells L => (j : Lattice)) Subtype.val_injective i).trans hsmall
    linarith only [hh, hA]
  · let c (j : {j : Fin n // j ∉ s}) : cubeCells L :=
      ⟨cellIndex (x j), cellIndex_mem_cubeCells (by
        have hh := hx j
        simp only [ite_eq_right j.property] at hh
        exact hh.1)⟩
    have hi := cellLowerBound_insertion_half_moments ht hβ hσ hR hs hsmall hV hVsym h x s i (by
        intro j
        have hh := hx j
        by_cases hj : j ∈ s
        · simpa only [binaryRegion, ite_eq_left hj] using hh
        · simpa only [binaryRegion, ite_eq_right hj] using hh)
      (fun j : cubeCells L => (j : Lattice)) Subtype.val_injective c (fun _ => rfl)
    convert hi using 1
    congr!

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.PairMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem momentConstant_pos {t β : ℝ} (ht : 0 < t) (hβ : 0 < β) (h : ℝ) :
    0 < momentConstant t β h := by unfold momentConstant; positivity

theorem cellLowerBound_pair_moment {t β : ℝ} (ht : 0 < t) (hβ : 0 < β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V)
    (hVm : Measurable (Function.uncurry V)) (hVsym : ∀ x y, V x y = V y x)
    (h L : ℝ) (z w : cubeCells L) :
    grandIntegral (occupationPairFamily (gibbsFamily V β h) (latticeCell z) (latticeCell w)) (cube L)/
      grandIntegral (gibbsFamily V β h) (cube L) ≤ momentConstant t β h := by
  have hfin : volume (cube L) ≠ ⊤ := by rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hF := cellLowerBound_gibbs_finite ht.le hβ.le hσ hR hs hsmall hV hVm hfin h
  have hfull (i : cubeCells L) := cellLowerBound_gibbs_moment_finite ht.le hβ.le hσ hR hs hsmall
    hV hVm hfin h i (le_refl (β*(t^2/8)/4))
  exact grand_pair_moment_le (measurableSet_cube L) (gibbsFamily_nonneg V β h)
    (fun ι _ => measurable_gibbsFamily hVm β h ι)
    (measurableSet_latticeCell z) (measurableSet_latticeCell w) (by positivity)
    (hfull z) (hfull w) (grandIntegral_gibbs_pos V β h (cube L) hF.summable)
    (cellLowerBound_exponential_moment_bound ht hβ.le hσ hR hs hsmall hV hVm hVsym h L z)
    (cellLowerBound_exponential_moment_bound ht hβ.le hσ hR hs hsmall hV hVm hVsym h L w)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.OccupationEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsEnergy_le_cell_pairs {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (W : Space → Space → ℝ) (hWsym : ∀ x y, W x y = W y x)
    (J : κ → κ → ℝ) (hJ : ∀ k l, 0 ≤ J k l)
    (x : ι → Space) (c : ι → κ) (e : κ → Lattice) (he : Function.Injective e)
    (hc : ∀ i, cellIndex (x i) = e (c i))
    (hW : ∀ i j, W (x i) (x j) ≤ J (c i) (c j)) :
    gibbsEnergy W x ≤ (1/2:ℝ)*∑ k, ∑ l,
      J k l*occupation (latticeCell (e k)) x*occupation (latticeCell (e l)) x := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hf (k : κ) : occupation (latticeCell (e k)) x = (Fintype.card {i : ι // c i = k} : ℝ) := by
    unfold occupation
    congr 1
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    change cellIndex (x i) = e k ↔ c i = k
    rw [hc i, he.eq_iff]
  simp_rw [hf]
  rw [gibbsEnergy_eq_pairSum _ hWsym]
  exact pairSum_le_cell_quadratic c J (fun i j => W (x i) (x j)) hJ (fun i j => hWsym _ _) hW

theorem interactionFamily_nonneg (F : ConfigFamily)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (W : Space → Space → ℝ) (hW : ∀ x y, 0 ≤ W x y) (ι : Type) [Fintype ι] (x : ι → Space) :
    0 ≤ interactionFamily F W ι x := mul_nonneg (hF ι x) (gibbsEnergy_nonneg W hW x)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandInteraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem GrandFinite.cellPairEnvelope {κ : Type} [Fintype κ] {F : ConfigFamily}
    {D : Set Space} (e : κ → Lattice) (J : κ → κ → ℝ)
    (hp : ∀ k l, GrandFinite (occupationPairFamily F (latticeCell (e k)) (latticeCell (e l))) D) :
    GrandFinite (cellPairEnvelope F e J) D :=
  GrandFinite.sum _ (fun k => GrandFinite.sum _ (fun l => (hp k l).const_mul (J k l/2)))

theorem grandIntegral_cellPairEnvelope {κ : Type} [Fintype κ] {F : ConfigFamily}
    {D : Set Space} (e : κ → Lattice) (J : κ → κ → ℝ)
    (hp : ∀ k l, GrandFinite (occupationPairFamily F (latticeCell (e k)) (latticeCell (e l))) D) :
    grandIntegral (cellPairEnvelope F e J) D =
      ∑ k, ∑ l, (J k l/2)*grandIntegral (occupationPairFamily F (latticeCell (e k)) (latticeCell (e l))) D := by
  unfold cellPairEnvelope
  rw [grandIntegral_sum _ D
    (fun k n => (GrandFinite.sum _ (fun l => (hp k l).const_mul (J k l/2))).integrable (Fin n))
    (fun k => (GrandFinite.sum _ (fun l => (hp k l).const_mul (J k l/2))).summable)]
  apply Finset.sum_congr rfl
  intro k _
  rw [grandIntegral_sum _ D (fun l n => ((hp k l).const_mul (J k l/2)).integrable (Fin n))
    (fun l => ((hp k l).const_mul (J k l/2)).summable)]
  simp_rw [grandIntegral_const_mul]

theorem interactionFamily_le_cellPairEnvelope {κ : Type} [Fintype κ] [DecidableEq κ]
    (F : ConfigFamily) (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    {D : Set Space} (e : κ → Lattice) (he : Function.Injective e)
    (hcover : ∀ x ∈ D, ∃ k, cellIndex x = e k)
    (J : κ → κ → ℝ) (hJ : ∀ k l, 0 ≤ J k l)
    (W : Space → Space → ℝ) (hWs : ∀ x y, W x y = W y x)
    (hW : ∀ k l x y, x ∈ D → y ∈ D → cellIndex x = e k → cellIndex y = e l → W x y ≤ J k l)
    (ι : Type) [Fintype ι] (x : ι → Space) (hx : ∀ i, x i ∈ D) :
    interactionFamily F W ι x ≤ cellPairEnvelope F e J ι x := by
  let c (i : ι) : κ := Classical.choose (hcover (x i) (hx i))
  have hc (i : ι) : cellIndex (x i) = e (c i) := Classical.choose_spec (hcover (x i) (hx i))
  have hh := mul_le_mul_of_nonneg_left
    (gibbsEnergy_le_cell_pairs W hWs J hJ x c e he hc
      (fun i j => hW (c i) (c j) (x i) (x j) (hx i) (hx j) (hc i) (hc j))) (hF ι x)
  apply hh.trans_eq
  unfold cellPairEnvelope occupationPairFamily
  simp only [Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem grand_interaction_bound {κ : Type} [Fintype κ] [DecidableEq κ]
    (F : ConfigFamily) {D : Set Space} (hD : MeasurableSet D)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (e : κ → Lattice) (he : Function.Injective e) (hcover : ∀ x ∈ D, ∃ k, cellIndex x = e k)
    (J : κ → κ → ℝ) (hJ : ∀ k l, 0 ≤ J k l)
    (W : Space → Space → ℝ) (hWs : ∀ x y, W x y = W y x)
    (hWm : Measurable (Function.uncurry W)) (hW0 : ∀ x y, 0 ≤ W x y)
    (hW : ∀ k l x y, x ∈ D → y ∈ D → cellIndex x = e k → cellIndex y = e l → W x y ≤ J k l)
    (hp : ∀ k l, GrandFinite (occupationPairFamily F (latticeCell (e k)) (latticeCell (e l))) D)
    {M : ℝ} (hZ : 0 < grandIntegral F D)
    (hmom : ∀ k l, grandIntegral (occupationPairFamily F (latticeCell (e k)) (latticeCell (e l))) D/
      grandIntegral F D ≤ M) :
    GrandFinite (interactionFamily F W) D ∧
      grandIntegral (interactionFamily F W) D/grandIntegral F D ≤ (M/2)*∑ k, ∑ l, J k l := by
  have hG := GrandFinite.cellPairEnvelope e J hp
  have hb := interactionFamily_le_cellPairEnvelope F hF e he hcover J hJ W hWs hW
  have hH := GrandFinite.of_le_on hD hG (fun ι _ => (hFm ι).mul (measurable_gibbsEnergy hWm))
    (interactionFamily_nonneg F hF W hW0) hb
  refine ⟨hH, ?_⟩
  have hi := grandIntegral_mono (interactionFamily F W) (cellPairEnvelope F e J) hD
    (fun n => hH.integrable (Fin n)) (fun n => hG.integrable (Fin n)) hH.summable hG.summable
    (fun n => hb (Fin n))
  rw [grandIntegral_cellPairEnvelope e J hp] at hi
  apply (div_le_div_of_nonneg_right hi hZ.le).trans
  simp only [Finset.sum_div, mul_div_assoc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro l _
  have hh := mul_le_mul_of_nonneg_left (hmom k l) (div_nonneg (hJ k l) (by norm_num : (0:ℝ) ≤ 2))
  convert hh using 1
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GrandPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem grand_log_perturbation_bound (F₀ F₁ H : ConfigFamily) {D : Set Space}
    (hD : MeasurableSet D) (h₀ : GrandFinite F₀ D) (h₁ : GrandFinite F₁ D) (hH : GrandFinite H D)
    (hZ₁ : 0 < grandIntegral F₁ D)
    (hF₁ : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F₁ ι x)
    (B : ConfigFamily)
    (hrel : ∀ (ι : Type) [Fintype ι] (x : ι → Space),
      F₀ ι x = F₁ ι x*Real.exp (-B ι x))
    (hHB : ∀ (ι : Type) [Fintype ι] (x : ι → Space), H ι x = F₁ ι x*B ι x) :
    Real.log (grandIntegral F₁ D)-Real.log (grandIntegral F₀ D) ≤
      grandIntegral H D/grandIntegral F₁ D := by
  let a := grandIntegral H D/grandIntegral F₁ D
  let G : ConfigFamily := fun ι _ x => Real.exp (-a)*((1+a)*F₁ ι x+(-1)*H ι x)
  have hG : GrandFinite G D := ((h₁.const_mul (1+a)).add (hH.const_mul (-1))).const_mul _
  have hpoint (ι : Type) [Fintype ι] (x : ι → Space) : G ι x ≤ F₀ ι x := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a-B ι x))
      (mul_nonneg (Real.exp_pos (-a)).le (hF₁ ι x))
    rw [hrel ι x]
    dsimp only [G]
    rw [hHB ι x]
    have he : Real.exp (-a)*Real.exp (a-B ι x) = Real.exp (-B ι x) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (Real.exp (-a)*F₁ ι x)*(a-B ι x+1) := by ring
      _ ≤ (Real.exp (-a)*F₁ ι x)*Real.exp (a-B ι x) := hh
      _ = F₁ ι x*(Real.exp (-a)*Real.exp (a-B ι x)) := by ring
      _ = _ := by rw [he]
  have hh := grandIntegral_mono G F₀ hD (fun n => hG.integrable (Fin n))
    (fun n => h₀.integrable (Fin n)) hG.summable h₀.summable (fun n x _ => hpoint (Fin n) x)
  have he : grandIntegral G D = Real.exp (-a)*grandIntegral F₁ D := by
    rw [grandIntegral_const_mul, grandIntegral_add _ _ D
      (fun n => (h₁.const_mul _).integrable (Fin n))
      (fun n => (hH.const_mul _).integrable (Fin n))
      (h₁.const_mul _).summable (hH.const_mul _).summable,
      grandIntegral_const_mul, grandIntegral_const_mul]
    dsimp only [a]
    field_simp
    ring
  rw [he] at hh
  have hl := Real.log_le_log (mul_pos (Real.exp_pos (-a)) hZ₁) hh
  rw [Real.log_mul (Real.exp_pos (-a)).ne' hZ₁.ne', Real.log_exp] at hl
  change _ ≤ a
  linarith only [hl]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ModifiedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsFamily_perturbation (U V : Space → Space → ℝ) (β h : ℝ)
    (ι : Type) [Fintype ι] (x : ι → Space) :
    gibbsFamily U β h ι x = gibbsFamily V β h ι x *
      Real.exp (-β*gibbsEnergy (fun x y => U x y-V x y) x) := by
  unfold gibbsFamily
  split_ifs
  · rw [gibbsEnergy_sub, ← Real.exp_add]
    congr 1
    ring
  · simp

theorem modified_log_grand_comparison {t β : ℝ} (ht : 0 < t) (hβ : 0 < β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {U V : Space → Space → ℝ} (hU : CellLowerBound t σ R U) (hV : CellLowerBound t σ R V)
    (hUm : Measurable (Function.uncurry U)) (hVm : Measurable (Function.uncurry V))
    (hUs : ∀ x y, U x y = U y x) (hVs : ∀ x y, V x y = V y x)
    (hVU : ∀ x y, V x y ≤ U x y) (h L : ℝ)
    (J : cubeCells L → cubeCells L → ℝ) (hJ : ∀ k l, 0 ≤ J k l)
    (hbound : ∀ (k l : cubeCells L) x y, x ∈ cube L → y ∈ cube L →
      cellIndex x = k → cellIndex y = l → U x y-V x y ≤ J k l) :
    Real.log (grandIntegral (gibbsFamily V β h) (cube L))-
      Real.log (grandIntegral (gibbsFamily U β h) (cube L)) ≤
      β*(momentConstant t β h/2)*∑ k, ∑ l, J k l := by
  have hfin : volume (cube L) ≠ ⊤ := by rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hF := cellLowerBound_gibbs_finite ht.le hβ.le hσ hR hs hsmall hV hVm hfin h
  have hF₀ := cellLowerBound_gibbs_finite ht.le hβ.le hσ hR hs hsmall hU hUm hfin h
  have hmom (z : cubeCells L) := cellLowerBound_gibbs_moment_finite ht.le hβ.le hσ hR hs hsmall
    hV hVm hfin h z (le_refl (β*(t^2/8)/4))
  have hp (z w : cubeCells L) := GrandFinite.occupationPair (gibbsFamily_nonneg V β h)
    (fun ι _ => measurable_gibbsFamily hVm β h ι) (measurableSet_latticeCell z)
    (measurableSet_latticeCell w) (by positivity : 0 < β*(t^2/8)/4) (hmom z) (hmom w)
  have hZ := grandIntegral_gibbs_pos V β h (cube L) hF.summable
  let W := fun x y => U x y-V x y
  have hWs (x y : Space) : W x y = W y x := by dsimp only [W]; rw [hUs x y, hVs x y]
  have hWm : Measurable (Function.uncurry W) := hUm.sub hVm
  have hWx : ∀ x y, 0 ≤ W x y := fun x y => sub_nonneg.mpr (hVU x y)
  have hcover : ∀ x ∈ cube L, ∃ k : cubeCells L, cellIndex x = (k : Lattice) := fun x hx =>
    ⟨⟨cellIndex x, cellIndex_mem_cubeCells hx⟩, rfl⟩
  obtain ⟨hH, hb⟩ := grand_interaction_bound (gibbsFamily V β h) (measurableSet_cube L)
    (gibbsFamily_nonneg V β h) (fun ι _ => measurable_gibbsFamily hVm β h ι)
    (fun k : cubeCells L => (k : Lattice)) Subtype.val_injective hcover J hJ W hWs hWm hWx hbound hp hZ
    (cellLowerBound_pair_moment ht hβ hσ hR hs hsmall hV hVm hVs h L)
  have he := grand_log_perturbation_bound (gibbsFamily U β h) (gibbsFamily V β h)
    (fun ι _ x => β*interactionFamily (gibbsFamily V β h) W ι x)
    (measurableSet_cube L) hF₀ hF (hH.const_mul β) hZ (gibbsFamily_nonneg V β h)
    (fun ι _ x => β*gibbsEnergy W x)
    (fun ι _ x => by simpa only [neg_mul] using gibbsFamily_perturbation U V β h ι x)
    (fun ι _ x => by dsimp only [interactionFamily]; ring)
  rw [grandIntegral_const_mul, mul_div_assoc] at he
  exact he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hb hβ.le])

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.GibbsMonotonicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem gibbsFamily_antitone {U V : Space → Space → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hUV : ∀ x y, U x y ≤ V x y) (h : ℝ) (ι : Type) [Fintype ι] (x : ι → Space) :
    gibbsFamily V β h ι x ≤ gibbsFamily U β h ι x := by
  unfold gibbsFamily
  split_ifs
  · apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (gibbsEnergy_mono x (fun i j => hUV (x i) (x j))) hβ
    linarith only [hh]
  · rfl

theorem grandIntegral_gibbs_antitone {U V : Space → Space → ℝ} {β : ℝ} (hβ : 0 ≤ β)
    (hUV : ∀ x y, U x y ≤ V x y) (h : ℝ) {D : Set Space} (hD : MeasurableSet D)
    (hU : GrandFinite (gibbsFamily U β h) D) (hV : GrandFinite (gibbsFamily V β h) D) :
    grandIntegral (gibbsFamily V β h) D ≤ grandIntegral (gibbsFamily U β h) D :=
  grandIntegral_mono _ _ hD (fun n => hV.integrable (Fin n)) (fun n => hU.integrable (Fin n))
    hV.summable hU.summable (fun n x _ => gibbsFamily_antitone hβ hUV h (Fin n) x)

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TailComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem physical_log_tail_bound {t β : ℝ} (ht : 0 < t) (hβ : 0 < β)
    {σ τ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ)
    (hsmall : 2197*t*kernelHeight*(∑' n, (σ n+τ n)) ≤ (t^2/8)/8) (h L : ℝ) :
    0 ≤ Real.log (grandPartition (physicalProfile t (fun n => σ n+τ n) R) t β h L)-
      Real.log (grandPartition (physicalProfile t σ R) t β h L) ∧
    Real.log (grandPartition (physicalProfile t (fun n => σ n+τ n) R) t β h L)-
      Real.log (grandPartition (physicalProfile t σ R) t β h L) ≤
      β*(momentConstant t β (t*h)/2)*(cubeCells L).card*(2197*t*kernelHeight*(∑' n, τ n)) := by
  let U := fun x y : Space => physicalProfile t σ R ‖x-y‖
  let V := fun x y : Space => physicalProfile t (fun n => σ n+τ n) R ‖x-y‖
  have hστ (n : ℕ) : 0 ≤ σ n+τ n := add_nonneg (hσ n) (hτ n)
  have hVU (x y : Space) : V x y ≤ U x y := physicalProfile_add_mono ht.le hσ hτ hR hs hτs ‖x-y‖
  have hV := physical_cellLowerBound ht.le hστ hR (hs.add hτs)
  have hU := hV.mono hVU
  have hUm := measurable_physical_interaction t hσ hR hs
  have hVm := measurable_physical_interaction t hστ hR (hs.add hτs)
  have hfin : volume (cube L) ≠ ⊤ := by rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hUF := cellLowerBound_gibbs_finite ht.le hβ.le hστ hR (hs.add hτs) hsmall hU hUm hfin (t*h)
  have hVF := cellLowerBound_gibbs_finite ht.le hβ.le hστ hR (hs.add hτs) hsmall hV hVm hfin (t*h)
  have hmono := grandIntegral_gibbs_antitone hβ.le hVU (t*h) (measurableSet_cube L) hVF hUF
  have hZ := grandIntegral_gibbs_pos U β (t*h) (cube L) hUF.summable
  have hnonneg := sub_nonneg.mpr (Real.log_le_log hZ hmono)
  have hbound := modified_log_grand_comparison ht hβ hστ hR (hs.add hτs) hsmall hU hV hUm hVm
    (fun x y => by simp only [U, norm_sub_rev])
    (fun x y => by simp only [norm_sub_rev]) hVU (t*h) L
    (fun k l => physicalCoupling t τ R k l)
    (fun k l => physicalCoupling_nonneg ht.le hτ hR k l)
    (fun k l x y _ _ hx hy => by
      dsimp only [U, V]
      rw [physicalProfile_add_diff t hσ hτ hR hs hτs]
      have hh := attraction_le_mixedEnvelope ht.le hτ hR hτs x y
      simpa only [hx, hy, physicalCoupling] using hh)
  have hrow := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (cubeCells L))) =>
    physicalCoupling_row ht.le hτ hR hτs (fun l : cubeCells L => (l : Lattice)) Subtype.val_injective k)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe] at hrow
  have hh := hbound.trans (mul_le_mul_of_nonneg_left hrow
    (mul_nonneg hβ.le (div_nonneg (momentConstant_pos ht hβ (t*h)).le (by norm_num))))
  dsimp only [U, V] at hnonneg hh
  rw [grandIntegral_radial, grandIntegral_radial] at hnonneg hh
  refine ⟨hnonneg, ?_⟩
  simpa only [mul_assoc] using hh

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.AppendAttraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem summable_prepend (a : ℝ) {σ : ℕ → ℝ} (hs : Summable σ) : Summable (prepend a σ) := by
  exact (summable_nat_add_iff 1).mp hs

theorem tsum_prepend (a : ℝ) {σ : ℕ → ℝ} (hs : Summable σ) :
    ∑' n, prepend a σ n = a+∑' n, σ n := by
  exact (summable_prepend a hs).tsum_eq_zero_add

theorem attraction_prepend (t : ℝ) {a S : ℝ} {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (r : ℝ) :
    attraction t (prepend a σ) (prepend S R) r = t*a*scaledKernelProfile S r+attraction t σ R r := by
  unfold attraction
  have he : (fun n => prepend a σ n*scaledKernelProfile (prepend S R n) r) =
      prepend (a*scaledKernelProfile S r) (fun n => σ n*scaledKernelProfile (R n) r) := by
    funext n; cases n <;> rfl
  rw [he, tsum_prepend _ (summable_attraction_terms hσ hR hs r)]
  ring

theorem physicalProfile_prepend (t : ℝ) {a S : ℝ} {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ) (r : ℝ) :
    physicalProfile t (prepend a σ) (prepend S R) r = physicalProfile t σ R r-t*a*scaledKernelProfile S r := by
  unfold physicalProfile
  rw [attraction_prepend t hσ hR hs]
  ring

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TriangleSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma vertexCoordinate_center {p : ℝ} (hp : 0 < p) (i : Fin 3) :
    vertexCoordinate p (triangleCenter p) i = 1/3 := by
  fin_cases i <;> norm_num [vertexCoordinate,triangleCenter]
  all_goals field_simp [hp.ne']; ring

lemma vertexCoordinate_affine (p a b : ℝ) (hab : a+b=1) (x y : Parameter) (i : Fin 3) :
    vertexCoordinate p (a • x+b • y) i = a*vertexCoordinate p x i+b*vertexCoordinate p y i := by
  fin_cases i <;> simp [vertexCoordinate]
  · linear_combination -hab
  · ring
  · ring

lemma vertex_halfspace_convex (p c : ℝ) (i : Fin 3) :
    Convex ℝ {z | vertexCoordinate p z i ≤ c} := by
  intro x hx y hy a b ha hb hab
  change vertexCoordinate p (a • x+b • y) i ≤ c
  rw [vertexCoordinate_affine p a b hab]
  exact (add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)).trans_eq (by rw [← add_mul,hab,one_mul])

lemma coordinates_of_near_vertex {p τ : ℝ} {i : Fin 3} {w : Parameter}
    (hw : w ∈ closedBall (triangleVertex p i) τ) :
    |w.1-(triangleVertex p i).1| ≤ τ ∧ |w.2-(triangleVertex p i).2| ≤ τ := by
  simpa only [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
    Real.norm_eq_abs,max_le_iff] using hw

lemma vertexCoordinate_near_other {p τ : ℝ} (hp : 0 < p) (hτ : τ ≤ p/100)
    {i j : Fin 3} (hij : i ≠ j) {w : Parameter}
    (hw : w ∈ closedBall (triangleVertex p j) τ) : vertexCoordinate p w i ≤ 1/6 := by
  obtain ⟨h1,h2⟩ := coordinates_of_near_vertex hw
  obtain ⟨hl1,hu1⟩ := abs_le.mp h1
  obtain ⟨hl2,hu2⟩ := abs_le.mp h2
  apply (mul_le_mul_iff_right₀ hp).mp
  fin_cases i <;> fin_cases j <;> norm_num [vertexCoordinate,triangleVertex] at hl1 hu1 hl2 hu2 ⊢
  all_goals try contradiction
  all_goals field_simp [hp.ne']; nlinarith only [hl1,hu1,hl2,hu2,hτ,hp]

lemma all_vertex_groups_nonempty {p τ : ℝ} (hp : 0 < p) (hτ : τ ≤ p/100)
    (K : Fin 3 → Set Parameter) (hk : ∀ i, K i ⊆ closedBall (triangleVertex p i) τ)
    (hg : triangleCenter p ∈ convexHull ℝ (⋃ i, K i)) : ∀ i, (K i).Nonempty := by
  intro i
  by_contra hn
  have hs : (⋃ j, K j) ⊆ {z | vertexCoordinate p z i ≤ 1/6} := by
    rintro z ⟨_,⟨j,rfl⟩,hz⟩
    have hji : i ≠ j := by intro he; subst j; exact hn ⟨z,hz⟩
    exact vertexCoordinate_near_other hp hτ hji (hk j hz)
  have hh := convexHull_min hs (vertex_halfspace_convex p (1/6) i) hg
  change vertexCoordinate p (triangleCenter p) i ≤ 1/6 at hh
  rw [vertexCoordinate_center hp] at hh
  norm_num at hh

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Regroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma support_ball_of_vertex_groups {P : Parameter → ℝ} {x : Parameter} {p τ γ : ℝ}
    (hgeom : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
      closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w))
    {K : Fin 3 → Set Parameter} (hne : ∀ i, (K i).Nonempty)
    (hK : ∀ i, K i ⊆ closedBall (triangleVertex p i) τ)
    (he : subgradients pressureDomain P x = convexHull ℝ (⋃ i, K i)) :
    closedBall (triangleCenter p) γ ⊆ subgradients pressureDomain P x := by
  choose w hw using hne
  rw [he]
  exact (hgeom w (fun i => hK i (hw i))).trans (convexHull_mono (range_subset_iff.mpr fun i => mem_iUnion.mpr ⟨i,hw i⟩))

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.LocalSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma supportOn_of_local {S : Set Parameter} {F : Parameter → ℝ}
    (hF : ConvexOn ℝ S F) {x v : Parameter} (hx : x ∈ S)
    (hl : ∀ᶠ y in 𝓝 x, F x+pDot v (y-x) ≤ F y) : SupportOn S F x v := by
  intro y hy
  let Z : ℝ → Parameter := fun c => (1-c) • x+c • y
  have hcont : Continuous Z := by dsimp [Z]; fun_prop
  have hZ : Tendsto Z (𝓝 (0:ℝ)) (𝓝 x) := by simpa [Z] using hcont.tendsto 0
  obtain ⟨c,hc,hc1,hcl⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ F x+pDot v (Z c-x) ≤ F (Z c) := by
    have hmem : ∀ᶠ c in 𝓝[>] (0:ℝ), c ∈ Ioi 0 := self_mem_nhdsWithin
    have he : ∀ᶠ c in 𝓝[>] (0:ℝ),
        c ∈ Ioi 0 ∧ c < 1 ∧ F x+pDot v (Z c-x) ≤ F (Z c) :=
      hmem.and ((eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds |>.and
        ((hZ.eventually hl).filter_mono nhdsWithin_le_nhds))
    exact he.exists
  have hc0 : 0 ≤ 1-c := by linarith
  have hh := hF.2 hx hy hc0 hc.le (show (1-c)+c=1 by ring)
  have he : pDot v (Z c-x) = c*pDot v (y-x) := by dsimp [Z,pDot]; ring
  rw [he] at hcl
  change F (Z c) ≤ (1-c)*F x+c*F y at hh
  have hh' : c*(F x+pDot v (y-x)) ≤ c*F y := by nlinarith only [hcl,hh]
  exact (mul_le_mul_iff_right₀ hc).mp (by simpa only [mul_comm] using hh')

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma initial_ball_moderate : closedBall initialPoint (1/2) ⊆ moderateBox := by
  intro x hx
  have hh : |x.1-1| ≤ 1/2 ∧ |x.2-(-3/4)| ≤ 1/2 := by
    simpa only [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
      Real.norm_eq_abs,max_le_iff,initialPoint] using hx
  obtain ⟨h1,h2⟩ := hh
  obtain ⟨h1,h1'⟩ := abs_le.mp h1
  obtain ⟨h2,h2'⟩ := abs_le.mp h2
  exact ⟨by linarith,by linarith,by linarith⟩

lemma moderateBox_subset : moderateBox ⊆ pressureDomain := by
  intro x hx
  change 0 < x.1
  linarith only [hx.1]

lemma physicalProfile_zero (t : ℝ) (R : ℕ → ℝ) :
    physicalProfile t (fun _ => 0) R = coreProfile t := by
  funext r
  simp [physicalProfile,attraction]

lemma physical_convex_bounded {t : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : 17576*kernelHeight*(∑' n, σ n) ≤ t) :
    ConvexOn ℝ pressureDomain (physicalPressure (physicalProfile t σ R) t) := by
  have ht0 := lt_trans zero_lt_one ht
  exact convexOn_physicalPressure (measurable_radialPotential (measurable_physicalProfile t hσ hR hs)) ht
    (physicalProfile_stable ht0.le hσ hR hs (strengthened_smallness ht0 hm).1)
    (fun r _ => physicalProfile_le_core ht0.le hσ hR r)

lemma physical_meanField_bounded {t a : ℝ} (ht : 1 < t) (ha : 0 < a) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hm : 17576*kernelHeight*(∑' n, σ n) ≤ t) (hat : 1024*a < t) :
    IsMeanField (physicalPressure (physicalProfile t σ R) t) a
      (meanField (physicalPressure (physicalProfile t σ R) t) a) ∧
    (∀ x ∈ pressureDomain, ∃ d, quadraticCost (physicalPressure (physicalProfile t σ R) t) a x d =
      meanField (physicalPressure (physicalProfile t σ R) t) a x) := by
  have ht0 := lt_trans zero_lt_one ht
  have hsmall := (strengthened_smallness ht0 hm).1
  have hgap := strengthened_gap ht0 hm hat
  exact ⟨isMeanField_meanField (physical_meanField ht ha.le hσ hR hs hsmall hgap.le),
    fun _ hx => physical_meanField_attained ht ha hσ hR hs hsmall hgap hx⟩

lemma strong_smallness {t m : ℝ} (ht : 0 < t)
    (hm : 140608*kernelHeight*m ≤ t) : 2197*t*kernelHeight*m ≤ (t^2/8)/8 := by
  have h := mul_le_mul_of_nonneg_left hm ht.le
  nlinarith only [h]

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TripleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma HasVertexTriple.support_ball {P : Parameter → ℝ} {x : Parameter} {p b τ γ : ℝ}
    (h : HasVertexTriple P x p b) (hp : 0 < p) (hb : b ≤ τ) (hτ : τ ≤ p/100)
    (hgeom : ∀ w : Fin 3 → Parameter, (∀ i, dist (w i) (triangleVertex p i) ≤ τ) →
      closedBall (triangleCenter p) γ ⊆ convexHull ℝ (range w)) :
    closedBall (triangleCenter p) γ ⊆ subgradients pressureDomain P x := by
  have hK (i : Fin 3) : slopeGroups P x (triangleVertex p) b i ⊆ closedBall (triangleVertex p i) τ :=
    inter_subset_right.trans (closedBall_subset_closedBall hb)
  exact support_ball_of_vertex_groups hgeom
    (all_vertex_groups_nonempty hp hτ _ hK (h.hull ▸ h.center)) hK h.hull

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma ConstructionCap.weak {t M m : ℝ} (h : ConstructionCap t M) (hm : m ≤ M) :
    17576*kernelHeight*m ≤ t := by
  calc
    17576*kernelHeight*m ≤ 17576*kernelHeight*M := mul_le_mul_of_nonneg_left hm (by positivity [kernelHeight_pos])
    _ ≤ 140608*kernelHeight*M := by nlinarith only [mul_pos kernelHeight_pos h.mass_pos]
    _ ≤ t := h.strong

lemma ConstructionCap.small {t M m : ℝ} (h : ConstructionCap t M) (hm : m ≤ M) :
    2197*t*kernelHeight*m ≤ (t^2/8)/8 := by
  apply strong_smallness (lt_trans zero_lt_one h.t_large)
  exact (mul_le_mul_of_nonneg_left hm (by positivity [kernelHeight_pos])).trans h.strong

lemma ConstructionCap.lt_gap {t M a : ℝ} (h : ConstructionCap t M) (ha : a ≤ M) :
    1024*a < t := (mul_le_mul_of_nonneg_left ha (by norm_num)).trans_lt h.gap

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma geometricBudget_pos (n : ℕ) : 0 < geometricBudget n := pow_pos (by norm_num) _
lemma groupRadius_le {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) : groupRadius τ n ≤ τ := by
  dsimp [groupRadius]
  nlinarith only [mul_nonneg hτ (geometricBudget_pos (n+1)).le]
lemma locationRadius_lt (n : ℕ) : locationRadius n < 1/8 := by
  dsimp [locationRadius]
  linarith only [geometricBudget_pos n]

lemma ConstructionStage.mass_total {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    s.a+∑' k, s.σ k ≤ firstMass p+1 :=
  s.mass.trans (sub_le_self _ (geometricBudget_pos n).le)

lemma ConstructionStage.base_mass {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    ∑' k, s.σ k ≤ firstMass p+1 := by
  linarith only [s.mass_total,s.a_pos]

lemma ConstructionStage.a_le {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    s.a ≤ firstMass p+1 := by
  have hh : 0 ≤ ∑' k, s.σ k := tsum_nonneg s.σ_nonneg
  linarith only [s.mass_total,hh]

lemma ConstructionStage.x_near {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n) :
    s.x ∈ ball initialPoint (1/8) := s.location.trans (locationRadius_lt n)

lemma ConstructionStage.convex {t p τ : ℝ} {n : ℕ} (s : ConstructionStage t p τ n)
    (hcap : ConstructionCap t (firstMass p+1)) : ConvexOn ℝ pressureDomain s.ideal := by
  exact meanField_convex (physical_convex_bounded hcap.t_large s.σ_nonneg s.R_one s.σ_summable (hcap.weak s.base_mass))
    (physical_meanField_bounded hcap.t_large s.a_pos s.σ_nonneg s.R_one s.σ_summable
      (hcap.weak s.base_mass) (hcap.lt_gap s.a_le)).1

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionMasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma prefixMass_nonneg {σ : ℕ → ℝ} (hσ : ∀ k, 0 ≤ σ k) (n k : ℕ) : 0 ≤ prefixMass σ n k := by
  unfold prefixMass
  split_ifs
  · exact hσ k
  · exact le_refl _

lemma tailMass_nonneg {σ : ℕ → ℝ} (hσ : ∀ k, 0 ≤ σ k) (n k : ℕ) : 0 ≤ tailMass σ n k := by
  unfold tailMass
  split_ifs
  · exact hσ k
  · exact le_refl _

lemma prefixMass_add_tailMass (σ : ℕ → ℝ) (n : ℕ) :
    (fun k => prefixMass σ n k+tailMass σ n k) = σ := by
  funext k
  by_cases hk : k < n
  · simp [prefixMass,tailMass,hk,Nat.not_le.mpr hk]
  · simp [prefixMass,tailMass,hk,Nat.le_of_not_gt hk]

lemma prefixMass_summable {σ : ℕ → ℝ} (hσ : ∀ k, 0 ≤ σ k) (hs : Summable σ) (n : ℕ) :
    Summable (prefixMass σ n) := by
  apply hs.of_nonneg_of_le (prefixMass_nonneg hσ n)
  intro k
  unfold prefixMass
  split_ifs <;> simp_all

lemma tailMass_summable {σ : ℕ → ℝ} (hσ : ∀ k, 0 ≤ σ k) (hs : Summable σ) (n : ℕ) :
    Summable (tailMass σ n) := by
  apply hs.of_nonneg_of_le (tailMass_nonneg hσ n)
  intro k
  unfold tailMass
  split_ifs <;> simp_all

lemma tsum_prefixMass (σ : ℕ → ℝ) (n : ℕ) :
    ∑' k, prefixMass σ n k = ∑ k ∈ Finset.range n, σ k := by
  rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
    simp only [Finset.mem_range] at hk
    simp only [prefixMass,ite_eq_right hk])]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [prefixMass,Finset.mem_range.mp hk,ite_true]

lemma tailMass_tsum_tendsto {σ : ℕ → ℝ} (hσ : ∀ k, 0 ≤ σ k) (hs : Summable σ) :
    Tendsto (fun n => ∑' k, tailMass σ n k) atTop (𝓝 0) := by
  have he (n : ℕ) : ∑' k, tailMass σ n k = (∑' k, σ k)-∑ k ∈ Finset.range n, σ k := by
    have hh := (prefixMass_summable hσ hs n).tsum_add (tailMass_summable hσ hs n)
    rw [prefixMass_add_tailMass,tsum_prefixMass] at hh
    linarith
  simp_rw [he]
  simpa only [sub_self] using (tendsto_const_nhds (x := ∑' k, σ k)).sub hs.hasSum.tendsto_sum_nat

lemma ConstructionData.reference_mass {p : ℝ} (C : ConstructionData p) (n : ℕ) :
    ∑' k, (C.stages n).σ k = ∑ k ∈ Finset.range n, C.masses k := by
  induction n with
  | zero => simp [C.initial_zero]
  | succ n ih =>
    rw [(C.transitions n).mass_eq,tsum_prepend _ (C.stages n).σ_summable,ih,Finset.sum_range_succ]
    dsimp [ConstructionData.masses]
    ring

lemma ConstructionData.masses_nonneg {p : ℝ} (C : ConstructionData p) (n : ℕ) : 0 ≤ C.masses n :=
  (C.stages n).a_pos.le

lemma ConstructionData.sum_masses_le {p : ℝ} (C : ConstructionData p) (n : ℕ) :
    ∑ k ∈ Finset.range n, C.masses k ≤ firstMass p+1 := by
  rw [← C.reference_mass]
  exact (C.stages n).base_mass

lemma ConstructionData.masses_summable {p : ℝ} (C : ConstructionData p) : Summable C.masses :=
  summable_of_sum_range_le C.masses_nonneg C.sum_masses_le

lemma ConstructionData.mass_bound {p : ℝ} (C : ConstructionData p) : ∑' k, C.masses k ≤ firstMass p+1 :=
  Real.tsum_le_of_sum_range_le C.masses_nonneg C.sum_masses_le

lemma ConstructionData.ranges_one {p : ℝ} (C : ConstructionData p) (n : ℕ) : 1 ≤ C.ranges n := by
  have hh := (C.transitions n).range_large
  linarith

lemma ConstructionData.reference_profile {p : ℝ} (C : ConstructionData p) (n : ℕ) (r : ℝ) :
    physicalProfile C.t (C.stages n).σ (C.stages n).R r =
      coreProfile C.t r-C.t*∑ k ∈ Finset.range n, C.masses k*scaledKernelProfile (C.ranges k) r := by
  induction n with
  | zero => simp [C.initial_zero,physicalProfile_zero]
  | succ n ih =>
    rw [(C.transitions n).mass_eq,(C.transitions n).range_eq,
      physicalProfile_prepend C.t (C.stages n).σ_nonneg (C.stages n).R_one (C.stages n).σ_summable,ih,
      Finset.sum_range_succ]
    dsimp [ConstructionData.masses]
    ring

lemma attraction_prefixMass (t : ℝ) (σ R : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    attraction t (prefixMass σ n) R r = t*∑ k ∈ Finset.range n, σ k*scaledKernelProfile (R k) r := by
  unfold attraction
  congr 1
  rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
    simp only [Finset.mem_range] at hk
    simp only [prefixMass,ite_eq_right hk,zero_mul])]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [prefixMass,Finset.mem_range.mp hk,ite_true]

lemma ConstructionData.reference_eq_prefix {p : ℝ} (C : ConstructionData p) (n : ℕ) :
    physicalProfile C.t (C.stages n).σ (C.stages n).R = physicalProfile C.t (prefixMass C.masses n) C.ranges := by
  funext r
  rw [C.reference_profile]
  unfold physicalProfile
  rw [attraction_prefixMass]

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionLocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma geometricBudget_tendsto : Tendsto geometricBudget atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma ConstructionData.positions_cauchy {p : ℝ} (C : ConstructionData p) :
    CauchySeq (fun n => (C.stages n).x) := by
  apply cauchySeq_of_le_geometric (1/2) (1/32) (by norm_num)
  intro n
  have hh := (C.transitions n).displacement.le
  rw [dist_comm] at hh
  simpa only [geometricBudget,div_eq_mul_inv,mul_comm,one_mul] using hh

lemma ConstructionData.exists_limit_position {p : ℝ} (C : ConstructionData p) :
    ∃ x : Parameter, Tendsto (fun n => (C.stages n).x) atTop (𝓝 x) ∧
      dist x initialPoint ≤ 1/8 := by
  obtain ⟨x,hx⟩ := cauchySeq_tendsto_of_complete C.positions_cauchy
  refine ⟨x,hx,?_⟩
  apply le_of_tendsto (hx.dist tendsto_const_nhds)
  exact Eventually.of_forall (fun n => (C.stages n).x_near.le)

lemma initial_near_beta {x : Parameter} (hx : dist x initialPoint ≤ 1/8) :
    x.1 ∈ Ioo (1/2:ℝ) (3/2:ℝ) := by
  have hh : |x.1-1| ≤ 1/8 ∧ |x.2-(-3/4)| ≤ 1/8 := by
    simpa only [dist_eq_norm_sub,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
      Real.norm_eq_abs,max_le_iff,initialPoint] using hx
  have hb := hh.1
  rcases abs_le.mp hb with ⟨h₁,h₂⟩
  constructor <;> linarith

lemma initial_near_moderate {x : Parameter} (hx : dist x initialPoint ≤ 1/8) :
    x ∈ moderateBox := initial_ball_moderate (hx.trans (by norm_num : (1:ℝ)/8 ≤ 1/2))

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem cubeCells_card_coarse {L : ℝ} (hL : 1 ≤ L) :
    ((cubeCells L).card : ℝ) ≤ 216*L^3 := by
  have h0 : 0 ≤ L := le_trans zero_le_one hL
  have hh : 4*L+2 ≤ 6*L := by linarith only [hL]
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 4*L+2) hh 3
  have hb := card_cubeCells_le h0
  nlinarith only [hp, hb]

theorem physical_small_subpart {t : ℝ} (ht : 0 ≤ t) {σ τ : ℕ → ℝ}
    (hτ : ∀ n, 0 ≤ τ n) (hs : Summable σ) (hτs : Summable τ)
    (hsmall : 2197*t*kernelHeight*(∑' n, (σ n+τ n)) ≤ (t^2/8)/8) :
    2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8 := by
  have hb := hs.tsum_le_tsum (fun n => le_add_of_nonneg_right (hτ n)) (hs.add hτs)
  have hm := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2197) ht) kernelHeight_pos.le)
  nlinarith only [hm, hsmall, sq_nonneg t]

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.TailPressure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem physical_pressure_tail_bound {t β : ℝ} (ht : 1 < t) (hβ : 0 < β)
    {σ τ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ)
    (hsmall : 2197*t*kernelHeight*(∑' n, (σ n+τ n)) ≤ (t^2/8)/8) (h : ℝ) :
    0 ≤ physicalPressure (physicalProfile t (fun n => σ n+τ n) R) t (β,h)-
      physicalPressure (physicalProfile t σ R) t (β,h) ∧
    physicalPressure (physicalProfile t (fun n => σ n+τ n) R) t (β,h)-
      physicalPressure (physicalProfile t σ R) t (β,h) ≤
      108*2197*β*kernelHeight*momentConstant t β (t*h)*(∑' n, τ n) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hστ (n : ℕ) : 0 ≤ σ n+τ n := add_nonneg (hσ n) (hτ n)
  have hbfull : 2197*t*kernelHeight*(∑' n, (σ n+τ n))/2 ≤ t^2/8 := by
    nlinarith only [hsmall, sq_nonneg t]
  have hbσ := physical_small_subpart ht0.le hτ hs hτs hsmall
  have hlimσ := physicalPressure_tendsto
    (measurable_radialPotential (measurable_physicalProfile t hσ hR hs)) ht hβ.le
    (physicalProfile_stable ht0.le hσ hR hs hbσ)
    (fun r _ => physicalProfile_le_core ht0.le hσ hR r) (h := h)
  have hlimfull := physicalPressure_tendsto
    (measurable_radialPotential (measurable_physicalProfile t hστ hR (hs.add hτs))) ht hβ.le
    (physicalProfile_stable ht0.le hστ hR (hs.add hτs) hbfull)
    (fun r _ => physicalProfile_le_core ht0.le hστ hR r) (h := h)
  have hlim := hlimfull.sub hlimσ
  constructor
  · apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    have hh := (physical_log_tail_bound ht0 hβ hσ hτ hR hs hτs hsmall h L).1
    simpa only [← sub_div] using div_nonneg hh (mul_pos ht0 (pow_pos hL 3)).le
  · apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
    have hh := (physical_log_tail_bound ht0 hβ hσ hτ hR hs hτs hsmall h L).2
    have hcard := cubeCells_card_coarse hL
    have hmc := momentConstant_pos ht0 hβ (t*h)
    have hmass : 0 ≤ ∑' n, τ n := tsum_nonneg hτ
    have hk := kernelHeight_pos
    have hc0 : 0 ≤ β*(momentConstant t β (t*h)/2)*(2197*t*kernelHeight*(∑' n, τ n)) := by
      positivity
    have hcard' := mul_le_mul_of_nonneg_left hcard hc0
    have hb : Real.log (grandPartition (physicalProfile t (fun n => σ n+τ n) R) t β h L)-
        Real.log (grandPartition (physicalProfile t σ R) t β h L) ≤
        (108*2197*β*kernelHeight*momentConstant t β (t*h)*(∑' n, τ n))*(t*L^3) := by
      nlinarith only [hh, hcard']
    rw [← sub_div]
    exact (div_le_iff₀ (mul_pos ht0 (pow_pos hL0 3))).2 hb

end ContinuumTemperature
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.ConstructionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma ConstructionData.pressure_convex {p : ℝ} (C : ConstructionData p) :
    ConvexOn ℝ pressureDomain C.pressure :=
  physical_convex_bounded C.cap.t_large C.masses_nonneg C.ranges_one C.masses_summable (C.cap.weak C.mass_bound)

lemma ConstructionData.pressure_tendsto {p : ℝ} (C : ConstructionData p) {x : Parameter} (hx : x ∈ pressureDomain) :
    Tendsto (fun n => (C.stages n).pressure x) atTop (𝓝 (C.pressure x)) := by
  have hb (n : ℕ) := physical_pressure_tail_bound C.cap.t_large hx
    (prefixMass_nonneg C.masses_nonneg n) (tailMass_nonneg C.masses_nonneg n) C.ranges_one
    (prefixMass_summable C.masses_nonneg C.masses_summable n)
    (tailMass_summable C.masses_nonneg C.masses_summable n)
    (by rw [prefixMass_add_tailMass]; exact C.cap.small C.mass_bound) x.2
  have hb' (n : ℕ) : 0 ≤ C.pressure x-(C.stages n).pressure x ∧
      C.pressure x-(C.stages n).pressure x ≤
      108*2197*x.1*kernelHeight*momentConstant C.t x.1 (C.t*x.2)*(∑' k, tailMass C.masses n k) := by
    have hh := hb n
    rw [prefixMass_add_tailMass,← C.reference_eq_prefix n] at hh
    exact hh
  have hd : Tendsto (fun n => C.pressure x-(C.stages n).pressure x) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (hb' n).1) (fun n => (hb' n).2)
    simpa only [mul_zero] using (tailMass_tsum_tendsto C.masses_nonneg C.masses_summable).const_mul
      (108*2197*x.1*kernelHeight*momentConstant C.t x.1 (C.t*x.2))
  simpa only [sub_sub_cancel,sub_zero] using (tendsto_const_nhds (x := C.pressure x)).sub hd

lemma initial_quarter_subset : ball initialPoint (1/4) ⊆ pressureDomain :=
  ball_subset_closedBall.trans ((closedBall_subset_closedBall (by norm_num : (1:ℝ)/4 ≤ 1/2)).trans
    (initial_ball_moderate.trans moderateBox_subset))

lemma ConstructionData.ideal_tendsto {p : ℝ} (C : ConstructionData p) {x : Parameter}
    (hx : x ∈ ball initialPoint (1/4)) :
    Tendsto (fun n => (C.stages n).ideal x) atTop (𝓝 (C.pressure x)) := by
  have hd : Tendsto (fun n => (C.stages n).ideal x-(C.stages (n+1)).pressure x) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ geometricBudget_tendsto
    intro n
    simpa only [Real.norm_eq_abs,abs_sub_comm] using (C.transitions n).approximation x (ball_subset_closedBall hx)
  have hn := (C.pressure_tendsto (initial_quarter_subset hx)).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hd.add hn

lemma ConstructionData.ideal_locally_uniform {p : ℝ} (C : ConstructionData p) :
    TendstoLocallyUniformlyOn (fun n => (C.stages n).ideal) C.pressure atTop (ball initialPoint (1/4)) := by
  apply convex_pointwise_locally_uniform isOpen_ball
  · exact Eventually.of_forall (fun n => ((C.stages n).convex C.cap).subset initial_quarter_subset (convex_ball _ _))
  · exact fun _ hx => C.ideal_tendsto hx

lemma ConstructionData.limit_support_ball {p : ℝ} (C : ConstructionData p) (hp : 0 < p)
    {x : Parameter} (hx : Tendsto (fun n => (C.stages n).x) atTop (𝓝 x))
    (hnear : dist x initialPoint ≤ 1/8) :
    closedBall (triangleCenter p) C.γ ⊆ subgradients pressureDomain C.pressure x := by
  have hxW : x ∈ ball initialPoint (1/4) := hnear.trans_lt (by norm_num : (1:ℝ)/8 < 1/4)
  have hc := C.pressure_convex.continuousOn isOpen_pressureDomain
  have heval := C.ideal_locally_uniform.tendsto_comp (hc.mono initial_quarter_subset x hxW) hxW
    (tendsto_nhdsWithin_iff.mpr ⟨hx,Eventually.of_forall (fun n =>
      (C.stages n).x_near.trans (by norm_num : (1:ℝ)/8 < 1/4))⟩)
  intro v hv
  apply supportOn_of_local C.pressure_convex (initial_quarter_subset hxW)
  filter_upwards [isOpen_ball.mem_nhds hxW] with y hy
  have hd : Tendsto (fun n => pDot v (y-(C.stages n).x)) atTop (𝓝 (pDot v (y-x))) := by
    exact (show Continuous (fun z : Parameter => pDot v (y-z)) by unfold pDot; fun_prop).continuousAt.tendsto.comp hx
  apply le_of_tendsto_of_tendsto (heval.add hd) (C.ideal_tendsto hy)
  exact Eventually.of_forall (fun n =>
    ((C.stages n).triple.support_ball hp (groupRadius_le C.τ_pos.le n) C.τ_small C.geometry hv) y
      (initial_quarter_subset hy))

end ContinuumTemperature
end
end

end OAI
end

section
-- module Solutions.OAIQW_ContinuumTemperature.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Topology BigOperators
open Set Filter Metric MeasureTheory
noncomputable section
namespace ContinuumTemperature

lemma SlopeBall_subset_closedBall {g : Parameter} {γ : ℝ} (hγ : 0 ≤ γ) :
    SlopeBall g γ ⊆ closedBall g γ := by
  intro v hv
  change (v.1-g.1)^2+(v.2-g.2)^2 ≤ γ^2 at hv
  simp only [mem_closedBall,dist_eq_norm_sub,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
    Real.norm_eq_abs,max_le_iff]
  constructor
  · nlinarith only [hv,sq_nonneg (v.2-g.2),sq_abs (v.1-g.1),abs_nonneg (v.1-g.1),hγ]
  · nlinarith only [hv,sq_nonneg (v.1-g.1),sq_abs (v.2-g.2),abs_nonneg (v.2-g.2),hγ]

theorem main_theorem_oai : MainStatement := by
  obtain ⟨C⟩ := exists_constructionData
  obtain ⟨x,hx,hnear⟩ := C.exists_limit_position
  have ht : 1 < C.t := C.cap.t_large
  have ht0 : 0 < C.t := lt_trans zero_lt_one ht
  have hsmall : 2197*C.t*kernelHeight*(∑' k, C.masses k)/2 ≤ C.t^2/8 := by
    have hh := C.cap.small C.mass_bound
    nlinarith only [hh,sq_nonneg C.t]
  have hφ : Measurable (radialPotential C.profile) :=
    measurable_radialPotential (measurable_physicalProfile C.t C.masses_nonneg C.ranges_one C.masses_summable)
  have hstable := physicalProfile_stable ht0.le C.masses_nonneg C.ranges_one C.masses_summable hsmall
  have hcore : ∀ r, 0 < r → C.profile r ≤ coreProfile C.t r :=
    fun r _ => physicalProfile_le_core ht0.le C.masses_nonneg C.ranges_one r
  have hβ : 0 < x.1 := moderateBox_subset (initial_near_moderate hnear)
  have hball : ∀ v ∈ SlopeBall (triangleCenter packingDensity) C.γ, Supports C.pressure x v := by
    intro v hv
    apply supports_iff_supportOn.mpr
    exact C.limit_support_ball packingDensity_pos hx hnear (SlopeBall_subset_closedBall C.γ_pos.le hv)
  have hg : 0 < (triangleCenter packingDensity).2 := by
    change 0 < 5*packingDensity/3
    positivity [packingDensity_pos]
  obtain ⟨I,hIo,hIc,hIn,hIp,hjump⟩ := canonical_interval_of_support_ball
    (physical_partialConjugate hφ ht hstable hcore) ht0 hβ C.γ_pos hg
    (fun d hd => concaveOn_physicalCanonical hφ ht hstable hcore hd.le) hball
  refine ⟨C.profile,canonicalFreeEnergy C.profile,I,x.1,?_,?_,?_,hIo,hIc,hIn,hIp,initial_near_beta hnear,?_⟩
  · exact admissible_physicalProfile ht C.masses_nonneg C.ranges_one C.masses_summable hsmall
      (C.stages 0).a_pos (C.transitions 0).range_large.le
  · exact physicalProfile_isLittleO ht C.masses_nonneg C.ranges_one C.masses_summable
  · exact hasCanonicalFreeEnergy_of_core hφ ht hstable hcore
  · intro d hd
    obtain ⟨l,r,hl,hr,_,hstrict⟩ := hjump d hd
    have he : (fun β => C.t*physicalCanonical C.profile C.t β d/β) =
        fun β => canonicalFreeEnergy C.profile β d := by
      funext β
      simp only [physicalCanonical,canonicalFreeEnergy]
      congr 1
      field_simp
    rw [he] at hl hr
    exact ⟨l,r,hl,hr,hstrict⟩

end ContinuumTemperature
end
end

end OAI
end

theorem solution : type_of% @OAI.ContinuumTemperature.main_theorem_oai := @OAI.ContinuumTemperature.main_theorem_oai
