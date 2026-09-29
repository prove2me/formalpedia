-- Prove2me | solution 1 for LocalParametrix.exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4c7082b3-ed6c-5a4d-bd26-b4825c81008c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalParametrix_exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton

set_option autoImplicit false

open MeasureTheory Topology Metric

noncomputable section

namespace R4Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def cb {c : E} (f : ContDiffBump c) : E → ℂ := fun x => ((f x : ℝ) : ℂ)

theorem cb_apply {c : E} (f : ContDiffBump c) (x : E) : cb f x = ((f x : ℝ) : ℂ) := rfl

theorem contDiff_cb {c : E} (f : ContDiffBump c) : ContDiff ℝ (⊤ : ℕ∞) (cb f) :=
  Complex.ofRealCLM.contDiff.comp f.contDiff

theorem continuous_cb {c : E} (f : ContDiffBump c) : Continuous (cb f) :=
  Complex.continuous_ofReal.comp f.continuous

theorem hasCompactSupport_cb {c : E} (f : ContDiffBump c) : HasCompactSupport (cb f) :=
  f.hasCompactSupport.comp_left Complex.ofReal_zero

theorem tsupport_cb_subset {c : E} (f : ContDiffBump c) : tsupport (cb f) ⊆ closedBall c f.rOut := by
  rw [← f.tsupport_eq]
  exact closure_mono (Function.support_comp_subset Complex.ofReal_zero f)

theorem cb_eq_one_of_mem {c : E} (f : ContDiffBump c) {x : E} (hx : x ∈ closedBall c f.rIn) :
    cb f x = 1 := by
  rw [cb_apply, f.one_of_mem_closedBall hx, Complex.ofReal_one]

theorem cb_eq_zero_of_le {c : E} (f : ContDiffBump c) {x : E} (hx : f.rOut ≤ dist x c) :
    cb f x = 0 := by
  rw [cb_apply, f.zero_of_le_dist hx, Complex.ofReal_zero]

theorem cb_eventuallyEq_one {c : E} (f : ContDiffBump c) {x : E} (hx : x ∈ ball c f.rIn) :
    cb f =ᶠ[𝓝 x] fun _ => (1 : ℂ) := by
  filter_upwards [f.eventuallyEq_one_of_mem_ball hx] with y hy
  rw [cb_apply, hy, Pi.one_apply, Complex.ofReal_one]

variable [MeasurableSpace E] [BorelSpace E]

theorem main (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (D : (E → ℂ) → (E → ℂ))
    (hD_add : ∀ F G : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G → D (F + G) = D F + D G)
    (hD_cont : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → Continuous (D F))
    (hD_supp : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport (D F) ⊆ tsupport F)
    (hD_tr : ∀ g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∃ h : E → ℂ, Continuous h ∧ tsupport h ⊆ tsupport g ∧
        ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
          ∫ x, D F x * g x ∂μ = ∫ x, F x * h x ∂μ)
    (x₀ : E) (u w : E → ℂ) (hu : Continuous u) (hw : Continuous w)
    (hu' : ContDiffOn ℝ (⊤ : ℕ∞) u {x₀}ᶜ)
    (hid : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      F x₀ = (∫ x, D F x * u x ∂μ) + ∫ x, F x * w x ∂μ)
    (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ := by
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV

  let χ : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let χ₁ : ContDiffBump x₀ := ⟨ε / 8, ε / 4, by positivity, by linarith⟩
  let χ₂ : ContDiffBump x₀ := ⟨ε / 16, ε / 8, by positivity, by linarith⟩
  have hχrIn : χ.rIn = ε / 4 := rfl
  have hχrOut : χ.rOut = ε / 2 := rfl
  have hχ₁rIn : χ₁.rIn = ε / 8 := rfl
  have hχ₁rOut : χ₁.rOut = ε / 4 := rfl
  have hχ₂rIn : χ₂.rIn = ε / 16 := rfl
  have hχ₂rOut : χ₂.rOut = ε / 8 := rfl
  have hballV : closedBall x₀ (ε / 2) ⊆ V :=
    (closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hεV

  set g₁ : E → ℂ := fun x => cb χ x * u x with hg₁_def
  set gt : E → ℂ := fun x => (1 - cb χ₂ x) * (cb χ x * u x) with hgt_def
  have hg₁_cont : Continuous g₁ := (continuous_cb χ).mul hu
  have hg₁_cpt : HasCompactSupport g₁ := (hasCompactSupport_cb χ).mul_right
  have hg₁_tsupp : tsupport g₁ ⊆ closedBall x₀ (ε / 2) :=
    (tsupport_mul_subset_left (f := cb χ) (g := u)).trans (tsupport_cb_subset χ)
  have hgt_cpt : HasCompactSupport gt := by
    change HasCompactSupport ((fun x => 1 - cb χ₂ x) * g₁)
    exact hg₁_cpt.mul_left
  have hgt_tsupp : tsupport gt ⊆ closedBall x₀ (ε / 2) := by
    change tsupport ((fun x => 1 - cb χ₂ x) * g₁) ⊆ _
    exact (tsupport_mul_subset_right (f := fun x => 1 - cb χ₂ x) (g := g₁)).trans hg₁_tsupp
  have hgt_smooth : ContDiff ℝ (⊤ : ℕ∞) gt := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball x₀ χ₂.rIn
    ·
      have hev : gt =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [cb_eventuallyEq_one χ₂ hx] with y hy
        simp only [hgt_def, hy, sub_self, zero_mul]
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev
    · have hxne : x ≠ x₀ := by
        rintro rfl
        exact hx (mem_ball_self χ₂.rIn_pos)
      have hux : ContDiffAt ℝ (⊤ : ℕ∞) u x :=
        hu'.contDiffAt (isOpen_compl_singleton.mem_nhds hxne)
      exact ((contDiff_const.sub (contDiff_cb χ₂)).contDiffAt).mul
        ((contDiff_cb χ).contDiffAt.mul hux)

  obtain ⟨h, hh_cont, hh_supp, hh_id⟩ := hD_tr gt hgt_smooth hgt_cpt
  have hh_tsupp : tsupport h ⊆ closedBall x₀ (ε / 2) := hh_supp.trans hgt_tsupp
  have hh_zero : ∀ x, x ∉ closedBall x₀ (ε / 2) → h x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hh_tsupp hx')

  set g₂ : E → ℂ := fun x => cb χ₁ x * w x - (1 - cb χ₁ x) * h x with hg₂_def
  have hg₂_cont : Continuous g₂ :=
    ((continuous_cb χ₁).mul hw).sub ((continuous_const.sub (continuous_cb χ₁)).mul hh_cont)
  have hg₂_zero : ∀ x, x ∉ closedBall x₀ (ε / 2) → g₂ x = 0 := by
    intro x hx
    have hdist : ε / 2 < dist x x₀ := by
      by_contra hle
      exact hx (mem_closedBall.mpr (not_lt.mp hle))
    have h1 : cb χ₁ x = 0 := cb_eq_zero_of_le χ₁ (by rw [hχ₁rOut]; linarith)
    simp only [hg₂_def, h1, hh_zero x hx, zero_mul, mul_zero, sub_self]
  have hg₂_cpt : HasCompactSupport g₂ :=
    HasCompactSupport.intro (isCompact_closedBall x₀ (ε / 2)) hg₂_zero
  have hg₂_tsupp : tsupport g₂ ⊆ closedBall x₀ (ε / 2) := by
    refine closure_minimal ?_ isClosed_closedBall
    intro x hx
    by_contra hx'
    exact hx (hg₂_zero x hx')
  refine ⟨g₁, g₂, hg₁_cont, hg₂_cont, hg₁_cpt, hg₂_cpt, hg₁_tsupp.trans hballV,
    hg₂_tsupp.trans hballV, ?_⟩

  intro F hF hFc
  set F₁ : E → ℂ := fun x => cb χ₁ x * F x with hF₁_def
  set F₂ : E → ℂ := fun x => (1 - cb χ₁ x) * F x with hF₂_def
  have hF₁s : ContDiff ℝ (⊤ : ℕ∞) F₁ := (contDiff_cb χ₁).mul hF
  have hF₂s : ContDiff ℝ (⊤ : ℕ∞) F₂ := (contDiff_const.sub (contDiff_cb χ₁)).mul hF
  have hF₁c : HasCompactSupport F₁ := by
    change HasCompactSupport (cb χ₁ * F); exact hFc.mul_left
  have hF₂c : HasCompactSupport F₂ := by
    change HasCompactSupport ((fun x => 1 - cb χ₁ x) * F); exact hFc.mul_left
  have hsum : F₁ + F₂ = F := by
    funext x; simp only [Pi.add_apply, hF₁_def, hF₂_def]; ring
  have hF₁x₀ : F₁ x₀ = F x₀ := by
    simp only [hF₁_def]
    rw [cb_eq_one_of_mem χ₁ (mem_closedBall_self χ₁.rIn_pos.le), one_mul]

  have hF₁_tsupp : tsupport F₁ ⊆ closedBall x₀ (ε / 4) :=
    (tsupport_mul_subset_left (f := cb χ₁) (g := F)).trans (tsupport_cb_subset χ₁)
  have hDF₁_tsupp : tsupport (D F₁) ⊆ closedBall x₀ (ε / 4) := (hD_supp F₁ hF₁s hF₁c).trans hF₁_tsupp

  have hDF₂_zero : ∀ x, x ∈ ball x₀ (ε / 8) → D F₂ x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxD
    have hxF : x ∈ tsupport F₂ := hD_supp F₂ hF₂s hF₂c hxD
    have hev : F₂ =ᶠ[𝓝 x] 0 := by
      filter_upwards [cb_eventuallyEq_one χ₁ (by rwa [hχ₁rIn])] with y hy
      simp only [hF₂_def, hy, sub_self, zero_mul, Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hev) hxF

  have hint : ∀ (G k : E → ℂ), Continuous G → Continuous k → HasCompactSupport k →
      Integrable (fun x => G x * k x) μ := fun G k hG hk hkc =>
    (hG.mul hk).integrable_of_hasCompactSupport hkc.mul_left
  have hint' : ∀ (G k : E → ℂ), Continuous G → HasCompactSupport G → Continuous k →
      Integrable (fun x => G x * k x) μ := fun G k hG hGc hk =>
    (hG.mul hk).integrable_of_hasCompactSupport hGc.mul_right

  have ha : F x₀ = (∫ x, D F₁ x * g₁ x ∂μ) + ∫ x, F₁ x * w x ∂μ := by
    rw [← hF₁x₀, hid F₁ hF₁s hF₁c]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : D F₁ x = 0
    · simp only [hx, zero_mul]
    · have hxmem : x ∈ closedBall x₀ (ε / 4) := hDF₁_tsupp (subset_tsupport _ hx)
      simp only [hg₁_def]
      rw [cb_eq_one_of_mem χ (by rwa [hχrIn]), one_mul]

  have hb : (∫ x, D F x * g₁ x ∂μ) = (∫ x, D F₁ x * g₁ x ∂μ) + ∫ x, D F₂ x * g₁ x ∂μ := by
    rw [← integral_add (hint _ _ (hD_cont F₁ hF₁s hF₁c) hg₁_cont hg₁_cpt)
      (hint _ _ (hD_cont F₂ hF₂s hF₂c) hg₁_cont hg₁_cpt)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have := congrFun (hD_add F₁ F₂ hF₁s hF₁c hF₂s hF₂c) x
    rw [hsum] at this
    simp only [this, Pi.add_apply, add_mul]

  have hc : (∫ x, D F₂ x * g₁ x ∂μ) = ∫ x, F₂ x * h x ∂μ := by
    rw [← hh_id F₂ hF₂s hF₂c]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : cb χ₂ x = 0
    · simp only [hgt_def, hg₁_def, hx, sub_zero, one_mul]
    · have hxmem : x ∈ ball x₀ (ε / 8) := by
        by_contra hx'
        apply hx
        apply cb_eq_zero_of_le χ₂
        rw [hχ₂rOut]
        exact not_lt.mp fun hlt => hx' (mem_ball.mpr hlt)
      simp only [hgt_def, hg₁_def, hDF₂_zero x hxmem, zero_mul]

  have hd : (∫ x, F x * g₂ x ∂μ) = (∫ x, F₁ x * w x ∂μ) - ∫ x, F₂ x * h x ∂μ := by
    rw [← integral_sub (hint' _ _ hF₁s.continuous hF₁c hw) (hint' _ _ hF₂s.continuous hF₂c hh_cont)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hg₂_def, hF₁_def, hF₂_def]
    ring
  rw [hb, hd, hc]
  linear_combination ha

end R4Cutoff

end

open MeasureTheory Topology in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (D : (E → ℂ) → (E → ℂ))
    (hD_add : ∀ F G : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G → D (F + G) = D F + D G)
    (hD_cont : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F → Continuous (D F))
    (hD_supp : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport (D F) ⊆ tsupport F)
    (hD_tr : ∀ g : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∃ h : E → ℂ, Continuous h ∧ tsupport h ⊆ tsupport g ∧
        ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
          ∫ x, D F x * g x ∂μ = ∫ x, F x * h x ∂μ)
    (x₀ : E) (u w : E → ℂ) (hu : Continuous u) (hw : Continuous w)
    (hu' : ContDiffOn ℝ (⊤ : ℕ∞) u {x₀}ᶜ)
    (hid : ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      F x₀ = (∫ x, D F x * u x ∂μ) + ∫ x, F x * w x ∂μ)
    (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, D F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ :=
  R4Cutoff.main μ D hD_add hD_cont hD_supp hD_tr x₀ u w hu hw hu' hid V hV

end S_LocalParametrix_exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton
end P2MW
export P2MW.S_LocalParametrix_exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton (solution)
