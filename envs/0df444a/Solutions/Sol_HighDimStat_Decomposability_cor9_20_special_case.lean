-- Prove2me | solution 1 for HighDimStat.Decomposability.cor9_20_special_case
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:22:22.324929+00:00
-- url     : https://prove2.me/submissions/6bef2859-1abf-4a43-a762-6bd40acb1814

import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

/-- The loss used in the counterexample. -/
noncomputable def aux_c920_Ln (θ : ℝ) : ℝ :=
  1 / 2 * (θ - 61 / 20) + max (31 / 64 * (θ - 61 / 20) ^ 2) (-(3 / 2) * (θ - 61 / 20) - 1 / 64)

lemma aux_c920_regNorm : IsRegularizerNorm (fun x : ℝ => |x|) where
  nonneg x := abs_nonneg x
  eq_zero_iff x := abs_eq_zero
  smul_abs c x := by simp [smul_eq_mul, abs_mul]
  triangle x y := abs_add_le x y

lemma aux_c920_decomp : IsDecomposable (fun x : ℝ => |x|) ⊤ ⊤ := by
  refine ⟨le_refl _, ?_⟩
  intro α _ β hβ
  rw [Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hβ
  subst hβ
  simp

lemma aux_c920_conv : ConvexOn ℝ Set.univ aux_c920_Ln := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [aux_c920_Ln, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  have key1 : 31 / 64 * (a * x + (1 - a) * y - 61 / 20) ^ 2 ≤
      a * (31 / 64 * (x - 61 / 20) ^ 2) + (1 - a) * (31 / 64 * (y - 61 / 20) ^ 2) := by
    nlinarith [mul_nonneg ha hb, sq_nonneg (x - y)]
  have key2 : -(3 / 2) * (a * x + (1 - a) * y - 61 / 20) - 1 / 64 =
      a * (-(3 / 2) * (x - 61 / 20) - 1 / 64) + (1 - a) * (-(3 / 2) * (y - 61 / 20) - 1 / 64) := by
    ring
  have hx1 := le_max_left (31 / 64 * (x - 61 / 20) ^ 2) (-(3 / 2) * (x - 61 / 20) - 1 / 64)
  have hx2 := le_max_right (31 / 64 * (x - 61 / 20) ^ 2) (-(3 / 2) * (x - 61 / 20) - 1 / 64)
  have hy1 := le_max_left (31 / 64 * (y - 61 / 20) ^ 2) (-(3 / 2) * (y - 61 / 20) - 1 / 64)
  have hy2 := le_max_right (31 / 64 * (y - 61 / 20) ^ 2) (-(3 / 2) * (y - 61 / 20) - 1 / 64)
  have hmax : max (31 / 64 * (a * x + (1 - a) * y - 61 / 20) ^ 2)
      (-(3 / 2) * (a * x + (1 - a) * y - 61 / 20) - 1 / 64) ≤
      a * max (31 / 64 * (x - 61 / 20) ^ 2) (-(3 / 2) * (x - 61 / 20) - 1 / 64) +
      (1 - a) * max (31 / 64 * (y - 61 / 20) ^ 2) (-(3 / 2) * (y - 61 / 20) - 1 / 64) := by
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left hx1 ha, mul_le_mul_of_nonneg_left hy1 hb]
    · rw [key2]
      nlinarith [mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hy2 hb]
  nlinarith [hmax]

lemma aux_c920_grad : HasGradientAt aux_c920_Ln (1 / 2 : ℝ) (61 / 20) := by
  have hd : HasDerivAt (fun θ : ℝ => 1 / 2 * (θ - 61 / 20) + 31 / 64 * (θ - 61 / 20) ^ 2)
      (1 / 2 : ℝ) (61 / 20) := by
    have h1 : HasDerivAt (fun θ : ℝ => θ - 61 / 20) 1 (61 / 20) :=
      (hasDerivAt_id _).sub_const _
    have h2 : HasDerivAt (fun θ : ℝ => 1 / 2 * (θ - 61 / 20) + 31 / 64 * (θ - 61 / 20) ^ 2)
        (1 / 2 * 1 + 31 / 64 * (((2 : ℕ) : ℝ) * (61 / 20 - 61 / 20 : ℝ) ^ (2 - 1) * 1)) (61 / 20) :=
      (h1.const_mul (1 / 2 : ℝ)).add ((h1.pow 2).const_mul (31 / 64 : ℝ))
    exact h2.congr_deriv (by norm_num)
  refine hd.hasGradientAt'.congr_of_eventuallyEq ?_
  have hopen : ∀ᶠ θ in nhds (61 / 20 : ℝ), -(3 / 2) * (θ - 61 / 20) - 1 / 64 < 0 := by
    have hc : Continuous (fun θ : ℝ => -(3 / 2) * (θ - 61 / 20) - 1 / 64) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hopen] with θ hθ
  simp only [aux_c920_Ln]
  rw [max_eq_left]
  nlinarith [sq_nonneg (θ - 61 / 20)]

lemma aux_c920_subLip : subspaceLip (fun x : ℝ => |x|) ⊤ = 1 := by
  unfold subspaceLip
  have : {r : ℝ | ∃ u ∈ (⊤ : Submodule ℝ ℝ), u ≠ 0 ∧ r = |u| / ‖u‖} = {1} := by
    ext r
    simp only [Set.mem_singleton_iff, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Real.norm_eq_abs]
      exact div_self (abs_ne_zero.mpr hu)
    · rintro rfl
      exact ⟨1, one_ne_zero, by simp⟩
  rw [this, csSup_singleton]

lemma aux_c920_good : goodEvent (fun x : ℝ => |x|) (1 / 2 : ℝ) 1 := by
  unfold goodEvent dualNorm
  apply csSup_le
  · exact ⟨0, 0, by simp⟩
  · rintro r ⟨u, hu, rfl⟩
    rw [Real.inner_apply]
    have := (abs_le.mp hu).2
    linarith

lemma aux_c920_eps :
    epsilonSq (fun x : ℝ => |x|) ⊤ ⊤ (61 / 20) 1 1 (1 / 64) = 9 := by
  unfold epsilonSq
  have h0 : (⊤ : Submodule ℝ ℝ)ᗮ.starProjection (61 / 20 : ℝ) = 0 := by
    have hmem := Submodule.starProjection_apply_mem (⊤ : Submodule ℝ ℝ)ᗮ (61 / 20 : ℝ)
    have hle : (⊤ : Submodule ℝ ℝ)ᗮ ≤ ⊥ := (Submodule.top_orthogonal_eq_bot).le
    exact (Submodule.mem_bot ℝ).mp (hle hmem)
  rw [aux_c920_subLip, h0]
  norm_num

end HighDimStat.Decomposability

open HighDimStat.Decomposability
open scoped RealInnerProductSpace

theorem solution : ¬ (∀ {Ω : Type} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω]
    [FiniteDimensional ℝ Ω]
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN κ τnSq R : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hRSC : RSC Ln g θstar Φ κ τnSq R)
    (hκ : 0 < κ) (hR : 0 < R) (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN)
    (htol : τnSq * subspaceLip Φ Mbar ^ 2 ≤ κ / 64)
    (hRbound : Real.sqrt (epsilonSq Φ M Mbar θstar lamN κ τnSq) ≤ R)
    (hθM : θstar ∈ M),
    Φ (θhat - θstar) ≤ 6 * lamN / κ * subspaceLip Φ Mbar ^ 2 ∧
      ‖θhat - θstar‖ ^ 2 ≤ 9 * lamN ^ 2 / κ ^ 2 * subspaceLip Φ Mbar ^ 2) := by
  intro h
  have hRSC : RSC aux_c920_Ln (1 / 2 : ℝ) (61 / 20) (fun x : ℝ => |x|) 1 (1 / 64) 3 := by
    intro Δ _
    unfold taylorError
    simp only [aux_c920_Ln, Real.inner_apply, Real.norm_eq_abs, sq_abs]
    have h0 : max (31 / 64 * ((61 / 20 : ℝ) - 61 / 20) ^ 2)
        (-(3 / 2) * ((61 / 20 : ℝ) - 61 / 20) - 1 / 64) = 0 := by norm_num
    have hm := le_max_left (31 / 64 * ((61 / 20 : ℝ) + Δ - 61 / 20) ^ 2)
        (-(3 / 2) * ((61 / 20 : ℝ) + Δ - 61 / 20) - 1 / 64)
    rw [h0]
    nlinarith [hm]
  have hopt : ∀ θ : ℝ, aux_c920_Ln 0 + 1 * |(0 : ℝ)| ≤ aux_c920_Ln θ + 1 * |θ| := by
    intro θ
    simp only [aux_c920_Ln]
    have hm0 : max (31 / 64 * ((0 : ℝ) - 61 / 20) ^ 2) (-(3 / 2) * ((0 : ℝ) - 61 / 20) - 1 / 64)
        = -(3 / 2) * ((0 : ℝ) - 61 / 20) - 1 / 64 := by
      rw [max_eq_right]; norm_num
    rw [hm0]
    have hm := le_max_right (31 / 64 * (θ - 61 / 20) ^ 2) (-(3 / 2) * (θ - 61 / 20) - 1 / 64)
    have ha := le_abs_self θ
    rw [abs_zero]
    linarith [hm, ha]
  have hRb : Real.sqrt (epsilonSq (fun x : ℝ => |x|) ⊤ ⊤ (61 / 20) 1 1 (1 / 64)) ≤ 3 := by
    rw [aux_c920_eps, Real.sqrt_le_iff]
    norm_num
  have htol : (1 / 64 : ℝ) * subspaceLip (fun x : ℝ => |x|) ⊤ ^ 2 ≤ 1 / 64 := by
    rw [aux_c920_subLip]; norm_num
  have := (h (Ω := ℝ) aux_c920_Ln (fun x : ℝ => |x|) ⊤ ⊤ (61 / 20) 0 (1 / 2) 1 1 (1 / 64) 3
    aux_c920_regNorm aux_c920_decomp aux_c920_conv aux_c920_grad hRSC (by norm_num) (by norm_num)
    (by norm_num) hopt aux_c920_good htol hRb (Submodule.mem_top)).2
  rw [aux_c920_subLip, Real.norm_eq_abs, sq_abs] at this
  norm_num at this
