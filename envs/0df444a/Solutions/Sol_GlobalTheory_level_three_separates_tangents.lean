-- Prove2me | solution 1 for GlobalTheory.level_three_separates_tangents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:12.915835+00:00
-- url     : https://prove2.me/submissions/cff96dbe-2735-4d74-9627-471c6c2dd10e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Theorems.Thm_GlobalTheory_exists_mem_four_of_open_dense
import Theorems.Thm_GlobalTheory_exists_linear_increment
import Theorems.Thm_GlobalTheory_fderiv_sec_add
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
variable {ι : Type} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution {ι : Type} [Fintype ι] (Y : GT ι) (θ : EuclideanSpace ℂ ι → ℂ) (hθ : θ ∈ Y.Sec 1) (h0 : θ ≠ 0)
    (c₀ : ℂ) (c : EuclideanSpace ℂ ι)
    (h : ∀ a b, c₀ * (θ a * θ b * θ (-a - b)) + fderiv ℂ (fun v => θ (v + a) * θ (v + b) * θ (v - a - b)) 0 c = 0) : c = 0 ∧ c₀ = 0 := by
  have hd : Differentiable ℂ θ := hθ.1
  have han : AnalyticOnNhd ℂ θ Set.univ := fun x _ =>
    SCV.analyticAt_of_differentiableOn (s := Set.univ) hd.differentiableOn univ_mem
  set U : Set (EuclideanSpace ℂ ι) := {x | θ x ≠ 0} with hU
  have ho : IsOpen U := isOpen_ne_fun hd.continuous continuous_const
  have hden : Dense U := by
    intro x
    by_contra hx
    apply h0
    refine han.eq_of_eventuallyEq (g := 0) (z₀ := x) analyticOnNhd_const ?_
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    by_contra hy'
    exact hy (subset_closure hy')
  have hder : ∀ a b, fderiv ℂ (fun v => θ (v + a) * θ (v + b) * θ (v - a - b)) 0 c =
      fderiv ℂ θ a c * θ b * θ (-a - b) + θ a * fderiv ℂ θ b c * θ (-a - b)
        + θ a * θ b * fderiv ℂ θ (-a - b) c := by
    intro a b
    have ht : ∀ x, HasFDerivAt (fun v => θ (v + x)) (fderiv ℂ θ x) 0 := fun x =>
      (hasFDerivAt_comp_add_right x).2 (by simpa using (hd x).hasFDerivAt)
    have e : (fun v => θ (v + a) * θ (v + b) * θ (v - a - b)) =
        ((fun v => θ (v + a)) * fun v => θ (v + b)) * fun v => θ (v + (-a - b)) := by
      funext v
      simp only [Pi.mul_apply]
      congr 2
      abel
    rw [e, (((ht a).mul (ht b)).mul (ht (-a - b))).fderiv]
    simp
    ring
  set f : EuclideanSpace ℂ ι → ℂ := fun x => fderiv ℂ θ x c / θ x with hfdef
  have hf : ∀ a ∈ U, ∀ b ∈ U, -a - b ∈ U → c₀ + f a + f b + f (-a - b) = 0 := by
    intro a ha b hb hab
    have ha' : θ a ≠ 0 := ha
    have hb' : θ b ≠ 0 := hb
    have hab' : θ (-a - b) ≠ 0 := hab
    have := h a b
    rw [hder] at this
    simp only [hfdef]
    field_simp
    linear_combination this
  obtain ⟨a₀, ha₀⟩ := hden.nonempty
  have ha₀' : θ a₀ ≠ 0 := ha₀
  have hdf : DifferentiableAt ℂ f a₀ := by
    simp only [hfdef, div_eq_mul_inv]
    exact (((han a₀ trivial).fderiv.differentiableAt).clm_apply (differentiableAt_const c)).mul
      ((hd a₀).inv ha₀')
  obtain ⟨L, hL⟩ := exists_linear_increment ho hden hf ha₀ hdf
  have hlat : ∀ γ ∈ lat Y.b, L γ = Real.pi * Hf c γ := by
    intro γ hγ
    have hne : θ (a₀ + γ) ≠ 0 := by
      rw [hθ.2 γ hγ]
      have : Y.ka γ ≠ 0 := by
        intro hk
        have := Y.ka_abs γ hγ
        simp [hk] at this
      exact mul_ne_zero (mul_ne_zero this (exp_ne_zero _)) ha₀'
    rw [← hL a₀ γ ha₀ hne]
    have := fderiv_sec_add Y hθ hγ a₀ c
    simp only [hfdef]
    field_simp
    linear_combination this
  have hH : ∀ v w : EuclideanSpace ℂ ι, Hf v w = inner ℂ w v := fun v w => by
    simp [Hf, PiLp.inner_apply]
  let M : EuclideanSpace ℂ ι →ₗ[ℝ] ℂ :=
    { toFun := fun v => Real.pi * inner ℂ v c
      map_add' := fun x y => by rw [inner_add_left]; ring
      map_smul' := fun r x => by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left]
        simp
        ring }
  have hM : (L : EuclideanSpace ℂ ι →ₗ[ℂ] ℂ).restrictScalars ℝ = M := by
    refine Y.b.ext fun i => ?_
    have := hlat (Y.b i) (Submodule.subset_span ⟨i, rfl⟩)
    rw [hH] at this
    exact this
  have hLM : ∀ v, L v = Real.pi * inner ℂ v c := fun v => LinearMap.congr_fun hM v
  have hc : c = 0 := by
    have h1 := hLM (I • c)
    rw [map_smul, hLM, inner_smul_left, conj_I, smul_eq_mul] at h1
    have h2 : (2 * I * Real.pi) * inner ℂ c c = 0 := by linear_combination h1
    have h3 : (2 * I * Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    exact inner_self_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left h3)
  refine ⟨hc, ?_⟩
  obtain ⟨d, hd1, hd2, -⟩ := exists_mem_four_of_open_dense ho hden (Homeomorph.refl _)
    (Homeomorph.subLeft (-a₀)) (Homeomorph.refl _) (Homeomorph.refl _)
  have := hf a₀ ha₀ d hd1 hd2
  simpa [hfdef, hc] using this
end GlobalTheory
