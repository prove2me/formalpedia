-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e0e395df-ec3e-5e04-9253-855b3e35d69c

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction
open LanglandsTunnell.CubicInduction.SlabL2 Topology Filter

noncomputable section

namespace SlabL2MassConc48

attribute [local instance] NumberField.AdelicHaar.glBorel

abbrev G : Type := AdelicGL 3 (𝓞 ℚ) ℚ

abbrev μ : Measure G := NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ

scoped instance borelSpace_G : BorelSpace G := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ

theorem exists_open_nhds_one_forall_norm_sub_lt (F : G → ℂ) (hF : Continuous F) (K : Set G) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧ ∀ x ∈ K, ∀ y ∈ W, ‖F (x * y) - F x‖ < ε := by
  set n : Set (G × G) := {p | ‖F (p.1 * p.2) - F p.1‖ < ε} with hn
  have hn_open : IsOpen n := by
    have hc : Continuous fun p : G × G => ‖F (p.1 * p.2) - F p.1‖ :=
      ((hF.comp continuous_mul).sub (hF.comp continuous_fst)).norm
    exact isOpen_lt hc continuous_const
  have hsub : K ×ˢ ({1} : Set G) ⊆ n := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show ‖F (x * 1) - F x‖ < ε
    rw [mul_one, sub_self, norm_zero]
    exact hε
  obtain ⟨V, W, hV, hW, hKV, h1W, hVW⟩ := generalized_tube_lemma hK isCompact_singleton hn_open hsub
  refine ⟨W, hW, h1W (Set.mem_singleton 1), fun x hx y hy => ?_⟩
  have h : (x, y) ∈ n := hVW (Set.mk_mem_prod (hKV hx) hy)
  exact h

theorem norm_eq_re_of_nonneg {z : ℂ} (h : 0 ≤ z.re ∧ z.im = 0) : ‖z‖ = z.re := by
  have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h.2])
  rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by simpa using h.1)]
  simp

theorem integrable_of_integral_eq_one {φ : G → ℂ} (h : ∫ g, φ g ∂μ = 1) : Integrable φ μ := by
  by_contra hφ
  rw [integral_undef hφ] at h
  exact zero_ne_one h

theorem integral_norm_eq_one {φ : G → ℂ} (hnn : ∀ g, 0 ≤ (φ g).re ∧ (φ g).im = 0) (h : ∫ g, φ g ∂μ = 1) :
    ∫ g, ‖φ g‖ ∂μ = 1 := by
  have hint := integrable_of_integral_eq_one h
  have hre : (fun g => ‖φ g‖) = fun g => RCLike.re (φ g) := by
    funext g
    rw [norm_eq_re_of_nonneg (hnn g)]
    rfl
  rw [hre, integral_re hint, h]
  simp

theorem exists_bound_on_prod (F : G → ℂ) (hF : Continuous F) (K C : Set G) (hK : IsCompact K) (hC : IsCompact C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ∀ y ∈ C, ‖F (x * y) - F x‖ ≤ M := by
  have hc : Continuous fun p : G × G => ‖F (p.1 * p.2) - F p.1‖ :=
    ((hF.comp continuous_mul).sub (hF.comp continuous_fst)).norm
  obtain ⟨M, hM⟩ := (hK.prod hC).bddAbove_image hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x hx y hy => ?_⟩
  exact (hM ⟨(x, y), Set.mk_mem_prod hx hy, rfl⟩).trans (le_max_left _ _)

theorem norm_smoothingOperator_sub_le' (F : G → ℂ) (hF : Continuous F) (K C : Set G) (ε M δ : ℝ) (hε : 0 < ε)
    (hM : 0 ≤ M) (_hδ : 0 ≤ δ) (hMδ : ε / 2 + M * δ ≤ ε)
    (W : Set G) (hWm : MeasurableSet W) (hW : ∀ x ∈ K, ∀ y ∈ W, ‖F (x * y) - F x‖ < ε / 2)
    (hKC : ∀ x ∈ K, ∀ y ∈ C, ‖F (x * y) - F x‖ ≤ M)
    (φ : G → ℂ) (hnn : ∀ g, 0 ≤ (φ g).re ∧ (φ g).im = 0) (hsupp : tsupport φ ⊆ C)
    (hφ : Integrable φ μ) (hint : ∫ g, φ g ∂μ = 1) (hmass : ∫ g in Wᶜ, (φ g).re ∂μ ≤ δ)
    (x : G) (hx : x ∈ K) :
    ‖smoothingOperator φ F x - F x‖ ≤ ε := by
  set ψ : G → ℂ := fun g => φ g * (F (x * g) - F x) with hψ
  have hψ_meas : AEStronglyMeasurable ψ μ := by
    refine hφ.aestronglyMeasurable.mul ?_
    exact ((hF.comp (continuous_const.mul continuous_id)).sub continuous_const).aestronglyMeasurable

  set bnd : G → ℝ := fun g => ε / 2 * ‖φ g‖ + M * Set.indicator Wᶜ (fun g => (φ g).re) g with hbnd
  have hre_int : Integrable (fun g => (φ g).re) μ := hφ.re
  have hbnd_int : Integrable bnd μ :=
    (hφ.norm.const_mul (ε / 2)).add ((hre_int.indicator hWm.compl).const_mul M)
  have hbound : ∀ g, ‖ψ g‖ ≤ bnd g := by
    intro g
    have hφre : ‖φ g‖ = (φ g).re := norm_eq_re_of_nonneg (hnn g)
    by_cases hgφ : g ∈ tsupport φ
    · by_cases hgW : g ∈ W
      · have h1 : ‖F (x * g) - F x‖ < ε / 2 := hW x hx g hgW
        have : ‖ψ g‖ ≤ ε / 2 * ‖φ g‖ := by
          rw [hψ, norm_mul, mul_comm (ε / 2)]
          exact mul_le_mul_of_nonneg_left h1.le (norm_nonneg _)
        refine this.trans ?_
        simp only [hbnd, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hgW), mul_zero, add_zero, le_refl]
      · have h1 : ‖F (x * g) - F x‖ ≤ M := hKC x hx g (hsupp hgφ)
        have : ‖ψ g‖ ≤ M * ‖φ g‖ := by
          rw [hψ, norm_mul, mul_comm M]
          exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        refine this.trans ?_
        simp only [hbnd, Set.indicator_of_mem (Set.mem_compl hgW), hφre]
        nlinarith [(hnn g).1, hε.le]
    · have h0 : φ g = 0 := image_eq_zero_of_notMem_tsupport hgφ
      have : bnd g = 0 ∨ 0 ≤ bnd g := Or.inr (by
        simp only [hbnd]
        refine add_nonneg (mul_nonneg (by linarith) (norm_nonneg _)) (mul_nonneg hM ?_)
        by_cases hgW : g ∈ Wᶜ
        · rw [Set.indicator_of_mem hgW]; exact (hnn g).1
        · rw [Set.indicator_of_notMem hgW])
      simp only [hψ, h0, zero_mul, norm_zero]
      rcases this with h | h
      · rw [h]
      · exact h
  have hψ_int : Integrable ψ μ := Integrable.mono' hbnd_int hψ_meas (Eventually.of_forall hbound)
  have hconst : Integrable (fun g => φ g * F x) μ := hφ.mul_const _
  have hconst_val : ∫ g, φ g * F x ∂μ = F x := by rw [integral_mul_const, hint, one_mul]
  have hsum : (fun g => φ g * F (x * g)) = fun g => ψ g + φ g * F x := by
    funext g; simp only [hψ]; ring
  have hval : smoothingOperator φ F x - F x = ∫ g, ψ g ∂μ := by
    rw [smoothingOperator_apply]
    change ∫ g, φ g * F (x * g) ∂μ - F x = ∫ g, ψ g ∂μ
    rw [hsum, integral_add hψ_int hconst, hconst_val, add_sub_cancel_right]
  rw [hval]
  calc ‖∫ g, ψ g ∂μ‖ ≤ ∫ g, bnd g ∂μ := norm_integral_le_of_norm_le hbnd_int (Eventually.of_forall hbound)
    _ = ε / 2 * ∫ g, ‖φ g‖ ∂μ + M * ∫ g in Wᶜ, (φ g).re ∂μ := by
        rw [hbnd, integral_add (hφ.norm.const_mul (ε / 2)) ((hre_int.indicator hWm.compl).const_mul M),
          integral_const_mul, integral_const_mul, integral_indicator hWm.compl]
    _ ≤ ε / 2 * 1 + M * δ := by
        rw [integral_norm_eq_one hnn hint]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass hM)
    _ ≤ ε := by linarith

end SlabL2MassConc48
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le.SlabL2MassConc48"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le.SlabL2MassConc48"

open SlabL2MassConc48 in
attribute [local instance] NumberField.AdelicHaar.glBorel in
theorem solution
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : Continuous F) (K C : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hK : IsCompact K) (hC : IsCompact C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ nhds (1 : AdelicGL 3 (𝓞 ℚ) ℚ), ∃ δ : ℝ, 0 < δ ∧ ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
      (∀ g, 0 ≤ (φ g).re ∧ (φ g).im = 0) → tsupport φ ⊆ C →
      Integrable φ (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) →
      ∫ g, φ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) = 1 →
      ∫ g in Uᶜ, (φ g).re ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤ δ →
        ∀ x ∈ K, ‖smoothingOperator φ F x - F x‖ ≤ ε := by
  obtain ⟨W, hWo, h1W, hW⟩ := exists_open_nhds_one_forall_norm_sub_lt F hF K hK (ε / 2) (by linarith)
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_prod F hF K C hK hC
  refine ⟨W, hWo.mem_nhds h1W, ε / (2 * (M + 1)), by positivity, ?_⟩
  intro φ hnn hsupp hφ hint hmass x hx
  have hMδ : ε / 2 + M * (ε / (2 * (M + 1))) ≤ ε := by
    have hM1 : 0 < M + 1 := by linarith
    have : M * (ε / (2 * (M + 1))) ≤ ε / 2 := by
      rw [show M * (ε / (2 * (M + 1))) = (ε / 2) * (M / (M + 1)) by field_simp]
      exact mul_le_of_le_one_right (by linarith) ((div_le_one hM1).mpr (by linarith))
    linarith
  exact norm_smoothingOperator_sub_le' F hF K C ε M _ hε hM0 (by positivity) hMδ W hWo.measurableSet hW hM φ hnn hsupp
    hφ hint hmass x hx

end S_LanglandsTunnell_CubicInduction_SlabL2_exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_nhds_one_forall_norm_smoothingOperator_sub_le_of_setIntegral_compl_le (solution)
