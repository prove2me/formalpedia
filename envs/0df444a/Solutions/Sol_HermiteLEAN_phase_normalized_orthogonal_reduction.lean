-- Prove2me | solution 1 for HermiteLEAN.phase_normalized_orthogonal_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:53.386361+00:00
-- url     : https://prove2.me/submissions/245ca7f7-f5cd-4db3-aa38-e7a374936c24

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_HighFreqBandEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LocalCircleEstimate
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_ImportedAnalyticInputs

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators
noncomputable section
open HermiteLEAN
namespace HermiteLEAN
theorem _root_.solution
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (defect : H → ℝ)
    (hdefect_nonneg : ∀ h : H, 0 ≤ defect h)
    (f0 : H)
    (hf0 : ‖f0‖ = 1)
    (C : ℝ)
    (hC : 0 < C)
    (horth : ∀ g : H, inner ℂ g f0 = (0 : ℂ) → ‖g‖ ≤ C * defect g)
    (hscalar :
      ∀ h : H, (inner ℂ h f0).im = 0 →
        |(2 : ℝ) * (inner ℂ h f0).re + ‖h‖ ^ 2| ≤ defect h * (2 + ‖h‖))
    (hcompare :
      ∀ h : H, ∀ a : ℝ, defect (h - (a : ℂ) • f0) ≤ |a| + defect h) :
    ∃ δ Mloc : ℝ, 0 < δ ∧ 0 < Mloc ∧
      ∀ h : H, ‖h‖ ≤ δ → (inner ℂ h f0).im = 0 → ‖h‖ ≤ Mloc * defect h := by
  /-
  Scaffolding guidance:
  - this is the reusable phase-normalized local reduction step;
  - the orthogonal coercivity hypothesis is passed in as `horth`;
  - `hscalar` and `hcompare` package the two modulus estimates coming from the
    underlying `L²` embedding in the scaffolding-note proof;
  - the conclusion is local in `h`, with the phase normalization encoded by `(inner h f0).im = 0`.
  -/
  refine ⟨1 / (C + 1), 5 * C + 3, ?_, ?_, ?_⟩
  · have hCp1 : 0 < C + 1 := by linarith only [hC]
    exact one_div_pos.mpr hCp1
  · linarith only [hC]
  · intro h hhδ him
    set a : ℝ := (inner ℂ h f0).re
    set g : H := h - (a : ℂ) • f0
    have hinner_real : inner ℂ h f0 = (a : ℂ) := by apply Complex.ext <;> simp [a, him]
    have hf0_inner : inner ℂ f0 f0 = (1 : ℂ) := by
      simp_all
    have hsmul : inner ℂ ((a : ℂ) • f0) f0 = (a : ℂ) := by
      rw [inner_smul_left, hf0_inner]
      simp
    have hgorth : inner ℂ g f0 = (0 : ℂ) := by
      dsimp [g]
      rw [inner_sub_left, hinner_real]
      exact sub_eq_zero.mpr hsmul.symm
    have hg_bound : ‖g‖ ≤ C * (|a| + defect h) :=
      (horth g hgorth).trans (mul_le_mul_of_nonneg_left (hcompare h a) hC.le)
    have hscalar_h := hscalar h him
    have htwoa : 2 * |a| ≤ defect h * (2 + ‖h‖) + ‖h‖ ^ 2 := by
      rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases ((2 : ℝ) * a + ‖h‖ ^ 2) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
        nlinarith [sq_nonneg ‖h‖, hscalar_h, h1, h2]
    have hg_add : g + (a : ℂ) • f0 = h := by simp [g]
    have hsplit : ‖h‖ ≤ ‖g‖ + |a| := by
      calc
        ‖h‖ = ‖g + (a : ℂ) • f0‖ := by rw [← hg_add]
        _ ≤ ‖g‖ + ‖(a : ℂ) • f0‖ := norm_add_le _ _
        _ = ‖g‖ + |a| := by simp [norm_smul, hf0, Real.norm_eq_abs]
    have hh_main : ‖h‖ ≤ (C + 1) * |a| + C * defect h := by linarith only [hg_bound, hsplit]
    have hCp1 : 0 < C + 1 := by linarith only [hC]
    have hx_le_one : ‖h‖ ≤ 1 := hhδ.trans (by rw [div_le_iff₀ hCp1]; linarith only [hC])
    have ha_simple : |a| ≤ (3 : ℝ) / 2 * defect h + ‖h‖ ^ 2 / 2 := by
      nlinarith only [hdefect_nonneg, htwoa, hx_le_one, hdefect_nonneg h, norm_nonneg h]
    have hx_sq : (C + 1) * ‖h‖ ^ 2 ≤ ‖h‖ := by
      rw [le_div_iff₀ hCp1] at hhδ
      nlinarith only [hhδ, norm_nonneg h, hCp1]
    nlinarith only [hC, hg_bound, hsplit, ha_simple, hx_sq, hh_main, hdefect_nonneg h, abs_nonneg a]
end HermiteLEAN
