-- Prove2me | solution 1 for MilnorDynamics.isHolomorphicOn_smul_gl
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-10-01T13:52:22.438112+00:00
-- url     : https://prove2.me/submissions/2529aa50-6477-4f76-9847-1594f4634255

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint Topology
open Filter Set
open MilnorDynamics

/-- The translation `x ↦ x + 1` of the Riemann sphere, as an invertible matrix. -/
noncomputable def escG : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of ![![1, 1], ![0, 1]])
    (by simp [Matrix.det_fin_two])

lemma escG_00 : escG 0 0 = (1 : ℂ) := by simp [escG]
lemma escG_01 : escG 0 1 = (1 : ℂ) := by simp [escG]
lemma escG_10 : escG 1 0 = (0 : ℂ) := by simp [escG]
lemma escG_11 : escG 1 1 = (1 : ℂ) := by simp [escG]

lemma escG_infty : escG • (∞ : OnePoint ℂ) = ∞ := by
  rw [OnePoint.smul_infty_eq_ite, escG_10]
  simp

lemma escG_zero : escG • ((0 : ℂ) : OnePoint ℂ) = ((1 : ℂ) : OnePoint ℂ) := by
  rw [OnePoint.smul_some_eq_ite, escG_10, escG_11, escG_00, escG_01]
  simp

/-- The counterexample map: `∞` at `0`, and `0` everywhere else. -/
noncomputable def escF : ℂ → OnePoint ℂ := fun w => if w = 0 then ∞ else ((0 : ℂ) : OnePoint ℂ)

lemma escF_zero : escF 0 = (∞ : OnePoint ℂ) := by simp [escF]

lemma escF_ne_zero {w : ℂ} (hw : w ≠ 0) : escF w = ((0 : ℂ) : OnePoint ℂ) := by
  simp [escF, hw]

lemma chartInfinite_infty : chartInfinite (∞ : OnePoint ℂ) = 0 := by simp [chartInfinite]

lemma chartInfinite_one : chartInfinite ((1 : ℂ) : OnePoint ℂ) = 1 := by
  simp [chartInfinite]

/-- The image of the counterexample map under `escG` is `∞` at `0` and `1` elsewhere. -/
noncomputable def escH : ℂ → ℂ := fun w => chartInfinite ((fun z => escG • escF z) w)

lemma escH_zero : escH 0 = (0 : ℂ) := by
  simp [escH, escF_zero, escG_infty, chartInfinite_infty]

lemma escH_ne {w : ℂ} (hw : w ≠ 0) : escH w = (1 : ℂ) := by
  simp [escH, escF_ne_zero hw, escG_zero, chartInfinite_one]

lemma not_differentiableAt_escH : ¬ DifferentiableAt ℂ escH 0 := by
  intro hd
  have hc : Tendsto escH (𝓝 (0 : ℂ)) (𝓝 (escH 0)) := hd.continuousAt
  have h1 : Tendsto escH (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hle : Tendsto escH (𝓝[{0}ᶜ] (0 : ℂ)) (𝓝 (escH 0)) :=
      hc.mono_left nhdsWithin_le_nhds
    rw [escH_zero] at hle
    exact hle
  have heq : (fun _ : ℂ => (1 : ℂ)) =ᶠ[𝓝[≠] (0 : ℂ)] escH := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (escH_ne hw).symm
  have h2 : Tendsto escH (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) :=
    Tendsto.congr' heq tendsto_const_nhds
  have hone : (1 : ℂ) = (0 : ℂ) := tendsto_nhds_unique h2 h1
  exact one_ne_zero hone

lemma escF_holomorphic : IsHolomorphicOn ({0} : Set ℂ) escF := by
  refine ⟨continuousOn_singleton _ _, ?_, ?_⟩
  · intro z hz hzinfty
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact absurd escF_zero hzinfty
  · intro z hz hz0
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hfun : (fun w : ℂ => chartInfinite (escF w)) = fun _ => (0 : ℂ) := by
      funext w
      by_cases hw : w = 0
      · rw [hw, escF_zero, chartInfinite_infty]
      · simp [escF_ne_zero hw, chartInfinite]
    rw [hfun]
    exact differentiableAt_const 0

lemma not_holomorphic_escG_escF :
    ¬ IsHolomorphicOn ({0} : Set ℂ) (fun z => escG • escF z) := by
  rintro ⟨-, -, h3⟩
  have hne : (fun z => escG • escF z) 0 ≠ ((0 : ℂ) : OnePoint ℂ) := by
    show escG • escF 0 ≠ ((0 : ℂ) : OnePoint ℂ)
    rw [escF_zero, escG_infty]
    exact OnePoint.infty_ne_coe 0
  have hd : DifferentiableAt ℂ escH 0 := h3 0 (by simp) hne
  exact not_differentiableAt_escH hd

theorem solution :
    ¬ (∀ (g : GL (Fin 2) ℂ) (U : Set ℂ) (f : ℂ → OnePoint ℂ),
        IsHolomorphicOn U f → IsHolomorphicOn U (fun z => g • f z)) := by
  intro h
  exact not_holomorphic_escG_escF (h escG {0} escF escF_holomorphic)
