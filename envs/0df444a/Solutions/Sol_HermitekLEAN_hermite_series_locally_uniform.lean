-- Prove2me | solution 1 for HermitekLEAN.hermite_series_locally_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:15.075472+00:00
-- url     : https://prove2.me/submissions/cbede34f-1f43-49b7-a867-3107015b5621

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_continuous_Phi
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_expansion
public import Theorems.Thm_HermitekLEAN_truncate_locally_uniform
section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
private theorem continuous_finiteHermiteSum (k : ℕ) {D : ℕ} (a : Fin D → ℂ) :
    Continuous (finiteHermiteSum k a) := by
  unfold finiteHermiteSum
  exact continuous_finsetSum _ (fun m _ => continuous_const.mul (continuous_Phi k m.1))
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {k : ℕ} {G : ℂ → ℂ},
      G ∈ Hk k →
        ∃ g : ℕ → ℂ,
          G = hermiteSeries k g ∧
            Continuous G := by
  intro k G hG
  refine ⟨hermiteCoeff k G, hermiteCoeff_expansion hG, ?_⟩
  rw [continuous_iff_continuousAt]
  intro z₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- Use locally uniform convergence: for R = ‖z₀‖ + 1, ε/3, get J0
  set R := ‖z₀‖ + 1 with hR_def
  have hRpos : 0 < R := by positivity
  have hε3 : (0 : ℝ) < ε / 3 := by linarith only [hε]
  obtain ⟨J0, hJ0⟩ := truncate_locally_uniform hG R (ε / 3) hRpos hε3
  -- truncate k J0 G is continuous
  have hcont_trunc : Continuous (truncate k J0 G) := continuous_finiteHermiteSum k _
  -- By continuity of truncate at z₀, find δ₁ such that dist < ε/3
  have hcontAt : ContinuousAt (truncate k J0 G) z₀ := hcont_trunc.continuousAt
  rw [Metric.continuousAt_iff] at hcontAt
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hcontAt (ε / 3) hε3
  -- Also need ‖z‖ ≤ R, so take δ₂ = 1
  set δ := min δ₁ 1 with hδ_def
  have hδpos : 0 < δ := lt_min hδ₁pos one_pos
  refine ⟨δ, hδpos, fun {z} hz => ?_⟩
  have hz_R : ‖z‖ ≤ R := by
    have h1 : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_le_insert' z z₀
    have h2 : ‖z - z₀‖ = dist z z₀ := by rw [dist_eq_norm]
    linarith only [hz, h1, h2, min_le_right δ₁ 1]
  have hz₀_R : ‖z₀‖ ≤ R := by linarith only []
  have hclose_z : ‖truncate k J0 G z - G z‖ ≤ ε / 3 := hJ0 J0 (le_refl _) z hz_R
  have hclose_z₀ : ‖truncate k J0 G z₀ - G z₀‖ ≤ ε / 3 := hJ0 J0 (le_refl _) z₀ hz₀_R
  have hclose_trunc : dist (truncate k J0 G z) (truncate k J0 G z₀) < ε / 3 :=
    hδ₁ (lt_of_lt_of_le hz (min_le_left δ₁ 1))
  rw [dist_eq_norm] at hclose_trunc
  calc dist (G z) (G z₀)
      = ‖G z - G z₀‖ := dist_eq_norm (G z) (G z₀)
    _ = ‖(G z - truncate k J0 G z) + (truncate k J0 G z - truncate k J0 G z₀) +
          (truncate k J0 G z₀ - G z₀)‖ := by ring_nf
    _ ≤ ‖G z - truncate k J0 G z‖ + ‖truncate k J0 G z - truncate k J0 G z₀‖ +
          ‖truncate k J0 G z₀ - G z₀‖ := by
        exact norm_add₃_le
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h1 : ‖G z - truncate k J0 G z‖ ≤ ε / 3 := by
          rw [show G z - truncate k J0 G z = -(truncate k J0 G z - G z) by ring, norm_neg]
          exact hclose_z
        linarith only [hclose_z₀, hclose_trunc, h1]
    _ = ε := by ring
end HermitekLEAN
