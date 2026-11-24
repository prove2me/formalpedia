-- Prove2me | solution 1 for HermitekLEAN.circle_representation_hermiteCoeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:06:35.57826+00:00
-- url     : https://prove2.me/submissions/12655512-9b65-4618-b0a7-98514ab1ddf9

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_phi_polar
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_expansion
attribute [local simp] HermitekLEAN.qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0

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
        ∀ r : ℝ, 0 < r →
          ∀ t : Circle,
            G (circlePoint r t) =
              circleLeadingFactor k r *
                (fourier (-(k : ℤ)) t : ℂ) *
                  circleSeries k (hermiteCoeff k G) r t := by
  intro k G hG r hr t
  have hseries := congrFun (hermiteCoeff_expansion (k := k) (G := G) hG) (circlePoint r t)
  rw [hseries]
  unfold hermiteSeries circleSeries
  simp_rw [phi_polar (k := k) (r := r) hr t]
  let c : ℂ := circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ)
  have htsum :
      (∑' n : ℕ,
          hermiteCoeff k G n *
            (circleLeadingFactor k r * (fourier (-(k : ℤ)) t : ℂ) *
              ((qkn k n r : ℂ) * fourier (n : ℤ) t))) =
        ∑' n : ℕ, c * (hermiteCoeff k G n * ((qkn k n r : ℂ) * fourier (n : ℤ) t)) := by
    apply tsum_congr
    intro n
    simp [c]
    ac_rfl
  rw [htsum, tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  ac_rfl
end HermitekLEAN
