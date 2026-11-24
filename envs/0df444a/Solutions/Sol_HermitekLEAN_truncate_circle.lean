-- Prove2me | solution 1 for HermitekLEAN.truncate_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:18.852116+00:00
-- url     : https://prove2.me/submissions/50b1a0fd-14be-46d0-8025-05b13b2b9f1f

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_finiteHermiteSum_circle

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ (k J : ℕ) (G : ℂ → ℂ) {r : ℝ},
      0 < r →
        ∀ t : Circle,
          truncate k J G (circlePoint r t) =
            circleLeadingFactor k r *
              (fourier (-(k : ℤ)) t : ℂ) *
                truncCirclePoly k r J G t := by
  intro k J G r hr t
  exact
    (finiteHermiteSum_circle (k := k) (D := J + 1)
      (a := fun n : Fin (J + 1) => hermiteCoeff k G n.1) (r := r) hr t)
end HermitekLEAN
