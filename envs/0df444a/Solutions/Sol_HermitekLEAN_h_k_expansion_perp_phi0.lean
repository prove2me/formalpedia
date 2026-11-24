-- Prove2me | solution 1 for HermitekLEAN.h_k_expansion_perp_phi0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:46.507842+00:00
-- url     : https://prove2.me/submissions/01978dd9-d92f-4f18-bae0-bf45b5db125b

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_orthogonal_phi0_iff_hermiteCoeff_zero
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_expansion

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
        weightedInner G (Phi k 0) = 0 →
          ∃ g : ℕ → ℂ,
            G = hermiteSeries k g ∧
              g 0 = 0 := by
  intro k G hG hperp
  refine ⟨hermiteCoeff k G, hermiteCoeff_expansion (k := k) (G := G) hG, ?_⟩
  exact
    (orthogonal_phi0_iff_hermiteCoeff_zero (k := k) (G := G)).mp hperp
end HermitekLEAN
