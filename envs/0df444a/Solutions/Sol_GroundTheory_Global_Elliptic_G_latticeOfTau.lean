-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.G_latticeOfTau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:29:34.768172+00:00
-- url     : https://prove2.me/submissions/3fb4230b-3f67-4902-ac44-a5ed060a01e9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_latticeOfTau____cd64e51b6620
import Theorems.Thm_P2M_GroundTheory_Global_Elliptic_latticeOfTau____29e4a99442e2
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_one
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_two
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_one
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_two
attribute [local simp] GroundTheory.Global.Elliptic.weierstrassCoeff_zero


attribute [local simp] GroundTheory.Global.Elliptic.latticeOfTau_ω₁
attribute [local simp] GroundTheory.Global.Elliptic.latticeOfTau_ω₂

set_option autoImplicit false
open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology
open scoped PeriodPair Real
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {k : ℕ} (hk : 3 ≤ k) (τ : ℍ) :
    (latticeOfTau τ).G k = 2 * riemannZeta k * E hk τ := by
  have hE : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  have h1 : (latticeOfTau τ).G k = ∑' v : Fin 2 → ℤ, eisSummand k v τ := by
    rw [PeriodPair.G, ← (latticeOfTau τ).latticeEquivProd.symm.toEquiv.tsum_eq,
      ← (finTwoArrowEquiv ℤ).tsum_eq]
    refine tsum_congr fun v ↦ ?_
    simp only [LinearEquiv.coe_toEquiv, PeriodPair.latticeEquiv_symm_apply, finTwoArrowEquiv_apply,
      latticeOfTau_ω₁, latticeOfTau_ω₂, mul_one, eisSummand, zpow_neg, zpow_natCast]
    rfl
  rw [h1, tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk, hE]
  ring
end GroundTheory.Global.Elliptic
