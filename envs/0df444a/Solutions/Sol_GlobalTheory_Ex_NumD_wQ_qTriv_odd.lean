-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.wQ_qTriv_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:37:14.512516+00:00
-- url     : https://prove2.me/submissions/2cf6f244-5ead-4d9b-acaf-b02a09f37f5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Theorems.Thm_GlobalTheory_Ex_NumD_tk_qTriv_right
import Theorems.Thm_GlobalTheory_T_degenerationData_psi_quadratic_generators_linear
import Theorems.Thm_GlobalTheory_T_wQ_characterization_and_mul_relation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution {k : ℕ} (hk : Odd k) (z : N.X) : N.wQ (N.qTriv k z) = N.ψ z ^ k := by
  symm
  rw [(GlobalTheory.T.wQ_characterization_and_mul_relation O N k hk (N.qTriv k z) (N.qTriv k z)).1, tk_qTriv_right]
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N k z
  constructor
  · change _ * dbl N.θ N.σ (N.c z) ^ k = N.τ z z ^ k
    rw [h₁, mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2]
  · change _ = N.ψ (k • z) * mulq N.θ N.σ k (N.c z)
    rw [h₂, ← pow_mul, sq]
end GlobalTheory.Ex.NumD
