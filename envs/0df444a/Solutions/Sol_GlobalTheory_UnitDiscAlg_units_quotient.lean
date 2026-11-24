-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.units_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:19:00.318198+00:00
-- url     : https://prove2.me/submissions/5f61ec4f-ce4a-4de7-baa7-bfcf28979be6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralIdempotentLiftNewtonStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecomposeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommutantValuationDecompositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuotientIntegralUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitDiscriminantMatrixQuotientIsUnit
import Theorems.Thm_GlobalTheory_UnitDiscAlg_unit_split
import Theorems.Thm_GlobalTheory_T_matrix_commutant_valuation_decomposition
import Theorems.Thm_GlobalTheory_T_quotient_integral_unit_alt
import Theorems.Thm_GlobalTheory_UnitDiscAlg_comm_of_bezout


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.UnitDiscAlg
namespace GlobalTheory.UnitDiscAlg
theorem _root_.solution : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N c b : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → IsUnit c → c * N = N * c → b * N = N * b → (∀ i j, ‖b i j‖ ≤ 1) → ‖b.det‖ = 1 → IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) ∧ IsUnit (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) ∧ IsUnit (ϖ • c ^ 2 + b ^ 2) ∧ IsUnit (ϖ • c ^ 3 + b ^ 3) ∧ (∀ i j, ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹) i j‖ ≤ 1) ∧ ‖((ϖ • c ^ 3 + b ^ 3) * (ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 2) * ((ϖ • (1 : Matrix (Fin n) (Fin n) E) + c ^ 3) * (ϖ • c ^ 2 + b ^ 2))⁻¹).det‖ = 1 := by
  intro E _ _ _ n N c b ϖ hN hB h0 h1 hϖ hc hcN hbN hb hbd
  have hB' : ∃ u v : Polynomial E, u * N.charpoly + v * Polynomial.derivative N.charpoly = 1 := by
    obtain ⟨u, v, -, -, h⟩ := hB
    exact ⟨u, v, h⟩
  have hcomm : ∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x :=
    fun x y hx hy => comm_of_bezout hB' hx hy
  obtain ⟨e₁, e₂, e₃, u, a₂, a₃, hN6, hI6, hu, h11, h22, h33, h12, h13, h23, hs, hc1, hc2, hc3⟩ :=
    GlobalTheory.T.matrix_commutant_valuation_decomposition E n N ϖ h0 h1 hcomm (unit_split hN hB h0 h1 hϖ hcomm) c hc hcN
  exact GlobalTheory.T.quotient_integral_unit_alt E n N c b e₁ e₂ e₃ u a₂ a₃ ϖ h0 h1 hcomm hc hcN hbN hb hbd hN6 hI6 hu h11 h22 h33
    h12 h13 h23 hs hc1 hc2 hc3
end GlobalTheory.UnitDiscAlg
