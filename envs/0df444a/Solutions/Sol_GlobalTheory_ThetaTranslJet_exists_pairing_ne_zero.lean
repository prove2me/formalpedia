-- Prove2me | solution 1 for GlobalTheory.ThetaTranslJet.exists_pairing_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:41:33.934063+00:00
-- url     : https://prove2.me/submissions/727850e3-b223-4957-b18e-b983853e24dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_sum
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ThetaGauss.transl_apply
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open Matrix ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslJet
namespace GlobalTheory.ThetaTranslJet
theorem _root_.solution {σ : Type} [Fintype σ] {P : MvPolynomial σ ℂ} (hP : P ≠ 0) :
    ∃ x ∈ germIdeal σ ℂ ^ P.totalDegree, pairing P x ≠ 0 := by
  classical
  obtain ⟨m, hm, hd⟩ := Finset.exists_mem_eq_sup P.support (MvPolynomial.support_nonempty.2 hP)
    (fun s => s.sum fun _ e => e)
  have hd' : P.totalDegree = m.degree := hd
  refine ⟨MvPowerSeries.monomial m 1, mem_germIdeal_pow_iff.2 fun d hd => ?_, ?_⟩
  · refine MvPowerSeries.coeff_monomial_ne (fun h => ?_) _
    subst h; omega
  · simp only [pairing, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Finset.sum_eq_single m (fun d _ hd => by rw [MvPowerSeries.coeff_monomial_ne hd, smul_zero])
      (fun h => absurd hm h), MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
    exact mul_ne_zero (MvPolynomial.mem_support_iff.1 hm) (cast_prod_factorial_ne_zero m)
end GlobalTheory.ThetaTranslJet
