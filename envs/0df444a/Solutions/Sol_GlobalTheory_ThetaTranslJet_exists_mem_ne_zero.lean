-- Prove2me | solution 1 for GlobalTheory.ThetaTranslJet.exists_mem_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:41:29.390739+00:00
-- url     : https://prove2.me/submissions/fc8d76a4-8a1d-44d9-b6f6-f7e9f5576aec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
import Theorems.Thm_GlobalTheory_ThetaTranslJet_polyDeriv_eq_pairing
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_GlobalTheory_taylorDir_sum
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
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
namespace GlobalTheory.ThetaTranslJet
theorem _root_.solution {σ V : Type} [Fintype σ] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {n : ℕ} (P : MvPolynomial σ ℂ) (u : σ → Fin n → V) (T : Set (V → ℂ))
    (hT : ∀ G ∈ T, Differentiable ℂ G) (F : Fin n → V → ℂ) (hF : ∀ b, F b ∈ Submodule.span ℂ T)
    (h : polyDeriv P u (fun z => ∏ b, F b (z b)) 0 ≠ 0) :
    ∃ G : Fin n → V → ℂ, (∀ b, G b ∈ T) ∧ polyDeriv P u (fun z => ∏ b, G b (z b)) 0 ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  apply h
  choose N c G hG using fun b => Submodule.mem_span_set'.1 (hF b)
  have e : (fun z : Fin n → V => ∏ b, F b (z b)) = fun z => ∑ p : ∀ b, Fin (N b),
      ((∏ b, c b (p b)) • fun z : Fin n → V => ∏ b, (G b (p b) : V → ℂ) (z b)) z := by
    funext z
    simp only [← hG, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    simp only [Finset.prod_mul_distrib]
  have han : ∀ p : ∀ b, Fin (N b),
      AnalyticAt ℂ (fun z : Fin n → V => ∏ b, (G b (p b) : V → ℂ) (z b)) 0 := fun p =>
    Finset.analyticAt_fun_prod _ fun b _ => ThetaJet.analyticAt_of_differentiable
      ((hT _ (G b (p b)).2).comp (differentiable_apply b)) 0
  rw [e, polyDeriv_eq_pairing, taylorDir_sum u _ fun p _ => (han p).const_smul, map_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [taylorDir_smul u _ (han p), map_smul, ← polyDeriv_eq_pairing,
    hcon (fun b => G b (p b)) fun b => (G b (p b)).2, smul_zero]
end GlobalTheory.ThetaTranslJet
