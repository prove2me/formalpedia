-- Prove2me | solution 1 for GlobalTheory.ThetaTranslJet.exists_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:38:18.978562+00:00
-- url     : https://prove2.me/submissions/77c568c0-cf3b-4595-a959-efee23ce622c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
import Theorems.Thm_GlobalTheory_ThetaTranslJet_differentiable_herm
import Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_two_points
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_ThetaJet_TwistedLaw_mul
import Theorems.Thm_GlobalTheory_ThetaJet_TwistedLaw_pow
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
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
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
namespace GlobalTheory.ThetaTranslJet
theorem _root_.solution {Λ : AddSubgroup (Fin g → ℂ)} {χ θ : (Fin g → ℂ) → ℂ}
    (hd : Differentiable ℂ θ) (h0 : θ ≠ 0)
    (hθ : ∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
      Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) (M : ℕ) (S : Fin g → ℂ) {κ : Type}
    (t : Finset κ) (x : κ → Fin g → ℂ) (ht : t.card + 2 ≤ M) :
    ∃ h : (Fin g → ℂ) → ℂ, Differentiable ℂ h ∧ h 0 ≠ 0 ∧ ∀ a ∈ Λ, ∀ z,
      (∏ j ∈ t, θ (z + a + x j)) * h (z + a) = χ a ^ M *
        Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec S - star S ⬝ᵥ Hm.mulVec a)) *
        Complex.exp (M * (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
          Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a))) * ((∏ j ∈ t, θ (z + x j)) * h z) := by
  obtain ⟨p, rfl⟩ : ∃ p, M = t.card + (p + 1) + 1 := ⟨M - t.card - 2, by omega⟩
  obtain ⟨c, hc, hc'⟩ := exists_two_points hd h0 (S - ∑ j ∈ t, x j) (p := p + 1) (by omega)
  set c' := S - ∑ j ∈ t, x j - (p + 1) • c with hc'def
  have hS : S = ∑ j ∈ t, x j + (p + 1) • c + c' := by rw [hc'def]; abel
  refine ⟨fun z => Complex.exp (-(Real.pi * (star S ⬝ᵥ Hm.mulVec z))) *
    (θ (z + c) ^ (p + 1) * θ (z + c')), ?_, by simp [hc, hc'], fun a ha z => ?_⟩
  · exact ((differentiable_herm S).const_mul _).neg.cexp.mul
      (((hd.comp (differentiable_id.add_const c)).pow _).mul
        (hd.comp (differentiable_id.add_const c')))
  · set j : ℂ := Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a) with hj
    have h1 : ∀ y, θ (z + a + y) = χ a * Complex.exp j *
        Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec y)) * θ (z + y) := fun y => by
      rw [add_right_comm, hθ a ha, mul_assoc (χ a) (Complex.exp j), ← Complex.exp_add, hj, mulVec_add,
        dotProduct_add]
      congr 3
      ring
    have h2 : Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec S)) =
        (∏ i ∈ t, Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec (x i)))) *
        Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec c)) ^ (p + 1) *
        Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec c')) := by
      rw [← Complex.exp_sum, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      conv_lhs => rw [hS]
      rw [mulVec_add, mulVec_add, dotProduct_add, dotProduct_add, mulVec_sum, dotProduct_sum,
        mulVec_smul, dotProduct_smul, ← Finset.mul_sum, nsmul_eq_mul]
      ring
    clear_value j
    simp only [h1, Finset.prod_mul_distrib, Finset.prod_const]
    rw [mul_sub, sub_eq_add_neg, Complex.exp_add, h2, Complex.exp_nat_mul, mulVec_add,
      dotProduct_add, mul_add, neg_add, Complex.exp_add]
    ring
end GlobalTheory.ThetaTranslJet
